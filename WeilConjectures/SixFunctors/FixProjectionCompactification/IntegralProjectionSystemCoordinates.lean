/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FixProjectionCompactification.ProjectionCompactificationData
public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.RefinementProjection.RefinementProjectionCounit
import WeilConjectures.SixFunctors.FixProjectionCompactification.IntegralSupportReductionNormalization
import WeilConjectures.SixFunctors.FixProjectionCompactification.IntegralProjectionReductionNormalization

/-! # Coordinates for individual integral projection and refinement maps

Source: prop-sf-pf-coherence.proof.md, compactification-independence sentence, and
integral compactification system realization, generator intertwining.
(blueprint: lem-sf-integral-projection-system-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.FixProjectionCompactification
open IntegralSystemRealization

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence

private theorem realizeCoefficientMap
    {A B : Type*} [Category A] [Category B] {R : A ⥤ B} {L : B ⥤ A}
    (adj : R ⊣ L) {a b : A} {M N : B} (s : R.obj a ≅ M) (t : R.obj b ≅ N)
    (ea : L.obj (R.obj a) ≅ a) (eb : L.obj (R.obj b) ≅ b)
    (ha : ea.inv = adj.unit.app a) (hb : eb.inv = adj.unit.app b)
    (p : a ⟶ b) (v : M ⟶ N) (h : s.hom ≫ v = R.map p ≫ t.hom) :
    L.map v ≫ (L.mapIso t.symm ≪≫ eb).hom =
      (L.mapIso s.symm ≪≫ ea).hom ≫ p := by
  have hn := adj.unit.naturality p
  change p ≫ adj.unit.app b = adj.unit.app a ≫ L.map (R.map p) at hn
  rw [← ha, ← hb] at hn
  have hn' : L.map (R.map p) ≫ eb.hom = ea.hom ≫ p := by
    apply (cancel_epi ea.inv).mp
    calc
      ea.inv ≫ (L.map (R.map p) ≫ eb.hom) = (p ≫ eb.inv) ≫ eb.hom := by
        rw [← Category.assoc, ← hn]
      _ = ea.inv ≫ (ea.hom ≫ p) := by simp
  have h' : v ≫ t.inv = s.inv ≫ R.map p := by
    apply (cancel_epi s.hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using congrArg (fun k ↦ k ≫ t.inv) h
  change L.map v ≫ (L.map t.inv ≫ eb.hom) = (L.map s.inv ≫ ea.hom) ≫ p
  calc
    L.map v ≫ (L.map t.inv ≫ eb.hom) = L.map (v ≫ t.inv) ≫ eb.hom := by
      rw [Functor.map_comp, Category.assoc]
    _ = L.map (s.inv ≫ R.map p) ≫ eb.hom := by rw [h']
    _ = L.map s.inv ≫ (L.map (R.map p) ≫ eb.hom) := by
      rw [Functor.map_comp, Category.assoc]
    _ = (L.map s.inv ≫ ea.hom) ≫ p := by rw [hn', Category.assoc]

private theorem whiskeredCoefficientSquare
    {A B : Type*} [Category A] [Category B] (F G : A ⥤ B)
    {M N : A} {X Y : B} (s : X ⟶ F.obj N) (t : Y ⟶ G.obj N)
    (p : X ⟶ Y) (qM : F.obj M ⟶ G.obj M) (qN : F.obj N ⟶ G.obj N)
    (v : N ⟶ M) (hn : F.map v ≫ qM = qN ≫ G.map v) (h : s ≫ qN = p ≫ t) :
    (s ≫ F.map v) ≫ qM = p ≫ (t ≫ G.map v) := by
  rw [Category.assoc, hn, ← Category.assoc, h, Category.assoc]

private theorem tensorCoefficientSquare
    {A B C : Type*} [Category A] [Category B] [Category C]
    (T : A × B ⥤ C) {Xd Xc Ud Uc : A} (N : B) {Zd Zc : C}
    (sd : Xd ⟶ Ud) (sc : Xc ⟶ Uc) (p : Xd ⟶ Xc) (q : Ud ⟶ Uc)
    (ed : Zd ⟶ T.obj (Xd, N)) (ec : Zc ⟶ T.obj (Xc, N)) (rho : Zd ⟶ Zc)
    (h : sd ≫ q = p ≫ sc)
    (hn : rho ≫ ec = ed ≫ T.map (Prod.mkHom p (𝟙 N))) :
    (ed ≫ T.map (Prod.mkHom sd (𝟙 N))) ≫ T.map (Prod.mkHom q (𝟙 N)) =
      rho ≫ (ec ≫ T.map (Prod.mkHom sc (𝟙 N))) := by
  rw [Category.assoc, ← T.map_comp]
  simp only [CategoryTheory.prod_comp, Category.comp_id]
  rw [h]
  have hp : Prod.mkHom (p ≫ sc) (𝟙 N) =
      Prod.mkHom p (𝟙 N) ≫ Prod.mkHom sc (𝟙 N) := by
    simp only [CategoryTheory.prod_comp, Category.comp_id]
  rw [hp, T.map_comp, ← Category.assoc, ← hn, Category.assoc]

private theorem firstTensorCoefficientNaturality
    {A B : Type*} [Category A] [Category B] (T : A ⥤ A ⥤ A)
    (F : A ⥤ B) (U : B × B ⥤ B)
    (e : Functor.uncurry.obj T ⋙ F ≅ (F.prod F) ⋙ U)
    {X Y : A} (f : X ⟶ Y) (L : A) :
    F.map ((T.map f).app L) ≫ e.hom.app (Y, L) =
      e.hom.app (X, L) ≫ U.map (Prod.mkHom (F.map f) (𝟙 (F.obj L))) := by
  have h := e.hom.naturality (Prod.mkHom f (𝟙 L))
  change F.map ((T.map f).app L ≫ (T.obj Y).map (𝟙 L)) ≫ e.hom.app (Y, L) =
    e.hom.app (X, L) ≫ U.map (Prod.mkHom (F.map f) (F.map (𝟙 L))) at h
  rw [(T.obj Y).map_id L, Category.comp_id, F.map_id L] at h
  exact h

private theorem systemComparison_naturality
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    {M N : System C.l E X} (v : M ⟶ N) :
    (Operations.shriek C.l E o d.i ⋙ Operations.push C.l E o d.g).map v ≫
        RefinementProjection.systemComparison C.l E D o z r N =
      RefinementProjection.systemComparison C.l E D o z r M ≫
        (Operations.shriek C.l E o c.i ⋙ Operations.push C.l E o c.g).map v := by
  let := c.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
  let := d.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
  let Jc := Operations.shriek C.l E o c.i
  let Jd := Operations.shriek C.l E o d.i
  let Sd := Operations.push C.l E o d.g
  let Sr := Operations.push C.l E o r.hom
  let idIso := z.canonicalBridge.push C.l E (𝟙 X) ≪≫
    SemilinearProperOpen.sId (scalarRings C.l E) (scalarTransitions C.l E) X
  let γ := z.properOpen.gamma c.i (𝟙 X) r.hom d.i
    (r.i_hom.trans (Category.id_comp _).symm)
  let a : Jd ⟶ Jc ⋙ Sr :=
    (Functor.leftUnitor Jd).inv ≫ whiskerRight idIso.inv Jd ≫ γ
  let q : Jd ⋙ Sd ⟶ Jc ⋙ Operations.push C.l E o c.g :=
    whiskerRight a Sd ≫ (Functor.associator Jc Sr Sd).hom ≫
      whiskerLeft Jc (z.compositors.pushComp C.l E r.hom d.g).hom ≫
      whiskerLeft Jc (eqToIso (congrArg (Operations.push C.l E o) r.hom_g)).hom
  simpa only [q, a, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.leftUnitor_inv_app, Functor.associator_hom_app, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc, RefinementProjection.systemComparison,
    Jc, Jd, Sd, Sr, idIso, γ] using q.naturality v

/-- Realize each individual projection and each directed refinement map in the supplied
operation coordinates. This asserts no equality between the two routes around a square.

Source: prop-sf-pf-coherence.proof.md, compactification-independence sentence;
lem-sf-integral-projection-refinement-square, proof steps 1 and 3.
(blueprint: lem-sf-integral-projection-system-coordinates).

Proof: integral residue Tor gives common finite reduction bounds for both constructible
inputs. Pullback, tensor, proper image and quasi-compact open extension preserve the
normalized constructible domains; choose their compatible etale-origin witnesses.
Finite-type schemes over the field are Noetherian, so the opens used here are
quasi-compact. Apply the simultaneous compactification-system realization to the two
expressions S_p J_j(K tensor P_f L) and (S_p J_j K) tensor L, for each compactification.
Their comparisons give beta and alpha, respectively, followed by the operation datum's
prescribed support, pullback and tensor identifications. The normalization by the entire
reduction-limit counit makes these the same identifications for every occurrence of
an expression, rather than choices inferred from finite evaluations.
For the first equation paste the generator-intertwining squares for the proper counit,
proper tensor comparison, normalized open tensor map and inverse pullback compositor.
The open-adjunction normalization and the datum's tensor-pullback normalization identify
the result with projectionComponent. For a refinement paste instead the squares for
identity direct image, proper/open interchange, and the direct-image compositor. The
support-projection normalization identifies this directed map with the inverse datum
comparison. Applying the tensor context gives the second comparison equation with
exactly the same alpha. The compactification comparison and its tensor-input instance
use the same construction. These are equalities of individual arrows under realization;
the system counit/projection equation is not used. Identity refinements use the triangle
identity; zero inputs and empty opens use the unique maps of zero objects. -/
theorem integralProjectionSystemCoordinates
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left)
    (hL : finiteTorConstructibleIntegral C.l E Y.obj.left L.obj) :
    let M := (calculus C.l E X.obj.left).reduction.obj K.obj
    let N := (calculus C.l E Y.obj.left).reduction.obj L.obj
    let T := (calculus C.l E X.obj.left).systemClosed.tensor.obj
      (M, (pull C.l E f.hom.left).obj N)
    let F := (sfIntegralConstructible C.l E Y.obj.left).ι
    let R := coefficientSequenceLimit C.l E Y.obj.left
    let U := fun c : Compactification f.hom.left ↦
      (calculus C.l E Y.obj.left).systemClosed.tensor.obj
        ((Operations.push C.l E o c.g).obj ((Operations.shriek C.l E o c.i).obj M), N)
    let V := fun c : Compactification f.hom.left ↦
      (Operations.push C.l E o c.g).obj ((Operations.shriek C.l E o c.i).obj T)
    let A := fun c : Compactification f.hom.left ↦
      ((S.higher.integralTensor Y).obj ((S.higher.integral.support f c).obj K)).obj L
    let B := fun c : Compactification f.hom.left ↦
      (S.higher.integral.support f c).obj
        (((S.higher.integralTensor X).obj K).obj ((S.higher.integral.pull f).obj L))
    ∃ (alpha : ∀ c, R.obj (U c) ≅ F.obj (A c))
      (beta : ∀ c, R.obj (V c) ≅ F.obj (B c)),
      (∀ c, R.map (compactificationProjection C.l E o z.compositors z.openComparisons c M N) ≫
          (beta c).hom = (alpha c).hom ≫
            F.map ((S.higher.integralExchange (identitySquare f c)).projectionComponent K L)) ∧
      (∀ (c d : Compactification f.hom.left) (r : c.Refinement d),
        R.map (RefinementProjection.systemComparison C.l E D o z r T) ≫ (beta c).hom =
          (beta d).hom ≫ F.map ((S.higher.integral.comparison f c d).inv.app
            (((S.higher.integralTensor X).obj K).obj ((S.higher.integral.pull f).obj L))) ∧
        R.map ((calculus C.l E Y.obj.left).systemClosed.tensor.map
          (Prod.mkHom (RefinementProjection.systemComparison C.l E D o z r M) (𝟙 N))) ≫
            (alpha c).hom = (alpha d).hom ≫
              F.map (((S.higher.integralTensor Y).map
                ((S.higher.integral.comparison f c d).inv.app K)).app L)) := by
  have hsupport := integralSupportReductionNormalization D C E n hn S hl o z
    (X := X) (Y := Y) f
  have hi := hsupport.1
  have hr := hsupport.2
  let N := (calculus C.l E Y.obj.left).reduction.obj L.obj
  let W := ((S.higher.integralTensor X).obj K).obj ((S.higher.integral.pull f).obj L)
  let F := (sfIntegralConstructible C.l E Y.obj.left).ι
  let R := (calculus C.l E Y.obj.left).reduction
  let A := fun c : Compactification f.hom.left ↦
    ((S.higher.integralTensor Y).obj ((S.higher.integral.support f c).obj K)).obj L
  let B := fun c : Compactification f.hom.left ↦ (S.higher.integral.support f c).obj W
  let := hi
  have hs (c : Compactification f.hom.left) :
      IsIso (Coordinates.sourceMap D C E S.higher hl o z f c K L) := by
    let a := Coordinates.datumTensorReduction D C E S.higher hl Y
      ((S.higher.integral.support f c).obj K) L
    let b := (calculus C.l E Y.obj.left).systemClosed.tensor.mapIso
      (Iso.prod (asIso (Coordinates.supportReduction D C E S.higher hl o z f c K))
        (Iso.refl N))
    change IsIso (a.hom ≫ b.hom)
    exact inferInstanceAs (IsIso (a ≪≫ b).hom)
  have ht (c : Compactification f.hom.left) :
      IsIso (Coordinates.targetMap D C E S.higher hl o z f c K L) := by
    dsimp only [Coordinates.targetMap]
    infer_instance
  let := hs
  let := ht
  let s := fun c ↦ asIso (Coordinates.sourceMap D C E S.higher hl o z f c K L)
  let t := fun c ↦ asIso (Coordinates.targetMap D C E S.higher hl o z f c K L)
  let alpha := fun c ↦ (coefficientSequenceLimit C.l E Y.obj.left).mapIso (s c).symm ≪≫
    Coordinates.reconstruction D C E Y.obj.left (A c)
  let beta := fun c ↦ (coefficientSequenceLimit C.l E Y.obj.left).mapIso (t c).symm ≪≫
    Coordinates.reconstruction D C E Y.obj.left (B c)
  refine ⟨alpha, beta, ?_, ?_⟩
  · intro c
    exact realizeCoefficientMap (calculus C.l E Y.obj.left).adjunction (s c) (t c)
      (Coordinates.reconstruction D C E Y.obj.left (A c))
      (Coordinates.reconstruction D C E Y.obj.left (B c)) rfl rfl _ _
      (integralProjectionReductionNormalization D C E n hn S hl o z f c K L hL)
  · intro c d r
    constructor
    · apply realizeCoefficientMap (calculus C.l E Y.obj.left).adjunction (t d) (t c)
        (Coordinates.reconstruction D C E Y.obj.left (B d))
        (Coordinates.reconstruction D C E Y.obj.left (B c)) rfl rfl
      change Coordinates.targetMap D C E S.higher hl o z f d K L ≫ _ =
        R.map _ ≫ Coordinates.targetMap D C E S.higher hl o z f c K L
      dsimp only [Coordinates.targetMap]
      exact whiskeredCoefficientSquare
        (Operations.shriek C.l E o d.i ⋙ Operations.push C.l E o d.g)
        (Operations.shriek C.l E o c.i ⋙ Operations.push C.l E o c.g)
        _ _ _ _ _ (Coordinates.inputReduction D C E S.higher hl o z f K L).inv
        (systemComparison_naturality D C E o z r _) (hr c d r W)
    · apply realizeCoefficientMap (calculus C.l E Y.obj.left).adjunction (s d) (s c)
        (Coordinates.reconstruction D C E Y.obj.left (A d))
        (Coordinates.reconstruction D C E Y.obj.left (A c)) rfl rfl
      change Coordinates.sourceMap D C E S.higher hl o z f d K L ≫ _ =
        R.map _ ≫ Coordinates.sourceMap D C E S.higher hl o z f c K L
      dsimp only [Coordinates.sourceMap]
      let T := (calculus C.l E Y.obj.left).systemClosed.tensor
      have hn := firstTensorCoefficientNaturality (S.higher.integralTensor Y) (F ⋙ R) T
        (Coordinates.datumTensorReductionIso D C E S.higher hl Y)
        ((S.higher.integral.comparison f c d).inv.app K) L
      exact tensorCoefficientSquare T N _ _ _ _ _ _ _ (hr c d r K) hn

end WeilConjectures.FixProjectionCompactification
