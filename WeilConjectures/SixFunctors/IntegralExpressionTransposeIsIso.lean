/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralExpressionRecursionData
import WeilConjectures.AlgebraicGeometry.SfIntegralConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.ProEtaleBoundedConstructibleTriangulated

/-! # Invertibility of the expression coefficient transpose -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField
  WeilConjectures.integralDerivedPullback WeilConjectures.integralCompletedTensor
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization.ExpressionRecursion
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem normalized_of_iso {V : Scheme.{u}}
    {A B : coefficientSequenceDerived.{u, u} l E V} (e : A ≅ B)
    (hA : IsNormalizedCoefficientSequence l E V A) :
    IsNormalizedCoefficientSequence l E V B := by
  intro m n h P
  let F := coefficientSequenceDerivedEvaluation.{u, u} l E V m
  let G := coefficientSequenceDerivedEvaluation.{u, u} l E V n
  let U := normalizedDVRRes l E V h
  let τ := coefficientSequenceDerivedTransition.{u, u} l E V h
  constructor
  · intro f g hfg
    apply (cancel_epi (G.map e.hom)).1
    apply (hA h P).1
    simp only [Functor.map_comp]
    change τ.app A ≫ (G ⋙ U).map e.hom ≫ U.map f =
      τ.app A ≫ (G ⋙ U).map e.hom ≫ U.map g
    change τ.app B ≫ U.map f = τ.app B ≫ U.map g at hfg
    rw [← τ.naturality_assoc e.hom, ← τ.naturality_assoc e.hom, hfg]
  · intro f
    obtain ⟨g, hg⟩ := (hA h P).2 (F.map e.hom ≫ f)
    refine ⟨G.map e.inv ≫ g, ?_⟩
    apply (cancel_epi (F.map e.hom)).1
    rw [← Category.assoc, τ.naturality e.hom]
    simp only [Functor.comp_map, Category.assoc, Functor.map_comp]
    rw [← U.map_comp_assoc, ← G.map_comp, Iso.hom_inv_id, G.map_id, U.map_id,
      Category.id_comp]
    exact hg

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem bounds_of_iso {W : Scheme.{u}} {M N : System l E W}
    (e : M ≅ N) (hM : LevelBounds l E W M) : LevelBounds l E W N := by
  obtain ⟨a, b, c, d, hab, hcd, hlevels⟩ := hM
  refine ⟨a, b, c, d, hab, hcd, fun n ↦ ?_⟩
  let Rn := Padic.coefficientExtensionRing l E (n + 1)
  let A : proEtaleDerivedCategory W Rn :=
    (coefficientSequenceDerivedEvaluation l E W n).obj M
  let B : proEtaleDerivedCategory W Rn :=
    (coefficientSequenceDerivedEvaluation l E W n).obj N
  let q : A ≅ B := (coefficientSequenceDerivedEvaluation l E W n).mapIso e
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W) :=
    (proEtale_bounded_constructible_isTriangulated W Rn).1
  have hc : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W B :=
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W).prop_of_iso
      q (hlevels n).1
  have hb : proEtaleCohomologicalSupport (Y := W) (A := Rn) B ⊆ Set.Icc a b := by
    intro i hi
    apply (hlevels n).2.1
    intro hz
    exact hi (hz.of_iso ((DerivedCategory.homologyFunctor
      (proEtaleRingModules W (proEtaleConstantRing W Rn)) i).mapIso q).symm)
  have ht : HasProEtaleTorAmplitude W Rn B c d := by
    refine ⟨(hlevels n).2.2.1, ?_⟩
    rintro L P ⟨r⟩ f hf hP A i hi
    exact (hlevels n).2.2.2 L P ⟨r ≪≫ q.symm⟩ f hf hP A i hi
  exact ⟨hc, hb, ht⟩

private theorem origins_of_iso {W : Scheme.{u}} {M N : System l E W}
    (e : M ≅ N) (q : Origins l E W M) : Nonempty (Origins l E W N) := by
  refine ⟨{
    level := q.level
    origin := q.origin
    etaleTransition := q.etaleTransition
    fixedTransition := q.fixedTransition
    originSquare := q.originSquare
    evaluation := fun n ↦ q.evaluation n ≪≫
      (coefficientSequenceDerivedEvaluation.{u, u} l E W n).mapIso e
    transitionSquare := ?_ }⟩
  intro n
  erw [q.transitionSquare]
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc]
  rw [(coefficientSequenceDerivedTransition.{u, u} l E W (Nat.le_succ n)).naturality_assoc e.hom]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc, ← Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]


private theorem good_of_iso {W : Scheme.{u}} {M N : System l E W}
    (e : M ≅ N) (hM : Good l E W M) : Good l E W N := by
  refine ⟨normalized_of_iso l E e hM.1, bounds_of_iso l E e hM.2.1, ?_⟩
  obtain ⟨q⟩ := hM.2.2
  exact origins_of_iso l E e q

private theorem unary_step {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (d : Primitives l E D o) (rec : Reconstruction l E D)
    {U V : Over (Spec (.of D.k))} (a : Unary _ U V)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (H : Integral l E U.left) (M : System l E U.left)
    (r : (calculus l E U.left).reduction.obj H ⟶ M) [IsIso r]
    (hH : sfIntegralConstructible l E U.left H)
    (hAM : Good l E V.left ((a.system l E o).obj M)) :
    sfIntegralConstructible l E V.left ((a.integral l E).obj H) ∧
      IsIso ((d.unaryReduction a).app H ≫ (a.system l E o).map r) := by
  have hA := good_of_iso l E ((a.system l E o).mapIso (asIso r)).symm hAM
  let K : (basicUnaryDomain l E U.left V.left (a.system l E o)).FullSubcategory :=
    ⟨H, hH, rec.reduction U H hH, hA⟩
  have hc := (sfIntegralConstructible l E V.left).prop_of_iso ((d.unary a).app K)
    (rec.limit V _ hA)
  have := rec.counit V _ hA
  have : IsIso ((d.unaryReduction a).app H) := by
    rw [d.unaryTranspose a K]
    infer_instance
  exact ⟨hc, inferInstance⟩

private theorem tensor_step {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (d : Primitives l E D o) (rec : Reconstruction l E D)
    (W : Over (Spec (.of D.k))) [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    (H J : Integral l E W.left) (M N : System l E W.left)
    (r : (calculus l E W.left).reduction.obj H ⟶ M)
    (s : (calculus l E W.left).reduction.obj J ⟶ N) [IsIso r] [IsIso s]
    (hH : sfIntegralConstructible l E W.left H)
    (hJ : sfIntegralConstructible l E W.left J)
    (hMN : Good l E W.left ((calculus l E W.left).systemClosed.tensor.obj (M, N))) :
    sfIntegralConstructible l E W.left ((integralCompletedTensor l E W.left).obj (H, J)) ∧
      IsIso ((d.tensorReduction W).app (H, J) ≫
        (calculus l E W.left).systemClosed.tensor.map (Prod.mkHom r s)) := by
  have ht := good_of_iso l E
    ((calculus l E W.left).systemClosed.tensor.mapIso ((asIso r).prod (asIso s))).symm hMN
  let K : (basicTensorDomain l E W.left).FullSubcategory :=
    ⟨(H, J), hH, hJ, rec.reduction W H hH, rec.reduction W J hJ, ht⟩
  have hc := (sfIntegralConstructible l E W.left).prop_of_iso ((d.tensor W).app K)
    (rec.limit W _ ht)
  have := rec.counit W _ ht
  have : IsIso ((d.tensorReduction W).app (H, J)) := by
    rw [d.tensorTranspose W K]
    infer_instance
  have : IsIso (Prod.mkHom r s) := ((asIso r).prod (asIso s)).isIso_hom
  exact ⟨hc, inferInstance⟩

private theorem coefficientMap_constructible_isIso {D : FiniteFieldDatum.{u}}
    {o : Operations l E} (d : Primitives l E D o) (rec : Reconstruction l E D)
    {I : Type u} {X : I → Over (Spec (.of D.k))}
    {W : Over (Spec (.of D.k))} (e : Expression _ I X W) :
    ∀ (g : e.geometric) (K : ∀ i, Integral l E (X i).left), e.domain l E o K →
      sfIntegralConstructible l E W.left
        ((e.evaluate (integralInterpretation l E)).obj K) ∧
      IsIso (coefficientMap l E d e g K) := by
  induction e with
  | var i =>
    intro g K hK
    exact ⟨(hK.1 i).1, inferInstanceAs (IsIso (𝟙 _))⟩
  | @pull U V f e ih =>
    intro g K hK
    have h := ih g.2.2.2.2.2 K ⟨hK.1, hK.2.2⟩
    let := g.1
    let := g.2.1
    let := (geometricRoot e g.2.2.2.2.2).1
    let := (geometricRoot e g.2.2.2.2.2).2
    let := h.2
    exact unary_step l E d rec (.pull f g.2.2.1 g.2.2.2.1 g.2.2.2.2.1)
      _ _ (coefficientMap l E d e g.2.2.2.2.2 K) h.1 hK.2.1
  | @push U V f hp e ih =>
    intro g K hK
    have h := ih g.2.2 K ⟨hK.1, hK.2.2⟩
    let := g.1
    let := g.2.1
    let := (geometricRoot e g.2.2).1
    let := (geometricRoot e g.2.2).2
    let := h.2
    exact unary_step l E d rec (.push f hp) _ _ (coefficientMap l E d e g.2.2 K)
      h.1 hK.2.1
  | @shriek U V j hj hqc e ih =>
    intro g K hK
    have h := ih g.2.2 K ⟨hK.1, hK.2.2⟩
    let := hj
    let := g.1
    let := g.2.1
    let := (geometricRoot e g.2.2).1
    let := (geometricRoot e g.2.2).2
    let := h.2
    exact unary_step l E d rec (.shriek j hj hqc) _ _ (coefficientMap l E d e g.2.2 K)
      h.1 hK.2.1
  | @tensor W e t ih jt =>
    intro g K hK
    have h := ih g.2.2.1 K ⟨hK.1, hK.2.2.1⟩
    have k := jt g.2.2.2 K ⟨hK.1, hK.2.2.2⟩
    let := g.1
    let := g.2.1
    let := h.2
    let := k.2
    exact tensor_step l E d rec W _ _ _ _
      (coefficientMap l E d e g.2.2.1 K) (coefficientMap l E d t g.2.2.2 K)
      h.1 k.1 hK.2.1
  | @compactSupport U V f c e ih =>
    intro g K hK
    have h := ih g.2.2.2.2.2 K ⟨hK.1, hK.2.2.1⟩
    let Z : Over (Spec (.of D.k)) := Over.mk (c.g ≫ V.hom)
    let j : U ⟶ Z := Over.homMk c.i
      ((Category.assoc c.i c.g V.hom).symm.trans
        ((congrArg (fun z ↦ z ≫ V.hom) c.comm.symm).trans f.w))
    let p : Z ⟶ V := Over.homMk c.g rfl
    let := g.1
    let := g.2.1
    let := (geometricRoot e g.2.2.2.2.2).1
    let := (geometricRoot e g.2.2.2.2.2).2
    let : LocallyOfFiniteType Z.hom := inferInstanceAs
      (LocallyOfFiniteType (c.g ≫ V.hom))
    let : QuasiCompact Z.hom := inferInstanceAs (QuasiCompact (c.g ≫ V.hom))
    let := h.2
    have hj := unary_step l E d rec
      (.shriek j (inferInstance : IsOpenImmersion c.i)
        (compactOpenQuasiCompact c g.2.2.2.2.1)) _ _
      (coefficientMap l E d e g.2.2.2.2.2 K) h.1 hK.2.2.2
    let rj :=
      (d.unaryReduction (.shriek j (inferInstance : IsOpenImmersion c.i)
        (compactOpenQuasiCompact c g.2.2.2.2.1))).app
          ((e.evaluate (integralInterpretation l E)).obj K) ≫
      (Operations.shriek l E o c.i).map (coefficientMap l E d e g.2.2.2.2.2 K)
    have : IsIso rj := hj.2
    exact unary_step l E d rec (.push p (inferInstance : IsProper c.g)) _ _
      rj hj.1 hK.2.1

/-- The explicitly transposed coefficient map is invertible on the expression domain.
No recursive equations or compactification normalization are asserted here.
Source: fix-prop-coherence.proof.md, coefficient-comparison sentence; the extracted
expression-recursion proof, steps 1--7
(blueprint: lem-sf-integral-expression-transpose-is-iso).

Proof: induct on the finite expression. At a leaf the transpose is the actual unit,
which Reconstruction.unit makes invertible. For a unary node, let M be the child
system and H its integral value. The induction hypothesis identifies H with L M.
Reconstruction.limit and the child Good condition show L M is constructible;
Reconstruction.reduction gives Good (R L M), and Reconstruction.counit identifies
R L M with M. Transport Good along this isomorphism, and through the unary
functor, to obtain the required basicUnaryDomain witness at L M. The given d_A
and inverse of L A(e_M) are isomorphisms there. Naturality of r_A at the child
transpose and the assumed primitive transpose identity show the parent transpose
is A_int of the child transpose followed by the inverse of a_A(M): apply the
adjunction hom-set equivalence, use counit naturality at A(e_M), and cancel the
child transpose. This is a composite of isomorphisms. For tensor do the same with
the pair of child transposes and counits; the tensor functor preserves that pair
of isomorphisms. For compact support apply the unary argument first to the open
extension and then to proper image. The expression domain retains the intermediate
open Good condition and the geometric hypotheses make its compactification scheme
finite type. No invertibility on objects outside the stated domains is needed. -/
theorem transposeComparison_isIso (D : FiniteFieldDatum.{u})
    (o : Operations l E) (d : Primitives l E D o) (rec : Reconstruction l E D)
    {I : Type u} {X : I → Over (Spec (.of D.k))}
    {W : Over (Spec (.of D.k))} (e : Expression _ I X W) (g : e.geometric)
    (K : (e.domain l E o).FullSubcategory) :
    IsIso ((transposeComparison l E d e g).app K) := by
  have h := coefficientMap_constructible_isIso l E d rec e g K.obj K.property
  let := (geometricRoot e g).1
  let := (geometricRoot e g).2
  have := rec.unit W _ h.1
  have := h.2
  simp only [transposeComparison, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, coefficientTransformation_app]
  change IsIso ((calculus l E W.left).adjunction.unit.app
    ((e.evaluate (integralInterpretation l E)).obj K.obj) ≫
      (coefficientSequenceLimit l E W.left).map (coefficientMap l E d e g K.obj))
  infer_instance

/-- The comparison is the inverse of the explicit adjunction transpose.
The preceding theorem supplies only its invertibility, hence determines its
inverse uniquely; no arbitrary object is selected from an existence statement.
Source: fix-prop-coherence, expression counit substitution
(blueprint: lem-sf-integral-expression-transpose-is-iso). -/
def canonicalComparisons (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (d : Primitives l E D o) (rec : Reconstruction l E D) : Comparisons l E D o := by
  intro I _ X W e g
  let t := transposeComparison l E d e g
  haveI : ∀ K, IsIso (t.app K) := fun K ↦ transposeComparison_isIso l E D o d rec e g K
  haveI : IsIso t := NatIso.isIso_of_isIso_app t
  exact (asIso t).symm

/-- The canonical comparison satisfies the prescribed whole-system coefficient identity.
Proof: its inverse is the explicit transpose, and the inverse adjunction hom-set
equivalence sends that transpose back to the coefficient map.
Source: fix-prop-coherence, counit substitution
(blueprint: lem-sf-integral-expression-transpose-is-iso). -/
theorem canonicalComparisons_coefficient (D : FiniteFieldDatum.{u})
    (o : Operations l E) (d : Primitives l E D o) (rec : Reconstruction l E D)
    {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
    {W : Over (Spec (.of D.k))} (e : Expression _ I X W) (g : e.geometric)
    (K : (e.domain l E o).FullSubcategory) :
    coefficientMap l E d e g K.obj =
      (calculus l E W.left).reduction.map
        ((canonicalComparisons l E D o d rec e g).inv.app K) ≫
      (calculus l E W.left).adjunction.counit.app
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) := by
  exact (transposeComparison_coefficient l E d e g K).symm

end WeilConjectures.IntegralSystemRealization.ExpressionRecursion
