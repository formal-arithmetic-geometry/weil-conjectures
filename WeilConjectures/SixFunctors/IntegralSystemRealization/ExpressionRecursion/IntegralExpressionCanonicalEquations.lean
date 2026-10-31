/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.ExpressionRecursion.IntegralExpressionTransposeIsIso
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated

/-! # Equations for the canonical expression comparison -/

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
universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization.ExpressionRecursion
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem unary_transport
    {C : Type u₁} {S : Type u₂} {D : Type u₃} {T : Type u₄}
    [Category.{v₁} C] [Category.{v₂} S] [Category.{v₃} D] [Category.{v₄} T]
    (R : C ⥤ S) (L : S ⥤ C) (R' : D ⥤ T) (L' : T ⥤ D)
    (adj' : R' ⊣ L') (A : S ⥤ T) (B : C ⥤ D)
    (r : B ⋙ R' ⟶ R ⋙ A) (M : S) (H : C)
    (c : L.obj M ≅ H) (b : L'.obj (A.obj M) ≅ B.obj H)
    (δ : L'.obj (A.obj (R.obj (L.obj M))) ≅ B.obj (L.obj M))
    (ε : R.obj (L.obj M) ⟶ M) [IsIso ε]
    (hδ : r.app (L.obj M) = R'.map δ.inv ≫ adj'.counit.app (A.obj (R.obj (L.obj M))))
    (hb : R'.map b.inv ≫ adj'.counit.app (A.obj M) =
      r.app H ≫ A.map (R.map c.inv ≫ ε)) :
    b.hom = inv (L'.map (A.map (ε))) ≫ δ.hom ≫ B.map c.hom := by
  let q := B.map c.inv ≫ δ.inv ≫ L'.map (A.map (ε))
  have hi : b.inv = q := by
    apply (adj'.homEquiv _ _).symm.injective
    change R'.map b.inv ≫ adj'.counit.app _ = R'.map q ≫ adj'.counit.app _
    rw [hb]
    dsimp only [q]
    simp only [Functor.map_comp, Category.assoc]
    change r.app H ≫ A.map (R.map c.inv) ≫ A.map (ε) =
      R'.map (B.map c.inv) ≫ R'.map δ.inv ≫
        (L' ⋙ R').map (A.map (ε)) ≫ adj'.counit.app (A.obj M)
    erw [adj'.counit.naturality (A.map (ε))]
    simp only [Functor.comp_obj, Functor.id_map]
    rw [← Category.assoc (R'.map δ.inv), ← hδ]
    have hn := r.naturality c.inv
    simp only [Functor.comp_map] at hn
    rw [← Category.assoc (R'.map (B.map c.inv)), hn, Category.assoc]
  have hid : q ≫ (inv (L'.map (A.map (ε))) ≫ δ.hom ≫ B.map c.hom) = 𝟙 _ := by
    dsimp only [q]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
      ← Functor.map_comp, Iso.inv_hom_id]
    exact B.map_id _
  rw [← hi] at hid
  simpa using ((Iso.inv_comp_eq b).mp hid).symm

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


private theorem invzero_eq_inv {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y : C} (f : X ⟶ Y) [IsIso f] : GeneratorReduction.inverseOrZero f = inv f := by
  simp only [GeneratorReduction.inverseOrZero, dif_pos (inferInstance : IsIso f)]

private theorem unary_step (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (d : Primitives l E D o) (rec : Reconstruction l E D)
    {U V : Over (Spec (.of D.k))} (a : Unary _ U V)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (M : System l E U.left) (hM : Good l E U.left M)
    (hA : Good l E V.left ((a.system l E o).obj M))
    (H : Integral l E U.left) (c : (coefficientSequenceLimit l E U.left).obj M ≅ H)
    (b : (coefficientSequenceLimit l E V.left).obj ((a.system l E o).obj M) ≅
      (a.integral l E).obj H)
    (hb : (calculus l E V.left).reduction.map b.inv ≫
        (calculus l E V.left).adjunction.counit.app ((a.system l E o).obj M) =
      (d.unaryReduction a).app H ≫ (a.system l E o).map
        ((calculus l E U.left).reduction.map c.inv ≫
          (calculus l E U.left).adjunction.counit.app M)) :
    ∃ h : basicUnaryDomain l E U.left V.left (a.system l E o)
        ((coefficientSequenceLimit l E U.left).obj M),
      b.hom = unaryA l E d a M h ≫ (a.integral l E).map c.hom ∧
        IsIso (unaryA l E d a M h) := by
  have := rec.counit U M hM
  let ρ := asIso ((calculus l E U.left).adjunction.counit.app M)
  have h : basicUnaryDomain l E U.left V.left (a.system l E o)
      ((coefficientSequenceLimit l E U.left).obj M) :=
    ⟨rec.limit U M hM, rec.reduction U _ (rec.limit U M hM),
      good_of_iso l E ((a.system l E o).mapIso ρ.symm) hA⟩
  refine ⟨h, ?_, ?_⟩
  · have he := unary_transport
      (calculus l E U.left).reduction (coefficientSequenceLimit l E U.left)
      (calculus l E V.left).reduction (coefficientSequenceLimit l E V.left)
      (calculus l E V.left).adjunction (a.system l E o) (a.integral l E)
      (d.unaryReduction a) M H c b ((d.unary a).app ⟨_, h⟩)
      ((calculus l E U.left).adjunction.counit.app M) (d.unaryTranspose a ⟨_, h⟩) hb
    simpa only [unaryA, invzero_eq_inv, Iso.app_hom, Category.assoc] using he
  · dsimp only [unaryA]
    rw [invzero_eq_inv]
    infer_instance

private theorem tensor_step (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (d : Primitives l E D o) (rec : Reconstruction l E D)
    (W : Over (Spec (.of D.k))) [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    (M N : System l E W.left) (hM : Good l E W.left M) (hN : Good l E W.left N)
    (hT : Good l E W.left ((calculus l E W.left).systemClosed.tensor.obj (M, N)))
    (H J : Integral l E W.left)
    (c : (coefficientSequenceLimit l E W.left).obj M ≅ H)
    (z : (coefficientSequenceLimit l E W.left).obj N ≅ J)
    (b : (coefficientSequenceLimit l E W.left).obj
        ((calculus l E W.left).systemClosed.tensor.obj (M, N)) ≅
      (integralCompletedTensor l E W.left).obj (H, J))
    (hb : (calculus l E W.left).reduction.map b.inv ≫
        (calculus l E W.left).adjunction.counit.app
          ((calculus l E W.left).systemClosed.tensor.obj (M, N)) =
      (d.tensorReduction W).app (H, J) ≫ (calculus l E W.left).systemClosed.tensor.map
        (Prod.mkHom
          ((calculus l E W.left).reduction.map c.inv ≫
            (calculus l E W.left).adjunction.counit.app M)
          ((calculus l E W.left).reduction.map z.inv ≫
            (calculus l E W.left).adjunction.counit.app N))) :
    ∃ h : basicTensorDomain l E W.left
        ((coefficientSequenceLimit l E W.left).obj M,
          (coefficientSequenceLimit l E W.left).obj N),
      b.hom = tensorA l E d W M N h ≫
        (integralCompletedTensor l E W.left).map (Prod.mkHom c.hom z.hom) ∧
        IsIso (tensorA l E d W M N h) := by
  have := rec.counit W M hM
  have := rec.counit W N hN
  let ρ := asIso ((calculus l E W.left).adjunction.counit.app M)
  let σ := asIso ((calculus l E W.left).adjunction.counit.app N)
  have : IsIso (Prod.mkHom ((calculus l E W.left).adjunction.counit.app M)
      ((calculus l E W.left).adjunction.counit.app N)) := (ρ.prod σ).isIso_hom
  have h : basicTensorDomain l E W.left
      ((coefficientSequenceLimit l E W.left).obj M,
        (coefficientSequenceLimit l E W.left).obj N) :=
    ⟨rec.limit W M hM, rec.limit W N hN,
      rec.reduction W _ (rec.limit W M hM), rec.reduction W _ (rec.limit W N hN),
      good_of_iso l E ((calculus l E W.left).systemClosed.tensor.mapIso
        (ρ.prod σ).symm) hT⟩
  refine ⟨h, ?_, ?_⟩
  · have he := unary_transport
      ((calculus l E W.left).reduction.prod (calculus l E W.left).reduction)
      ((coefficientSequenceLimit l E W.left).prod (coefficientSequenceLimit l E W.left))
      (calculus l E W.left).reduction (coefficientSequenceLimit l E W.left)
      (calculus l E W.left).adjunction (calculus l E W.left).systemClosed.tensor
      (integralCompletedTensor l E W.left) (d.tensorReduction W) (M, N) (H, J)
      (c.prod z) b ((d.tensor W).app ⟨_, h⟩)
      (Prod.mkHom ((calculus l E W.left).adjunction.counit.app M)
        ((calculus l E W.left).adjunction.counit.app N))
      (d.tensorTranspose W ⟨_, h⟩) hb
    simpa only [tensorA, invzero_eq_inv, Iso.app_hom, Iso.prod_hom, Category.assoc] using he
  · dsimp only [tensorA]
    rw [invzero_eq_inv]
    infer_instance

/-- The inverse transposed coefficient comparison has the displayed tree equations.
This is a statement about an already explicitly constructed family; it does not
construct another comparison and asserts no direct compactification agreement.
Source: fix-prop-coherence.proof.md, coefficient-comparison sentence; extracted
expression-recursion proof, steps 2--7
(blueprint: lem-sf-integral-expression-canonical-equations).

Proof: induct on the finite expression, including both tensor children. At a leaf
coefficientMap is identity, so its transpose is the actual unit and its inverse is
the inverse unit. For a unary node let M be the child system. The child comparison
is an isomorphism to its integral value. Reconstruction.limit, reduction, and
counit, together with the Good assumptions at child and parent, give the witness
for basicUnaryDomain at L M. The map L A(e_M) is invertible, so unaryA is an
isomorphism. Take the inverse of the composite unaryA followed by A_int of the
child comparison. Reduce this inverse and compose with the parent counit.
Naturality of r_A and the child coefficient identity move the child inverse past
r_A. Counit naturality at A(e_M), followed by unaryTranspose, identifies the result
with the parent's coefficientMap. Injectivity of the adjunction hom-set equivalence
then identifies this inverse with the explicit transpose. Invert again to get the
claimed equation and include the child induction hypothesis. For tensor use the
same calculation with the pair of child inverses and the tensor of both counits;
tensorTranspose replaces unaryTranspose. Bifunctoriality combines the two induction
hypotheses, with no distinct-variable assumption. For compact support perform the
open step followed by the proper step, retaining the intermediate Good condition
and the finite-type compactification scheme. These are precisely the two domain
witnesses and the composite written in Equations. -/
theorem canonicalComparisons_equations (D : FiniteFieldDatum.{u})
    (o : Operations l E) (d : Primitives l E D o) (rec : Reconstruction l E D)
    {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
    {W : Over (Spec (.of D.k))} (e : Expression _ I X W) (g : e.geometric)
    (K : (e.domain l E o).FullSubcategory) :
    Equations l E d (canonicalComparisons l E D o d rec) e g K := by
  induction e with
  | var i =>
      have := g.1
      have := g.2.1
      have := rec.unit (X i) (K.obj i) (K.property.1 i).1
      change (canonicalComparisons l E D o d rec (.var i) g).hom.app K = _
      have htr : (transposeComparison l E d (.var i) g).app K =
          (calculus l E (X i).left).adjunction.unit.app (K.obj i) := by
        simp [transposeComparison, coefficientTransformation, Expression.realizationSource,
          Expression.realizationTarget, Expression.evaluate, Pi.eval]
      have := transposeComparison_isIso l E D o d rec (.var i) g K
      rw [canonicalComparisons]
      simp only [Iso.symm_hom, asIso_inv, NatIso.isIso_inv_app]
      change inv ((transposeComparison l E d (.var i) g).app K) = _
      simp only [htr]
      exact (invzero_eq_inv (f := (calculus l E (X i).left).adjunction.unit.app (K.obj i))).symm
  | @pull U V f e ih =>
    have := g.1
    have := g.2.1
    have := (geometricRoot e g.2.2.2.2.2).1
    have := (geometricRoot e g.2.2.2.2.2).2
    let K' : (e.domain l E o).FullSubcategory :=
      ⟨K.obj, K.property.1, K.property.2.2⟩
    let c := (canonicalComparisons l E D o d rec e g.2.2.2.2.2).app K'
    let b := (canonicalComparisons l E D o d rec (.pull f e) g).app K
    have hb := (canonicalComparisons_coefficient l E D o d rec (.pull f e) g K).symm
    simp only [coefficientMap] at hb
    rw [canonicalComparisons_coefficient l E D o d rec e g.2.2.2.2.2 K'] at hb
    obtain ⟨h, he, hi⟩ := unary_step l E D o d rec
      (.pull f g.2.2.1 g.2.2.2.1 g.2.2.2.2.1)
      _ (e.admissibleGood l E o _ K'.property.2) K.property.2.1 _ c b hb
    exact ⟨h, he, hi, ih _ K'⟩
  | @push U V f hp e ih =>
    have := g.1
    have := g.2.1
    have := (geometricRoot e g.2.2).1
    have := (geometricRoot e g.2.2).2
    let K' : (e.domain l E o).FullSubcategory :=
      ⟨K.obj, K.property.1, K.property.2.2⟩
    let c := (canonicalComparisons l E D o d rec e g.2.2).app K'
    let b := (canonicalComparisons l E D o d rec (.push f hp e) g).app K
    have hb := (canonicalComparisons_coefficient l E D o d rec (.push f hp e) g K).symm
    simp only [coefficientMap] at hb
    rw [canonicalComparisons_coefficient l E D o d rec e g.2.2 K'] at hb
    obtain ⟨h, he, hi⟩ := unary_step l E D o d rec (.push f hp)
      _ (e.admissibleGood l E o _ K'.property.2) K.property.2.1 _ c b hb
    exact ⟨h, he, hi, ih _ K'⟩
  | @shriek U V f hj hqc e ih =>
    have := hj
    have := g.1
    have := g.2.1
    have := (geometricRoot e g.2.2).1
    have := (geometricRoot e g.2.2).2
    let K' : (e.domain l E o).FullSubcategory :=
      ⟨K.obj, K.property.1, K.property.2.2⟩
    let c := (canonicalComparisons l E D o d rec e g.2.2).app K'
    let b := (canonicalComparisons l E D o d rec (.shriek f hj hqc e) g).app K
    have hb := (canonicalComparisons_coefficient l E D o d rec (.shriek f hj hqc e) g K).symm
    simp only [coefficientMap] at hb
    rw [canonicalComparisons_coefficient l E D o d rec e g.2.2 K'] at hb
    obtain ⟨h, he, hi⟩ := unary_step l E D o d rec (.shriek f hj hqc)
      _ (e.admissibleGood l E o _ K'.property.2) K.property.2.1 _ c b hb
    exact ⟨h, he, hi, ih _ K'⟩
  | @tensor W e t ih jt =>
    have := g.1
    have := g.2.1
    let Ke : (e.domain l E o).FullSubcategory :=
      ⟨K.obj, K.property.1, K.property.2.2.1⟩
    let Kt : (t.domain l E o).FullSubcategory :=
      ⟨K.obj, K.property.1, K.property.2.2.2⟩
    let c := (canonicalComparisons l E D o d rec e g.2.2.1).app Ke
    let z := (canonicalComparisons l E D o d rec t g.2.2.2).app Kt
    let b := (canonicalComparisons l E D o d rec (.tensor e t) g).app K
    have hb := (canonicalComparisons_coefficient l E D o d rec (.tensor e t) g K).symm
    simp only [coefficientMap] at hb
    rw [canonicalComparisons_coefficient l E D o d rec e g.2.2.1 Ke,
      canonicalComparisons_coefficient l E D o d rec t g.2.2.2 Kt] at hb
    obtain ⟨h, he, hi⟩ := tensor_step l E D o d rec W
      _ _ (e.admissibleGood l E o _ Ke.property.2)
      (t.admissibleGood l E o _ Kt.property.2) K.property.2.1 _ _ c z b hb
    exact ⟨h, he, hi, ih _ Ke, jt _ Kt⟩
  | @compactSupport U V f cf e ih =>
    have := g.1
    have := g.2.1
    have := (geometricRoot e g.2.2.2.2.2).1
    have := (geometricRoot e g.2.2.2.2.2).2
    let Z : Over (Spec (.of D.k)) := Over.mk (cf.g ≫ V.hom)
    let j : U ⟶ Z := Over.homMk cf.i
      ((Category.assoc cf.i cf.g V.hom).symm.trans
        ((congrArg (fun z ↦ z ≫ V.hom) cf.comm.symm).trans f.w))
    let p : Z ⟶ V := Over.homMk cf.g rfl
    have : LocallyOfFiniteType Z.hom := inferInstanceAs
      (LocallyOfFiniteType (cf.g ≫ V.hom))
    have : QuasiCompact Z.hom := inferInstanceAs (QuasiCompact (cf.g ≫ V.hom))
    let aj : Unary _ U Z := .shriek j (inferInstance : IsOpenImmersion cf.i)
      (compactOpenQuasiCompact cf g.2.2.2.2.1)
    let ap : Unary _ Z V := .push p (inferInstance : IsProper cf.g)
    let ej : Expression _ I X Z := .shriek j (inferInstance : IsOpenImmersion cf.i)
      (compactOpenQuasiCompact cf g.2.2.2.2.1) e
    have gj : ej.geometric := ⟨inferInstance, inferInstance, g.2.2.2.2.2⟩
    let Ke : (e.domain l E o).FullSubcategory :=
      ⟨K.obj, K.property.1, K.property.2.2.1⟩
    let Kj : (ej.domain l E o).FullSubcategory :=
      ⟨K.obj, K.property.1, K.property.2.2.2, K.property.2.2.1⟩
    let c := (canonicalComparisons l E D o d rec e g.2.2.2.2.2).app Ke
    let cj := (canonicalComparisons l E D o d rec ej gj).app Kj
    let b := (canonicalComparisons l E D o d rec (.compactSupport f cf e) g).app K
    have hjb := (canonicalComparisons_coefficient l E D o d rec ej gj Kj).symm
    dsimp only [ej, coefficientMap] at hjb
    rw [canonicalComparisons_coefficient l E D o d rec e g.2.2.2.2.2 Ke] at hjb
    obtain ⟨hj, hej, _⟩ := unary_step l E D o d rec aj
      _ (e.admissibleGood l E o _ Ke.property.2) K.property.2.2.2 _ c cj hjb
    have hpb : (calculus l E V.left).reduction.map b.inv ≫
        (calculus l E V.left).adjunction.counit.app
          ((ap.system l E o).obj
            ((ej.evaluate (systemInterpretation l E o)).obj
              ((inputReduction l E X).obj K.obj))) =
      (d.unaryReduction ap).app ((ej.evaluate (integralInterpretation l E)).obj K.obj) ≫
        (ap.system l E o).map (coefficientMap l E d ej gj K.obj) :=
      (canonicalComparisons_coefficient l E D o d rec (.compactSupport f cf e) g K).symm
    rw [canonicalComparisons_coefficient l E D o d rec ej gj Kj] at hpb
    obtain ⟨hp, hep, _⟩ := unary_step l E D o d rec ap
      _ K.property.2.2.2 K.property.2.1 _ cj b hpb
    refine ⟨hj, hp, ?_, ih _ Ke⟩
    change b.hom = _
    rw [hep, hej]
    rfl

end WeilConjectures.IntegralSystemRealization.ExpressionRecursion
