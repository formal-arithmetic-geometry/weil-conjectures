/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GeometricFourier.CondensedFourierGeometricModel
import WeilConjectures.CategoryTheory.BaseLinearPasting
import WeilConjectures.PoincareDuality.CurrentProEtaleProjection.CurrentProEtaleProjectionFormula
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.FourierKernelLisse
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

/-! # Base linearity of the condensed Fourier--Deligne transform

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-fourier-transform/sec-fourier-inversion/sk-thm-inversion/prop-base-linear.md
and the adjacent prop-base-linear.proof.md
(blueprint: lem-fd-condensed-base-linear-iso).

The theorem uses the current condensed coefficient model and the specified
finite-field geometric Fourier model.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.GeometricFourier

open PurityTransport

variable (D : WeilConjectures.FiniteFieldDatum.{u})

/-- Specialize pullback–tensor stability to the named arithmetic Fourier kernel.
Keeping this specialization generic avoids unfolding the concrete E-valued kernel.
Proof: apply pullback–tensor stability to the geometric pullback of the arithmetic kernel.
Source: the preceding stability lemma and the definition of kernel
(blueprint: prop-base-linear). -/
private theorem kernel_tensor_mem
    (ell : ℕ) [Fact ell.Prime]
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) (ψ : AddChar D.k₀ (MonObj.Γ R))
    (b : Γ(pullback p.left p'.left, ⊤))
    [TopologicalSpace.NoetherianSpace (fiber D (square D p p'))]
    [IsLocallyNoetherian (fiber D V)] [CompactSpace (fiber D V)]
    (hadic : IsEllAdicCoefficient ell R inferInstance) (hR : LisseTensorHypotheses R)
    (hM : IsLocallyFree (condensedRingObj R (fiber D (square D p p')))
      ((upperStar R (projection D (square D p p'))).obj (arithmeticKernel D R p p' ψ b)))
    (K : ConstantModelBoundedConstructible R (fiber D V)) :
    boundedConstructible (condensedRingObj R (fiber D (square D p p')))
      ((upperStar R (map D (fst D p p'))).leftDerivedFunctor.obj K.obj ⊗
        kernel D R p p' ψ b) :=
  pullback_tensorRight_single_mem ell R (fiber D (square D p p')) (fiber D V)
    hadic hR (map D (fst D p p')) _ hM K

/-- Kernel tensor stability for the exact rational coefficient presentation used here.
Proof: apply the generic kernel stability lemma, using the continuous-field adic
predicate comparison and continuous-field tensor hypotheses.
Source: kernel_tensor_mem and tensorHypotheses_continuousMapRingObj
(blueprint: prop-base-linear). -/
private theorem rational_kernel_tensor_mem
    (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    {S V V' : Over (Spec (.of D.k₀))} (p : V ⟶ S) (p' : V' ⟶ S)
    (ψ : AddChar D.k₀ (MonObj.Γ ((Coefficient.rational E).obj ell)))
    (b : Γ(pullback p.left p'.left, ⊤))
    [TopologicalSpace.NoetherianSpace (fiber D (square D p p'))]
    [IsLocallyNoetherian (fiber D V)] [CompactSpace (fiber D V)]
    (hM : IsLocallyFree
      (condensedRingObj ((Coefficient.rational E).obj ell) (fiber D (square D p p')))
      ((upperStar ((Coefficient.rational E).obj ell) (projection D (square D p p'))).obj
        (arithmeticKernel D ((Coefficient.rational E).obj ell) p p' ψ b)))
    (K : ConstantModelBoundedConstructible ((Coefficient.rational E).obj ell) (fiber D V)) :
    boundedConstructible
      (condensedRingObj ((Coefficient.rational E).obj ell) (fiber D (square D p p')))
      ((upperStar ((Coefficient.rational E).obj ell)
          (map D (fst D p p'))).leftDerivedFunctor.obj K.obj ⊗
        kernel D ((Coefficient.rational E).obj ell) p p' ψ b) := by
  let := PadicAlgCl.normedFieldOfAlgebra ell E
  exact kernel_tensor_mem D ell ((Coefficient.rational E).obj ell) p p' ψ b
    (.continuous E) (tensorHypotheses_continuousMapRingObj ell E).lisseTensorHypotheses hM K


set_option maxHeartbeats 1200000 in
-- Keep the projection formula in geometric-fibre coordinates, before the tensor pasting.
private theorem geometric_projection_isIso
    (ell : ℕ) [Fact ell.Prime] [Fact (ell ≠ D.p)]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    {X Y : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (K : ConstantModelBoundedConstructible ((Coefficient.rational E).obj ell) (fiber D X))
    (L : ConstantModelBoundedConstructible ((Coefficient.rational E).obj ell) (fiber D Y)) :
    IsIso (exceptionalProjectionMorphismOfCompactification
      ((Coefficient.rational E).obj ell) (compactification D (f := f) c) K.obj L.obj) := by
  let := PadicAlgCl.normedFieldOfAlgebra ell E
  let B := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  let : (fiber D X).Over (Spec (.of D.k)) := ⟨pullback.snd X.hom B⟩
  let : (fiber D Y).Over (Spec (.of D.k)) := ⟨pullback.snd Y.hom B⟩
  have : LocallyOfFiniteType ((fiber D X) ↘ Spec (.of D.k)) := by
    change LocallyOfFiniteType (pullback.snd X.hom B)
    infer_instance
  have : QuasiCompact ((fiber D X) ↘ Spec (.of D.k)) := by
    change QuasiCompact (pullback.snd X.hom B)
    infer_instance
  have : IsSeparated ((fiber D X) ↘ Spec (.of D.k)) := by
    change IsSeparated (pullback.snd X.hom B)
    infer_instance
  have : LocallyOfFiniteType ((fiber D Y) ↘ Spec (.of D.k)) := by
    change LocallyOfFiniteType (pullback.snd Y.hom B)
    infer_instance
  have : QuasiCompact ((fiber D Y) ↘ Spec (.of D.k)) := by
    change QuasiCompact (pullback.snd Y.hom B)
    infer_instance
  have : IsSeparated ((fiber D Y) ↘ Spec (.of D.k)) := by
    change IsSeparated (pullback.snd Y.hom B)
    infer_instance
  let g := map D f
  have hg : g ≫ pullback.snd Y.hom B = pullback.snd X.hom B := by
    dsimp [g, map, B]
    simp only [pullback.map, pullback.lift_snd, Category.comp_id]
  let : g.IsOver (Spec (.of D.k)) := ⟨hg⟩
  have : LocallyOfFiniteType (g ≫ pullback.snd Y.hom B) := by
    rw [hg]; infer_instance
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (pullback.snd Y.hom B)
  have : QuasiCompact (g ≫ pullback.snd Y.hom B) := by rw [hg]; infer_instance
  have : QuasiCompact g := QuasiCompact.of_comp g (pullback.snd Y.hom B)
  have : IsSeparated (g ≫ pullback.snd Y.hom B) := by rw [hg]; infer_instance
  have : IsSeparated g := IsSeparated.of_comp g (pullback.snd Y.hom B)
  exact (WeilConjectures.CurrentProEtaleProjection.projection_formula D ell
    (Fact.out : ell ≠ D.p) g (compactification D (f := f) c)).2.2.1 E K L

private def FourierProjectionAssertion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) (ψ : AddChar D.k₀ (MonObj.Γ Λ))
    (b : Γ(pullback p.left p'.left, ⊤))
    (c : Compactification (pullback.snd p.left p'.left)) : Prop :=
  ∀ (K : ConstantModelBoundedConstructible Λ (fiber D V))
      (N : ConstantModelBoundedConstructible Λ (fiber D S)),
      IsIso (exceptionalProjectionMorphismOfCompactification Λ
        (compactification D (f := snd D p p') c)
        ((upperStar Λ (map D (fst D p p'))).leftDerivedFunctor.obj K.obj ⊗
          kernel D Λ p p' ψ b)
        ((upperStar Λ (map D p')).leftDerivedFunctor.obj N.obj))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
-- Paste the comparison with an abstract coefficient ring before specializing to E.
private theorem geometric_base_linear_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) (ψ : AddChar D.k₀ (MonObj.Γ Λ))
    (b : Γ(pullback p.left p'.left, ⊤))
    (c : Compactification (pullback.snd p.left p'.left)) (r : ℤ)
    (hproj : ∀ (K : ConstantModelBoundedConstructible Λ (fiber D V))
      (N : ConstantModelBoundedConstructible Λ (fiber D S)),
      IsIso (exceptionalProjectionMorphismOfCompactification Λ
        (compactification D (f := snd D p p') c)
        ((upperStar Λ (map D (fst D p p'))).leftDerivedFunctor.obj K.obj ⊗
          kernel D Λ p p' ψ b)
        ((upperStar Λ (map D p')).leftDerivedFunctor.obj N.obj))) :
    Nonempty (baseTensor D Λ p ⋙
        (Functor.whiskeringRight _ _ _).obj (transform D Λ p p' ψ b c r) ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (constantModelBoundedConstructible Λ (fiber D V)).ι ≅
      baseTensor D Λ p' ⋙
        (Functor.whiskeringLeft _ _ _).obj (transform D Λ p p' ψ b c r) ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (constantModelBoundedConstructible Λ (fiber D V)).ι) := by
  let P := (upperStar Λ (map D (fst D p p'))).leftDerivedFunctor
  let Q := (upperStar Λ (map D (snd D p p'))).leftDerivedFunctor
  let R := rightDerivedLowerShriekOfCompactification Λ
    (compactification D (f := snd D p p') c)
  let H := kernel D Λ p p' ψ b
  let U := (constantModelBoundedConstructible Λ (fiber D S)).ι ⋙
    (upperStar Λ (map D p)).leftDerivedFunctor
  let U' := (constantModelBoundedConstructible Λ (fiber D S)).ι ⋙
    (upperStar Λ (map D p')).leftDerivedFunctor
  let J := (constantModelBoundedConstructible Λ (fiber D V)).ι
  let : BraidedCategory (category D Λ (square D p p')) :=
    DerivedCategory.braidedCategory' _
  let pc : U ⋙ P ≅ U' ⋙ Q :=
    Functor.isoWhiskerLeft _ (pullbackSquareComparison Λ
      (square_isPullback D p p').toCommSq).symm
  let π : curriedTensorInsertFunctor₁ R ⟶
      curriedTensorPost R ⋙ (Functor.whiskeringLeft _ _ _).obj Q :=
    { app A :=
        { app L := exceptionalProjectionMorphismOfCompactification Λ _ A L
          naturality _ _ g :=
            exceptionalProjectionMorphismOfCompactification_natural_right Λ _ A g }
      naturality _ _ g := NatTrans.ext (funext fun L ↦
        exceptionalProjectionMorphismOfCompactification_natural_left Λ _ g L) }
  have hp (N : ConstantModelBoundedConstructible Λ (fiber D S))
      (K : ConstantModelBoundedConstructible Λ (fiber D V)) :
      IsIso ((π.app (P.obj (J.obj K) ⊗ H)).app (U'.obj N)) := by
    dsimp only [π]
    exact hproj K N
  obtain ⟨e⟩ := CategoryTheory.kernel_base_linear_of_projection U U' P Q R H J pc π hp
  exact CategoryTheory.kernel_base_linear_shift U U' J (P ⋙ tensorRight H ⋙ R) e r

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
-- Predicate conversion and derived tensor instances need the larger elaboration budget.
private theorem kernel_projection_assertion
    (ell : ℕ) [Fact ell.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) (ψ : AddChar D.k₀ (MonObj.Γ Λ))
    (b : Γ(pullback p.left p'.left, ⊤))
    (c : Compactification (pullback.snd p.left p'.left))
    [TopologicalSpace.NoetherianSpace (fiber D (square D p p'))]
    [IsLocallyNoetherian (fiber D (square D p p'))]
    [CompactSpace (fiber D (square D p p'))]
    [IsLocallyNoetherian (fiber D V)] [CompactSpace (fiber D V)]
    [IsLocallyNoetherian (fiber D V')] [CompactSpace (fiber D V')]
    [IsLocallyNoetherian (fiber D S)] [CompactSpace (fiber D S)]
    (hadic : IsEllAdicCoefficient ell Λ inferInstance) (hR : LisseTensorHypotheses Λ)
    (hLF : IsLocallyFree (condensedRingObj Λ (fiber D (square D p p')))
      ((upperStar Λ (projection D (square D p p'))).obj
        (arithmeticKernel D Λ p p' ψ b)))
    (hproj : ∀ (K : ConstantModelBoundedConstructible Λ (fiber D (square D p p')))
      (L : ConstantModelBoundedConstructible Λ (fiber D V')),
      IsIso (exceptionalProjectionMorphismOfCompactification Λ
        (compactification D (f := snd D p p') c) K.obj L.obj)) :
    FourierProjectionAssertion D Λ p p' ψ b c := by
  intro K N
  have hA := kernel_tensor_mem D ell Λ p p' ψ b hadic hR hLF K
  have hN : boundedConstructible (condensedRingObj Λ (fiber D S)) N.obj := by
    rw [(adicConstructibilityPredicateComparison ell (fiber D S) Λ hadic).2]
    exact N.property
  have hL : boundedConstructible (condensedRingObj Λ (fiber D V'))
      ((upperStar Λ (map D p')).leftDerivedFunctor.obj N.obj) :=
    boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ _ N.obj hN
  have hA' : constantModelBoundedConstructible Λ (fiber D (square D p p'))
      ((upperStar Λ (map D (fst D p p'))).leftDerivedFunctor.obj K.obj ⊗
        kernel D Λ p p' ψ b) := by
    rw [← (adicConstructibilityPredicateComparison ell (fiber D (square D p p'))
      Λ hadic).2]
    exact hA
  have hL' : constantModelBoundedConstructible Λ (fiber D V')
      ((upperStar Λ (map D p')).leftDerivedFunctor.obj N.obj) := by
    rw [← (adicConstructibilityPredicateComparison ell (fiber D V') Λ hadic).2]
    exact hL
  exact hproj ⟨_, hA'⟩ ⟨_, hL'⟩


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
-- Keep the geometric instance calculations abstract in the coefficient ring.
private theorem geometric_fourier_projection_assertion
    (ell : ℕ) [Fact ell.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {S V V' : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
    (p : V ⟶ S) (p' : V' ⟶ S)
    (b : Γ(pullback p.left p'.left, ⊤)) (ψ : AddChar D.k₀ (MonObj.Γ Λ))
    (c : Compactification (pullback.snd p.left p'.left))
    (hadic : IsEllAdicCoefficient ell Λ inferInstance) (hR : LisseTensorHypotheses Λ)
    (hadm : IsAdmissibleCoefficient Λ) (hcard : IsUnit (Nat.card D.k₀ : MonObj.Γ Λ))
    (hproj : ∀ [LocallyOfFiniteType (square D p p').hom]
      [QuasiCompact (square D p p').hom] [IsSeparated (square D p p').hom],
      ∀ (K : ConstantModelBoundedConstructible Λ (fiber D (square D p p')))
        (L : ConstantModelBoundedConstructible Λ (fiber D V')),
        IsIso (exceptionalProjectionMorphismOfCompactification Λ
          (compactification D (f := snd D p p') c) K.obj L.obj)) :
    FourierProjectionAssertion D Λ p p' ψ b c := by
  let := Fintype.ofFinite D.k₀
  let B := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  have : LocallyOfFiniteType (p'.left ≫ S.hom) := by rw [p'.w]; infer_instance
  have : LocallyOfFiniteType p'.left := locallyOfFiniteType_of_comp p'.left S.hom
  have : QuasiCompact (p'.left ≫ S.hom) := by rw [p'.w]; infer_instance
  have : QuasiCompact p'.left := QuasiCompact.of_comp p'.left S.hom
  have : IsSeparated (p'.left ≫ S.hom) := by rw [p'.w]; infer_instance
  have : IsSeparated p'.left := IsSeparated.of_comp p'.left S.hom
  have : LocallyOfFiniteType (square D p p').hom := by dsimp [square]; infer_instance
  have : QuasiCompact (square D p p').hom := by dsimp [square]; infer_instance
  have : IsSeparated (square D p p').hom := by dsimp [square]; infer_instance
  have : IsLocallyNoetherian (fiber D (square D p p')) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (square D p p').hom B)
  have : CompactSpace (fiber D (square D p p')) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd (square D p p').hom B)
  have : IsNoetherian (fiber D (square D p p')) := ⟨⟩
  have : IsLocallyNoetherian (fiber D V) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd V.hom B)
  have : CompactSpace (fiber D V) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd V.hom B)
  have : IsLocallyNoetherian (fiber D S) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd S.hom B)
  have : CompactSpace (fiber D S) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd S.hom B)
  have : IsLocallyNoetherian (fiber D V') :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd V'.hom B)
  have : CompactSpace (fiber D V') :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd V'.hom B)
  have hunit : IsUnit (Fintype.card D.k₀ : MonObj.Γ Λ) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hLF : IsLocallyFree (condensedRingObj Λ (fiber D (square D p p')))
      ((upperStar Λ (projection D (square D p p'))).obj
        (arithmeticKernel D Λ p p' ψ b)) := by
    as_aux_lemma =>
      exact IsLocallyFree.upperStar Λ (projection D (square D p p'))
        ((isLocallyFree_iff _).2
          ((Etale.prop_kernel_lisse.2.2.2 Λ D.k₀ hunit hadm
            (square D p p').left ψ ψ b).1))
  exact kernel_projection_assertion D ell Λ p p' ψ b c hadic hR hLF hproj

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
-- Specializing the geometric projection reconstructs the finite-field fibre instances.
private theorem rational_fourier_projection_isIso
    (ell : ℕ) [Fact ell.Prime] [Fact (ell ≠ D.p)]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    {S V V' : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
    (p : V ⟶ S) (p' : V' ⟶ S)
    (b : Γ(pullback p.left p'.left, ⊤))
    (ψ : AddChar D.k₀ (MonObj.Γ ((Coefficient.rational E).obj ell)))
    (c : Compactification (pullback.snd p.left p'.left))
    : FourierProjectionAssertion D ((Coefficient.rational E).obj ell) p p' ψ b c := by
  let := PadicAlgCl.normedFieldOfAlgebra ell E
  have hadm : IsAdmissibleCoefficient ((Coefficient.rational E).obj ell) :=
    ⟨ell, inferInstance, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩))))⟩
  have hcard : IsUnit (Nat.card D.k₀ : MonObj.Γ ((Coefficient.rational E).obj ell)) := by
    as_aux_lemma =>
      simpa only [map_natCast] using
        (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr Nat.card_pos.ne') :
          IsUnit (Nat.card D.k₀ : E)).map (Profinite.continuousMapConstRingHom E)
  apply geometric_fourier_projection_assertion D ell ((Coefficient.rational E).obj ell)
    p p' b ψ c (.continuous E)
    (tensorHypotheses_continuousMapRingObj ell E).lisseTensorHypotheses hadm hcard
  intro _ _ _ K L
  exact geometric_projection_isIso D ell E (snd D p p') c K L


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
-- The concrete square contains four derived module categories.
/-- The two-variable comparison from the blueprint projection-formula argument.
Source: prop-base-linear.proof.md, paragraphs 1--4
(blueprint: lem-fd-condensed-base-linear-iso).
Proof: monoidal pullback and the Fourier square identify the pulled base factor.
Associativity and braiding move it past the kernel. The kernel is lisse and both
projection inputs are bounded constructible, so the field projection theorem
inverts the specified map. Whisker by the rank shift and commute right tensor
with that shift. All operations are natural in both variables. -/
theorem baseLinearIso
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] [Fact (ell ≠ D.p)]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    {S V V' : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
    (p : V ⟶ S) (p' : V' ⟶ S) (r : ℕ)
    (b : Γ(pullback p.left p'.left, ⊤)) (bundle : DualBundlePairing p.left p'.left r b)
    (ψ : AddChar D.k₀ (MonObj.Γ (Coefficient.rational E |>.obj ell)))
    (c : Compactification (pullback.snd p.left p'.left)) :
    Nonempty (baseTensor D (Coefficient.rational E |>.obj ell) p ⋙
          (Functor.whiskeringRight _ _ _).obj
            (transform D (Coefficient.rational E |>.obj ell) p p' ψ b c (r : ℤ)) ⋙
          (Functor.whiskeringLeft _ _ _).obj
            (constantModelBoundedConstructible
              (Coefficient.rational E |>.obj ell) (fiber D V)).ι ≅
      baseTensor D (Coefficient.rational E |>.obj ell) p' ⋙
          (Functor.whiskeringLeft _ _ _).obj
            (transform D (Coefficient.rational E |>.obj ell) p p' ψ b c (r : ℤ)) ⋙
          (Functor.whiskeringLeft _ _ _).obj
            (constantModelBoundedConstructible
              (Coefficient.rational E |>.obj ell) (fiber D V)).ι) := by
  exact geometric_base_linear_iso D ((Coefficient.rational E).obj ell) p p' ψ b c (r : ℤ)
    (rational_fourier_projection_isIso D ell E p p' b ψ c)

end AlgebraicGeometry.ProEtale.CondensedRing.GeometricFourier
