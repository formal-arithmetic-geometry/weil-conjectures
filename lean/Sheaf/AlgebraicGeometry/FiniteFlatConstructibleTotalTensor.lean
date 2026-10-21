/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
import WeilConjectures.ConstructibleSheaf.Monoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.Data.Int.Interval

/-!
# Bounded flat constructible total tensors on the small etale site

Source: blueprint main-20261015, `sk-thm-sf-ctf-stability-direct-images`, proof (1),(2),
finite coefficients; Stacks Project, Tags 095I, 03RZ, 06YQ, 07A2 and 06YU
(blueprint: lem-sfb-finite-flat-constructible-total-tensor).

The total tensor is the existing signed direct-sum `CochainComplex.mapBifunctor`.
The equality naming `T` specifies this construction, rather than an arbitrary model.
All sheaves, cohomology objects and derived tensors use the same etale module category.
-/

@[expose] public section

set_option autoImplicit false

universe u vC uC wC

open CategoryTheory CategoryTheory.Limits MonoidalCategory

private noncomputable def bounded_total_term_iso
    {C : Type*} [Category C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [HasCountableCoproducts C]
    (P Q : CochainComplex C ℤ) (a b n : ℤ)
    (hP : ∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i)) :
    (CochainComplex.mapBifunctor P Q (curriedTensor C)).X n ≅
      ∐ (fun i : ↥(Finset.Icc a b) ↦ P.X i.1 ⊗ Q.X (n - i.1)) := by
  classical
  let F := fun i : ↥(Finset.Icc a b) ↦ P.X i.1 ⊗ Q.X (n - i.1)
  let f : ∀ (p q : ℤ), p + q = n → (P.X p ⊗ Q.X q ⟶ ∐ F) := by
    intro p q hpq
    by_cases hp : p ∈ Finset.Icc a b
    · have hq : q = n - p := by omega
      subst q
      exact Sigma.ι F ⟨p, hp⟩
    · exact 0
  let g : ∐ F ⟶ (CochainComplex.mapBifunctor P Q (curriedTensor C)).X n :=
    Sigma.desc fun i ↦ CochainComplex.ιMapBifunctor P Q (curriedTensor C)
      i.1 (n - i.1) n (by omega)
  refine ⟨HomologicalComplex.mapBifunctorDesc f, g, ?_, ?_⟩
  · apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change p + q = n at hpq
    rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
    by_cases hp : p ∈ Finset.Icc a b
    · have hq : q = n - p := by omega
      subst q
      simp [f, Finset.mem_Icc.mp hp, g]
    · have hz : IsZero (P.X p ⊗ Q.X q) :=
        (tensorRight (Q.X q)).map_isZero
          (hP p (by simpa only [Finset.mem_Icc, not_and_or, not_le] using hp))
      exact hz.eq_of_src _ _
  · apply Sigma.hom_ext
    intro i
    dsimp [g]
    rw [← Category.assoc, Sigma.ι_desc, HomologicalComplex.ι_mapBifunctorDesc]
    simp [f, Finset.mem_Icc.mp i.property, F]

/-- Compare the K-flat predicates before specializing the monoidal category. -/
private theorem kFlat_totalTensor_iff
    {C : Type*} [Category C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [HasCountableCoproducts C]
    [∀ (U V W Z : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt U V W Z]
    [∀ (U V W : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor U V W]
    [∀ (U V W : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ U V W]
    (P : CochainComplex C ℤ) :
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P ↔ P.IsKFlatForTotalTensor :=
  Iff.rfl

/-- Compare the tensor objects before specializing the monoidal category. -/
private noncomputable def tensor_total_iso
    {C : Type*} [Category C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [HasCountableCoproducts C]
    [∀ (U V W Z : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt U V W Z]
    [∀ (U V W : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor U V W]
    [∀ (U V W : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ U V W]
    (P Q : CochainComplex C ℤ) :
    P ⊗ Q ≅ CochainComplex.mapBifunctor P Q (curriedTensor C) :=
  Iso.refl _

/-- Extract the support bound in the generic derived category. -/
private theorem derived_flat_bound
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{wC} C] [Abelian.HasFunctorialFlatResolution C]
    (P : CochainComplex C ℤ) (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hP : ∀ i, ObjectProperty.flat (P.X i)) (N : C) (n : ℤ)
    (hn : n < a ∨ b < n) :
    IsZero ((_root_.DerivedCategory.homologyFunctor C n).obj
      (_root_.DerivedCategory.Q.obj P ⊗
        (_root_.DerivedCategory.singleFunctor C 0).obj N)) := by
  have ht := _root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat P a b hP N
  rcases hn with hn | hn
  · exact (_root_.DerivedCategory.isGE_iff _ a).1 ht.1 n hn
  · exact (_root_.DerivedCategory.isLE_iff _ b).1 ht.2 n hn

/-- Use the generic derived comparison without reducing its constructed isomorphism. -/
private theorem derived_total_comparison
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{wC} C] [Abelian.HasFunctorialFlatResolution C]
    (P Q : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    Nonempty (_root_.DerivedCategory.Q.obj
      (CochainComplex.mapBifunctor P Q (curriedTensor C)) ≅
        _root_.DerivedCategory.Q.obj P ⊗ _root_.DerivedCategory.Q.obj Q) := by
  exact ⟨(_root_.DerivedCategory.Q.mapIso (tensor_total_iso P Q)).symm ≪≫
    (_root_.DerivedCategory.QObjTensorQObjIsoOfKFlatLeft P Q hP).symm⟩

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Etale

section

variable (E : Type uC) [Category.{u + 1} E] [Abelian E]
  [IsGrothendieckAbelian.{u + 1} E] [MonoidalCategory E] [MonoidalPreadditive E]
  [SymmetricCategory E] [MonoidalClosed E] [Abelian.HasFunctorialFlatResolution E]

/-- The generic comparison in the exact tensor notation of the etale API. -/
private theorem etale_derived_total_comparison (X : Scheme.{u})
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology E) ℤ)
    (hP : (HomologicalComplex.quasiIso (Sheaf X.smallEtaleTopology E) (.up ℤ)).kFlat P) :
    Nonempty (_root_.DerivedCategory.Q.obj
      (CochainComplex.mapBifunctor P Q (curriedTensor _)) ≅
        ((derivedTensor E X).obj (_root_.DerivedCategory.Q.obj P)).obj
          (_root_.DerivedCategory.Q.obj Q)) := by
  exact derived_total_comparison P Q hP

/-- The flat-model Tor bound in the exact tensor notation of the etale API. -/
private theorem etale_derived_total_bound (X : Scheme.{u})
    (P : CochainComplex (Sheaf X.smallEtaleTopology E) ℤ)
    (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hP : ∀ i, ObjectProperty.flat (P.X i))
    (N : Sheaf X.smallEtaleTopology E) (n : ℤ) (hn : n < a ∨ b < n) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      (((derivedTensor E X).obj (_root_.DerivedCategory.Q.obj P)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj N))) := by
  exact derived_flat_bound P a b hP N n hn

end

/-- The signed total tensor of bounded flat constructible complexes over a finite ring
has flat constructible terms, the sum support interval, and constructible cohomology.
It is K-flat and represents the ordinary relative derived tensor. Tensoring its derived
image with any module sheaf in degree zero has cohomology in the same sum interval.

Source: blueprint main-20261015, `sk-thm-sf-ctf-stability-direct-images`, proof (1),(2),
finite coefficients; Stacks Project, Tags 095I, 03RZ, 06YQ, 07A2 and 06YU
(blueprint: lem-sfb-finite-flat-constructible-total-tensor).

Proof:
1. Braiding identifies tensor on the left and on the right, so the hypotheses give
   categorical flatness of every term of P and Q. Tensor products of flat objects
   are flat, and finite biproducts of flat objects are flat.
2. The private coproduct comparison discards the zero P terms outside [a,b]. In degree n
   the total tensor is the finite coproduct of P^i tensor Q^(n-i), indexed by i in [a,b].
   This proves flatness. The standard total-tensor support lemmas give [a+c,b+d].
3. Convert finite-value constructibility to the existing IsConstructibleSheaf predicate.
   Its tensorObj theorem uses the fibre-product common refinement and the monoidality
   of etale pullback. Its biproduct theorem gives constructibility of every total term.
4. The kernel and cokernel clauses of thm-constructible-serre show that the cycles and
   then their quotient by boundaries are constructible. The localization homology
   comparison identifies this quotient with the required derived cohomology sheaf.
5. The source bounded-above flat criterion makes P and the total tensor K-flat, using
   the same two-sided quasi-isomorphism test as the conclusion. The source comparison
   QObjTensorQObjIsoOfKFlatLeft identifies the actual total tensor with derived tensor.
6. The source torAmplitudeIn_Q_obj_of_flat theorem applies to the total tensor with
   interval [a+c,b+d]. It computes tensor with any sheaf in degree zero from the K-flat
   model; its terms, and hence cohomology, vanish outside that interval.

K-flatness uses `CochainComplex.IsKFlatForTotalTensor`, owned by the landed node
`def-sfb-preserves-kflat-quasi-iso`. Its two-sided quasi-isomorphism test equals the
acyclic-test K-flatness of `def-pc-kflat-complex` here: tensor preserves zero, so
preservation of quasi-isomorphisms sends an acyclic complex's map to zero to a
quasi-isomorphism. Conversely, the cone criterion and tensor's compatibility with
cones give preservation of quasi-isomorphisms from the acyclic test; signed tensor
symmetry identifies the left and right tests. No dependency record is rebound.
The zero ring, empty scheme, zero terms and one-degree intervals are included. -/
theorem finiteFlatConstructible_totalTensor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X]
    (a b c d : ℤ) (_hab : a ≤ b) (_hcd : c ≤ d)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (_hPflat : ∀ i : ℤ, exactFunctor _ _
      (@tensorRight _ _ (Sheaf.monoidalCategory X.smallEtaleTopology
        (ModuleCat.{u + 1} A)) (P.X i)))
    (_hQflat : ∀ j : ℤ, exactFunctor _ _
      (@tensorRight _ _ (Sheaf.monoidalCategory X.smallEtaleTopology
        (ModuleCat.{u + 1} A)) (Q.X j)))
    (_hPc : ∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (P.X i))
    (_hQc : ∀ j : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (Q.X j))
    (_hPbound : ∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i))
    (_hQbound : ∀ j : ℤ, (j < c ∨ d < j) → IsZero (Q.X j))
    (T : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (_hT : T = CochainComplex.mapBifunctor P Q
      (@curriedTensor _ _ (Sheaf.monoidalCategory X.smallEtaleTopology
        (ModuleCat.{u + 1} A)))) :
    (∀ n : ℤ, exactFunctor _ _
      (@tensorRight _ _ (Sheaf.monoidalCategory X.smallEtaleTopology
        (ModuleCat.{u + 1} A)) (T.X n))) ∧
    (∀ n : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (T.X n)) ∧
    (∀ n : ℤ, (n < a + c ∨ b + d < n) → IsZero (T.X n)) ∧
    (∀ n : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ n).obj
        (_root_.DerivedCategory.Q.obj T))) ∧
    (@CochainComplex.IsKFlatForTotalTensor _ _ _
      (Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} A)) _ _ T) ∧
    Nonempty (_root_.DerivedCategory.Q.obj T ≅
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj
        (_root_.DerivedCategory.Q.obj P)).obj (_root_.DerivedCategory.Q.obj Q)) ∧
    ∀ (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (n : ℤ),
      (n < a + c ∨ b + d < n) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          (_root_.DerivedCategory.Q.obj T)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj N))) := by
  classical
  let := Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let : ∀ (U V : GradedObject ℤ C), GradedObject.HasTensor U V :=
    fun _ _ _ ↦ inferInstance
  let : ∀ (U V W Z : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt U V W Z :=
    fun _ _ _ _ _ _ ↦ inferInstance
  let : ∀ (U V W : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor U V W :=
    fun _ _ _ _ _ ↦ inferInstance
  let : ∀ (U V W : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ U V W :=
    fun _ _ _ _ _ ↦ inferInstance
  let : MonoidalCategory (CochainComplex C ℤ) :=
    HomologicalComplex.monoidalCategory C (.up ℤ)
  have hP : ∀ i, ObjectProperty.flat (P.X i) := fun i ↦
    ⟨(exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight (P.X i)).symm (_hPflat i), _hPflat i⟩
  have hQ : ∀ i, ObjectProperty.flat (Q.X i) := fun i ↦
    ⟨(exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight (Q.X i)).symm (_hQflat i), _hQflat i⟩
  have : P.IsStrictlyGE a := (P.isStrictlyGE_iff a).2 fun i hi ↦ _hPbound i (.inl hi)
  have : P.IsStrictlyLE b := (P.isStrictlyLE_iff b).2 fun i hi ↦ _hPbound i (.inr hi)
  have : Q.IsStrictlyGE c := (Q.isStrictlyGE_iff c).2 fun i hi ↦ _hQbound i (.inl hi)
  have : Q.IsStrictlyLE d := (Q.isStrictlyLE_iff d).2 fun i hi ↦ _hQbound i (.inr hi)
  subst T
  let S := CochainComplex.mapBifunctor P Q (curriedTensor C)
  have : S.IsStrictlyGE (a + c) := CochainComplex.isStrictlyGE_tensorObj P Q a c
  have : S.IsStrictlyLE (b + d) := CochainComplex.isStrictlyLE_tensorObj P Q b d
  have hSfc : ∀ n, ObjectProperty.flat (S.X n) ∧
      Scheme.IsConstructibleSheaf (S.X n) := by
    intro n
    let F := fun i : ↥(Finset.Icc a b) ↦ P.X i.1 ⊗ Q.X (n - i.1)
    let e : S.X n ≅ ⨁ F :=
      bounded_total_term_iso P Q a b n _hPbound ≪≫ (biproduct.isoCoproduct F).symm
    have hf : ∀ i, ObjectProperty.flat (F i) := fun i ↦
      ObjectProperty.prop_tensor (hP i.1) (hQ (n - i.1))
    have : (ObjectProperty.flat (A := C)).IsClosedUnderLimitsOfShape
        (Discrete ↥(Finset.Icc a b)) :=
      CochainComplex.closedUnderLimitsOfShape_discrete_flat C _
    have hf' : ObjectProperty.flat (⨁ F) :=
      ObjectProperty.prop_of_isLimit _ (biproduct.isLimit F) (fun i ↦ hf i.as)
    have (i : ↥(Finset.Icc a b)) : Scheme.IsConstructibleSheaf (F i) :=
      ((Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1
        (_hPc i.1)).tensorObj
        ((Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1
          (_hQc (n - i.1)))
    have := Scheme.IsConstructibleSheaf.biproduct F
    exact ⟨(ObjectProperty.flat (A := C)).prop_of_iso e.symm hf',
      Scheme.IsConstructibleSheaf.of_iso e.symm⟩
  have hSf : ∀ n, ObjectProperty.flat (S.X n) := fun n ↦ (hSfc n).1
  have hSc : ∀ n, Scheme.IsConstructibleSheaf (S.X n) := fun n ↦ (hSfc n).2
  have : HasColimitsOfShape ℤ C := Sheaf.instHasColimitsOfShape
  have : HasExactColimitsOfShape ℤ C := inferInstance
  let : ∀ U : C, PreservesColimitsOfShape ℤ ((curriedTensor C).obj U) :=
    fun _ ↦ inferInstance
  let : ∀ U : C, PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj U) :=
    fun _ ↦ inferInstance
  have hSk := CochainComplex.kFlat_of_isStrictlyLE_of_flat S (b + d) hSf
  refine ⟨fun n ↦ (hSf n).2, fun n ↦ ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hSc n)
  · intro n hn
    rcases hn with hn | hn
    · exact S.isZero_of_isStrictlyGE (a + c) n hn
    · exact S.isZero_of_isStrictlyLE (b + d) n hn
  · intro n
    suffices ∀ U : CochainComplex C ℤ,
        (∀ i, Scheme.IsConstructibleSheaf (U.X i)) →
        Scheme.IsConstructibleEtaleModuleSheaf
          ((_root_.DerivedCategory.homologyFunctor C n).obj
            (_root_.DerivedCategory.Q.obj U)) by
      exact this S hSc
    intro U hUc
    have (i : ℤ) : Scheme.IsConstructibleSheaf (U.X i) := hUc i
    let V := U.sc n
    have : Scheme.IsConstructibleSheaf V.X₁ := hUc _
    have : Scheme.IsConstructibleSheaf V.X₂ := hUc _
    have : Scheme.IsConstructibleSheaf V.X₃ := hUc _
    have := Scheme.IsConstructibleSheaf.kernel V.g
    have : Scheme.IsConstructibleSheaf V.cycles :=
      Scheme.IsConstructibleSheaf.of_iso (F := kernel V.g)
        (V.cyclesIsKernel.conePointUniqueUpToIso (kernelIsKernel V.g)).symm
    have := Scheme.IsConstructibleSheaf.cokernel V.toCycles
    have : Scheme.IsConstructibleSheaf (U.homology n) :=
      Scheme.IsConstructibleSheaf.of_iso (F := cokernel V.toCycles)
        ((cokernelIsCokernel V.toCycles).coconePointUniqueUpToIso V.homologyIsCokernel)
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (Scheme.IsConstructibleSheaf.of_iso (F := U.homology n)
        ((_root_.DerivedCategory.homologyFunctorFactors C n).app U).symm)
  · exact (kFlat_totalTensor_iff S).1 hSk
  · exact etale_derived_total_comparison (ModuleCat.{u + 1} A) X P Q
      (CochainComplex.kFlat_of_isStrictlyLE_of_flat P b hP)
  · exact fun N n hn ↦
      etale_derived_total_bound (ModuleCat.{u + 1} A) X S (a + c) (b + d) hSf N n hn

end AlgebraicGeometry.Etale
