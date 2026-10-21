/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
import WeilConjectures.FromJoel.CategoryTheory.ObjectProperty.FiniteProducts
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

/-!
# Two-term scalar quotient resolutions after flat sheaf extension

Source: Stacks Project, Cohomology on Sites, Tags 06YQ and 06YU;
Modules on Sites, Tags 03EI and 03ER
(blueprint: lem-sfb-flat-scalar-cyclic-resolution).

The cone of scalar multiplication on the degree-zero ring complex is the displayed
complex in degrees -1 and 0. Its quotient is the sheaf cokernel, and the augmentation
is specified by its restriction to the degree-zero summand.
-/

@[expose] public section

universe u v r w

set_option autoImplicit false
set_option synthInstance.maxSize 4096

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C) (A : Type r) [CommRing A]
  [HasWeakSheafify J CommRingCat.{r}]

/-- The existing constant commutative ring sheaf.
Source: Stacks Tag 093I (blueprint: lem-sfb-flat-scalar-cyclic-resolution). -/
noncomputable abbrev scalarCyclicBase := (constantSheaf J CommRingCat.{r}).obj (CommRingCat.of A)

variable {J}

/-- Forget commutativity for the existing module-sheaf category.
Source: Stacks Tag 03CY (blueprint: lem-sfb-flat-scalar-cyclic-resolution). -/
noncomputable abbrev scalarCyclicRing (R : Sheaf J CommRingCat.{r}) :=
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R

variable {A} (R : Sheaf J CommRingCat.{r})
  (α : scalarCyclicBase J A ⟶ R)

/-- The constant presheaf map adjoint to the given constant-sheaf algebra structure.
Source: Stacks Tags 03CY, 093I (blueprint: lem-sfb-flat-scalar-cyclic-resolution). -/
noncomputable def scalarCyclicPresheafMap :
    (Functor.const Cᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj :=
  (sheafificationAdjunction J CommRingCat.{r}).homEquiv _ _ α

/-- Multiplication by the constant scalar, constructed from its compatible sections.
Source: Stacks Tags 03CY, 03ER (blueprint: lem-sfb-flat-scalar-cyclic-resolution). -/
noncomputable def scalarCyclicMultiplication (a : A) :
    unit (scalarCyclicRing R) ⟶ unit (scalarCyclicRing R) :=
  (unit (scalarCyclicRing R)).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun U ↦ (scalarCyclicPresheafMap R α).app U a)
      (fun U V f ↦ by
        exact congrArg (fun g : CommRingCat.of A ⟶ R.obj.obj V ↦ g a)
          ((scalarCyclicPresheafMap R α).naturality f).symm))

/-- The displayed two-term complex: the cone of `a : R[0] → R[0]`.
Its differential from degree -1 to degree 0 is multiplication by `a`.
Source: Stacks Tags 06YQ, 06YU (blueprint: lem-sfb-flat-scalar-cyclic-resolution). -/
noncomputable def scalarCyclicComplex (a : A) :
    CochainComplex (SheafOfModules.{r} (scalarCyclicRing R)) ℤ :=
  CochainComplex.mappingCone
    ((CochainComplex.singleFunctor _ 0).map (scalarCyclicMultiplication R α a))

/-- The quotient sheaf `R/aR`, as a module sheaf cokernel.
Source: Stacks Tag 03DA (blueprint: lem-sfb-flat-scalar-cyclic-resolution). -/
noncomputable def scalarCyclicQuotient (a : A) : SheafOfModules.{r} (scalarCyclicRing R) :=
  cokernel (scalarCyclicMultiplication R α a)

private theorem scalar_cyclic_multiplication_apply (a : A) (U : Cᵒᵖ)
    (x : R.obj.obj U) :
    (scalarCyclicMultiplication R α a).val.app U x =
      (scalarCyclicPresheafMap R α).app U a * x := by
  change x * (scalarCyclicPresheafMap R α).app U a = _
  exact mul_comm _ _

omit [EssentiallySmall.{r} C] in
private theorem scalar_cyclic_presheaf_map_apply (a : A) (U : Cᵒᵖ) :
    (scalarCyclicPresheafMap R α).app U a =
      α.hom.app U
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a) := by
  rfl

omit [HasWeakSheafify J CommRingCat.{r}] in
private theorem constant_ring_locally_bijective :
    J.WEqualsLocallyBijective CommRingCat.{r} := by
  let : PreservesFilteredColimitsOfSize.{r, r} (CategoryTheory.forget CommRingCat.{r}) :=
    preservesFilteredColimitsOfSize_shrink _
  have : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{r} C).inverse.op)
        CommRingCat.{r} := fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{r} _ _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := CommRingCat.{r})

private theorem constant_scalar_mul_eq_zero [IsDomain A] (a : A) (ha : a ≠ 0)
    (U : Cᵒᵖ)
    (x : (sheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).obj U)
    (hx : (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a * x = 0) :
    x = 0 := by
  have := constant_ring_locally_bijective (J := J)
  let B := sheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))
  have hB : Presheaf.IsSheaf J B :=
    ((presheafToSheaf J CommRingCat.{r}).obj
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).property
  let η := toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))
  apply hB.isSeparated _ _ (Presheaf.imageSieve_mem J η x)
  intro V f hf
  obtain ⟨b, hb⟩ := hf
  change A at b
  have hη (c : A) : B.map f.op (η.app U c) = η.app (Opposite.op V) c :=
    (NatTrans.naturality_apply η f.op c).symm
  have heq : η.app (Opposite.op V) (a * b) = η.app (Opposite.op V) 0 := by
    rw [map_mul, map_zero, hb, ← hη, ← map_mul, hx, map_zero]
  apply hB.isSeparated _ _ (Presheaf.equalizerSieve_mem J η (a * b) 0 heq)
  intro W g hg
  have hab : a * b = 0 := hg
  have hb0 : b = 0 := (mul_eq_zero.mp hab).resolve_left ha
  have hxV : B.map f.op x = 0 := by
    calc
      B.map f.op x = η.app (Opposite.op V) b := hb.symm
      _ = 0 := by rw [hb0]; exact map_zero (η.app (Opposite.op V)).hom
  change B.map g.op (B.map f.op x) = B.map g.op (B.map f.op 0)
  rw [hxV, map_zero (B.map f.op).hom]

private theorem flat_scalar_kernel [IsDomain A]
    (hflat : IsFlatOnSite (J := J) (R := scalarCyclicBase J A)
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map α)).obj
        (unit (scalarCyclicRing R))))
    (a : A) (ha : a ≠ 0) (U : Cᵒᵖ) (x : R.obj.obj U)
    (hx : (scalarCyclicMultiplication R α a).val.app U x = 0) : x = 0 := by
  classical
  let B := scalarCyclicBase J A
  let F := (restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map α)).obj
      (unit (scalarCyclicRing R))
  let η := toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))
  have hx' : η.app U a • (show F.val.obj U from x) = 0 := by
    change α.hom.app U (η.app U a) * x = 0
    rw [← scalar_cyclic_presheaf_map_apply R α a U,
      ← scalar_cyclic_multiplication_apply R α a U x]
    exact hx
  have hrel : (∑ _p : Fin 1, η.app U a • (show F.val.obj U from x)) = 0 := by
    simpa only [Fin.sum_univ_one] using hx'
  obtain ⟨S, hS, hf⟩ := local_equationalCriterion_of_isFlatOnSite.{u, v, r, r}
    B F hflat U.unop 1 (fun _ ↦ η.app U a) (fun _ ↦ x) hrel
  apply (unit (scalarCyclicRing R)).isSheaf.isSeparated _ S hS
  intro V f hmem
  obtain ⟨l, b, t, hb, hbt⟩ := hf V f hmem
  have hzero (q : Fin l) : b 0 q = 0 := by
    apply constant_scalar_mul_eq_zero a ha (Opposite.op V)
    have hη : B.obj.map f.op (η.app U a) = η.app (Opposite.op V) a :=
      (NatTrans.naturality_apply η f.op a).symm
    simpa only [Fin.sum_univ_one, hη] using hbt q
  have hz := hb 0
  simp only [hzero, zero_smul, Finset.sum_const_zero] at hz
  change R.obj.map f.op x = R.obj.map f.op 0
  exact hz.trans (map_zero (R.obj.map f.op).hom).symm

omit [HasWeakSheafify J CommRingCat.{r}] in
private theorem single_unit_flat_term (i : ℤ) :
    IsFlatOnSite (J := J) (R := R)
      (((CochainComplex.singleFunctor _ 0).obj (unit (scalarCyclicRing R))).X i) := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let S := (CochainComplex.singleFunctor _ 0).obj (unit (scalarCyclicRing R))
  have h : ObjectProperty.flat (S.X i) := by
    by_cases hi : i = 0
    · exact ObjectProperty.prop_of_iso _
        (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0
          (unit (scalarCyclicRing R)) i hi).symm (ObjectProperty.prop_unit _)
    · exact ObjectProperty.prop_of_isZero _
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
  exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R _).symm h.2

private theorem scalar_cyclic_flat_term (a : A) (i : ℤ) :
    IsFlatOnSite (J := J) (R := R) ((scalarCyclicComplex R α a).X i) := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let S := (CochainComplex.singleFunctor _ 0).obj (unit (scalarCyclicRing R))
  let f := (CochainComplex.singleFunctor _ 0).map (scalarCyclicMultiplication R α a)
  have hf (j : ℤ) : ObjectProperty.flat (S.X j) :=
    flat_to_cat R _ (single_unit_flat_term R j)
  have hb : ObjectProperty.flat (S.X (i + 1) ⊞ S.X i) :=
    ObjectProperty.prop_biprod_of_isClosedUnderBinaryProducts _ _ _ (hf _) (hf _)
  have h : ObjectProperty.flat ((scalarCyclicComplex R α a).X i) :=
    ObjectProperty.prop_of_iso _
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl).symm hb
  exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R _).symm h.2

private theorem scalar_cyclic_kflat (a : A) :
    CochainComplex.IsKFlatIndependentCoefficients (scalarCyclicComplex R α a) ∧
      CochainComplex.IsKFlatIndependentCoefficients
        ((CochainComplex.singleFunctor _ 0).obj (unit (scalarCyclicRing R))) := by
  let S := (CochainComplex.singleFunctor _ 0).obj (unit (scalarCyclicRing R))
  have : (scalarCyclicComplex R α a).IsStrictlyLE 0 := by
    apply (CochainComplex.isStrictlyLE_iff _ 0).2
    intro i hi
    apply (CochainComplex.mappingCone.isZero_X_iff _ i).2
    exact ⟨S.isZero_of_isStrictlyLE 0 (i + 1) (by omega),
      S.isZero_of_isStrictlyLE 0 i hi⟩
  exact ⟨isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R _ 0
      (scalar_cyclic_flat_term R α a),
    isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R S 0
      (single_unit_flat_term R)⟩

private theorem scalar_cyclic_derived_tensor
    [HasDerivedCategory.{w} (SheafOfModules.{r} (scalarCyclicRing R))]
    (a : A)
    (ε : scalarCyclicComplex R α a ⟶
      (CochainComplex.singleFunctor _ 0).obj (scalarCyclicQuotient R α a))
    [QuasiIso ε] (M : CochainComplex (SheafOfModules.{r} (scalarCyclicRing R)) ℤ) :
    Nonempty ((siteDerivedTensorIndependentCoefficients J R).obj
        (DerivedCategory.Q.obj M,
          DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
            (scalarCyclicQuotient R α a))) ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor M
        (scalarCyclicComplex R α a) (curriedTensor _))) := by
  obtain ⟨s, hs⟩ := KFlatFixedTensor.kFlat_fixed_tensor_triangulated R
  obtain ⟨cR, _, _⟩ :=
    (hs (scalarCyclicComplex R α a) (scalar_cyclic_kflat R α a).1
      (scalar_cyclic_flat_term R α a)).2.2.2.2.1
  exact ⟨((Functor.curry.obj (siteDerivedTensorIndependentCoefficients J R)).obj
      (DerivedCategory.Q.obj M)).mapIso (asIso (DerivedCategory.Q.map ε)).symm ≪≫
    (cR.app M).symm⟩

private theorem cone_cokernel_augmentation
    {D : Type*} [Category* D] [Abelian D] {X Y : D} (f : X ⟶ Y) [Mono f] :
    ∃ ε : CochainComplex.mappingCone ((CochainComplex.singleFunctor D 0).map f) ⟶
        (CochainComplex.singleFunctor D 0).obj (cokernel f),
      CochainComplex.mappingCone.inr ((CochainComplex.singleFunctor D 0).map f) ≫ ε =
        (CochainComplex.singleFunctor D 0).map (cokernel.π f) ∧ QuasiIso ε := by
  let S := ShortComplex.mk f (cokernel.π f) (by simp)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
  let T := S.map (CochainComplex.singleFunctor D 0)
  let : PreservesFiniteLimits (CochainComplex.singleFunctor D 0) :=
    inferInstanceAs (PreservesFiniteLimits (HomologicalComplex.single D (.up ℤ) 0))
  let : PreservesFiniteColimits (CochainComplex.singleFunctor D 0) :=
    inferInstanceAs (PreservesFiniteColimits (HomologicalComplex.single D (.up ℤ) 0))
  refine ⟨CochainComplex.mappingCone.descShortComplex T, ?_, ?_⟩
  · exact CochainComplex.mappingCone.inr_descShortComplex T
  · exact CochainComplex.mappingCone.quasiIso_descShortComplex
      (hS.map_of_exact (CochainComplex.singleFunctor D 0))

/-- A flat algebra over a constant domain has the indicated scalar quotient resolution.
The augmentation restricts to the cokernel projection on the degree-zero ring summand;
its source is the specified two-term complex, rather than an unspecified resolution.
The last clause computes derived tensor with the quotient for every unbounded complex.
Source: Stacks Tags 03EI, 03ER, 06YQ and 06YU
(blueprint: lem-sfb-flat-scalar-cyclic-resolution).

Proof:
1. Sections of the constant ring sheaf locally lift to constant sections. Local
   injectivity of the sheafification unit and cancellation in the domain show that
   a section annihilated by `a ≠ 0` vanishes locally, hence globally by separation.
2. Apply the local equational criterion for flatness to the single relation `a x = 0`.
   Locally write `x` as a finite linear combination whose coefficients are killed by
   `a`. Step 1 kills all coefficients, and separation then gives `x = 0`.
3. Mathlib's short-exact cone theorem constructs the augmentation to the cokernel,
   proves its specified restriction and shows that it is a quasi-isomorphism.
4. Terms of the cone are biproducts of terms of the degree-zero tensor unit complex.
   These terms are flat, and both complexes vanish above degree zero. Apply the
   bounded-flat criterion with independent coefficient universes to obtain K-flatness.
5. The fixed-factor K-flat tensor comparison computes ordinary total tensor with the
   cone in the derived category. Transport along the augmentation's derived isomorphism
   to obtain the required computation with the quotient for every unbounded complex.
-/
theorem flat_scalar_cyclic_resolution [IsDomain A]
    [HasDerivedCategory.{w} (SheafOfModules.{r} (scalarCyclicRing R))]
    (hflat : IsFlatOnSite (J := J) (R := scalarCyclicBase J A)
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map α)).obj
        (unit (scalarCyclicRing R))))
    (a : A) (ha : a ≠ 0) :
    Mono (scalarCyclicMultiplication R α a) ∧
      ∃ ε : scalarCyclicComplex R α a ⟶
          (CochainComplex.singleFunctor _ 0).obj (scalarCyclicQuotient R α a),
        CochainComplex.mappingCone.inr
            ((CochainComplex.singleFunctor _ 0).map (scalarCyclicMultiplication R α a)) ≫ ε =
          (CochainComplex.singleFunctor _ 0).map
            (cokernel.π (scalarCyclicMultiplication R α a)) ∧
        CochainComplex.IsKFlatResolutionIndependentCoefficients ε ∧
        CochainComplex.IsKFlatIndependentCoefficients
          ((CochainComplex.singleFunctor _ 0).obj (unit (scalarCyclicRing R))) ∧
        ∀ M : CochainComplex (SheafOfModules.{r} (scalarCyclicRing R)) ℤ,
          Nonempty ((siteDerivedTensorIndependentCoefficients J R).obj
              (DerivedCategory.Q.obj M,
                DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
                  (scalarCyclicQuotient R α a))) ≅
            DerivedCategory.Q.obj (CochainComplex.mapBifunctor M
              (scalarCyclicComplex R α a) (curriedTensor _))) := by
  have hm : Mono (scalarCyclicMultiplication R α a) := by
    apply (forget (scalarCyclicRing R)).mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro U x y hxy
    apply sub_eq_zero.mp
    apply flat_scalar_kernel R α hflat a ha U (x - y)
    change (scalarCyclicMultiplication R α a).val.app U x =
      (scalarCyclicMultiplication R α a).val.app U y at hxy
    simpa only [map_sub, sub_eq_zero] using hxy
  have : Mono (scalarCyclicMultiplication R α a) := hm
  obtain ⟨ε, hε, hq⟩ := cone_cokernel_augmentation (scalarCyclicMultiplication R α a)
  have : QuasiIso ε := hq
  obtain ⟨hk, hu⟩ := scalar_cyclic_kflat R α a
  exact ⟨hm, ε, hε, ⟨hq, hk⟩, hu, scalar_cyclic_derived_tensor R α a ε⟩

end SheafOfModules
