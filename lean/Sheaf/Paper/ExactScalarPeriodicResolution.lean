/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.LinearAlgebra.Basis.Basic

/-! # The exact scalar periodic resolution

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-def-localizing-closure-ctf-equals-bc.proof.md, "The examples";
Stacks Project, Tags 03ER, 06YN, 06YQ
(blueprint: lem-sfb-exact-scalar-periodic-resolution).

The complex and its augmentation are constructed from their prescribed components.
The sheaf theorem uses categorical exactness, with no assertion of sectionwise
surjectivity. The final theorem records the ordinary rank-one free resolution.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v r

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace CochainComplex

section Construction

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [HasZeroObject A]

/-- The terms of the periodic complex, cut off above degree zero.
Source: blueprint, "The examples" (blueprint: lem-sfb-exact-scalar-periodic-resolution). -/
def scalarPeriodicX (M : A) (i : ℤ) : A := if i ≤ 0 then M else 0

/-- The differential is the given endomorphism in negative degrees and zero otherwise.
Source: blueprint, "The examples" (blueprint: lem-sfb-exact-scalar-periodic-resolution). -/
def scalarPeriodicD {M : A} (f : M ⟶ M) (i : ℤ) :
    scalarPeriodicX M i ⟶ scalarPeriodicX M (i + 1) :=
  if hi : i < 0 then
    eqToHom (if_pos (le_of_lt hi)) ≫ f ≫
      eqToHom (if_pos (Int.add_one_le_iff.mpr hi)).symm
  else 0

/-- The prescribed differentials compose to zero.
Source: blueprint, "The examples" (blueprint: lem-sfb-exact-scalar-periodic-resolution).
Proof: if both indices are negative the composite is f squared, hence zero.
At the cutoff the second map is zero; above it the first map is zero. -/
theorem scalarPeriodicD_comp {M : A} (f : M ⟶ M) (hf : f ≫ f = 0) (i : ℤ) :
    scalarPeriodicD f i ≫ scalarPeriodicD f (i + 1) = 0 := by
  classical
  by_cases hi : i < 0
  · by_cases hj : i + 1 < 0
    · simp only [scalarPeriodicD, dif_pos hi, dif_pos hj, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← Category.assoc f f, hf, zero_comp, comp_zero]
    · simp [scalarPeriodicD, hj]
  · simp [scalarPeriodicD, hi]

/-- The actual cochain complex with the prescribed nonpositive terms and differentials.
Source: blueprint, "The examples" (blueprint: lem-sfb-exact-scalar-periodic-resolution). -/
def scalarPeriodic {M : A} (f : M ⟶ M) (hf : f ≫ f = 0) : CochainComplex A ℤ :=
  CochainComplex.of (scalarPeriodicX M) (scalarPeriodicD f) (scalarPeriodicD_comp f hf)

/-- Identification of each nonpositive term with the original module.
Source: blueprint, "The examples" (blueprint: lem-sfb-exact-scalar-periodic-resolution). -/
def scalarPeriodicXIso {M : A} (f : M ⟶ M) (hf : f ≫ f = 0)
    (i : ℤ) (hi : i ≤ 0) : (scalarPeriodic f hf).X i ≅ M :=
  eqToIso (if_pos hi)

variable [HasCokernels A]

/-- The degree-zero cokernel map kills the incoming differential.
Source: blueprint, "The examples" (blueprint: lem-sfb-exact-scalar-periodic-resolution).
Proof: the only incoming index is -1. After the term identifications the composite
is f followed by its cokernel quotient, zero by the cokernel equation. -/
theorem scalarPeriodicAugmentation_condition {M : A} (f : M ⟶ M) (hf : f ≫ f = 0)
    (i : ℤ) (hi : (ComplexShape.up ℤ).Rel i 0) :
    (scalarPeriodic f hf).d i 0 ≫
      (scalarPeriodicXIso f hf 0 le_rfl).hom ≫ cokernel.π f = 0 := by
  have hi' : i + 1 = 0 := hi
  have hi0 : i = -1 := by omega
  subst i
  simp [scalarPeriodic, CochainComplex.of.d, scalarPeriodicD,
    scalarPeriodicXIso]

/-- The augmentation has the quotient map in degree zero and zero elsewhere.
Source: blueprint, "The examples" (blueprint: lem-sfb-exact-scalar-periodic-resolution). -/
def scalarPeriodicAugmentation {M : A} (f : M ⟶ M) (hf : f ≫ f = 0) :
    scalarPeriodic f hf ⟶ (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj (cokernel f) :=
  HomologicalComplex.mkHomToSingle
    ((scalarPeriodicXIso f hf 0 le_rfl).hom ≫ cokernel.π f)
    (scalarPeriodicAugmentation_condition f hf)

end Construction

/-- Away from zero the periodic complex is exact: negative degrees are the given
exact short complex and positive-degree terms vanish. Source: blueprint, "The examples". -/
private theorem scalarPeriodic_exactAt
    {B : Type*} [Category* B] [Abelian B] {M : B}
    (f : M ⟶ M) (hf : f ≫ f = 0)
    (he : (ShortComplex.mk f f hf).Exact) (i : ℤ) (hi : i ≠ 0) :
    (scalarPeriodic f hf).ExactAt i := by
  by_cases hn : i < 0
  · rw [HomologicalComplex.exactAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)]
    let e : (scalarPeriodic f hf).sc' (i - 1) i (i + 1) ≅
        ShortComplex.mk f f hf :=
      ShortComplex.isoMk
        (scalarPeriodicXIso f hf (i - 1) (by omega))
        (scalarPeriodicXIso f hf i (by omega))
        (scalarPeriodicXIso f hf (i + 1) (by omega))
        (by simp [scalarPeriodic, CochainComplex.of.d, scalarPeriodicD,
          scalarPeriodicXIso, show i - 1 < 0 by omega])
        (by simp [scalarPeriodic, CochainComplex.of.d, scalarPeriodicD,
          scalarPeriodicXIso, hn])
    exact (ShortComplex.exact_iff_of_iso e).2 he
  · apply HomologicalComplex.ExactAt.of_isZero
    simpa [scalarPeriodic, scalarPeriodicX, show ¬i ≤ 0 by omega] using isZero_zero B

set_option backward.isDefEq.respectTransparency false in
/-- Cokernel exactness gives the augmentation quasi-isomorphism at zero; the other
degrees are exact on both sides. Source: blueprint, "The examples". -/
private theorem scalarPeriodic_quasiIso
    {B : Type*} [Category* B] [Abelian B] {M : B}
    (f : M ⟶ M) (hf : f ≫ f = 0)
    (he : (ShortComplex.mk f f hf).Exact) :
    QuasiIso (scalarPeriodicAugmentation f hf) := by
  rw [quasiIso_iff]
  intro i
  by_cases hi : i = 0
  · subst i
    rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp)]
    rw [ShortComplex.quasiIso_iff_of_zeros' _
      (by simp [scalarPeriodic, CochainComplex.of.d, scalarPeriodicD])
      (by simp) (by simp)]
    constructor
    · let e : ShortComplex.mk
          ((scalarPeriodic f hf).d (-1) 0)
          ((scalarPeriodicAugmentation f hf).f 0)
          (by rw [← (scalarPeriodicAugmentation f hf).comm (-1) 0]; simp) ≅
          ShortComplex.mk f (cokernel.π f) (cokernel.condition f) :=
        ShortComplex.isoMk
          (scalarPeriodicXIso f hf (-1) (by omega))
          (scalarPeriodicXIso f hf 0 le_rfl)
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (cokernel f))
          (by simp [scalarPeriodic, CochainComplex.of.d, scalarPeriodicD,
            scalarPeriodicXIso])
          (by simp [scalarPeriodicAugmentation, HomologicalComplex.mkHomToSingle_f])
      exact (ShortComplex.exact_iff_of_iso e).2
        (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f))
    · change Epi ((scalarPeriodicAugmentation f hf).f 0)
      dsimp [scalarPeriodicAugmentation]
      rw [HomologicalComplex.mkHomToSingle_f]
      infer_instance
  · exact (quasiIsoAt_iff_exactAt' _ i
      (HomologicalComplex.exactAt_single_obj (.up ℤ) 0 _ i hi)).2
      (scalarPeriodic_exactAt f hf he i hi)

end CochainComplex

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

/-- Multiplication by a compatible global section, via the rank-one universal property.
Source: blueprint, "The examples" (blueprint: lem-sfb-exact-scalar-periodic-resolution). -/
def exactScalarMultiplication
    (t : (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)).sections) :
    unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⟶
      unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) :=
  (unitHomEquiv _).symm t

/-- Multiplication by a section whose square is zero has square zero.
Source: blueprint, "The examples" (blueprint: lem-sfb-exact-scalar-periodic-resolution).
Proof: in each object U the composite sends a to t_U squared times a, which is zero.
Extensionality for module-sheaf morphisms gives the asserted equality. -/
theorem exactScalarMultiplication_sq
    (t : (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)).sections)
    (ht : ∀ U : Cᵒᵖ, (@id (R.obj.obj U) (t.val U)) * (@id (R.obj.obj U) (t.val U)) = 0) :
    exactScalarMultiplication R t ≫ exactScalarMultiplication R t = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (@id (R.obj.obj U) a * @id (R.obj.obj U) (t.val U)) *
    @id (R.obj.obj U) (t.val U) = 0
  rw [mul_assoc, ht U, mul_zero]

/-- The nonpositive periodic complex of the square-zero global scalar.
Source: blueprint, "The examples" (blueprint: lem-sfb-exact-scalar-periodic-resolution). -/
def exactScalarPeriodicComplex
    (t : (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)).sections)
    (ht : ∀ U : Cᵒᵖ, (@id (R.obj.obj U) (t.val U)) * (@id (R.obj.obj U) (t.val U)) = 0) :
    CochainComplex
      (ringedSiteModules.{r, r, v, u}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ :=
  CochainComplex.scalarPeriodic (exactScalarMultiplication R t)
    (exactScalarMultiplication_sq R t ht)

/-- The cokernel augmentation of the periodic scalar complex.
Source: blueprint, "The examples" (blueprint: lem-sfb-exact-scalar-periodic-resolution). -/
def exactScalarPeriodicAugmentation
    (t : (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)).sections)
    (ht : ∀ U : Cᵒᵖ, (@id (R.obj.obj U) (t.val U)) * (@id (R.obj.obj U) (t.val U)) = 0) :
    exactScalarPeriodicComplex R t ht ⟶
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (cokernel (exactScalarMultiplication R t)) :=
  CochainComplex.scalarPeriodicAugmentation (exactScalarMultiplication R t)
    (exactScalarMultiplication_sq R t ht)

/-- Exact scalar multiplication gives the prescribed periodic K-flat resolution.
Source: blueprint main-20261015, sec-proetale-coefficients,
sk-def-localizing-closure-ctf-equals-bc.proof.md, "The examples";
Stacks Project, Tags 03ER, 06YN, 06YQ
(blueprint: lem-sfb-exact-scalar-periodic-resolution).

Proof:
1. Compatibility of the global section gives the linear multiplication morphism.
   Its square is zero by the sectionwise square-zero hypothesis, so the displayed
   differentials make a complex. The cokernel equation supplies the augmentation.
2. In every negative degree, the assumed equality of kernel and image subobjects
   gives exactness and vanishing cohomology in the abelian module-sheaf category.
3. The cokernel quotient is epic and its kernel is the multiplication image. Thus
   the augmented sequence is exact at the last copy of O and at E. At zero the
   cohomology is this cokernel; above zero the complex vanishes. The augmentation
   induces the cokernel identification at zero and is therefore a quasi-isomorphism.
4. The unit and zero module sheaves are flat: tensoring with them is respectively
   the identity and zero functor, by the sectionwise tensor formulas and sheafification.
5. The complex is bounded above by zero. Apply
   lem-weil-pbc-independent-bounded-flat-kflat to get K-flatness at the stated
   universes; with Step 3 this is a K-flat resolution (def-pc-kflat-complex).
6. On the one-point site the image is tR and the cokernel is R/tR. Every nonpositive
   term is R with singleton basis 1, as recorded in the accompanying ring theorem. -/
theorem exact_scalar_periodic_resolution
    (t : (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)).sections)
    (ht : ∀ U : Cᵒᵖ, (@id (R.obj.obj U) (t.val U)) * (@id (R.obj.obj U) (t.val U)) = 0)
    (hexact : kernelSubobject (exactScalarMultiplication R t) =
      imageSubobject (exactScalarMultiplication R t)) :
    (ShortComplex.mk (exactScalarMultiplication R t) (exactScalarMultiplication R t)
      (exactScalarMultiplication_sq R t ht)).Exact ∧
    (ShortComplex.mk (exactScalarMultiplication R t)
      (cokernel.π (exactScalarMultiplication R t)) (cokernel.condition _)).Exact ∧
    Epi (cokernel.π (exactScalarMultiplication R t)) ∧
    Nonempty ((exactScalarPeriodicComplex R t ht).homology 0 ≅
      cokernel (exactScalarMultiplication R t)) ∧
    (∀ i : ℤ, i ≠ 0 → IsZero ((exactScalarPeriodicComplex R t ht).homology i)) ∧
    (∀ i : ℤ, IsFlatOnSite.{u, v, r, r} (C := C) (J := J) (R := R)
      ((exactScalarPeriodicComplex R t ht).X i)) ∧
    CochainComplex.IsKFlatResolutionIndependentCoefficients
      (exactScalarPeriodicAugmentation R t ht) := by
  let f := exactScalarMultiplication R t
  let hf := exactScalarMultiplication_sq R t ht
  have he : (ShortComplex.mk f f hf).Exact :=
    (ShortComplex.exact_iff_image_eq_kernel _).2 hexact.symm
  have hq : QuasiIso (exactScalarPeriodicAugmentation R t ht) :=
    CochainComplex.scalarPeriodic_quasiIso f hf he
  have hflat : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R)
      ((exactScalarPeriodicComplex R t ht).X i) := by
    let := isMonoidal_W_independentCoefficients R
    let := monoidalCategory R
    let := tensorPreadditive R
    intro i
    apply (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso R ((exactScalarPeriodicComplex R t ht).X i)).symm
    dsimp [exactScalarPeriodicComplex, CochainComplex.scalarPeriodic,
      CochainComplex.scalarPeriodicX]
    split_ifs
    · exact (ObjectProperty.prop_unit ObjectProperty.flat).2
    · have hz : IsZero (MonoidalCategory.tensorRight
          (0 : SheafOfModules.{r}
            ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) := by
        rw [Functor.isZero_iff]
        intro M
        exact (MonoidalCategory.tensorLeft M).map_isZero (isZero_zero _)
      have := Functor.preservesLimitsOfSize_of_isZero _ hz
      have := Functor.preservesColimitsOfSize_of_isZero _ hz
      change PreservesFiniteLimits _ ∧ PreservesFiniteColimits _
      exact ⟨inferInstance, inferInstance⟩
  have hb : (exactScalarPeriodicComplex R t ht).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    simpa [exactScalarPeriodicComplex, CochainComplex.scalarPeriodic,
      CochainComplex.scalarPeriodicX, show ¬i ≤ 0 by omega] using
      isZero_zero (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
  have : QuasiIso (exactScalarPeriodicAugmentation R t ht) := hq
  refine ⟨he, ShortComplex.cokernelSequence_exact f, inferInstance, ?_, ?_, hflat, hq, ?_⟩
  · exact ⟨asIso (HomologicalComplex.homologyMap
      (exactScalarPeriodicAugmentation R t ht) 0) ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (cokernel f)⟩
  · intro i hi
    exact (CochainComplex.scalarPeriodic_exactAt f hf he i hi).isZero_homology
  · exact isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R
      (exactScalarPeriodicComplex R t ht) 0 hflat

end SheafOfModules

namespace ModuleCat

/-- The square-zero equation for ordinary scalar multiplication.
Source: blueprint, "The examples" (blueprint: lem-sfb-exact-scalar-periodic-resolution).
Proof: the composite applied to a is t squared times a, zero by the hypothesis. -/
theorem scalarPeriodic_mul_sq (S : Type r) [CommRing S] (t : S) (ht : t * t = 0) :
    ModuleCat.ofHom (LinearMap.mul S S t) ≫ ModuleCat.ofHom (LinearMap.mul S S t) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change t * (t * a) = 0
  rw [← mul_assoc, ht, zero_mul]

/-- On the one-point site the same construction is an augmented free resolution
of S/tS, with basis 1 in every nonpositive degree.
Source: blueprint, "The examples" (blueprint: lem-sfb-exact-scalar-periodic-resolution).
Proof: the image of multiplication is the principal ideal tS. The annihilator
hypothesis gives exactness at every negative term, and the cokernel quotient
is onto with this kernel. Hence the augmentation is a quasi-isomorphism. The
canonical cokernel-to-quotient isomorphism respects the quotient maps. In each
nonpositive degree transport the singleton basis of S along the term isomorphism;
its basis vector is sent to 1. This is Step 6 of the node's proof. -/
theorem scalar_periodic_free_resolution (S : Type r) [CommRing S]
    (t : S) (ht : t * t = 0)
    (hexact : ∀ a : S, t * a = 0 ↔ a ∈ Ideal.span ({t} : Set S)) :
    QuasiIso (CochainComplex.scalarPeriodicAugmentation
      (ModuleCat.ofHom (LinearMap.mul S S t)) (scalarPeriodic_mul_sq S t ht)) ∧
    (∃ e : cokernel (ModuleCat.ofHom (LinearMap.mul S S t)) ≅
        ModuleCat.of S (S ⧸ Ideal.span ({t} : Set S)),
      ∀ a : S, e.hom (cokernel.π (ModuleCat.ofHom (LinearMap.mul S S t)) a) =
        Ideal.Quotient.mk (Ideal.span ({t} : Set S)) a) ∧
    (∀ (i : ℤ) (hi : i ≤ 0),
      ∃ b : Module.Basis PUnit S
        ((CochainComplex.scalarPeriodic (ModuleCat.ofHom (LinearMap.mul S S t))
          (scalarPeriodic_mul_sq S t ht)).X i),
        (CochainComplex.scalarPeriodicXIso (ModuleCat.ofHom (LinearMap.mul S S t))
          (scalarPeriodic_mul_sq S t ht) i hi).hom (b PUnit.unit) = 1) := by
  let f := ModuleCat.ofHom (LinearMap.mul S S t)
  let hf := scalarPeriodic_mul_sq S t ht
  have he : (ShortComplex.mk f f hf).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro a ha
    have ha' : t * a = 0 := ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 ((hexact a).1 ha')
    exact ⟨b, (mul_comm t b).trans hb⟩
  refine ⟨CochainComplex.scalarPeriodic_quasiIso f hf he, ?_, ?_⟩
  · let I := Ideal.span ({t} : Set S)
    let q : ModuleCat.of S S ⟶ ModuleCat.of S (S ⧸ I) := ModuleCat.ofHom I.mkQ
    have hfun : Function.Exact f.hom q.hom := by
      intro a
      change Ideal.Quotient.mk I a = 0 ↔ ∃ b : S, t * b = a
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact ⟨fun ⟨b, hb⟩ ↦ ⟨b, hb.symm⟩, fun ⟨b, hb⟩ ↦ ⟨b, hb.symm⟩⟩
    let hq := ModuleCat.isColimitCokernelCofork f q hfun (Submodule.mkQ_surjective I)
    let e := (cokernelIsCokernel f).coconePointUniqueUpToIso hq
    refine ⟨e, fun a ↦ ?_⟩
    have h : cokernel.π f ≫ e.hom = q :=
      (cokernelIsCokernel f).comp_coconePointUniqueUpToIso_hom hq WalkingParallelPair.one
    exact congrArg (fun g : ModuleCat.of S S ⟶ ModuleCat.of S (S ⧸ I) ↦ g a) h
  · intro i hi
    let e := (CochainComplex.scalarPeriodicXIso f hf i hi).toLinearEquiv
    refine ⟨(Module.Basis.singleton PUnit S).map e.symm, ?_⟩
    change e (((Module.Basis.singleton PUnit S).map e.symm) PUnit.unit) = 1
    simp

end ModuleCat
