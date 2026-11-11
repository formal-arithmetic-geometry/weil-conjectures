/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import WeilConjectures.Algebra.Homology.ReductionIsoShift
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear

/-!
# The two-term resolution of the finite coefficient sheaves

md`
(blueprint: det-pe-derived-nakayama-resolution).

All coefficients are continuous condensed rings pulled back from the point. A natural
cone is expressed using the standard cone functor on complexes, with its standard maps.
The comparison with a functor on the derived category also asserts its descent and naturality.

## Main definitions

* `quotientModule`: the continuous finite quotient with its restricted integer action.
* `reductionFunctor`: derived tensor with the pulled-back quotient in degree zero.
* `coneFunctor`: the standard localized mapping-cone model and its maps.

## Main statements

* `derived_nakayama_resolution`: exactness, the natural cone comparison, and the
  specified quotient-power triangles.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open CategoryTheory.Triangulated CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.DerivedNakayama

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The continuous condensed integer ring with its spectral absolute-value topology.
Source: blueprint resolution, On the point, step 1
(blueprint: det-pe-derived-nakayama-resolution). -/
abbrev integerRingSheaf : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Profinite.continuousCoefficientRingSheaf (Padic.coefficientExtensionIntegers l E)

/-- The finite quotient with the quotient topology, not a constant replacement of the integers.
Source: blueprint resolution, On the point, step 1
(blueprint: det-pe-derived-nakayama-resolution). -/
abbrev quotientRingSheaf (n : ℕ) : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Profinite.continuousCoefficientRingSheaf (Padic.coefficientExtensionRing l E n)

/-- Continuous postcomposition with the actual quotient homomorphism.
Source: blueprint resolution, On the point, step 2
(blueprint: det-pe-derived-nakayama-resolution). -/
def reductionRingSheaf (n : ℕ) : integerRingSheaf l E ⟶ quotientRingSheaf l E n :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  ⟨{
      app := fun S ↦ RingCat.ofHom
        ((ULift.ringEquiv
          (R := C(S.unop, Padic.coefficientExtensionRing l E n))).symm.toRingHom.comp
          (((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)).compLeftContinuous _
            continuous_quot_mk).comp ULift.ringEquiv.toRingHom))
      naturality := fun _ _ _ ↦ rfl }⟩

/-- The internal ring underlying the continuous condensed integer ring.
Source: blueprint resolution, On X, step 3
(blueprint: det-pe-derived-nakayama-resolution). -/
abbrev integerRing : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (integerRingSheaf l E)

/-- Pointwise commutativity of the integer ring object.
Source: blueprint resolution, On X, step 3
(blueprint: det-pe-derived-nakayama-resolution). -/
instance integerRing_isCommMonObj : IsCommMonObj (integerRing l E) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Profinite.isCommMonObj_continuousCoefficientRingObj _

/-- The internal finite quotient ring.
Source: blueprint resolution, On X, step 3
(blueprint: det-pe-derived-nakayama-resolution). -/
abbrev quotientRing (n : ℕ) : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (quotientRingSheaf l E n)

/-- Reduction as a morphism of internal rings.
Source: blueprint resolution, On X, step 3
(blueprint: det-pe-derived-nakayama-resolution). -/
abbrev reductionRing (n : ℕ) : integerRing l E ⟶ quotientRing l E n :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (reductionRingSheaf l E n)

/-- The quotient with its canonical restricted scalar action from the integers.
Source: blueprint resolution, On X, step 3
(blueprint: det-pe-derived-nakayama-resolution). -/
abbrev quotientModule (n : ℕ) :
    CategoryTheory.Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) (integerRing l E) :=
  (Mod.comap (reductionRing l E n)).obj (Mod.regular (quotientRing l E n))

/-- The exact inverse image on the internal integer-module objects.
Source: blueprint resolution, On X, step 3
(blueprint: det-pe-derived-nakayama-resolution). -/
abbrev pullback (X : Scheme.{u}) := (upperStarFromPoint X).mapMod (integerRing l E)

/-- The unbounded derived category with the pulled-back condensed integer coefficients.
Source: blueprint resolution, On X, step 5
(blueprint: det-pe-derived-nakayama-resolution). -/
abbrev Derived (X : Scheme.{u}) :=
  DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (integerRing l E) X))

/-- The actual derived reduction functor, with the finite quotient in degree zero.
Source: blueprint resolution, On X, step 5
(blueprint: det-pe-derived-nakayama-resolution). -/
abbrev reductionFunctor (X : Scheme.{u}) (n : ℕ) : Derived l E X ⥤ Derived l E X :=
  (CondensedRing.derivedTensor (integerRing l E) X).flip.obj
    ((DerivedCategory.singleFunctor _ 0).obj ((pullback l E X).obj (quotientModule l E n)))

/-- Degree-zero realization of a coefficient morphism, followed by derived tensor with K.
Source: blueprint resolution, Triangles, step 7
(blueprint: det-pe-derived-nakayama-resolution). -/
def reductionMap (X : Scheme.{u}) {m n : ℕ}
    (f : quotientModule l E m ⟶ quotientModule l E n) :
    reductionFunctor l E X m ⟶ reductionFunctor l E X n :=
  (CondensedRing.derivedTensor (integerRing l E) X).flip.map
    ((DerivedCategory.singleFunctor _ 0).map ((pullback l E X).map f))

/-- Strong monoidal pullback takes the regular module to the regular module.
Source: blueprint resolution, On X, step 3
(blueprint: det-pe-derived-nakayama-resolution).

Proof: both underlying objects are p_X^* R. The transported regular action is the
monoidal comparison followed by p_X^* of multiplication, exactly the multiplication
of the transported ring. Extensionality for module objects and proof irrelevance give
the equality. This is the scalar-action identification used in step 3 of the node. -/
theorem pullback_regular (X : Scheme.{u}) :
    (pullback l E X).obj (Mod.regular (integerRing l E)) =
      Mod.regular (condensedRingObj (integerRing l E) X) := by
  rfl

/-- The regular-module comparison, with underlying identity, obtained from its named equality.
Source: blueprint resolution, On X, step 3
(blueprint: det-pe-derived-nakayama-resolution). -/
def regularPullbackIso (X : Scheme.{u}) :
    (pullback l E X).obj (Mod.regular (integerRing l E)) ≅
      Mod.regular (condensedRingObj (integerRing l E) X) :=
  eqToIso (pullback_regular l E X)

/-- The scalar action induced by an endomorphism of the regular module, using unitors.
Source: blueprint resolution, On X, step 5
(blueprint: det-pe-derived-nakayama-resolution). -/
def scalarOnModules (X : Scheme.{u})
    (d : End (Mod.regular (integerRing l E))) :
    𝟭 (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integerRing l E) X)) ⟶ 𝟭 _ :=
  let dX : End (Mod.regular (condensedRingObj (integerRing l E) X)) :=
    .of ((regularPullbackIso l E X).inv ≫ (pullback l E X).map d.asHom ≫
      (regularPullbackIso l E X).hom)
  (leftUnitorNatIso (CategoryTheory.Mod
    (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (integerRing l E) X))).inv ≫
      (tensoringLeft (CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integerRing l E) X))).map dX.asHom ≫ (leftUnitorNatIso _).hom

/-- Scalar multiplication as an actual chain map, degree by degree.
Source: blueprint resolution, On X, step 5
(blueprint: det-pe-derived-nakayama-resolution). -/
def scalarOnComplex (X : Scheme.{u}) (d : End (Mod.regular (integerRing l E)))
    (C : CochainComplex (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integerRing l E) X)) ℤ) : C ⟶ C :=
  (NatTrans.mapHomologicalComplex (scalarOnModules l E X d) (.up ℤ)).app C

/-- The standard cone model, functorial on complexes and then localized.
Its map is the standard cone map of the square with the same chain map on both sides.
Source: blueprint resolution, On X, step 5
(blueprint: det-pe-derived-nakayama-resolution). -/
def coneFunctor (X : Scheme.{u}) (d : End (Mod.regular (integerRing l E))) :
    CochainComplex (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integerRing l E) X)) ℤ ⥤ Derived l E X where
  obj C := DerivedCategory.Q.obj (CochainComplex.mappingCone (scalarOnComplex l E X d C))
  map {C D} f := DerivedCategory.Q.map
    (CochainComplex.mappingCone.map (scalarOnComplex l E X d C) (scalarOnComplex l E X d D)
      f f ((NatTrans.mapHomologicalComplex
        (scalarOnModules l E X d) (.up ℤ)).naturality f).symm)
  map_id C := by
    rw [CochainComplex.mappingCone.map_id]
    exact DerivedCategory.Q.map_id _
  map_comp f g := by
    rw [CochainComplex.mappingCone.map_comp]
    exact DerivedCategory.Q.map_comp _ _

section ScalarTools
universe v w
open Category BraidedCategory
namespace UnitScalar
variable (A : Type u) [Category.{v} A] [Preadditive A]
  [MonoidalCategory A] [MonoidalPreadditive A]
@[instance_reducible] private def scalarRing : CommRing (End (𝟙_ A)) :=
  { (inferInstance : Ring (End (𝟙_ A))) with
    mul_comm := fun a b ↦ by
      apply End.ext
      have h := unitEndAction_naturality a.asHom b
      simpa only [End.mul_asHom, unitEndAction_unit] using h }
-- A private copy fixes the scalar action on each Hom space.
private def Scalars := End (𝟙_ A)
private instance derivedNakayamaResolutionInst1 : CommRing (Scalars A) := scalarRing A
private def centerHom : Scalars A →+* CatCenter A where
  toFun a := .of
    { app := fun X ↦ (unitEndAction X a).asHom
      naturality := fun _ _ f ↦ (unitEndAction_naturality f a).symm }
  map_one' := CatCenter.ext _ _ fun X ↦ congrArg End.asHom (unitEndAction X).map_one
  map_mul' a b := CatCenter.ext _ _ fun X ↦ congrArg End.asHom ((unitEndAction X).map_mul a b)
  map_zero' := CatCenter.ext _ _ fun X ↦ congrArg End.asHom (unitEndRingHom X).map_zero
  map_add' a b := CatCenter.ext _ _ fun X ↦ congrArg End.asHom ((unitEndRingHom X).map_add a b)
private instance (priority := 2000) scalarLinear : Linear (Scalars A) A :=
  Linear.ofRingMorphism (centerHom A)
private theorem smul_eq {X Y : A} (a : Scalars A) (f : X ⟶ Y) :
    a • f = (unitEndAction X a).asHom ≫ f := rfl
variable [BraidedCategory A]
omit [Preadditive A] [MonoidalPreadditive A] [BraidedCategory A] in
private theorem action_tensor_right (X Y : A) (a : End (𝟙_ A)) :
    X ◁ (unitEndAction Y a).asHom = (unitEndAction (X ⊗ Y) a).asHom := by
  cases a
  simp only [unitEndAction_apply, whiskerLeft_comp]
  monoidal
omit [Preadditive A] [MonoidalPreadditive A] in
private theorem action_left (X : A) (a : End (𝟙_ A)) :
    (unitEndAction X a).asHom = (λ_ X).inv ≫ a.asHom ▷ X ≫ (λ_ X).hom := by
  apply (cancel_epi (λ_ X).hom).mp
  apply (cancel_mono (ρ_ X).inv).mp
  simpa only [unitEndAction_apply, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id, braiding_tensorUnit_left] using
    (braiding_naturality_left a.asHom X).symm
omit [Preadditive A] [MonoidalPreadditive A] in
private theorem action_tensor_left (X Y : A) (a : End (𝟙_ A)) :
    (unitEndAction X a).asHom ▷ Y = (unitEndAction (X ⊗ Y) a).asHom := by
  cases a
  rw [action_left, action_left]
  simp only [comp_whiskerRight]
  monoidal
private instance (priority := 2000) scalarMonoidal :
    MonoidalLinear (Scalars A) A where
  whiskerLeft_smul X _ _ a f := by
    simp only [smul_eq, whiskerLeft_comp, action_tensor_right]
  smul_whiskerRight a _ _ f X := by
    simp only [smul_eq, comp_whiskerRight, action_tensor_left]
end UnitScalar

namespace UnitScalar
variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [HasDerivedCategory.{v} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
attribute [local instance] DerivedCategory.instHasColimitsOfSizeReductionIsoShift
private def scalarNat (r : Scalars A) : 𝟭 (CochainComplex A ℤ) ⟶ 𝟭 _ where
  app C := r • 𝟙 C
  naturality C D f := by simp
private def coneOf (τ : 𝟭 (CochainComplex A ℤ) ⟶ 𝟭 _) :
    CochainComplex A ℤ ⥤ DerivedCategory A where
  obj C := DerivedCategory.Q.obj (CochainComplex.mappingCone (τ.app C))
  map {C D} f := DerivedCategory.Q.map
    (CochainComplex.mappingCone.map (τ.app C) (τ.app D) f f (τ.naturality f).symm)
  map_id C := by
    trans DerivedCategory.Q.map (𝟙 _)
    · apply DerivedCategory.Q.congr_map
      exact CochainComplex.mappingCone.map_id (τ.app C)
    · exact DerivedCategory.Q.map_id _
  map_comp f g := by
    rw [CochainComplex.mappingCone.map_comp]
    exact DerivedCategory.Q.map_comp _ _
private theorem reductionComparison {M : A} (r : Scalars A) (p : 𝟙_ A ⟶ M)
    (w : (r • 𝟙 (𝟙_ A)) ≫ p = 0)
    (hs : (ShortComplex.mk _ _ w).ShortExact)
    (τ : 𝟭 (CochainComplex A ℤ) ⟶ 𝟭 _) (hτ : τ = scalarNat r) :
    Nonempty (DerivedCategory.Q ⋙
      (curriedTensor (DerivedCategory A)).flip.obj
        ((DerivedCategory.singleFunctor A 0).obj M) ≅ coneOf τ) := by
  subst τ
  refine ⟨NatIso.ofComponents (fun C ↦ DerivedCategory.reductionIso w hs C) ?_⟩
  intro C D f
  exact DerivedCategory.reductionIso_hom_naturality w hs f
-- Transport through the named unit comparison using categorical identities.
-- Unfolding the equality of the underlying module records is expensive.
private theorem reductionComparisonViaIso {U M : A} (d : End U) (p : U ⟶ M)
    (w : d.asHom ≫ p = 0) (hs : (ShortComplex.mk _ _ w).ShortExact)
    (e : U ≅ 𝟙_ A) (r : Scalars A)
    (hr : (r : End (𝟙_ A)).asHom = e.inv ≫ d.asHom ≫ e.hom)
    (τ : 𝟭 (CochainComplex A ℤ) ⟶ 𝟭 _) (hτ : τ = scalarNat r) :
    Nonempty (DerivedCategory.Q ⋙
      (curriedTensor (DerivedCategory A)).flip.obj
        ((DerivedCategory.singleFunctor A 0).obj M) ≅ coneOf τ) := by
  have hscalar : r • 𝟙 (𝟙_ A) = e.inv ≫ d.asHom ≫ e.hom := by
    rw [smul_eq, unitEndAction_unit, comp_id, hr]
  let p' := e.inv ≫ p
  have w' : (r • 𝟙 (𝟙_ A)) ≫ p' = 0 := by
    rw [hscalar]
    dsimp [p']
    simp only [assoc, Iso.hom_inv_id_assoc]
    rw [w, comp_zero]
  have hs' : (ShortComplex.mk _ _ w').ShortExact := by
    apply ShortComplex.shortExact_of_iso _ hs
    refine ShortComplex.isoMk e e (Iso.refl _) ?_ ?_
    · dsimp
      rw [hscalar]
      simp
    · dsimp [p']
      simp
  exact reductionComparison r p' w' hs' τ hτ
end UnitScalar

end ScalarTools

section Sectionwise
universe v w
variable {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
  [HasSheafify J Ab.{u + 1}]
private theorem shortExact_of_sectionwise
    (S : ShortComplex (Sheaf J Ab.{u + 1}))
    (hS : ∀ T : Cᵒᵖ,
      ((S.map (sheafToPresheaf J Ab)).map ((evaluation Cᵒᵖ Ab).obj T)).ShortExact) :
    S.ShortExact := by
  let F := sheafToPresheaf J Ab.{u + 1}
  have hk : IsLimit (KernelFork.ofι (S.map F).f (S.map F).zero) :=
    evaluationJointlyReflectsLimits _ fun T ↦
      by
        have := (hS T).mono_f
        exact (KernelFork.isLimitMapConeEquiv ..).2 (hS T).exact.fIsKernel
  have hk' : IsLimit (KernelFork.ofι S.f S.zero) :=
    isLimitOfReflects F ((KernelFork.isLimitMapConeEquiv ..).2 hk)
  have : Mono S.f := mono_of_isLimit_fork hk'
  have : ∀ T, Epi (((S.map F).g).app T) := fun T ↦ (hS T).epi_g
  have : Epi ((S.map F).g) := NatTrans.epi_of_epi_app _
  have hEpi : Epi (F.map S.g) := by
    change Epi ((S.map F).g)
    infer_instance
  have : Epi S.g := Functor.epi_of_epi_map F hEpi
  exact ⟨S.exact_of_f_is_kernel hk'⟩
end Sectionwise

section QuotientTools
universe v
open Category
namespace PowerQuotients
variable {C : Type u} [Category.{v} C] [Abelian C]
  {U : C} (d : End U) (B : ℕ → C) (r : ∀ n, U ⟶ B n)
  (hz : ∀ n, (d ^ n).asHom ≫ r n = 0)
  (hs : ∀ n, (ShortComplex.mk _ _ (hz n)).ShortExact)
private def quotientIso (n : ℕ) : cokernel (d ^ n).asHom ≅ B n := by
  have := (hs n).epi_g
  exact IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
    (hs n).exact.gIsCokernel
private theorem quotientIso_hom (n : ℕ) :
    cokernel.π (d ^ n).asHom ≫ (quotientIso d B r hz hs n).hom = r n := by
  have := (hs n).epi_g
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
    (hs n).exact.gIsCokernel WalkingParallelPair.one
private theorem quotientIso_inv (n : ℕ) :
    r n ≫ (quotientIso d B r hz hs n).inv = cokernel.π (d ^ n).asHom := by
  rw [← quotientIso_hom d B r hz hs n, Category.assoc, Iso.hom_inv_id, comp_id]
include hz hs in
private theorem sequences :
    ∃ (i : ∀ m n, B m ⟶ B (n + m)) (q : ∀ m n, B (n + m) ⟶ B n),
      (∀ m n, r m ≫ i m n = (d ^ n).asHom ≫ r (n + m)) ∧
      (∀ m n, r (n + m) ≫ q m n = r n) ∧
      ∀ m n, ∃ h : i m n ≫ q m n = 0, (ShortComplex.mk _ _ h).ShortExact := by
  have hpow (m n : ℕ) : (d ^ m).asHom ≫ (d ^ n).asHom = (d ^ (n + m)).asHom := by
    rw [← End.mul_asHom, ← pow_add]
  let e (m n : ℕ) : cokernel ((d ^ m).asHom ≫ (d ^ n).asHom) ≅ B (n + m) :=
    cokernelIsoOfEq (hpow m n) ≪≫ quotientIso d B r hz hs (n + m)
  let S (m n : ℕ) := kernelCokernelCompSequence.snakeInput (d ^ m).asHom (d ^ n).asHom
  let i (m n : ℕ) : B m ⟶ B (n + m) :=
    (quotientIso d B r hz hs m).inv ≫ (S m n).L₃.f ≫ (e m n).hom
  let q (m n : ℕ) : B (n + m) ⟶ B n :=
    (e m n).inv ≫ (S m n).L₃.g ≫ (quotientIso d B r hz hs n).hom
  have he (m n : ℕ) :
      cokernel.π ((d ^ m).asHom ≫ (d ^ n).asHom) ≫ (e m n).hom = r (n + m) := by
    simp only [e, Iso.trans_hom, ← assoc, π_comp_cokernelIsoOfEq_hom]
    exact quotientIso_hom d B r hz hs _
  have he' (m n : ℕ) :
      r (n + m) ≫ (e m n).inv = cokernel.π ((d ^ m).asHom ≫ (d ^ n).asHom) := by
    rw [← he, assoc, Iso.hom_inv_id, comp_id]
  refine ⟨i, q, ?_, ?_, ?_⟩
  · intro m n
    dsimp [i]
    rw [← assoc, quotientIso_inv]
    change cokernel.π (d ^ m).asHom ≫
      cokernel.map (d ^ m).asHom ((d ^ m).asHom ≫ (d ^ n).asHom) (𝟙 U) (d ^ n).asHom (by simp) ≫ _ = _
    simp only [cokernel.map, cokernel.π_desc_assoc, assoc, he]
  · intro m n
    dsimp [q]
    rw [← assoc, he']
    change cokernel.π ((d ^ m).asHom ≫ (d ^ n).asHom) ≫
      cokernel.map ((d ^ m).asHom ≫ (d ^ n).asHom) (d ^ n).asHom (d ^ m).asHom (𝟙 U) (by simp) ≫ _ = _
    simp only [cokernel.map, cokernel.π_desc_assoc, id_comp, quotientIso_hom]
  · intro m n
    have hz' : i m n ≫ q m n = 0 := by simp [i, q]
    refine ⟨hz', ?_⟩
    have : Mono (d ^ n).asHom := (hs n).mono_f
    have hmono : Mono (S m n).L₃.f := by
      have h0 : (S m n).L₂'.f = 0 :=
        (isZero_kernel_of_mono (d ^ n).asHom).eq_of_src _ _
      exact ((S m n).L₂'.exact_iff_mono h0).mp (S m n).L₂'_exact
    have : Epi (S m n).L₂.g := by
      dsimp [S, kernelCokernelCompSequence.snakeInput]
      infer_instance
    have : Epi (S m n).L₃.g := (S m n).epi_L₃_g
    have hsep : (S m n).L₃.ShortExact := ⟨(S m n).L₃_exact⟩
    apply ShortComplex.shortExact_of_iso _ hsep
    exact ShortComplex.isoMk (quotientIso d B r hz hs m) (e m n)
      (quotientIso d B r hz hs n) (by simp [i]) (by simp [q])
end PowerQuotients

end QuotientTools

private theorem coefficientTopology :
    (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace =
      @UniformSpace.toTopologicalSpace E
        (Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toUniformSpace := by
  have h : (spectralNorm.normedField (Padic l) E).toPseudoMetricSpace =
      (Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toPseudoMetricSpace :=
    PseudoMetricSpace.ext (by
      ext x y
      change spectralNorm (Padic l) E (x - y) = spectralNorm (Padic l) E (-x + y)
      rw [neg_add_eq_sub, ← neg_sub x y,
        spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)])
  exact congrArg (fun m ↦ m.toUniformSpace.toTopologicalSpace) h

private theorem quotientDiscrete (n : ℕ) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    DiscreteTopology (Padic.coefficientExtensionRing l E n) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  cases n with
  | zero =>
    have : Subsingleton (Padic.coefficientExtensionRing l E 0) := by
      apply Ideal.Quotient.subsingleton_iff.mpr
      simp [Padic.coefficientExtensionIdeal]
    exact Subsingleton.discreteTopology
  | succ n =>
    have htop := coefficientTopology l E
    have hb : ∀ x : Padic.coefficientExtensionIntegers l E,
        (nhds x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
          {y | Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) y =
            Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x}) := by
      have h := Padic.coefficientExtension_integers_coset_basis l E
      change ∀ x, Filter.HasBasis
        (@nhds _ (TopologicalSpace.induced Subtype.val
          (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace) x) _ _ at h
      rw [htop] at h
      exact h
    have hq : IsLocallyConstant
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) := by
      apply (IsLocallyConstant.iff_eventually_eq _).mpr
      intro x
      exact (hb x).mem_of_mem (i := n) trivial
    apply discreteTopology_iff_isOpen_singleton.mpr
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← isQuotientMap_quot_mk.isOpen_preimage]
    exact hq.isOpen_fiber _

private def uniformizerMap : integerRing l E ⟶ integerRing l E := by
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  refine ⟨{ app := fun S ↦ ?_, naturality := ?_ }⟩
  · exact AddCommGrpCat.ofHom
      { toFun := fun f ↦ ULift.up
          (ContinuousMap.const S.unop (Padic.coefficientExtensionUniformizer l E) * f.down)
        map_zero' := by apply ULift.ext; exact mul_zero _
        map_add' := by intro f g; apply ULift.ext; exact mul_add _ _ _ }
  · intro S T f
    rfl

private def uniformizerEnd : End (Mod.regular (integerRing l E)) := by
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  refine .of (Mod.homMk (uniformizerMap l E) ?_)
  change MonObj.mul ≫ uniformizerMap l E =
    integerRing l E ◁ uniformizerMap l E ≫ MonObj.mul
  apply Sheaf.tensor_hom_ext
  simp only [Functor.map_comp]
  rw [← Category.assoc, Sheaf.μ_sheafToPresheaf_comp_map_mul_sheafCompose]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc,
    Sheaf.μ_sheafToPresheaf_comp_map_mul_sheafCompose]
  apply NatTrans.ext
  funext S
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.toIntLinearMap_injective
  apply TensorProduct.ext'
  intro f g
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change Padic.coefficientExtensionUniformizer l E * (f.down x * g.down x) =
    f.down x * (Padic.coefficientExtensionUniformizer l E * g.down x)
  ring

private def reductionHom (n : ℕ) :
    Mod.regular (integerRing l E) ⟶ quotientModule l E n :=
  Mod.homMk (reductionRing l E n) (by
    change MonObj.mul ≫ reductionRing l E n =
      integerRing l E ◁ reductionRing l E n ≫
        reductionRing l E n ▷ quotientRing l E n ≫ MonObj.mul
    simpa only [tensorHom_def', Category.assoc] using
      (IsMonHom.mul_hom (reductionRing l E n)))

private theorem uniformizerEnd_apply (S : Profinite.{u}ᵒᵖ)
    (f : (integerRing l E).obj.obj S) (x : S.unop) :
    (((uniformizerEnd l E).asHom.hom.hom.app S) f).down x =
      Padic.coefficientExtensionUniformizer l E * f.down x := by
  rfl

private theorem uniformizer_ne_zero : Padic.coefficientExtensionUniformizer l E ≠ 0 := by
  let h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hm : Padic.coefficientExtensionMaximalIdeal l E ≠ ⊥ :=
    h.2.2.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  intro h0
  apply hm
  rw [← hgen, h0, Ideal.span_singleton_eq_bot]

private theorem uniformizerPower_apply (n : ℕ) (S : Profinite.{u}ᵒᵖ)
    (f : (integerRing l E).obj.obj S) (s : S.unop) :
    (((uniformizerEnd l E ^ n).asHom.hom.hom.app S) f).down s =
      Padic.coefficientExtensionUniformizer l E ^ n * f.down s := by
  induction n generalizing f with
  | zero =>
    change f.down s = _
    simp
  | succ n ih =>
    rw [pow_succ, End.mul_asHom]
    change (((uniformizerEnd l E ^ n).asHom.hom.hom.app S)
      (((uniformizerEnd l E).asHom.hom.hom.app S) f)).down s = _
    rw [ih, uniformizerEnd_apply, pow_succ, mul_assoc]

private theorem reduction_zero (n : ℕ) :
    (uniformizerEnd l E ^ n).asHom ≫ reductionHom l E n = 0 := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  apply Mod.hom_ext
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext S
  apply AddCommGrpCat.hom_ext
  ext f
  apply ULift.ext
  apply ContinuousMap.ext
  intro s
  change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
      ((((uniformizerEnd l E ^ n).asHom.hom.hom.app S) f).down s) = 0
  rw [uniformizerPower_apply, map_mul]
  have h : Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
      (Padic.coefficientExtensionUniformizer l E ^ n) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  rw [h, zero_mul]

private instance pointFiniteLimits : PreservesFiniteLimits pointUpperStar.{u} := by
  have : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
    AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
  dsimp [pointUpperStar, Functor.sheafPullbackConstruction.sheafPullback]
  infer_instance

private instance pullbackFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (pullback l E X) := by
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    dsimp [upperStarFromPoint]
    infer_instance
  dsimp [pullback]
  infer_instance

private instance pullbackFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (pullback l E X) := by
  have : (upperStarFromPoint X).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint
  have : PreservesFiniteColimits (upperStarFromPoint X) := by infer_instance
  dsimp [pullback]
  infer_instance

private theorem pointResolution (n : ℕ) :
    (ShortComplex.mk (uniformizerEnd l E ^ n).asHom (reductionHom l E n)
      (reduction_zero l E n)).ShortExact := by
  let S := ShortComplex.mk (uniformizerEnd l E ^ n).asHom (reductionHom l E n)
    (reduction_zero l E n)
  have hs : (S.map (Mod.forget _)).ShortExact := by
    apply shortExact_of_sectionwise
    intro T
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let := quotientDiscrete l E n
    let S' := ((S.map (Mod.forget _)).map
      (sheafToPresheaf (coherentTopology Profinite.{u}) Ab)).map
        ((evaluation Profinite.{u}ᵒᵖ Ab).obj T)
    have hf : Function.Injective S'.f := by
      intro f g h
      apply ULift.ext
      apply ContinuousMap.ext
      intro t
      have h' := congrArg (fun f ↦ f.down t) h
      change (((uniformizerEnd l E ^ n).asHom.hom.hom.app T) f).down t =
        (((uniformizerEnd l E ^ n).asHom.hom.hom.app T) g).down t at h'
      rw [uniformizerPower_apply, uniformizerPower_apply] at h'
      exact mul_left_cancel₀ (pow_ne_zero n (uniformizer_ne_zero l E)) h'
    have hg : Function.Surjective S'.g := by
      intro f
      let lift : Padic.coefficientExtensionRing l E n →
          Padic.coefficientExtensionIntegers l E :=
        Function.surjInv Ideal.Quotient.mk_surjective
      refine ⟨ULift.up ⟨lift ∘ f.down, continuous_of_discreteTopology.comp f.down.continuous⟩, ?_⟩
      apply ULift.ext
      apply ContinuousMap.ext
      intro t
      exact Function.surjInv_eq Ideal.Quotient.mk_surjective _
    have he : S'.Exact := by
      apply S'.ab_exact_iff.mpr
      intro f hf
      have hdiv : ∀ t : T.unop, (f.down t : E) ∈ Set.range
          (fun a : Padic.coefficientExtensionIntegers l E ↦
            (Padic.coefficientExtensionUniformizer l E : E) ^ n * (a : E)) := by
        intro t
        have hft := congrArg (fun f ↦ f.down t) hf
        change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n) (f.down t) = 0 at hft
        rw [Ideal.Quotient.eq_zero_iff_mem, Padic.coefficientExtensionIdeal,
          Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hft
        obtain ⟨a, ha⟩ := hft
        refine ⟨a, ?_⟩
        have ha' := congrArg
          (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) ha.symm
        simpa using ha'
      obtain ⟨g, hg, hgf, _⟩ := (Padic.continuous_uniformizer_division l E n).2
        f.down f.down.continuous hdiv
      refine ⟨ULift.up ⟨g, hg⟩, ?_⟩
      apply ULift.ext
      apply ContinuousMap.ext
      intro t
      change (((uniformizerEnd l E ^ n).asHom.hom.hom.app T)
        (ULift.up (⟨g, hg⟩ : C(T.unop, Padic.coefficientExtensionIntegers l E)))).down t = _
      rw [uniformizerPower_apply]
      exact Subtype.ext (by simpa using hgf t)
    have : Mono S'.f := (AddCommGrpCat.mono_iff_injective _).mpr hf
    have : Epi S'.g := (AddCommGrpCat.epi_iff_surjective _).mpr hg
    exact ⟨he⟩
  have := hs.mono_f
  have := hs.epi_g
  have : Mono S.f := Functor.mono_of_mono_map (Mod.forget _) hs.mono_f
  have : Epi S.g := Functor.epi_of_epi_map (Mod.forget _) hs.epi_g
  exact ⟨(S.exact_map_iff_of_faithful (Mod.forget _)).mp hs.exact⟩

private def unitEndOnX (X : Scheme.{u})
    (d : End (Mod.regular (integerRing l E))) :
    UnitScalar.Scalars (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integerRing l E) X)) :=
  .of ((regularPullbackIso l E X).inv ≫ (pullback l E X).map d.asHom ≫
    (regularPullbackIso l E X).hom)

private theorem scalarOnComplex_eq (X : Scheme.{u})
    (d : End (Mod.regular (integerRing l E)))
    (C : CochainComplex (CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integerRing l E) X)) ℤ) :
    scalarOnComplex l E X d C = unitEndOnX l E X d • 𝟙 C := by
  apply HomologicalComplex.Hom.ext
  funext j
  change (λ_ (C.X j)).inv ≫ (unitEndOnX l E X d).asHom ▷ C.X j ≫ (λ_ (C.X j)).hom =
    unitEndOnX l E X d • 𝟙 (C.X j)
  rw [UnitScalar.smul_eq, Category.comp_id, UnitScalar.action_left]

private theorem naturalCone (X : Scheme.{u}) (n : ℕ) :
    Nonempty (DerivedCategory.Q ⋙ reductionFunctor l E X n ≅
      coneFunctor l E X (uniformizerEnd l E ^ n)) := by
  let A := CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (integerRing l E) X)
  let r : UnitScalar.Scalars A := unitEndOnX l E X (uniformizerEnd l E ^ n)
  let τ : 𝟭 (CochainComplex A ℤ) ⟶ 𝟭 _ :=
    NatTrans.mapHomologicalComplex
      (scalarOnModules l E X (uniformizerEnd l E ^ n)) (.up ℤ)
  have hτ : τ = UnitScalar.scalarNat r := by
    apply NatTrans.ext
    funext C
    exact scalarOnComplex_eq l E X (uniformizerEnd l E ^ n) C
  change Nonempty (DerivedCategory.Q ⋙
    (curriedTensor (Derived l E X)).flip.obj
      ((DerivedCategory.singleFunctor A 0).obj
        ((pullback l E X).obj (quotientModule l E n))) ≅ UnitScalar.coneOf τ)
  let S := (ShortComplex.mk (uniformizerEnd l E ^ n).asHom (reductionHom l E n)
    (reduction_zero l E n)).map (pullback l E X)
  exact UnitScalar.reductionComparisonViaIso (.of S.f) S.g S.zero
    ((pointResolution l E n).map_of_exact (pullback l E X))
    (regularPullbackIso l E X) r rfl τ hτ

/-- The coefficient sequence, its natural cone interpretation, and the quotient-power triangles.
(blueprint: det-pe-derived-nakayama-resolution).

Proof:
1. The DVR theorem gives a nonzero uniformizer, continuous division on its image and finite
   quotient rings. Its positive-power ideals are open, so their quotient topologies are discrete
   (`lem-weil-l-adic-extension-integers-dvr`, `lem-weil-pbc-standard-quotients-perfect`).
2. On each profinite S, division identifies the kernel and a lift chosen on each clopen fibre
   proves surjectivity of continuous reduction. Kernels are sectionwise and cokernels sheafify
   (`lem-weil-pbc-sheafification-exact`); all maps are linear for pointwise actions.
3. Exact monoidal inverse image from the point transports this sequence and its actions to X
   (`lem-weil-pbc-left-exact-site-inverse-image-tensor`, `lem-sfb-finite-upper-star-exact`).
   The internal/section-module equivalence preserves underlying sheaves
   (`def-weil-pbc-internal-abelian-sheaf-module-equivalence`,
   `lem-weil-pbc-sheaf-tensor-closed`, `def-weil-sheaf-of-modules-category`).
4. The complex [R -- pi^n --> R] in degrees -1,0 augments quasi-isomorphically to B_n[0].
   Its rank-one free terms are flat and it is bounded above, hence K-flat
   (`lem-weil-pbc-independent-bounded-flat-kflat`, `def-pc-flat-sheaf-modules`).
5. Choose a K-flat representative for arbitrary unbounded K (`lem-pc-kflat-resolution`).
   Tensor-model descent (`lem-weil-pbc-site-derived-tensor-descent`) and signed interchange
   compute its reduction by the cone differential (dx + pi^n y, -dy). This is functorial in
   chain maps. The displayed natural isomorphism identifies this standard cone model with
   the reduction functor after localization; hence it descends naturally to the derived category.
6. The maps [x] |-> [pi^n x] and [y] |-> [y] give the short exact quotient-power sequence:
   cancellation proves injectivity, representatives give the kernel and surjectivity. Finite
   discreteness gives continuous lifts on clopen fibres, and exact pullback gives the X sequence.
7. Its short-exact-sequence triangle (`lem-weil-pbc-complex-ses-triangle`) stays distinguished
   after derived tensor with K (`lem-sc-source-kflat-tensor-left-triangulated`). The two arrows
   are precisely the displayed derived images of the normalized quotient maps. Take m=1 for
   the final triangle. No boundedness of K or invertibility of l on X is used. -/
theorem derived_nakayama_resolution :
    ∃ (d : End (Mod.regular (integerRing l E))),
      (∀ (S : Profinite.{u}ᵒᵖ) (f : (integerRing l E).obj.obj S) (s : S.unop),
        ((d.asHom.hom.hom.app S) f).down s =
          Padic.coefficientExtensionUniformizer l E * f.down s) ∧
      ∃ (r : ∀ n : ℕ, Mod.regular (integerRing l E) ⟶ quotientModule l E n),
        (∀ n : ℕ, (r n).hom = reductionRing l E n) ∧
        ∃ (i : ∀ m n : ℕ, quotientModule l E m ⟶ quotientModule l E (n + m))
          (q : ∀ m n : ℕ, quotientModule l E (n + m) ⟶ quotientModule l E n),
          (∀ m n : ℕ, r m ≫ i m n = (d ^ n).asHom ≫ r (n + m)) ∧
          (∀ m n : ℕ, r (n + m) ≫ q m n = r n) ∧
          ∀ (X : Scheme.{u}) (n : ℕ), 1 ≤ n →
            (∃ h : (pullback l E X).map (d ^ n).asHom ≫ (pullback l E X).map (r n) = 0,
              (ShortComplex.mk _ _ h).ShortExact) ∧
            Nonempty (DerivedCategory.Q ⋙ reductionFunctor l E X n ≅
              coneFunctor l E X (d ^ n)) ∧
            (∀ (m : ℕ), 1 ≤ m → m ≤ n → ∀ K : Derived l E X,
              ∃ δ : (reductionFunctor l E X n).obj K ⟶
                  ((reductionFunctor l E X m).obj K)⟦(1 : ℤ)⟧,
                Triangle.mk ((reductionMap l E X (i m n)).app K)
                  ((reductionMap l E X (q m n)).app K) δ ∈ distTriang (Derived l E X)) := by
  obtain ⟨i, q, hi, hq, hseq⟩ := PowerQuotients.sequences
    (uniformizerEnd l E) (quotientModule l E) (reductionHom l E)
    (reduction_zero l E) (pointResolution l E)
  refine ⟨uniformizerEnd l E, uniformizerEnd_apply l E,
    reductionHom l E, fun _ ↦ rfl, i, q, hi, hq, ?_⟩
  intro X n hn
  have hs := (pointResolution l E n).map_of_exact (pullback l E X)
  refine ⟨⟨_, hs⟩, naturalCone l E X n, ?_⟩
  intro m hm hmn K
  obtain ⟨hz, hshort⟩ := hseq m n
  let A := CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (integerRing l E) X)
  let S := ((ShortComplex.mk (i m n) (q m n) hz).map (pullback l E X)).map
    (HomologicalComplex.single A (.up ℤ) 0)
  have hsS : S.ShortExact :=
    (hshort.map_of_exact (pullback l E X)).map_of_exact _
  let T := DerivedCategory.triangleOfSES hsS
  let F := tensorLeft K
  refine ⟨(F.mapTriangle.obj T).mor₃, ?_⟩
  change F.mapTriangle.obj T ∈ distTriang (Derived l E X)
  exact F.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished hsS)

end AlgebraicGeometry.ProEtale.DerivedNakayama
