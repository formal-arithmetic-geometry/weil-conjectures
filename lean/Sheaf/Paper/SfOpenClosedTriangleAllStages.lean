/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Paper.IntegralRationalQbarCompactSupport
public import Sheaf.AlgebraicGeometry.FiniteOpenClosedRecollement
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.Paper.IntegralCompactSupportCoefficientData
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlat
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Sheaf.Paper.PbcRationalTransport
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.PbcScalarExtension
import Sheaf.Paper.PbcDescentFunctors
import Sheaf.Paper.PbcVerdierAxioms
import Sheaf.AlgebraicGeometry.FrobeniusDetailed
import Sheaf.CategoryTheory.MateIsoAlongEquivalences
import Sheaf.Paper.BasicOperationsCoefficientReduction
import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.Paper.SfCommonStageDirectImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement

/-!
# The canonical open-closed triangle at all coefficient stages

Source: Weil blueprint, sec-smooth-purity, prop-sf-open-closed-triangle-all-stages,
order 1851 (current main: order 2195)
(blueprint: prop-sf-open-closed-triangle-all-stages).

The integral presentation uses the actual closed inverse-image/direct-image unit.
Its kernel is the open term, with its kernel inclusion as counit. This fixes the
maps before passage to complexes, completion, scalar localization, or common stages.

## Main statements

* `sfOpenClosedTriangle_finite`: canonical finite-coefficient triangle and uniqueness.
* `sfOpenClosedTriangle_integral_rational`: normalized integral and rational triangles.
* `sfOpenClosedTriangle_qbar`: the common-stage triangle.
* `sfOpenClosedTriangle_rational_weil`, `sfOpenClosedTriangle_qbar_weil`: all three
  arrows are equivariant for the recorded fixed-pair Weil structures.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u v w w₁
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical inverse-image coefficient map, adjoint to the completed structural
map. Source: blueprint proof step 3; Stacks 098T
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfRecollementCoefficientMap {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).symm
    (sfCompletedCoefficientMap l E f)

/-- The actual completed coefficient comparison is invertible.
Source: blueprint proof step 3; Stacks 098T
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: the normalized structural map has precisely the constant finite quotient
coordinates. Profinite coefficient inverse image identifies its adjunct with the
canonical limit comparison, which is an isomorphism. -/
@[instance] theorem sfRecollementCoefficientMap_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (sfRecollementCoefficientMap l E f) := by
  exact PurCompactSupport.completedPullMap_isIso l E f

/-- The normalized ordinary integral module adjunction.
Source: blueprint proof steps 3 and 7; Stacks 03D2, 07A6
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfRecollementModuleAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  proEtaleRingModuleAdjunction f (completedIntegralCommRingSheafUnrestricted l E Y)
    (completedIntegralCommRingSheafUnrestricted l E X)
    (asIso (sfRecollementCoefficientMap l E f))

/-- The closed term on module sheaves, before taking its derived functor.
Source: blueprint proof step 7; Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfRecollementModuleClosed {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  proEtaleRingModulePullback i (completedIntegralCommRingSheafUnrestricted l E X)
      (completedIntegralCommRingSheafUnrestricted l E Z)
      (asIso (sfRecollementCoefficientMap l E i)) ⋙
    proEtaleRingModuleDirectImage i (completedIntegralCommRingSheafUnrestricted l E X)
      (completedIntegralCommRingSheafUnrestricted l E Z)
      (asIso (sfRecollementCoefficientMap l E i))

/-- The closed unit, on actual completed-coefficient module sheaves.
Source: blueprint proof step 7; Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfRecollementModuleUnit {Z X : Scheme.{u}} (i : Z ⟶ X) :
    𝟭 (scalarReductionSource.{u, u} l E X) ⟶ sfRecollementModuleClosed l E i :=
  (sfRecollementModuleAdjunction l E i).unit

/-- The open term is the kernel of the closed unit. The ringed localization sequence
identifies this exact kernel, with its inclusion, with j!j* and its counit.
Source: blueprint proof steps 1 and 7; Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfRecollementModuleOpen {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  kernel (sfRecollementModuleUnit l E i)

/-- The specified open counit in the kernel presentation.
Source: blueprint proof step 7; Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfRecollementModuleCounit {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  kernel.ι (sfRecollementModuleUnit l E i)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sfLocalCoefficientEquivalence (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R := by
  let : (CategoryTheory.Equivalence.refl (C := X.ProEt)).functor.IsContinuous
      (ProEt.topology X) (ProEt.topology X) := by
    change (𝟭 X.ProEt).IsContinuous _ _
    infer_instance
  let : (CategoryTheory.Equivalence.refl (C := X.ProEt)).inverse.IsContinuous
      (ProEt.topology X) (ProEt.topology X) := by
    change (𝟭 X.ProEt).IsContinuous _ _
    infer_instance
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (J := ProEt.topology X) (K := ProEt.topology X) (S := R) (R := S)
    (CategoryTheory.Equivalence.refl (C := X.ProEt)) c.hom c.inv
    (by
      apply NatTrans.ext
      funext U
      dsimp [CategoryTheory.Equivalence.refl]
      erw [S.obj.map_id]
      exact congrArg (fun q ↦ q.hom.app U) c.inv_hom_id.symm)
    (by
      apply NatTrans.ext
      funext U
      dsimp [CategoryTheory.Equivalence.refl]
      erw [R.obj.map_id, Category.comp_id]
      exact congrArg (fun q ↦ q.hom.app U) c.hom_inv_id)

private noncomputable def sfLocalCoefficientTransport {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    proEtaleRingModules X S ≌
      proEtaleRingModules X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) :=
  sfLocalCoefficientEquivalence X
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sfLocalDirectImageComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    proEtaleRingModuleDirectImage f R S c ≅
      (sfLocalCoefficientTransport f R S c).functor ⋙ proEtaleRingedDirectImage f R := by
  let φ : proEtaleModuleCoefficients R ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj
          (proEtaleModuleCoefficients
            ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)) :=
    ⟨Functor.whiskerRight ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let ψ : proEtaleModuleCoefficients
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) ⟶
        proEtaleModuleCoefficients S := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom
  exact (SheafOfModules.pushforwardComp (F := proEtaleBaseChange f)
    (G := 𝟭 X.ProEt) (K' := ProEt.topology X)
    (R' := proEtaleModuleCoefficients S) φ ψ).symm

private noncomputable def sfLocalPullbackComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (a : proEtaleModuleInverseImage f R ⊣ proEtaleRingedDirectImage f R) :
    proEtaleRingModulePullback f R S c ≅
      proEtaleModuleInverseImage f R ⋙ (sfLocalCoefficientTransport f R S c).inverse :=
  (proEtaleRingModuleAdjunction f R S c).leftAdjointUniq
    ((a.comp (sfLocalCoefficientTransport f R S c).symm.toAdjunction).ofNatIsoRight
      (sfLocalDirectImageComparison f R S c).symm)

private noncomputable def sfLocalUnitKernelCompEquivalenceIso
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (e : D ≌ E) :
    kernel a.unit ≅ kernel (a.comp e.toAdjunction).unit := by
  let q : L ⋙ R ≅ (L ⋙ e.functor) ⋙ (e.inverse ⋙ R) :=
    Functor.isoWhiskerLeft L
      ((Functor.leftUnitor R).symm ≪≫ Functor.isoWhiskerRight e.unitIso R ≪≫
        Functor.associator _ _ _) ≪≫ (Functor.associator _ _ _).symm
  refine kernel.mapIso _ _ (Iso.refl _) q ?_
  ext X
  simp [q, Adjunction.comp_unit_app]

private noncomputable def sfLocalUnitKernelIsoOfLeftIso
    {C D : Type*} [Category* C] [Category* D] [Abelian C]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R') (e : L ≅ L') :
    kernel a.unit ≅ kernel b.unit := by
  let b' := b.ofNatIsoLeft e.symm
  let r := a.rightAdjointUniq b'
  let q : L ⋙ R ≅ L' ⋙ R' :=
    Functor.isoWhiskerLeft L r ≪≫ Functor.isoWhiskerRight e R'
  refine kernel.mapIso _ _ (Iso.refl _) q ?_
  ext X
  change a.unit.app X ≫ (r.hom.app (L.obj X) ≫ R'.map (e.hom.app X)) =
    𝟙 X ≫ b.unit.app X
  rw [← Category.assoc, Adjunction.unit_rightAdjointUniq_hom_app]
  simp [b', Adjunction.ofNatIsoLeft_unit, ← R'.map_comp]

private theorem sfLocalUnitEpiOfLeftIso
    {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R') (e : L ≅ L')
    (X : C) [Epi (b.unit.app X)] : Epi (a.unit.app X) := by
  let b' := b.ofNatIsoLeft e.symm
  let r := a.rightAdjointUniq b'
  have he : a.unit.app X ≫ (r.hom.app (L.obj X) ≫ R'.map (e.hom.app X)) =
      b.unit.app X := by
    rw [← Category.assoc, Adjunction.unit_rightAdjointUniq_hom_app]
    simp [b', Adjunction.ofNatIsoLeft_unit, ← R'.map_comp]
  have : Epi (a.unit.app X ≫ (r.hom.app (L.obj X) ≫ R'.map (e.hom.app X))) := by
    rw [he]
    infer_instance
  exact (epi_comp_iff_of_isIso (a.unit.app X)
    (r.hom.app (L.obj X) ≫ R'.map (e.hom.app X))).1 inferInstance

/-- Exactness and additivity of both localization terms.
Source: blueprint proof steps 1, 3--7; Stacks 09AH, 09BM
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: profinite coefficients identify ordinary inverse image with restriction.
Ringed open-closed localization identifies the kernel term with open extension of
restriction and the closed term with closed direct image of restriction. All four
module functors are exact and additive; these properties pass to their composites
and across the kernel identification. -/
theorem sfRecollementModule_exact {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] :
    (sfRecollementModuleOpen l E i).Additive ∧
    PreservesFiniteLimits (sfRecollementModuleOpen l E i) ∧
    PreservesFiniteColimits (sfRecollementModuleOpen l E i) ∧
    (sfRecollementModuleClosed l E i).Additive ∧
    PreservesFiniteLimits (sfRecollementModuleClosed l E i) ∧
    PreservesFiniteColimits (sfRecollementModuleClosed l E i) := by
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let S := completedIntegralCommRingSheafUnrestricted l E Z
  let c := asIso (sfRecollementCoefficientMap l E i)
  let V : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let U : X.ProEt := ProEt.mk V.ι
  have : IsOpenImmersion U.hom := inferInstanceAs (IsOpenImmersion V.ι)
  have : QuasiCompact U.hom := inferInstanceAs (QuasiCompact V.ι)
  have hU : Set.range U.hom = (Set.range i)ᶜ := V.range_ι
  obtain ⟨q, ⟨e⟩, ai, aj, hc, hu, hz, hzi, hlimL, hcolL, hlimH, hcolH, hs, _⟩ :=
    proEtale_ringed_open_closed i U hU R
  let ei := sfLocalCoefficientTransport i R S c
  let d := sfLocalDirectImageComparison i R S c
  have : PreservesFiniteColimits (proEtaleRingModuleDirectImage i R S c) :=
    preservesFiniteColimits_of_natIso d.symm
  have : PreservesLimitsOfSize.{0, 0} (proEtaleRingModuleDirectImage i R S c) :=
    (sfRecollementModuleAdjunction l E i).rightAdjoint_preservesLimits
  have : (sfRecollementModuleClosed l E i).Additive := by
    dsimp [sfRecollementModuleClosed]
    infer_instance
  have : PreservesFiniteLimits (sfRecollementModuleClosed l E i) := by
    dsimp [sfRecollementModuleClosed]
    infer_instance
  have : PreservesFiniteColimits (sfRecollementModuleClosed l E i) := by
    dsimp [sfRecollementModuleClosed]
    infer_instance
  let li := sfLocalPullbackComparison i R S c ai
  let li' : proEtaleRingModulePullback i R S c ⋙ ei.functor ≅
      proEtaleModuleInverseImage i R :=
    Functor.isoWhiskerRight li ei.functor ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ei.counitIso ≪≫ Functor.rightUnitor _
  let ek : sfRecollementModuleOpen l E i ≅ kernel ai.unit :=
    sfLocalUnitKernelCompEquivalenceIso (sfRecollementModuleAdjunction l E i) ei ≪≫
      sfLocalUnitKernelIsoOfLeftIso
        ((sfRecollementModuleAdjunction l E i).comp ei.toAdjunction) ai li'
  let J := SheafOfModules.overFunctor.{u + 1} (proEtaleModuleCoefficients R) U
  let L := proEtaleRingedExtensionByZero U R
  have : PreservesLimitsOfSize.{0, 0} J := aj.rightAdjoint_preservesLimits
  have : PreservesFiniteLimits J := inferInstance
  have : PreservesFiniteColimits J := by
    obtain ⟨_, _, hj, _⟩ :=
      (proEtale_immersion_inverseImage_preservesLimits U.hom).2.2 R
    have := hj
    exact preservesFiniteColimits_of_natIso e
  have : PreservesFiniteLimits L := hlimL
  have : PreservesFiniteColimits L := hcolL
  have hzero : aj.counit ≫ ai.unit = 0 := by
    apply NatTrans.ext
    funext M
    exact (hs M).2.2.toIsComplex.zero 0
  let hker : IsLimit (KernelFork.ofι aj.counit hzero) := by
    apply evaluationJointlyReflectsLimits
    intro M
    apply (KernelFork.isLimitMapConeEquiv ..).2
    have := (hs M).1
    have hex : (ShortComplex.mk (aj.counit.app M) (ai.unit.app M)
        (congr_app hzero M)).Exact := by
      exact (ShortComplex.exact_iff_exact_toComposableArrows _).2 (hs M).2.2
    exact hex.fIsKernel
  let eo : sfRecollementModuleOpen l E i ≅ J ⋙ L :=
    ek ≪≫ (kernelIsKernel ai.unit).conePointUniqueUpToIso hker
  have : PreservesFiniteLimits (sfRecollementModuleOpen l E i) :=
    preservesFiniteLimits_of_natIso eo.symm
  have : PreservesFiniteColimits (sfRecollementModuleOpen l E i) :=
    preservesFiniteColimits_of_natIso eo.symm
  have : (sfRecollementModuleOpen l E i).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact ⟨inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance⟩

private theorem sfLocalModuleUnitEpi {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] (M : scalarReductionSource.{u, u} l E X) :
    Epi ((sfRecollementModuleUnit l E i).app M) := by
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let S := completedIntegralCommRingSheafUnrestricted l E Z
  let c := asIso (sfRecollementCoefficientMap l E i)
  let V : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let U : X.ProEt := ProEt.mk V.ι
  have : IsOpenImmersion U.hom := inferInstanceAs (IsOpenImmersion V.ι)
  have : QuasiCompact U.hom := inferInstanceAs (QuasiCompact V.ι)
  have hU : Set.range U.hom = (Set.range i)ᶜ := V.range_ι
  obtain ⟨q, ⟨e⟩, ai, aj, hc, hu, hz, hzi, hlimL, hcolL, hlimH, hcolH, hs, _⟩ :=
    proEtale_ringed_open_closed i U hU R
  let ei := sfLocalCoefficientTransport i R S c
  let b := ai.comp ei.symm.toAdjunction
  have : Epi (ai.unit.app M) := (hs M).2.1
  have : Epi (b.unit.app M) := by
    dsimp only [b]
    rw [Adjunction.comp_unit_app]
    infer_instance
  exact sfLocalUnitEpiOfLeftIso (sfRecollementModuleAdjunction l E i) b
    (sfLocalPullbackComparison i R S c ai) M

/-- Exact open functor's additive structure. Source: Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
instance sfRecollementModuleOpen_additive {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] : (sfRecollementModuleOpen l E i).Additive :=
  (sfRecollementModule_exact l E i).1

/-- Exact open functor's left exactness. Source: Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
instance sfRecollementModuleOpen_limits {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] :
    PreservesFiniteLimits (sfRecollementModuleOpen l E i) :=
  (sfRecollementModule_exact l E i).2.1

/-- Exact open functor's right exactness. Source: Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
instance sfRecollementModuleOpen_colimits {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] :
    PreservesFiniteColimits (sfRecollementModuleOpen l E i) :=
  (sfRecollementModule_exact l E i).2.2.1

/-- Exact closed functor's additive structure. Source: Stacks 09BM
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
instance sfRecollementModuleClosed_additive {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] : (sfRecollementModuleClosed l E i).Additive :=
  (sfRecollementModule_exact l E i).2.2.2.1

/-- Exact closed functor's left exactness. Source: Stacks 09BM
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
instance sfRecollementModuleClosed_limits {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] :
    PreservesFiniteLimits (sfRecollementModuleClosed l E i) :=
  (sfRecollementModule_exact l E i).2.2.2.2.1

/-- Exact closed functor's right exactness. Source: Stacks 09BM
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
instance sfRecollementModuleClosed_colimits {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] :
    PreservesFiniteColimits (sfRecollementModuleClosed l E i) :=
  (sfRecollementModule_exact l E i).2.2.2.2.2

private theorem sfLocalSequenceTriangle
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F G : C ⥤ C) [F.Additive] [G.Additive]
    (α : F ⟶ 𝟭 C) (β : 𝟭 C ⟶ G) (h : α ≫ β = 0)
    (hS : (ShortComplex.mk α β h).ShortExact) (B : CochainComplex C ℤ) :
    ∃ δ, Triangle.mk
      (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α (.up ℤ)).app B))
      (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex β (.up ℤ)).app B)) δ ∈
      distTriang (DerivedCategory C) := by
  let f := (NatTrans.mapHomologicalComplex α (.up ℤ)).app B
  let g := (NatTrans.mapHomologicalComplex β (.up ℤ)).app B
  have hz : f ≫ g = 0 := by
    ext n
    exact congrArg (fun q ↦ q.app (B.X n)) h
  let S : ShortComplex (CochainComplex C ℤ) := ShortComplex.mk f g hz
  have hs : S.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    have := hS.mono_f
    have := hS.epi_g
    exact hS.map ((CategoryTheory.evaluation C C).obj (B.X n))
  exact ⟨DerivedCategory.triangleOfSESδ hs, DerivedCategory.triangleOfSES_distinguished hs⟩

private theorem sfLocalIntegralSequenceTriangle {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X]
    (B : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ) :
    ∃ δ, Triangle.mk
      (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (F := sfRecollementModuleOpen l E i) (G := 𝟭 _)
        (sfRecollementModuleCounit l E i) (.up ℤ)).app B))
      (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (sfRecollementModuleUnit l E i) (.up ℤ)).app B)) δ ∈
      distTriang (DerivedCategory (scalarReductionSource.{u, u} l E X)) := by
  let C := scalarReductionSource.{u, u} l E X
  let α : sfRecollementModuleOpen l E i ⟶ 𝟭 C := sfRecollementModuleCounit l E i
  let β : 𝟭 C ⟶ sfRecollementModuleClosed l E i := sfRecollementModuleUnit l E i
  have hz : α ≫ β = 0 := kernel.condition β
  have hEpi : ∀ M, Epi (β.app M) := fun M ↦ sfLocalModuleUnitEpi l E i M
  have : Epi β := @NatTrans.epi_of_epi_app _ _ _ _ _ _ β hEpi
  have hs : (ShortComplex.mk α β hz).ShortExact := by
    change (ShortComplex.mk (kernel.ι β) β (kernel.condition β)).ShortExact
    exact { exact := ShortComplex.exact_kernel β }
  exact sfLocalSequenceTriangle _ _ α β hz hs B

/-- The two functorial vertices and the prescribed first two arrows of a recollement
triangle. This is only presentation data, without an existence or vanishing assertion.
Source: blueprint displayed open-closed triangle
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
structure SfRecollementPresentation (C : Type w) [Category.{w₁} C] where
  openTerm : C ⥤ C
  closedTerm : C ⥤ C
  counit : openTerm ⟶ 𝟭 C
  unit : 𝟭 C ⟶ closedTerm

/-- Distinguished completion, all integer-shift Hom vanishing, uniqueness of the third
arrow, and its naturality for every morphism. Source: blueprint statement, order 1851
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfRecollementConclusion {C : Type w} [Category.{w₁} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [shiftAdditive : ∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (P : SfRecollementPresentation C) : Prop :=
  (∀ K : C, ∃! δ : P.closedTerm.obj K ⟶ (P.openTerm.obj K)⟦(1 : ℤ)⟧,
    Triangle.mk (P.counit.app K) (P.unit.app K) δ ∈ distTriang C) ∧
  (∀ (K : C) (m : ℤ), Subsingleton ((P.openTerm.obj K)⟦m⟧ ⟶ P.closedTerm.obj K)) ∧
  ∀ (K L : C) (f : K ⟶ L)
    (δ : P.closedTerm.obj K ⟶ (P.openTerm.obj K)⟦(1 : ℤ)⟧)
    (δ' : P.closedTerm.obj L ⟶ (P.openTerm.obj L)⟦(1 : ℤ)⟧),
    Triangle.mk (P.counit.app K) (P.unit.app K) δ ∈ distTriang C →
    Triangle.mk (P.counit.app L) (P.unit.app L) δ' ∈ distTriang C →
    P.closedTerm.map f ≫ δ' = δ ≫ (shiftFunctor C (1 : ℤ)).map (P.openTerm.map f)

/-- The finite presentation uses precisely the dependency's two adjunction maps.
Source: blueprint finite-stage paragraph; Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfFiniteRecollementPresentation {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A] :
    SfRecollementPresentation (proEtaleDerivedCategory X A) where
  openTerm := sfIntrinsicDerivedPullback A j ⋙ sfIntrinsicDerivedOpen A j
  closedTerm := sfIntrinsicDerivedPullback A i ⋙ proEtaleConstantDerivedDirectImage i A
  counit := (exceptionalOpenAdjunction j A).counit
  unit := (finiteRecollementDerivedAdjunction i A).unit

/-- The conclusion on a full constructible subcategory of an ambient derived category.
Distinguishedness is tested in the ambient category, as in the recorded finite
recollement definition; the outer vertices are required to remain constructible.
Source: blueprint statement (blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfRecollementConclusionOn {C : Type w} [Category.{w₁} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (P : SfRecollementPresentation C) (S : ObjectProperty C) : Prop :=
  (∀ (K : C), S K → S (P.openTerm.obj K) ∧ S (P.closedTerm.obj K) ∧
    (∃! δ : P.closedTerm.obj K ⟶ (P.openTerm.obj K)⟦(1 : ℤ)⟧,
      Triangle.mk (P.counit.app K) (P.unit.app K) δ ∈ distTriang C) ∧
    ∀ m : ℤ, Subsingleton ((P.openTerm.obj K)⟦m⟧ ⟶ P.closedTerm.obj K)) ∧
  ∀ (K L : C), S K → S L → ∀ (f : K ⟶ L)
    (δ : P.closedTerm.obj K ⟶ (P.openTerm.obj K)⟦(1 : ℤ)⟧)
    (δ' : P.closedTerm.obj L ⟶ (P.openTerm.obj L)⟦(1 : ℤ)⟧),
    Triangle.mk (P.counit.app K) (P.unit.app K) δ ∈ distTriang C →
    Triangle.mk (P.counit.app L) (P.unit.app L) δ' ∈ distTriang C →
    P.closedTerm.map f ≫ δ' = δ ≫ (shiftFunctor C (1 : ℤ)).map (P.openTerm.map f)

private theorem sfLocalConclusionOn
    {C : Type w} [Category.{w₁} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : SfRecollementPresentation C) (S : ObjectProperty C)
    (hmem : ∀ K, S K → S (P.openTerm.obj K) ∧ S (P.closedTerm.obj K))
    (hex : ∀ K, S K → ∃ δ,
      Triangle.mk (P.counit.app K) (P.unit.app K) δ ∈ distTriang C)
    (hvan : ∀ K L, S K → S L → ∀ m : ℤ,
      Subsingleton ((P.openTerm.obj K)⟦m⟧ ⟶ P.closedTerm.obj L)) :
    SfRecollementConclusionOn P S := by
  constructor
  · intro K hK
    obtain ⟨δ, hδ⟩ := hex K hK
    refine ⟨(hmem K hK).1, (hmem K hK).2, ⟨δ, hδ, ?_⟩, hvan K K hK hK⟩
    intro δ' hδ'
    let := hvan K K hK hK 1
    let : Subsingleton ((Triangle.mk (P.counit.app K) (P.unit.app K) δ').obj₁⟦(1 : ℤ)⟧ ⟶
        (Triangle.mk (P.counit.app K) (P.unit.app K) δ).obj₃) := hvan K K hK hK 1
    obtain ⟨τ, hτ⟩ := exists_triangleHom_of_comp_eq_zero hδ' hδ (𝟙 K) (by
      change P.counit.app K ≫ 𝟙 K ≫ P.unit.app K = 0
      simpa using comp_distTriang_mor_zero₁₂ _ hδ')
    have h₁ : τ.hom₁ = 𝟙 _ := Triangle.cancel_mor₁_of_subsingleton hδ (by
      rw [← τ.comm₁, hτ]
      change P.counit.app K ≫ 𝟙 K = 𝟙 _ ≫ P.counit.app K
      simp)
    have h₃ : τ.hom₃ = 𝟙 _ := Triangle.cancel_mor₂_of_subsingleton hδ' (by
      rw [τ.comm₂, hτ]
      change 𝟙 K ≫ P.unit.app K = P.unit.app K ≫ 𝟙 _
      simp)
    have h := τ.comm₃
    rw [h₁, h₃] at h
    simpa using h
  · intro K L hK hL f δ δ' hδ hδ'
    let := hvan K L hK hL 1
    let : Subsingleton ((Triangle.mk (P.counit.app K) (P.unit.app K) δ).obj₁⟦(1 : ℤ)⟧ ⟶
        (Triangle.mk (P.counit.app L) (P.unit.app L) δ').obj₃) := hvan K L hK hL 1
    obtain ⟨τ, hτ⟩ := exists_triangleHom_of_comp_eq_zero hδ hδ' f (by
      change P.counit.app K ≫ f ≫ P.unit.app L = 0
      have hn : P.counit.app K ≫ f = P.openTerm.map f ≫ P.counit.app L :=
        (P.counit.naturality f).symm
      rw [← Category.assoc, hn, Category.assoc]
      erw [comp_distTriang_mor_zero₁₂ _ hδ']
      exact comp_zero)
    have h₁ : τ.hom₁ = P.openTerm.map f :=
      Triangle.cancel_mor₁_of_subsingleton hδ' (by
        rw [← τ.comm₁, hτ]
        exact (P.counit.naturality f).symm)
    have h₃ : τ.hom₃ = P.closedTerm.map f :=
      Triangle.cancel_mor₂_of_subsingleton hδ (by
        rw [τ.comm₂, hτ]
        exact P.unit.naturality f)
    have h := τ.comm₃
    rw [h₁, h₃] at h
    exact h.symm

private theorem sfLocalFiniteDisjoint {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A]
    (hij : Disjoint (Set.range j.base) (Set.range i.base))
    (M : proEtaleRingModules U (proEtaleConstantRing U A)) :
    IsZero ((sfIntrinsicPullback.{u} A i).obj ((sfIntrinsicExtensionByZero.{u} j A).obj M)) := by
  let L := ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j
  let I := ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i
  have hz : IsZero ((sfIntrinsicTransport A (L ⋙ I)).obj M) :=
    (sfIntrinsicModuleEquivalence Z A).functor.map_isZero
      (ProEtale.isZero_upperStar_openImmersionLowerShriek _ j i
        (Set.disjoint_iff_inter_eq_empty.mp hij)
        ((sfIntrinsicModuleEquivalence U A).inverse.obj M))
  exact hz.of_iso ((sfIntrinsicTransportComp A L I).symm.app M)

private theorem sfLocalFiniteHomVanishing {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A]
    (hij : Disjoint (Set.range j.base) (Set.range i.base))
    (K : proEtaleDerivedCategory U A) (M : proEtaleDerivedCategory Z A) (n : ℤ) :
    Subsingleton (((sfIntrinsicDerivedOpen.{u} A j).obj K)⟦n⟧ ⟶
      (proEtaleConstantDerivedDirectImage.{u} i A).obj M) := by
  let : HasDerivedCategory (proEtaleRingModules X (proEtaleConstantRing X A)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (proEtaleRingModules U (proEtaleConstantRing U A)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (proEtaleRingModules Z (proEtaleConstantRing Z A)) :=
    HasDerivedCategory.standard _
  let I := sfIntrinsicPullback.{u} A i
  let L := sfIntrinsicExtensionByZero.{u} j A
  have hz : IsZero (I.mapDerivedCategory.obj (L.mapDerivedCategory.obj K)) :=
    (Functor.isZero_mapDerivedCategory_obj (L ⋙ I) K
      (fun _ ↦ sfLocalFiniteDisjoint i j A hij _)).of_iso
        ((L.mapDerivedCategoryCompIso I).symm.app K)
  have hzs : IsZero (I.mapDerivedCategory.obj ((L.mapDerivedCategory.obj K)⟦n⟧)) :=
    ((shiftFunctor _ n).map_isZero hz).of_iso ((I.mapDerivedCategory.commShiftIso n).app _)
  have : Subsingleton (I.mapDerivedCategory.obj ((L.mapDerivedCategory.obj K)⟦n⟧) ⟶ M) :=
    ⟨fun _ _ ↦ hzs.eq_of_src _ _⟩
  exact ((finiteRecollementDerivedAdjunction.{u} i A).homEquiv _ _).symm.subsingleton

/-- Positive-level specialization with the recorded finiteness proof supplied
internally, so finiteness is not an extra theorem hypothesis.
Source: blueprint finite-stage paragraph
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfFiniteRecollementAt {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] (n : ℕ) (hn : 1 ≤ n) :
    SfRecollementPresentation (proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  sfFiniteRecollementPresentation i j (Padic.coefficientExtensionRing l E n)

/-- At positive finite coefficients the specified maps have unique distinguished
completion; the vertices remain constructible, Hom vanishing includes every integer
shift, and the triangle is natural. Source: blueprint proof steps 1--2, 8--9; Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: X is Noetherian, so the complementary open is quasi-compact. Finite locally
closed partitions restrict to U,Z and extend by zero to X. The exact ringed sheaf
sequence applied termwise gives the distinguished triangle by the complex short-exact
sequence triangle lemma. Exact functors give the stated derived operations and maps.
The open adjunction and j*i*=0 give Hom(j!N[m],i*M)=0 for arbitrary N,M. TR3 compares
completions; Hom exactness factors the difference of third components through a map
j!N[1] to i*M, which vanishes. The same argument for a map K to L proves naturality. -/
theorem sfOpenClosedTriangle_finite
    (k : Type u) [Field k] (_hk : IsUnit (l : k))
    {Z U X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    (_hij : Set.range j.base = (Set.range i.base)ᶜ)
    (n : ℕ) (hn : 1 ≤ n) :
    SfRecollementConclusionOn
      (sfFiniteRecollementAt l E i j n hn)
      (intrinsicFiniteTorsionConstructible l E n hn X) := by
  sorry

/-- The Noetherian structure supplied by the finite-type structure map over a field.
Source: blueprint proof step 1; Stacks 01T6
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: a field is Noetherian; the structure morphism is locally of finite type,
so its source is locally Noetherian. Quasi-compactness over the compact spectrum
of the field makes the source compact, giving the Noetherian structure. -/
theorem sfRecollementNoetherian (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] :
    IsNoetherian X := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  exact ⟨⟩

/-- The open complement has its inherited finite-type structure over k and is a
quasi-compact open immersion. Source: blueprint proof step 1; Stacks 01T6
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: X is Noetherian by finite type over the field. Every open subset of each
Noetherian affine is quasi-compact and a finite union of principal opens. Their
coordinate rings are finitely generated by adjoining inverses. These covers give
finite type over k; Noetherian quasi-compactness also gives quasi-compactness of j. -/
theorem sfRecollementOpenFiniteType (k : Type u) [Field k]
    {U X : Scheme.{u}} [X.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))] :
    LocallyOfFiniteType (U ↘ Spec (.of k)) ∧
      QuasiCompact (U ↘ Spec (.of k)) ∧ QuasiCompact j := by
  have : IsNoetherian X := sfRecollementNoetherian k X
  have : TopologicalSpace.NoetherianSpace U :=
    j.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := inferInstance
  have : LocallyOfFiniteType (j ≫ (X ↘ Spec (.of k))) := inferInstance
  have : QuasiCompact (j ≫ (X ↘ Spec (.of k))) := inferInstance
  rw [← comp_over j (Spec (.of k))]
  exact
    (show LocallyOfFiniteType (j ≫ (X ↘ Spec (.of k))) ∧
      QuasiCompact (j ≫ (X ↘ Spec (.of k))) ∧ QuasiCompact j from
        ⟨inferInstance, inferInstance, inferInstance⟩)

/-- A normalized integral presentation uses the exact sheaf kernel and closed term,
with their actual sheaf maps on every representative complex. This pins down the
arrows, not just the isomorphism classes of the three vertices.
Source: blueprint proof steps 3--7 (blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfIntegralRecollementNormalization {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (hX : IsNoetherian X)
    (P : SfRecollementPresentation (sfIntegralConstructibleCategory l E X)) : Prop :=
  letI := hX
  ∃ (a : (sfIntegralConstructible l E X).ι ⋙
        (sfRecollementModuleOpen l E i).mapDerivedCategory ≅
      P.openTerm ⋙ (sfIntegralConstructible l E X).ι)
    (c : (sfIntegralConstructible l E X).ι ⋙
        (sfRecollementModuleClosed l E i).mapDerivedCategory ≅
      P.closedTerm ⋙ (sfIntegralConstructible l E X).ι),
    ∀ (B : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ)
      (hB : sfIntegralConstructible l E X (DerivedCategory.Q.obj B)),
      a.hom.app ⟨DerivedCategory.Q.obj B, hB⟩ ≫
          (P.counit.app ⟨DerivedCategory.Q.obj B, hB⟩).hom =
        (sfRecollementModuleOpen l E i).mapDerivedCategoryFactors.hom.app B ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (F := sfRecollementModuleOpen l E i)
              (G := 𝟭 (scalarReductionSource.{u, u} l E X))
              (sfRecollementModuleCounit l E i) (.up ℤ)).app B) ∧
      (P.unit.app ⟨DerivedCategory.Q.obj B, hB⟩).hom ≫
          c.inv.app ⟨DerivedCategory.Q.obj B, hB⟩ ≫
          (sfRecollementModuleClosed l E i).mapDerivedCategoryFactors.hom.app B =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (F := 𝟭 (scalarReductionSource.{u, u} l E X))
            (G := sfRecollementModuleClosed l E i)
            (sfRecollementModuleUnit l E i) (.up ℤ)).app B)

/-- Rational presentations are obtained from exactly the integral functors and maps
by the recorded raw localization. The two comparison squares retain the prescribed
counit and unit. Source: blueprint proof step 10
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfRationalRecollementNormalization (X : Scheme.{u})
    (P : SfRecollementPresentation (sfIntegralConstructibleCategory l E X))
    (Q : SfRecollementPresentation (sfRationalConstructibleCategory l E X)) : Prop :=
  (∀ K, Q.openTerm.obj K = ⟨P.openTerm.obj K.obj⟩ ∧
    Q.closedTerm.obj K = ⟨P.closedTerm.obj K.obj⟩) ∧
  ∃ (a : sfRationalConstructibleLocalization l E X ⋙ Q.openTerm ≅
      P.openTerm ⋙ sfRationalConstructibleLocalization l E X)
    (c : sfRationalConstructibleLocalization l E X ⋙ Q.closedTerm ≅
      P.closedTerm ⋙ sfRationalConstructibleLocalization l E X),
    (∀ K, a.hom.app K ≫
        (sfRationalConstructibleLocalization l E X).map (P.counit.app K) =
      Q.counit.app ((sfRationalConstructibleLocalization l E X).obj K)) ∧
    ∀ K, Q.unit.app ((sfRationalConstructibleLocalization l E X).obj K) ≫ c.hom.app K =
      (sfRationalConstructibleLocalization l E X).map (P.unit.app K)

/-- Identification of the integral kernel presentation with the recorded completed
operations. Constructibility of the restricted pullback is included in the witness.
The closed term is the recorded integral direct image of the completed pullback: a
vertex of the specified Roos triangle of the finite-image tower, R lim Res_n Ri_{*,n}.
Exact countable products supply the derived-category products of that tower.
Source: blueprint proof steps 3--7
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfIntegralRecollementVertices
    (k : Type u) [Field k] (hk : IsUnit (l : k))
    {Z U X : Scheme.{u}}
    [X.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))]
    (P : SfRecollementPresentation (sfIntegralConstructibleCategory l E X)) : Prop :=
  letI : LocallyOfFiniteType (U ↘ Spec (.of k)) := (sfRecollementOpenFiniteType k j).1
  letI : QuasiCompact (U ↘ Spec (.of k)) := (sfRecollementOpenFiniteType k j).2.1
  letI : QuasiCompact j := (sfRecollementOpenFiniteType k j).2.2
  (∀ K : sfIntegralConstructibleCategory l E X,
    ∃ h : sfIntegralConstructible l E U ((integralDerivedPullback l E j).obj K.obj),
      Nonempty (P.openTerm.obj K ≅ sfIntegralCompactSupportValue l E k hk
        (Compactification.ofIsOpenImmersion j) ⟨_, h⟩)) ∧
  letI : HasCountableProducts (DerivedCategory (scalarReductionSource.{u, u} l E X)) :=
    integralOperationsDerivedCountableProducts l E X
  ∀ K : sfIntegralConstructibleCategory l E X,
    ∃ L : SfIntegralDirectImage l E i ((integralDerivedPullback l E i).obj K.obj),
      Nonempty ((P.closedTerm.obj K).obj ≅ L.obj)

/-- Integral and rational localization triangles, with their actual operation vertices
and specified maps. The Noetherian and induced finite-type hypotheses here are the
properties inherited by the three schemes in the statement.
Source: blueprint proof steps 3--10
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: identify immersion inverse images of completed coefficients with the actual
coefficient sheaves. Exact immersion restriction preserves countable products, hence
Roos triangles, and is the completed pullback. Open extension is the kernel of the
map j* to i*i*j*, so preserves products too. The slice tensor identity on K-flat
complexes identifies its reductions with finite extension, compatibly with transitions.
It is therefore complete with constructible reductions in one common interval, and
is the specified compact-support value. Closed exact direct image commutes with the
reduction tower and has the specified finite reductions. The termwise ringed sheaf
sequence gives the integral triangle in the full triangulated subcategory. The open
adjunction and disjoint support give cross-object vanishing. TR3 and Hom exactness
prove uniqueness and naturality as at finite coefficients. Localize the integral
linear functors and maps: localization is exact, and Hom groups tensor with E, so
vanishing persists. Apply the same TR3 argument to arbitrary rational morphisms. -/
theorem sfOpenClosedTriangle_integral_rational
    (k : Type u) [Field k] (hk : IsUnit (l : k))
    {Z U X : Scheme.{u}}
    [X.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))]
    (_hij : Set.range j.base = (Set.range i.base)ᶜ) :
    ∃ (P : SfRecollementPresentation (sfIntegralConstructibleCategory l E X))
      (Q : SfRecollementPresentation (sfRationalConstructibleCategory l E X)),
      SfIntegralRecollementNormalization l E i (sfRecollementNoetherian k X) P ∧
      SfIntegralRecollementVertices l E k hk i j P ∧
      SfRecollementConclusion P ∧
      SfRationalRecollementNormalization l E X P Q ∧ SfRecollementConclusion Q := by
  sorry

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The common-stage presentation is the descent of the actual rational presentations.
Naturality covers every common-stage representative, rather than only maps from one
fixed coefficient field. The comparison squares specify the descended counit and unit.
Source: blueprint proof step 11
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfCommonStageRecollementNormalization (X : Scheme.{u})
    (Q : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
      SfRecollementPresentation (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X L))
    (R : SfRecollementPresentation (generalAlgebraicallyClosedConstructibleCategory l Ω X)) :
    Prop :=
  (∀ K, R.openTerm.obj K = ⟨K.stage, (Q K.stage).openTerm.obj K.obj⟩ ∧
    R.closedTerm.obj K = ⟨K.stage, (Q K.stage).closedTerm.obj K.obj⟩) ∧
  ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
    ∃ (a : GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) L ⋙
          R.openTerm ≅ (Q L).openTerm ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion L)
      (c : GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) L ⋙
          R.closedTerm ≅ (Q L).closedTerm ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion L),
      (∀ K, a.hom.app K ≫ (GeneralAlgebraicallyClosedCoefficients.inclusion L).map
          ((Q L).counit.app K) =
        R.counit.app ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K)) ∧
      ∀ K, R.unit.app ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K) ≫
          c.hom.app K = (GeneralAlgebraicallyClosedCoefficients.inclusion L).map ((Q L).unit.app K)

/-- The algebraically closed coefficient localization triangle, with all finite-stage
operations retained through the recorded common-stage inclusions.
Source: blueprint proof step 11
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: apply the integral/rational construction at every finite coefficient field.
Tensor balancing and scalar-extension compatibility identify the counit and unit
across each field inclusion. Descend the exact functors and these transformations.
An object and each finite diagram of morphisms have a common coefficient stage.
Exactness of the stage inclusions carries the rational triangle to the common-stage
category. The Hom groups are filtered colimits of the vanishing stage groups.
TR3 and Hom exactness prove uniqueness and naturality for every common-stage map. -/
theorem sfOpenClosedTriangle_qbar
    (k : Type u) [Field k] (hk : IsUnit (l : k))
    {Z U X : Scheme.{u}}
    [X.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))]
    (_hij : Set.range j.base = (Set.range i.base)ᶜ) :
    ∃ (P : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
        SfRecollementPresentation (sfIntegralConstructibleCategory l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X))
      (Q : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
        SfRecollementPresentation (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X L)),
      (∀ L, SfIntegralRecollementNormalization l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) i
          (sfRecollementNoetherian k X) (P L) ∧
        SfIntegralRecollementVertices l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) k hk i j (P L) ∧
        SfRecollementConclusion (shiftAdditive := fun n => inferInstance) (P L) ∧
        SfRationalRecollementNormalization l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X (P L) (Q L) ∧
        SfRecollementConclusion (Q L)) ∧
      ∃ R : SfRecollementPresentation (generalAlgebraicallyClosedConstructibleCategory l Ω X),
        SfCommonStageRecollementNormalization l Ω X Q R ∧ SfRecollementConclusion R := by
  sorry

/-- Exactness for the shift structure on the specified geometric Frobenius functor.
The shift structure is included as data because its interface was not previously
exported by the recorded pullback module. Source: blueprint proof steps 12 and 16
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfRecollementFrobeniusExact
    {C : Type w} [Category.{w₁} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (G : C ⥤ C) (s : G.CommShift ℤ) : Prop :=
  letI := s
  G.IsTriangulated

/-- All three arrows are morphisms of the recorded fixed pairs. The outer Weil
isomorphisms are uniquely characterized by the first two commuting squares; the third
uses the induced shift of the open Weil structure.
Source: blueprint statement and proof steps 12--16
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfRecollementWeilEquivariant
    {C : Type w} [Category.{w₁} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : SfRecollementPresentation C) (G : C ⥤ C) (s : G.CommShift ℤ) : Prop :=
  letI := s
  ∀ K : CategoryTheory.Endofunctor.IsoAlgebra G,
    ∃! ac : (G.obj (P.openTerm.obj K.carrier) ≅ P.openTerm.obj K.carrier) ×
        (G.obj (P.closedTerm.obj K.carrier) ≅ P.closedTerm.obj K.carrier),
      (G.map (P.counit.app K.carrier) ≫ K.str.hom =
        ac.1.hom ≫ P.counit.app K.carrier) ∧
      (G.map (P.unit.app K.carrier) ≫ ac.2.hom =
        K.str.hom ≫ P.unit.app K.carrier) ∧
      ∀ δ : P.closedTerm.obj K.carrier ⟶ (P.openTerm.obj K.carrier)⟦(1 : ℤ)⟧,
        Triangle.mk (P.counit.app K.carrier) (P.unit.app K.carrier) δ ∈ distTriang C →
        G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app (P.openTerm.obj K.carrier) ≫
            (shiftFunctor C (1 : ℤ)).map ac.1.hom = ac.2.hom ≫ δ

/-- Finite-type geometric fibres inherit the Noetherian structure used by the
integral presentation. Source: blueprint proof steps 1 and 12; Stacks 01T6
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: finite type is stable under the base change defining the geometric fibre;
a finite-type scheme over the closure field is Noetherian. -/
theorem sfRecollementGeometricNoetherian (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    IsNoetherian (D.geometricFiber X₀).left := by
  have : LocallyOfFiniteType (D.geometricFiber X₀).hom := by
    dsimp [FiniteFieldDatum.geometricFiber]
    infer_instance
  have : QuasiCompact (D.geometricFiber X₀).hom := by
    dsimp [FiniteFieldDatum.geometricFiber]
    infer_instance
  have : IsLocallyNoetherian (D.geometricFiber X₀).left :=
    LocallyOfFiniteType.isLocallyNoetherian (D.geometricFiber X₀).hom
  have : CompactSpace (D.geometricFiber X₀).left :=
    QuasiCompact.compactSpace_of_compactSpace (D.geometricFiber X₀).hom
  exact ⟨⟩

/-- Weil equivariance at a rational coefficient stage, for the prescribed open and
closed terms and every connecting arrow supplied by the localization triangle.
The geometric map is the actual base change of the closed immersion over k₀;
no k-linearity hypothesis is imposed on the semilinear geometric Frobenius.
Source: blueprint proof steps 12--16
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: geometric Frobenius is semilinear on the closure and commutes with the
base-changed closed immersion and its open complement. The inverse automorphism
squares give inverse pullback, closed-image and open-extension comparisons. Their
mates are isomorphisms. The tensor-unit normalizations identify the ordinary maps
with the specified completed maps, and mate pasting makes the counit and unit
squares commute. Combine these comparisons with the middle Weil isomorphism to
obtain the two outer Weil isomorphisms. Pullback of the distinguished triangle is
distinguished. The two squares identify its first two arrows with the original
ones, so uniqueness forces its connecting arrow to be the original one. Shifted
Hom vanishing gives uniqueness of the outer structures with those squares. -/
theorem sfOpenClosedTriangle_rational_weil
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X₀ Z₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (i₀ : Z₀ ⟶ X₀) [IsClosedImmersion i₀.left]
    (i : (D.geometricFiber Z₀).left ⟶ (D.geometricFiber X₀).left)
    [IsClosedImmersion i]
    (_hi : i = ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map i₀).left)
    (P : SfRecollementPresentation
      (sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left))
    (Q : SfRecollementPresentation
      (sfRationalConstructibleCategory l E (D.geometricFiber X₀).left))
    (_hP : SfIntegralRecollementNormalization l E i (sfRecollementGeometricNoetherian D X₀) P)
    (_hQ : SfRationalRecollementNormalization l E (D.geometricFiber X₀).left P Q) :
    ∃ s : (sfWeilFrobeniusPullback D l hl X₀ E).CommShift ℤ,
      SfRecollementFrobeniusExact (sfWeilFrobeniusPullback D l hl X₀ E) s ∧
      SfRecollementWeilEquivariant Q (sfWeilFrobeniusPullback D l hl X₀ E) s := by
  sorry

/-- Weil equivariance after common-stage descent. This uses precisely the recorded
algebraically closed Weil category of fixed pairs, not a derived category of pairs.
Source: blueprint proof steps 11--16
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: the Frobenius comparisons and their mate unit/counit equations commute with
finite scalar extension. Descend them to common stages, where geometric Frobenius
is the recorded common-stage pullback. Each finite diagram, including the Weil
isomorphism, has a common coefficient stage; its inverse is represented after a
further extension. The rational argument gives the outer Weil structures and the
first two commuting squares there. Exact stage inclusion transports the triangle.
Uniqueness of its third arrow gives the final equivariance equation independently
of the representing stage. Shifted Hom vanishing gives uniqueness of the outer
structures characterized by the first two squares. -/
theorem sfOpenClosedTriangle_qbar_weil
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X₀ Z₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (i₀ : Z₀ ⟶ X₀) [IsClosedImmersion i₀.left]
    (i : (D.geometricFiber Z₀).left ⟶ (D.geometricFiber X₀).left)
    [IsClosedImmersion i]
    (_hi : i = ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map i₀).left)
    (P : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
      SfRecollementPresentation (sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (D.geometricFiber X₀).left))
    (Q : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
      SfRecollementPresentation
        (GeneralAlgebraicallyClosedCoefficients.Stage l Ω (D.geometricFiber X₀).left L))
    (_hPQ : ∀ L, SfIntegralRecollementNormalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) i
        (sfRecollementGeometricNoetherian D X₀) (P L) ∧
      SfRationalRecollementNormalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
        (D.geometricFiber X₀).left (P L) (Q L))
    (R : SfRecollementPresentation
      (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left))
    (_hR : SfCommonStageRecollementNormalization l Ω (D.geometricFiber X₀).left Q R) :
    ∃ s : (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).CommShift ℤ,
      SfRecollementFrobeniusExact (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω) s ∧
      SfRecollementWeilEquivariant R (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω) s := by
  sorry

end WeilConjectures
