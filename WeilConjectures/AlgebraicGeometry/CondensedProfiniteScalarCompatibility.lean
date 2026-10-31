/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedLisseEvaluationModel
import WeilConjectures.Algebra.Homology.CochainDerivedAdjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.RingedKFlatWordComparisonDescent
import WeilConjectures.AlgebraicGeometry.ProfiniteCoefficientSliceBaseChange

/-! # Scalar associativity for condensed realization on a profinite slice

Source: Hemo--Richarz--Scholbach, Remark 3.2 and formula (3.2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory
open CategoryTheory.Limits

private instance coefficientRestrictionLimits
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u + 1}} (f : R ⟶ B) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map f)) :=
  (SheafOfModules.sheafRingCoefficientOrdinaryAdjunction.{u + 1, u + 1, u} f).choose

private instance coefficientRestrictionColimits
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u + 1}} (f : R ⟶ B) :
    PreservesFiniteColimits (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map f)) :=
  (SheafOfModules.sheafRingCoefficientOrdinaryAdjunction.{u + 1, u + 1, u} f).choose_spec.choose

private theorem cochainScalarAdjunction
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    {J : GrothendieckTopology C} {R B : Sheaf J CommRingCat.{u + 1}}
    [HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u} J R))]
    [HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u} J B))]
    (f : R ⟶ B)
    (M : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2} f) :
    Nonempty (M.T ⊣ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map f)).mapDerivedCategory) :=
    by
  obtain ⟨hl, hc, ha⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction.{u + 1, u + 1, u} f
  let := hl
  let := hc
  obtain ⟨a, _⟩ := ha M.E M.obj_eq M.map_eq
  let := M.universal
  obtain ⟨d, _⟩ := Functor.exists_cochainDerivedAdjunction M.E _ a M.T M.ε
    (fun P ↦ P.IsKFlatIndependentCoefficients) (fun K ↦ by
      obtain ⟨P, p, hp, _, hq, _⟩ :=
        CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
      exact ⟨P, p, hp, hq⟩) M.computes
  exact ⟨d⟩

private noncomputable def constantScalarModelIso
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {R B : Type (u + 1)} [CommRing R] [CommRing B]
    [HasDerivedCategory.{u + 2} (realizationModules J R)]
    [HasDerivedCategory.{u + 2} (realizationModules J B)]
    (f : R →+* B)
    (M : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2}
      ((constantSheaf J CommRingCat.{u + 1}).map (CommRingCat.ofHom f))) :
    M.T ≅ ConstantScalarRealization.derivedExtension J f :=
  (cochainScalarAdjunction _ M).some.leftAdjointUniq
    (ConstantScalarRealization.derivedAdjunction J f)

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Realization on a profinite slice factors through its actual section ring.
No disconnectedness hypothesis is needed for scalar associativity.

Source: Hemo--Richarz--Scholbach, (3.2) and Remark 3.2; Stacks Tags 06YY and 07A4
(blueprint: lem-zl-condensed-profinite-scalar-compatibility).

Proof: restriction to the slice preserves constant sheaves and identifies the
restriction of the point coefficient map with the composite of the constant
scalar map R to A and the terminal constant-section map to the coefficient
sheaf. The ring isomorphism used here is `profiniteSectionRingIso`; its maps
preserve multiplication and the scalar inclusion by construction. Choose a
flat-term K-flat representative P of an arbitrary unbounded R-complex.
Restriction preserves the required K-flatness, and constants commute with
scalar extension by the constant-realization scalar comparison. Associativity
of ordinary balanced tensor products then gives the map
b tensor (a tensor p) to ba tensor p; its inverse is b tensor p to
b tensor (1 tensor p). The balanced relations prove that they are inverse,
and their formulas commute with differentials and with all chain maps.
Localizing the K-flat representatives gives the asserted natural isomorphism,
including all unbounded complexes. On the empty slice the section ring is zero,
so both sides are zero, as the same formulas require. -/
theorem condensed_profinite_scalar_compatibility
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (S : Profinite.{u}) :
    profiniteScalarClause Λ.X S := by
  let J := coherentTopology Profinite.{u}
  let K := J.over S
  let R := condensedScalarRing Λ.X
  let O := profiniteCoefficient Λ.X S
  let A := Evaluation.A K O (Over.mk (𝟙 S))
  let q := profiniteScalarMap Λ.X S
  let e := InternalAbelianSheafModule.sectionModuleEquivalence K O
  let := Functor.additive_of_preserves_binary_products e.inverse
  let a := (constantSheaf K CommRingCat.{u + 1}).map (CommRingCat.ofHom q)
  let b := Evaluation.scalarMap K O (Over.mk (𝟙 S)) Over.mkIdTerminal
  let Ma : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2}
      a :=
    SheafOfModules.canonicalDerivedChangeOfRingsModel a
  let Mb := Evaluation.extensionModel K O (Over.mk (𝟙 S)) Over.mkIdTerminal
  let Mc := profiniteDirectScalarModel Λ S
  obtain ⟨_, _, assoc, _, _⟩ := CategoryTheory.RingedKFlatWord.scalar_associator a b Ma Mb Mc
  obtain ⟨slice⟩ := profinite_coefficient_slice_base_change Λ S
  obtain ⟨constants⟩ := commutative_constant_slice_restriction J R S
  let := (commutativeSiteConstantModuleFunctor_exact J R).1
  let := (commutativeSiteConstantModuleFunctor_exact J R).2.1
  let := (commutativeSiteConstantModuleFunctor_exact J R).2.2
  let := (commutativeSiteConstantModuleFunctor_exact K R).1
  let := (commutativeSiteConstantModuleFunctor_exact K R).2.1
  let := (commutativeSiteConstantModuleFunctor_exact K R).2.2
  let constantsD := (Functor.mapDerivedCategoryCompIso
    (commutativeSiteConstantModuleFunctor J R)
    (commutativeConstantSliceRestriction J R S)).symm ≪≫
      Functor.mapDerivedCategoryNatIso constants
  let cJ := commutativeSiteDerivedConstantModuleFunctor J R
  let cK := commutativeSiteDerivedConstantModuleFunctor K R
  let cA := commutativeSiteDerivedConstantModuleFunctor K A
  let E := e.inverse.mapDerivedCategory
  let compare := ConstantScalarRealization.comparisonIso K q
  refine ⟨?_⟩
  change profiniteScalarRealization Λ.X S ≅
    RingDerivedScalarExtension.moduleDerivedExtension q ⋙ (cA ⋙ Mb.T ⋙ E)
  exact Functor.isoWhiskerLeft cJ slice ≪≫
    Functor.isoWhiskerRight constantsD (Mc.T ⋙ E) ≪≫
    Functor.isoWhiskerLeft cK (Functor.isoWhiskerRight assoc.symm E) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft cK (constantScalarModelIso K q Ma)) (Mb.T ⋙ E) ≪≫
    Functor.isoWhiskerRight compare (Mb.T ⋙ E)

end AlgebraicGeometry.ProEtale.CondensedRing
