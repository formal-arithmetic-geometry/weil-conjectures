/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sheaf.SheafSliceOrdinaryData
import WeilConjectures.CategoryTheory.Sheaf.SheafSliceOrdinarySquare
import all WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.GeometricRingTransport
import all Mathlib.CategoryTheory.Sites.Limits
import all WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import all WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import all WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.SmoothPurity.Supporting.ChangeOfRingsKFlatQuasiIsoSupplement
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.ProperBaseChange.ContinuousCocontinuousRingedRestriction
import WeilConjectures.CategoryTheory.ProperBaseChange.ElementSiteDescent

/-! # The ordinary ringed square for localization at a sheaf

Source: Stacks Project, Modules on Sites, Tag 04IF, and Sites, Tag 04H1.
(blueprint: lem-sbc-ringed-sheaf-slice-ordinary-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RingedCoefficientCounit

namespace CategoryTheory

set_option maxHeartbeats 800000 in
-- Tensor and localization structures on the element site require explicit universe transport.
private theorem restrictKFlat
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u)) :
    let _ := presentationElementRestriction_additive R A
    ∀ P : CochainComplex (modules R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u} (R := R) (P.X n)) →
      CochainComplex.IsKFlatIndependentCoefficients (R := presentationElementRing R A)
        ((onComplex (elementModulePullback.{u, u} (localCoefficientRings R) A)).obj P) ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u}
        (R := presentationElementRing R A)
        (((onComplex (elementModulePullback.{u, u} (localCoefficientRings R) A)).obj P).X n) := by
  dsimp only
  classical
  let := presentationElementRestriction_additive R A
  obtain ⟨_, hc, _, _⟩ := element_site_descent A
  let := hc
  obtain ⟨f, _, _, ⟨a⟩⟩ := continuous_cocontinuous_ringed_restriction
    (elementTopology A) J (elementProjection A) (localCoefficientRings R)
  obtain ⟨F, hF, aF, hpres, _⟩ := f.exists_kFlatPullback
    (elementTopology A) J (presentationElementRing R A) R
  let := hF
  let r : modules R ⥤ modules (presentationElementRing R A) :=
    elementModulePullback.{u, u} (localCoefficientRings R) A
  let e : F ≅ r := aF.leftAdjointUniq a
  let c := NatIso.mapHomologicalComplex e (.up ℤ)
  intro P hp hf
  obtain ⟨hk, hflat⟩ := hpres P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hp)
    (fun n ↦ (flat_iff_flatOnSite _).mpr (hf n))
  refine ⟨?_, ?_⟩
  · have hki := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mpr hk
    let := SheafOfModules.isMonoidal_W_independentCoefficients (presentationElementRing R A)
    let := SheafOfModules.monoidalCategory (presentationElementRing R A)
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
      (presentationElementRing R A)
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
      (presentationElementRing R A)
    intro T hT
    let d := ((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj T).mapIso (c.app P)
    have ht := hki T hT
    rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at ht ⊢
    exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso
      ((HomotopyCategory.quotient _ _).mapIso d) ht
  · intro n
    apply (flat_iff_flatOnSite _).mp
    let := SheafOfModules.monoidalCategory (presentationElementRing R A)
    change exactFunctor _ _ (MonoidalCategory.tensorRight (r.obj (P.X n)))
    have ht := hflat n
    change exactFunctor _ _ (MonoidalCategory.tensorRight (F.obj (P.X n))) at ht
    exact ObjectProperty.prop_of_iso _
      ((MonoidalCategory.curriedTensor _).flip.mapIso (e.app (P.X n))) ht

/-- Localization at a sheaf commutes with ordinary ringed inverse and direct images.
There are no derived-category or resolution hypotheses.

Source: Stacks Project, Modules on Sites, Tag 04IF; Sites, Tag 04H1;
Cohomology on Sites, Tags 0G7E and 08FI.
(blueprint: lem-sbc-ringed-sheaf-slice-ordinary-comparison).

Proof. Present both slices by their element sites. The arrowwise inverse image on
slice categories has right adjoint given by the pullback of the direct image along
the unit at the slicing sheaf. Transfer this adjunction along the fibre equivalences.
The product comparison identifies localization of inverse image with inverse image
of localization; on a fibre this identification is the second projection. Restrict
its structural ring map using this identification. The graph identities for ring
operations transfer to the slice, and give the induced module direct image. Choose
ordinary pullbacks by scalar extension of the algebraic inverse image. Restriction
commutes with this tensor construction and its scalar insertions, producing sigma.
On underlying sheaves the right adjoint sends a product over the pulled-back slicing
sheaf to the corresponding product over the original sheaf. Its fibrewise module
operations are exactly the original induced operations, giving delta with the stated
underlying geometric mate. The scalar-insertion formula for the two adjunctions
shows that sigma and delta are mates. Restriction is exact, has exact additive
extension by zero, and therefore preserves K-injective complexes. As pullback along
the ringed localization with identity structural map, it preserves K-flat complexes
with flat terms and flatness on the site. These constructions also apply when the
slicing sheaf is initial or terminal: fibres may be empty, and all identities are
identities on the existing sections, without a choice of a section of that sheaf. -/
theorem ringedSheafSliceOrdinaryComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RX : Sheaf J CommRingCat.{u}) (RY : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism (localCoefficientRings RX) (localCoefficientRings RY))
    (A : Sheaf K (Type u)) :
    Nonempty (RingedSheafSliceOrdinaryComparison RX RY f A) := by
  obtain ⟨s⟩ := ringedSheafSliceOrdinarySquare RX RY f A
  let ha := presentationElementRestriction_additive RY A
  let hb := presentationElementRestriction_additive RX (f.inverse.obj A)
  refine ⟨{
    sourceSlice := s.sourceSlice
    targetSlice := s.targetSlice
    sourceLocalization := s.sourceLocalization
    targetLocalization := s.targetLocalization
    slice := s.slice
    sliceInverse := s.sliceInverse
    starComparison := s.starComparison
    starComparison_formula := s.starComparison_formula
    sets := s.sets
    sets_formula := s.sets_formula
    structural := s.structural
    pullback := s.pullback
    pullbackAdditive := s.pullbackAdditive
    ordinaryAdjunction := s.ordinaryAdjunction
    slicePullback := s.slicePullback
    slicePullbackAdditive := s.slicePullbackAdditive
    sliceOrdinaryAdjunction := s.sliceOrdinaryAdjunction
    sigma := s.sigma
    delta := s.delta
    ordinary_mate := s.ordinary_mate
    delta_underlying := s.delta_underlying
    targetRestrictionAdditive := ha
    sourceRestrictionAdditive := hb
    targetRestrictionLimits := (presentationElementRestriction_exact RY A).1
    sourceRestrictionLimits := (presentationElementRestriction_exact RX (f.inverse.obj A)).1
    targetRestrictionColimits := (presentationElementRestriction_exact RY A).2.1
    sourceRestrictionColimits := (presentationElementRestriction_exact RX (f.inverse.obj A)).2.1
    targetKFlat := restrictKFlat RY A
    sourceKInjective := ?_ }⟩
  intro I hI
  let := hI
  exact presentationElementRestriction_kInjective RX (f.inverse.obj A) I

end CategoryTheory
