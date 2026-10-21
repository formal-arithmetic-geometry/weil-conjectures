/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.Paper.SheafSliceOrdinaryData
import Sheaf.Paper.SheafSliceOrdinarySquare
import all Sheaf.CategoryTheory.RingedToposKFlatPullback
import Sheaf.CategoryTheory.ContinuousCocontinuousRingedRestriction
import Sheaf.CategoryTheory.ElementSiteDescent

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
