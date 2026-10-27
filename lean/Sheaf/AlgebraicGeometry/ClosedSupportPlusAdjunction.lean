/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction

/-!
# Bounded-below closed-support adjunction

Source: Stacks Project, Tags 09XQ and 0A45; the bounded-below realization of the
current blueprint `lem-exc-closed-ambient`
(blueprint: def-per-closed-support-plus-adjunction).

The right adjoint is the right derived functor of the actual supported inverse image,
not a choice of an uncharacterized functor. Its adjunction comes from the canonical
supported-kernel Hom bijection. The shift structure is the mate of the direct-image
shift structure transported from the exact termwise functor.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The canonical open complement of the closed immersion.
Source: Stacks Project, Tag 09XQ
(blueprint: def-per-closed-support-plus-adjunction). -/
def closedSupportOpenComplement {Z T : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i] : T.Opens :=
  ⟨(Set.range i.base)ᶜ,
    (IsClosedImmersion.isClosedEmbedding i).isClosed_range.isOpen_compl⟩

/-- The bounded-below closed-support right adjoint, computed by applying
`i⁻¹ ker(1 → j_*j⁻¹)` termwise to bounded-below injective resolutions. The functor on
objects and morphisms is the localization's right derived functor, with its universal
property. `closedUpperShriek` is the existing module-valued supported inverse image.
Source: Stacks Project, Tags 09XQ and 0A45
(blueprint: def-per-closed-support-plus-adjunction). -/
noncomputable def closedSupportPlus (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      _root_.DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (closedUpperShriek (ModuleCat.{u + 1} A) i
    (closedSupportOpenComplement i).ι).rightDerivedFunctorPlus

/-- The fixed derived adjunction. The underived Hom bijection factors through the
supported kernel and the canonical closed unit, and `derivedPlus` derives that actual
adjunction. The left side is identified with right derived direct image by its
unique comparison with the exact termwise functor.
Source: Stacks Project, Tag 09XQ; derived adjunction, Tags 08BJ and 070I
(blueprint: def-per-closed-support-plus-adjunction). -/
noncomputable def closedSupportPlusAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) i ⊣ closedSupportPlus A i :=
  (lowerStarClosedUpperShriekAdjunction (ModuleCat.{u + 1} A) i
    (closedSupportOpenComplement i).ι
    (by rw [Scheme.Opens.range_ι]; exact (compl_compl _).symm)).derivedPlus.ofNatIsoLeft
      (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.symm

/-- The unit of the fixed closed-support adjunction.
Source: Stacks Project, Tag 09XQ
(blueprint: def-per-closed-support-plus-adjunction). -/
noncomputable def closedSupportPlusUnit (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    𝟭 _ ⟶ rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) i ⋙ closedSupportPlus A i :=
  (closedSupportPlusAdjunction A i).unit

/-- The counit of the fixed closed-support adjunction.
Source: Stacks Project, Tag 09XQ
(blueprint: def-per-closed-support-plus-adjunction). -/
noncomputable def closedSupportPlusCounit (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    closedSupportPlus A i ⋙ rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) i ⟶ 𝟭 _ :=
  (closedSupportPlusAdjunction A i).counit

/-- The direct-image shift structure, transported from the exact termwise functor along
the canonical derived-functor comparison. Its degreewise comparison before localization
is the identity, including the signs in the cochain differential.
Source: Stacks Project, Tag 0A8D; exact-functor derived factorization
(blueprint: def-per-closed-support-plus-adjunction). -/
@[instance_reducible]
noncomputable def closedSupportDirectImagePlusCommShift
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    (rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) i).CommShift ℤ :=
  Functor.CommShift.ofIso
    (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.symm ℤ

/-- The cohomological-shift comparison of the right adjoint, with zero and addition
coherence, obtained as the mate for the actual fixed unit and counit above. Its inverse
at `K,n` is `η_(G K[n]) ≫ G(e_(G K,n)) ≫ G(ε_K[n])`, as in the node's construction.
Source: Stacks Project, Tag 0A8D; Mathlib `Adjunction.rightAdjointCommShift`
(blueprint: def-per-closed-support-plus-adjunction). -/
@[instance_reducible]
noncomputable def closedSupportPlusCommShift
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    (closedSupportPlus A i).CommShift ℤ :=
  letI := closedSupportDirectImagePlusCommShift A i
  (closedSupportPlusAdjunction A i).rightAdjointCommShift ℤ

end AlgebraicGeometry.Etale
