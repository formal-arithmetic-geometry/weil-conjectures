/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
public import Sheaf.CategoryTheory.RingedSheafSliceAdjunction
public import Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Sheaf.CategoryTheory.RingedIdealGenerators
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Sheaf.CategoryTheory.LocalCoefficientLocalization
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-!
# Transport between presentations of a ringed topos

Source: Stacks Project, Modules on Sites, Tag 03CR (equivalence case), and
Algebraization, Tag 099J (opening presentation reduction)
(blueprint: lem-weil-pbc-ringed-presentation-transport).

## Main statement

- `ringed_presentation_transport`: transport on modules, derived categories, all slices
  and the two families of local vanishing tests.

## Main definitions

- `RingedPresentationFunctor`: exactness, K-injectives, derived Hom and localization.
- `RingedPresentationEquivalence`: the two inverse module and derived functors.
- `RingedPresentationRestrictions`: sheaf slices and further restrictions.
- `RingedPresentationTransport`: the full comparison, tied to the specified morphism.

All derived categories below use the standard localization, with morphisms in universe
`u + 1`. This fixes a model of the unbounded derived category, without a smallness
assumption on its morphisms. The abbreviations expose precisely the existing definitions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The existing module category, with commutativity forgotten.
Source: Stacks 03CR (blueprint: lem-weil-pbc-ringed-presentation-transport). -/
abbrev PresentationModules {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :=
  ringedSiteModules.{u} (localCoefficientRings R)

/-- The standard unbounded derived category of the recorded module category.
Source: Stacks 05RR (blueprint: lem-weil-pbc-ringed-presentation-transport). -/
abbrev PresentationDerived {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :=
  letI := HasDerivedCategory.standard (PresentationModules R)
  DerivedCategory (PresentationModules R)

/-- The localization functor for the standard derived-category model.
Source: Stacks 05RR (blueprint: lem-weil-pbc-ringed-presentation-transport). -/
def presentationQ {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    CochainComplex (PresentationModules R) ℤ ⥤ PresentationDerived R :=
  letI := HasDerivedCategory.standard (PresentationModules R)
  DerivedCategory.Q

/-- The existing derived internal Hom in the standard localization model.
Source: Stacks 08J7 (blueprint: lem-weil-pbc-ringed-presentation-transport). -/
def presentationRHom {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    (PresentationDerived R)ᵒᵖ × PresentationDerived R ⥤ PresentationDerived R :=
  letI := HasDerivedCategory.standard (PresentationModules R)
  derivedInternalHomOfUniverses.{u, u, u, u + 1} J R

/-- The underlying sheaf of sets of a module sheaf.
Source: Stacks 03CR (blueprint: lem-weil-pbc-ringed-presentation-transport). -/
abbrev presentationForget {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :=
  SheafOfModules.toSheaf (localCoefficientRings R) ⋙
    sheafCompose J (forget AddCommGrpCat.{u})

/-- Multiplication by an actual global ring section on the rank-one module.
Source: Stacks 0997 (blueprint: lem-weil-pbc-ringed-presentation-transport). -/
def presentationScalar {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (s : (R.obj ⋙ forget CommRingCat).sections) :
    SheafOfModules.unit (localCoefficientRings R) ⟶
      SheafOfModules.unit (localCoefficientRings R) where
  val := PresheafOfModules.sectionsSMul _ s

/-- Termwise application of an additive functor, with its instance made explicit.
Source: Stacks 05RR (blueprint: lem-weil-pbc-ringed-presentation-transport). -/
def presentationComplexMap {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (F : PresentationModules R ⥤ PresentationModules S) (h : F.Additive) :
    CochainComplex (PresentationModules R) ℤ ⥤ CochainComplex (PresentationModules S) ℤ :=
  letI := h
  F.mapHomologicalComplex (ComplexShape.up ℤ)

/-- The exact termwise functor localized at quasi-isomorphisms; no resolution is chosen.
Source: Stacks 05RR (blueprint: lem-weil-pbc-ringed-presentation-transport). -/
def presentationDerivedMap {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (F : PresentationModules R ⥤ PresentationModules S) (ha : F.Additive)
    (hl : PreservesFiniteLimits F) (hc : PreservesFiniteColimits F) :
    PresentationDerived R ⥤ PresentationDerived S :=
  letI := HasDerivedCategory.standard (PresentationModules R)
  letI := HasDerivedCategory.standard (PresentationModules S)
  letI := ha
  letI := hl
  letI := hc
  F.mapDerivedCategory

/-- The exact-functor, internal-Hom, K-injective and localization conclusions, for a
specified functor. The localization equation includes its canonical map from the ring.
The scalar comparison is an equality of multiplication maps, so imposes precisely the
transport of the chosen section, rather than an arbitrary choice of an inverted scalar.
Source: Stacks 03CR, 08JB and 0997
(blueprint: lem-weil-pbc-ringed-presentation-transport). -/
structure RingedPresentationFunctor
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (F : PresentationModules R ⥤ PresentationModules S) where
  additive : F.Additive
  finiteLimits : PreservesFiniteLimits F
  finiteColimits : PreservesFiniteColimits F
  termwise : Nonempty (presentationQ R ⋙
    presentationDerivedMap F additive finiteLimits finiteColimits ≅
      presentationComplexMap F additive ⋙ presentationQ S)
  unit : F.obj (SheafOfModules.unit (localCoefficientRings R)) ≅
    SheafOfModules.unit (localCoefficientRings S)
  kInjective : ∀ I : CochainComplex (PresentationModules R) ℤ,
    I.IsKInjective → ((presentationComplexMap F additive).obj I).IsKInjective
  internalHom : Nonempty (presentationRHom R ⋙
    presentationDerivedMap F additive finiteLimits finiteColimits ≅
      ((presentationDerivedMap F additive finiteLimits finiteColimits).op.prod
        (presentationDerivedMap F additive finiteLimits finiteColimits)) ⋙ presentationRHom S)
  localization : ∀ (s : (R.obj ⋙ forget CommRingCat).sections)
    (t : (S.obj ⋙ forget CommRingCat).sections),
    F.map (presentationScalar R s) ≫ unit.hom = unit.hom ≫ presentationScalar S t →
    ∃ l : F.obj (ringedSectionLocalizationOfUniverses R s) ≅
      ringedSectionLocalizationOfUniverses S t,
      F.map (ringedSectionLocalizationUnitOfUniverses R s) ≫ l.hom =
        unit.hom ≫ ringedSectionLocalizationUnitOfUniverses S t

/-- An exact module equivalence and its inverse, with the stated derived comparisons.
Source: Stacks 03CR, 05RR and 08J7
(blueprint: lem-weil-pbc-ringed-presentation-transport). -/
structure RingedPresentationEquivalence
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u}) where
  modules : PresentationModules R ≌ PresentationModules S
  forward : RingedPresentationFunctor R S modules.functor
  backward : RingedPresentationFunctor S R modules.inverse
  derivedUnit : Nonempty (
    presentationDerivedMap modules.functor forward.additive forward.finiteLimits
        forward.finiteColimits ⋙
      presentationDerivedMap modules.inverse backward.additive backward.finiteLimits
        backward.finiteColimits ≅ 𝟭 (PresentationDerived R))
  derivedCounit : Nonempty (
    presentationDerivedMap modules.inverse backward.additive backward.finiteLimits
        backward.finiteColimits ⋙
      presentationDerivedMap modules.functor forward.additive forward.finiteLimits
        forward.finiteColimits ≅ 𝟭 (PresentationDerived S))

/-- The functor on derived categories attached to the recorded exact functor.
Source: Stacks 05RR (blueprint: lem-weil-pbc-ringed-presentation-transport). -/
abbrev RingedPresentationFunctor.derived
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    {F : PresentationModules R ⥤ PresentationModules S} (T : RingedPresentationFunctor R S F) :=
  presentationDerivedMap F T.additive T.finiteLimits T.finiteColimits

/-- The commutative restricted ring on the existing element site: `(U,s) ↦ R(U)`.
This retains exactly the underlying ring of `elementRing`, with no new site construction.
Source: Stacks 0791 and 04IE (blueprint: lem-weil-pbc-ringed-presentation-transport). -/
def presentationElementRing {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u)) :
    Sheaf (elementTopology A) CommRingCat.{u} :=
  ⟨(elementProjection A).op ⋙ R.obj,
    (elementProjection A).op_comp_isSheaf_of_isSheaf _ _ _ R.property⟩

/-- The existing site-object vanishing tests, in the standard derived-category model.
No finiteness or boundedness assumption is built into this predicate.
Source: Stacks 0999 (blueprint: lem-weil-pbc-ringed-presentation-transport). -/
def presentationComplete {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (I : PresentationModules R)
    (ι : I ⟶ SheafOfModules.unit (localCoefficientRings R))
    (N : PresentationDerived R) : Prop :=
  letI := HasDerivedCategory.standard (PresentationModules R)
  letI (U : C) := HasDerivedCategory.standard (PresentationModules (R.over U))
  IsLocallyDerivedRingedIdealComplete R I ι N

/-- All the restriction comparisons used in the statement: arbitrary sheaf slices,
relocalization, and site-object slices through sheafified representables.
Internal Hom and localization comparisons are those in `RingedPresentationFunctor`.
Source: Stacks 04IE, 04J4, 08JB and 00Y1
(blueprint: lem-weil-pbc-ringed-presentation-transport). -/
structure RingedPresentationRestrictions
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) where
  restriction : ∀ A : Sheaf J (Type u),
    RingedPresentationFunctor R (presentationElementRing R A)
      (elementModulePullback.{u, u} (localCoefficientRings R) A)
  restrictionUnit : ∀ A : Sheaf J (Type u), (restriction A).unit = Iso.refl _
  overContinuous : ∀ {A B : Sheaf J (Type u)} (b : B ⟶ A),
    Functor.IsContinuous (elementMap b) (elementTopology B) (elementTopology A)
  overRestriction : ∀ {A B : Sheaf J (Type u)} (b : B ⟶ A),
    RingedPresentationFunctor (presentationElementRing R A) (presentationElementRing R B)
      (elementModulePullbackOver.{u, u} (localCoefficientRings R) b (overContinuous b))
  overUnit : ∀ {A B : Sheaf J (Type u)} (b : B ⟶ A),
    (overRestriction b).unit = Iso.refl _
  relocalization : ∀ {A B : Sheaf J (Type u)} (b : B ⟶ A),
    Nonempty (elementModulePullback.{u, u} (localCoefficientRings R) A ⋙
      elementModulePullbackOver.{u, u} (localCoefficientRings R) b (overContinuous b) ≅
        elementModulePullback.{u, u} (localCoefficientRings R) B)
  derivedRelocalization : ∀ {A B : Sheaf J (Type u)} (b : B ⟶ A),
    Nonempty ((restriction A).derived ⋙ (overRestriction b).derived ≅ (restriction B).derived)
  siteObject : ∀ U : C,
    ∃ E : RingedPresentationEquivalence (R.over U)
      (presentationElementRing R ((presheafToSheaf J (Type u)).obj (yoneda.obj U))),
      Nonempty (SheafOfModules.overFunctor.{u} (localCoefficientRings R) U ⋙ E.modules.functor ≅
        elementModulePullback.{u, u} (localCoefficientRings R)
          ((presheafToSheaf J (Type u)).obj (yoneda.obj U)))

/-- The module equivalence is the adjunction of the specified ringed-topos morphism.
The underlying comparison and the rank-one comparison identify the structural map itself.
Thus none of the functors in the conclusion can be an arbitrary unrelated equivalence.
Source: Stacks 03CR and 03D7
(blueprint: lem-weil-pbc-ringed-presentation-transport). -/
structure RingedPresentationAt
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S)) where
  transport : RingedPresentationEquivalence S R
  pushforward : transport.modules.inverse ≅ e.modules
  underlying : transport.modules.functor ⋙ presentationForget R ≅
    presentationForget S ⋙ e.inverse
  structural :
    (presentationForget R).map transport.forward.unit.hom =
      underlying.hom.app (SheafOfModules.unit (localCoefficientRings S)) ≫ e.ringMap

/-- Transport on the whole topos and every sheaf slice, with all restriction squares and
both families of local derived Hom tests. The ideal on the source is explicitly the image
of the ideal inclusion under module pullback and the rank-one ring identification.
Source: Stacks 03CR, 04IE, 04J4 and 099J
(blueprint: lem-weil-pbc-ringed-presentation-transport). -/
structure RingedPresentationTransport
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S)) where
  whole : RingedPresentationAt e
  sourceRestrictions : RingedPresentationRestrictions S
  targetRestrictions : RingedPresentationRestrictions R
  sourceSlices : ∀ A : Sheaf K (Type u),
    RingedSheafSliceAdjunctionData (localCoefficientRings S) A
  targetSlices : ∀ A : Sheaf J (Type u),
    RingedSheafSliceAdjunctionData (localCoefficientRings R) A
  sliceMorphism : ∀ A : Sheaf K (Type u),
    RingedToposMorphism
      (localCoefficientRings (presentationElementRing R (e.inverse.obj A)))
      (localCoefficientRings (presentationElementRing S A))
  sliceInverseEquivalence : ∀ A : Sheaf K (Type u),
    (sliceMorphism A).inverse.IsEquivalence
  sliceRingIsIso : ∀ A : Sheaf K (Type u), IsIso (sliceMorphism A).ringMap
  sliceTransport : ∀ A : Sheaf K (Type u), RingedPresentationAt (sliceMorphism A)
  sliceTopos : ∀ A : Sheaf K (Type u),
    Nonempty ((sliceMorphism A).inverse ≅
      (sourceSlices A).fibreEquivalence.functor ⋙ Over.post e.inverse ⋙
        (targetSlices (e.inverse.obj A)).fibreEquivalence.inverse)
  sliceSets : ∀ A : Sheaf K (Type u),
    e.inverse ⋙ elementSheafPullback (e.inverse.obj A) ≅
      elementSheafPullback A ⋙ (sliceMorphism A).inverse
  sliceStructural : ∀ A : Sheaf K (Type u),
    (sliceSets A).hom.app ((sheafCompose K (forget RingCat)).obj
      (localCoefficientRings S)) ≫ (sliceMorphism A).ringMap =
        (elementSheafPullback (e.inverse.obj A)).map e.ringMap
  restrictionModules : ∀ A : Sheaf K (Type u),
    Nonempty (whole.transport.modules.functor ⋙
      elementModulePullback.{u, u} (localCoefficientRings R) (e.inverse.obj A) ≅
        elementModulePullback.{u, u} (localCoefficientRings S) A ⋙
          (sliceTransport A).transport.modules.functor)
  restrictionDerived : ∀ A : Sheaf K (Type u),
    Nonempty (whole.transport.forward.derived ⋙
      (targetRestrictions.restriction (e.inverse.obj A)).derived ≅
        (sourceRestrictions.restriction A).derived ⋙
          (sliceTransport A).transport.forward.derived)
  furtherModules : ∀ {A B : Sheaf K (Type u)} (b : B ⟶ A),
    Nonempty ((sliceTransport A).transport.modules.functor ⋙
      elementModulePullbackOver.{u, u} (localCoefficientRings R) (e.inverse.map b)
        (targetRestrictions.overContinuous (e.inverse.map b)) ≅
      elementModulePullbackOver.{u, u} (localCoefficientRings S) b
        (sourceRestrictions.overContinuous b) ⋙ (sliceTransport B).transport.modules.functor)
  furtherDerived : ∀ {A B : Sheaf K (Type u)} (b : B ⟶ A),
    Nonempty ((sliceTransport A).transport.forward.derived ⋙
      (targetRestrictions.overRestriction (e.inverse.map b)).derived ≅
        (sourceRestrictions.overRestriction b).derived ⋙
          (sliceTransport B).transport.forward.derived)
  localTests : ∀ (N : PresentationDerived S) (I : PresentationModules S)
    (ι : I ⟶ SheafOfModules.unit (localCoefficientRings S)) [Mono ι],
    presentationComplete S I ι N ↔
      presentationComplete R (whole.transport.modules.functor.obj I)
        (whole.transport.modules.functor.map ι ≫ whole.transport.forward.unit.hom)
        (whole.transport.forward.derived.obj N)

/-- An equivalence of ringed topoi transports module sheaves, their unbounded derived
categories, all sheaf slices, derived internal Hom, section localizations and local tests.

Source: Stacks Project, Modules on Sites, Tag 03CR, equivalence case, and Algebraization,
Tag 099J, opening reduction (blueprint: lem-weil-pbc-ringed-presentation-transport).

Proof, following the nine steps of the node:
1. Use the tensor adjunction (lem-weil-pbc-ringed-topoi-module-adjunction). Since the
   structural ring map is invertible, pullback is inverse image with its transported
   scalar action. Transport the additive and scalar operations through the sheaf
   equivalence. The linear unit and counit are isomorphisms. An additive equivalence
   preserves kernels and cokernels, hence is exact.
2. Localize the two termwise functors using
   lem-weil-pbc-exact-functor-derived-factorization. Their termwise unit and counit give
   the inverse derived equivalences, without boundedness assumptions.
3. Adjunction on homotopy categories identifies maps from an acyclic complex into the
   transported complex with maps into the original K-injective. The inverse exact
   functor preserves acyclicity; the latter maps are null-homotopic. Interchange the
   functors for the reverse direction (def-pur-kinjective-complex).
4. Apply the equivalence to arrows into A. Its inverse uses the original equivalence
   unit. Finite-product preservation identifies the restricted rings. Use the element
   sites of lem-weil-pbc-ringed-sheaf-slice-adjunction. Further restrictions are the same
   fibre products. For site objects use lem-weil-pbc-localized-sheaves-over-representable
   over the sheafified representable; no subcanonicity is needed.
5. The pullback is exact and computes derived pullback. Tensor preservation from
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback and the closed adjunction from
   lem-sf-ringed-derived-closed-symmetric-monoidal identify, naturally in C,L,M,
   Hom(C,F RHom(L,M)) with Hom(G C,RHom(L,M)), then Hom(G C tensor L,M), then
   Hom(C tensor F L,F M), then Hom(C,RHom(F L,F M)). Yoneda gives the comparison.
6. The exact left adjoint j_A! makes j_A* preserve K-injectives by
   lem-weil-pbc-right-adjoint-preserves-kinjective. On the element site, slicing at (U,s)
   is C/U. Restriction preserves sheaf Hom and sectionwise products, hence the Hom
   complex with differential d phi = d_I phi - (-1)^n phi d_L. Compute derived Hom
   with a K-injective target (def-pur-sheaf-hom, def-pur-hom-complex and
   def-pur-derived-internal-hom). The same restriction formulas give relocalization.
7. Section localization is the module-sheaf colimit of repeated multiplication by the
   section (def-weil-pbc-local-coefficient-localization). Equivalences and restriction
   preserve this colimit and its map from the ring. The multiplication comparison
   therefore identifies the two localizations and their unit maps.
8. Tests on site objects imply tests on an arbitrary sheaf A: restrict the derived Hom
   to every (U,s) of its element site. Steps 6-7 give zero; exactness makes every
   cohomology sheaf have zero values, so the object is zero. Conversely take A to be
   the sheafified representable. Empty sites and empty covering sieves cause no exception.
9. Full faithfulness identifies ideal sections under inverse image, and essential
   surjectivity covers every test sheaf on the other side. Steps 5 and 7 identify the
   test objects; the slice equivalences preserve and reflect zero. Step 8 gives exactly
   the two site-object families, for every ideal and every unbounded N. -/
theorem ringed_presentation_transport
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence] [IsIso e.ringMap] :
    Nonempty (RingedPresentationTransport e) := by
  sorry

end CategoryTheory
