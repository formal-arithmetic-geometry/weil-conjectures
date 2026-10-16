/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapCompositeStageMap
import Sheaf.AlgebraicGeometry.PerfectHomComparisonTriangle
import Sheaf.AlgebraicGeometry.PerfectOverlapCanonicalSiteTriangle
import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionLocalization
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare
import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons
import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreTransport
import Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence
import Sheaf.AlgebraicGeometry.TwoOpenComparisonDiagram

/-! # A component of composite overlap compatibility
Source: Stacks Project, Tags 08DW and 0D5S.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local irreducible] derivedPullback perfectHomComposition
attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

/-- The gluing-side composite equals the constructed cartesian stage map.
Source: Stacks Project, Tags 08DW and 0D5S, restriction comparisons in Tag 09RE.

Proof: Fix either branch L = U or L = V and put W = U ∩ V. Cancel the
larger open immersion to identify the two restricted scheme composites.
Replace exact restriction along a nested inclusion by its pinned inclusion
pullback comparison. On objects restricted from the global category, three
applications of associativity for the fixed pullback-composition family equate
the two paths through this square. The normalization equation for
`overlapOpenInclusionPullbackIso` cancels the inclusion comparisons, giving
compatibility with exact nested restriction.

The defining coherence equation for the restriction comparison diagram now
identifies gamma inverse, followed by the open-site overlap comparison, with
the inverse-site image of this nested-square comparison inverse. First derive
this identity on globally restricted objects: substitute the component formula
for `perfectOverlapRestrictionBeta`, use the open-site return triangle, and
apply the preceding nested-restriction identity. Open restriction is a
localization and hence essentially surjective. Naturality along an isomorphism
from a restricted preimage proves the identity on every object on the
corresponding open of K.

Substitute theta = kappa followed by the inverse-site image of phi followed
by the site-return map. The U or V theorem of
`PerfectOverlapCanonicalSiteTriangle` cancels the site-return map against tau
and the prescribed apex-object comparison. The kappa component is the
inverse-site image of `perfectOverlapCompositeLocalIso`. Naturality of the
open-site overlap comparison moves kappa across gamma. Naturality of the
site counit then leaves precisely the counit, the nested-square inverse,
the restricted local composition comparison, and the fixed stage-object map.
These are the four factors of `perfectOverlapCompositeStageMapAt`; the branch
formula for `perfectOverlapCompositeStageMap` finishes the equation. No cover,
nonempty-open or boundedness hypothesis is used.
(blueprint: lem-pc-perfect-overlap-composite-site-component). -/
theorem perfectOverlapCompositeSiteComponent
    {X Y K C S : Scheme.{u}}
    (f : K ⟶ Y) (gk : X ⟶ K) (g : X ⟶ Y) (hgf : gk ≫ f = g)
    (pX : X ⟶ C) (pY : Y ⟶ S)
    (b : C ⟶ S)
    (hg : IsPullback g pX pY b)
    (U V : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (E : schemeDerivedCategory X)
    (φU : (derivedPullback (g ∣_ U)).obj A ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback (g ∣_ V)).obj B ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ V)).mapDerivedCategory.obj E) :
  let W := U ⊓ V
  let _r := gk.resLE (f ⁻¹ᵁ W) (g ⁻¹ᵁ W)
    (by rw [← Scheme.Hom.comp_preimage, hgf])
  let data := transportDataOfComposite f gk g hgf U V A B E φU φV
  let F : Bool → schemeDerivedCategory (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V).toScheme := fun a ↦
    if a then
      (schemeOpenOverlapRestriction K
        (homOfLE (inf_le_right : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V))).mapDerivedCategory.obj
        ((derivedPullback (f ∣_ V)).obj B)
    else
      (schemeOpenOverlapRestriction K
        (homOfLE (inf_le_left : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U))).mapDerivedCategory.obj
        ((derivedPullback (f ∣_ U)).obj A)
  let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
    (homOfLE (inf_le_left : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U))).mapDerivedCategory
  let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
    (homOfLE (inf_le_right : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ V))).mapDerivedCategory
  let τU := (Functor.mapDerivedCategoryCompIso
    (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (g ⁻¹ᵁ U))
    (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
      (homOfLE (inf_le_left : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U)))).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (inf_le_left : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U)))
  let τV := (Functor.mapDerivedCategoryCompIso
    (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (g ⁻¹ᵁ V))
    (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
      (homOfLE (inf_le_right : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ V)))).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (inf_le_right : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ V)))
  let ψ : ∀ a, data.d.toDiagram.HW.obj (F a) ≅
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
        (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)).mapDerivedCategory.obj E := fun a ↦
    Bool.casesOn a
      (data.d.toDiagram.γU.symm.app ((derivedPullback (f ∣_ U)).obj A) ≪≫
        SP.mapIso data.θU ≪≫ τU.app E)
      (data.d.toDiagram.γV.symm.app ((derivedPullback (f ∣_ V)).obj B) ≪≫
        SQ.mapIso data.θV ≪≫ τV.app E)
  let apex := perfectOverlapApexEquivalence g pX pY b hg U V
  let ρ : ∀ a : Bool, apex.functor.obj
      ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
        (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)).mapDerivedCategory.obj E) ≅
        (derivedPullback (pullback.fst (W.ι ≫ pY) b)).obj
          (if a then (derivedPullback (Y.homOfLE (inf_le_right : W ≤ V))).obj B
          else (derivedPullback (Y.homOfLE (inf_le_left : W ≤ U))).obj A) := fun a ↦
    Bool.casesOn a
      (perfectOverlapApexObjectIso g pX pY b hg U V U inf_le_left A E φU)
      (perfectOverlapApexObjectIso g pX pY b hg U V V inf_le_right B E φV)
  (apex.functor.map (ψ false).hom ≫ (ρ false).hom =
    perfectOverlapCompositeStageMap f gk g hgf pX pY b hg U V A B E φU φV false) ∧
  (apex.functor.map (ψ true).hom ≫ (ρ true).hom =
    perfectOverlapCompositeStageMap f gk g hgf pX pY b hg U V A B E φU φV true) := by sorry

end AlgebraicGeometry
