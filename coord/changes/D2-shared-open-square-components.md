# openPullbackRestrictionIso_inv_app_eq_square and the shared open-square component API

## Reason

Repair the return at d06c318b7: NestedSiteCompatibility duplicated four theorems
already public in OpenSquareCube. Directly importing that module would cycle:
OpenSquareCube imports Transport, whose repaired constructor imports
NestedSiteCompatibility. Both already publicly import CoreComparisons, where
all objects in the four statements are defined or publicly imported. Relocate
the existing four theorem declarations unchanged into CoreComparisons and
remove the four private duplicates from NestedSiteCompatibility. Each fact has
one declaration and one proof. No definition, theorem type, universe, instance
binder or public name changes. This is a dependency repair, not a split for the
compile limit. No target-meaning review is reopened by this relocation itself.

## Old

In lean/Sheaf/AlgebraicGeometry/PerfectOverlapOpenSquareCube.lean:

```lean
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
/-- The inverse of the named open-pullback restriction comparison is the
componentwise pinned open square. Both use the same chosen pullback-composition
isomorphism; their open comparisons cancel in opposite order. -/
theorem openPullbackRestrictionIso_inv_app_eq_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) (P : X.Opens) (U : Y.Opens)
    (h : P ≤ g ⁻¹ᵁ U) (M : schemeDerivedCategory Y) :
    (openPullbackRestrictionIso g P U h).inv.app M =
      (singleComplexOpenPullbackSquareIso g U P (g.resLE U P h)
        (Scheme.Hom.resLE_comp_ι g h)).hom.app M := by
  simp only [openPullbackRestrictionIso, singleComplexOpenPullbackSquareIso,
    NatIso.ofComponents_hom_app, Iso.trans_inv, NatTrans.comp_app,
    Iso.symm_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Iso.symm_inv, eqToIso.hom, eqToIso.inv, eqToHom_app]
  simp only [Category.assoc, perfectHomComposition,
    singleComplexOpenPinnedComposition]

/-- The forward named restriction comparison is the inverse pinned open
square component. This is the inverse of the preceding component equality. -/
theorem openPullbackRestrictionIso_hom_app_eq_square_inv
    {X Y : Scheme.{u}} (g : X ⟶ Y) (P : X.Opens) (U : Y.Opens)
    (h : P ≤ g ⁻¹ᵁ U) (M : schemeDerivedCategory Y) :
    (openPullbackRestrictionIso g P U h).hom.app M =
      (singleComplexOpenPullbackSquareIso g U P (g.resLE U P h)
        (Scheme.Hom.resLE_comp_ι g h)).inv.app M := by
  have he : (openPullbackRestrictionIso g P U h).symm.app M =
      (singleComplexOpenPullbackSquareIso g U P (g.resLE U P h)
        (Scheme.Hom.resLE_comp_ι g h)).app M := by
    apply Iso.ext
    exact openPullbackRestrictionIso_inv_app_eq_square g P U h M
  have := congrArg Iso.symm he
  exact congrArg Iso.hom this

section

variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian

/-- The canonical restriction/pullback component is the inverse pinned open
square, transported into the localized site and preceded by its return unit. -/
theorem perfectOverlapRestrictionBeta_hom_app_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) (P : X.Opens) (U : Y.Opens)
    (h : P ≤ g ⁻¹ᵁ U) (M : schemeDerivedCategory Y) :
    (perfectOverlapRestrictionBeta g U P h).hom.app M =
      (openSiteReturnIso X P).inv.app ((derivedPullback g).obj M) ≫
        (overlapSiteInverse P).mapDerivedCategory.map
          ((singleComplexOpenPullbackSquareIso g U P (g.resLE U P h)
            (Scheme.Hom.resLE_comp_ι g h)).inv.app M) := by
  rw [perfectOverlapRestrictionBeta_hom_app,
    openPullbackRestrictionIso_hom_app_eq_square_inv]

/-- The inverse canonical restriction/pullback component is the forward
pinned open square, followed by the site return map. -/
theorem perfectOverlapRestrictionBeta_inv_app_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) (P : X.Opens) (U : Y.Opens)
    (h : P ≤ g ⁻¹ᵁ U) (M : schemeDerivedCategory Y) :
    (perfectOverlapRestrictionBeta g U P h).inv.app M =
      (overlapSiteInverse P).mapDerivedCategory.map
        ((singleComplexOpenPullbackSquareIso g U P (g.resLE U P h)
          (Scheme.Hom.resLE_comp_ι g h)).hom.app M) ≫
        (openSiteReturnIso X P).hom.app ((derivedPullback g).obj M) := by
  rw [perfectOverlapRestrictionBeta_inv_app,
    openPullbackRestrictionIso_inv_app_eq_square]

end

```

NestedSiteCompatibility separately contained four private copies of the above
statements and proofs, rejected by the duplicate check.

## New

The exact block above is moved into a fresh section at the end of
lean/Sheaf/AlgebraicGeometry/PerfectOverlapObjectRealizationCoreComparisons.lean.
OpenSquareCube retains its existing public import of CoreComparisons and
contains no redeclaration. NestedSiteCompatibility retains its existing public
import of CoreComparisons, deletes its four private duplicates, and applies
perfectOverlapRestrictionBeta_inv_app_square and
perfectOverlapRestrictionBeta_hom_app_square directly in normalized_gamma_rhs.
The moved theorem signatures, surrounding instance binders, and proofs are
verbatim the Old block. Public visibility is unchanged. The core comparison
node records the moved API and its pinned-square proof dependencies.

The refreshed linter also reports six pre-existing `letI` proof locals in
perfectOverlapNaturalComparisonOfSquare_hom_app. They become `let` in that
proved theorem, as suggested by Lean; no definition body is changed. The
pre-existing unused over-site section instance in
perfectOverlapCompositeLocalMap_eq is retained to preserve its signature, with
a scoped unusedSectionVars suppression.

## Users

The declaration-use scan for all four names finds only OpenSquareCube and
CanonicalGammaLocal in the existing library. NestedSiteCompatibility is the
new user in this delivery. No existing consumer needs an adaptation for this
relocation; OpenSquareCube's existing public import preserves all old access.
The relocated declarations have no uses of Transport or of the later cube.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons | unclaimed | owns the four existing theorems; all previous declarations unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapOpenSquareCube | unclaimed | public import reexports the same four names and statements; local copies removed |
| Sheaf.AlgebraicGeometry.PerfectOverlapNestedSiteCompatibility | D2 (new module) | uses imported component API; four duplicate private proofs removed |
| Sheaf.AlgebraicGeometry.PerfectOverlapCanonicalGammaLocal | unclaimed | same beta component theorems remain public through OpenSquareCube |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreTransport | unclaimed | uses NestedSiteCompatibility without importing the downstream cube |

## Status

landed 20261016T095751-L-2157367 2026-10-16 (merge of deliver/D2/Sheaf.AlgebraicGeometry.PerfectOverlapCompositeSiteComponent)
