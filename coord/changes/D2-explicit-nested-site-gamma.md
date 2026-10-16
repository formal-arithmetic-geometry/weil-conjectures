# schemeComparisonFromRestrictions

## Reason

The returned branch split merely relabelled the two conjuncts and is removed.
The direct proof exposed an expensive computational representation: the gamma
fields were projections of the generic localization-preimage construction.
The revised constructor stores fixed functors directly and constructs gamma
from the site-overlap map and fixed nested pullback square. The new API proves
agreement with the old gamma from its prescribed coherence, using faithful
precomposition with restriction. Forward coherence follows directly from square
normalization; the constructor no longer constructs the old localization lift.
Thus the chosen maps, their coherence, and the public signatures are preserved.

The normalization and compatibility modules are required by this constructor
repair: the constructor must import their proofs without importing the parent
or PerfectOverlapOpenSquareCube (which imports the constructor). Both modules
are fully proved. No obligation is deferred to them.

Local reducibility attributes keep module-category instances and preimages accessible
while preventing elaboration from unfolding the pullback and comparison bodies.
These attributes are local and change no exported reducibility or signature.
The new explicit gamma is a real `@[no_expose]` definition with proved component
and coherence lemmas. Its implementation is checked in its own module; importing
modules use its API instead of expanding the derived comparison construction.

The obsolete direct public import of DerivedOpenRestrictionLocalization is removed
from the constructor module. Localization is needed only by the new gamma
uniqueness proof and remains available through CoreComparisons, so exported
localization declarations are preserved.

The declaration perfectOverlapRestrictedComposite retains its existing unused
section instances; its pre-existing unusedSectionVars warning is scoped off.

## Old

```lean
noncomputable def schemeComparisonFromRestrictions
    {X Y : Scheme.{u}} (g : X ⟶ Y) (U V : Y.Opens) (P Q : X.Opens)
    (hP : P ≤ g ⁻¹ᵁ U) (hQ : Q ≤ g ⁻¹ᵁ V) :
    SchemeTwoOpenComparisonDiagram X Y g U V P Q := by
  let S (W : X.Opens) := (overlapSiteInverse W).mapDerivedCategory
  let H (W : Y.Opens) (T : X.Opens) (hT : T ≤ g ⁻¹ᵁ W) :=
    derivedPullback (g.resLE W T hT) ⋙ S T
  let HU := H U P hP
  let HV := H V Q hQ
  let HW := H (U ⊓ V) (P ⊓ Q) (by
    intro x hx
    exact ⟨hP hx.1, hQ hx.2⟩)
  let β (W : Y.Opens) (T : X.Opens) (hT : T ≤ g ⁻¹ᵁ W) :
      derivedPullback g ⋙
          (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) T).mapDerivedCategory ≅
        (schemeOpenRestriction Y W).mapDerivedCategory ⋙ H W T hT :=
    perfectOverlapRestrictionBeta g W T hT
  let TU := (schemeOpenRestriction Y U).mapDerivedCategory
  let TV := (schemeOpenRestriction Y V).mapDerivedCategory
  let T := DerivedCategory (SheafOfModules.{u}
    ((moduleRings X.toRingedSpace).over (P ⊓ Q)))
  have : TU.IsLocalization ((MorphismProperty.isomorphisms _).inverseImage TU) :=
    schemeDerivedOpenRestriction_isLocalization Y U
  have : TV.IsLocalization ((MorphismProperty.isomorphisms _).inverseImage TV) :=
    schemeDerivedOpenRestriction_isLocalization Y V
  have := Localization.full_whiskeringLeft TU
    ((MorphismProperty.isomorphisms _).inverseImage TU) T
  have := Localization.faithful_whiskeringLeft TU
    ((MorphismProperty.isomorphisms _).inverseImage TU) T
  have := Localization.full_whiskeringLeft TV
    ((MorphismProperty.isomorphisms _).inverseImage TV) T
  have := Localization.faithful_whiskeringLeft TV
    ((MorphismProperty.isomorphisms _).inverseImage TV) T
  refine ⟨comparisonFromRestrictions (derivedPullback g) TU TV _ _ _ _ _ _ _ _ _ _ _ _
    HU HV HW (β U P hP) (β V Q hQ) (β (U ⊓ V) (P ⊓ Q) _)⟩
```

## New

```lean
noncomputable def schemeComparisonFromRestrictions
    {X Y : Scheme.{u}} (g : X ⟶ Y) (U V : Y.Opens) (P Q : X.Opens)
    (hP : P ≤ g ⁻¹ᵁ U) (hQ : Q ≤ g ⁻¹ᵁ V) :
    SchemeTwoOpenComparisonDiagram X Y g U V P Q := by
  let hW : P ⊓ Q ≤ g ⁻¹ᵁ (U ⊓ V) := fun _ hx ↦ ⟨hP hx.1, hQ hx.2⟩
  exact ⟨{
    HU := derivedPullback (g.resLE U P hP) ⋙ (overlapSiteInverse P).mapDerivedCategory
    HV := derivedPullback (g.resLE V Q hQ) ⋙ (overlapSiteInverse Q).mapDerivedCategory
    HW := derivedPullback (g.resLE (U ⊓ V) (P ⊓ Q) hW) ⋙
      (overlapSiteInverse (P ⊓ Q)).mapDerivedCategory
    βU := perfectOverlapRestrictionBeta g U P hP
    βV := perfectOverlapRestrictionBeta g V Q hQ
    βW := perfectOverlapRestrictionBeta g (U ⊓ V) (P ⊓ Q) hW
    γU := perfectOverlapNestedSiteGamma g (homOfLE inf_le_left) (homOfLE inf_le_left) hP hW
    γV := perfectOverlapNestedSiteGamma g (homOfLE inf_le_right) (homOfLE inf_le_right) hQ hW
    coherenceU := perfectOverlapNestedSiteGamma_coherence g
      (homOfLE inf_le_left) (homOfLE inf_le_left) hP hW
    coherenceV := perfectOverlapNestedSiteGamma_coherence g
      (homOfLE inf_le_right) (homOfLE inf_le_right) hQ hW }⟩
```

## Users

The declaration-use scan lists the constructor and the three direct users below.
Other downstream modules see the same signatures. No consumer adaptation is
needed for this constructor repair. The separate comparison-interface change
record describes the one implementation-unfolding consumer adapted with the
new local-isomorphism equation API.
The parent is also listed because its repaired proof uses the new component API.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOverlapCanonicalCounitU | unclaimed | compiles unchanged against the revised constructor |
| Sheaf.AlgebraicGeometry.PerfectOverlapCanonicalGammaLocal | unclaimed | compiles unchanged against the revised constructor |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreOfData | unclaimed | compiles unchanged against the revised constructor |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreTransport | unclaimed | constructor and computational gamma fields repaired; signatures unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapCompositeSiteComponent | D2 | proof repaired; original theorem signature unchanged |

The dependent target-meaning review must recheck this constructor change under
stage 2 §4; the proved uniqueness API supplies agreement of the comparison maps.

## Status

landed 20261016T095751-L-2157367 2026-10-16 (merge of deliver/D2/Sheaf.AlgebraicGeometry.PerfectOverlapCompositeSiteComponent)
