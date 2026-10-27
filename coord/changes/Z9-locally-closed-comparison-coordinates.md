# AlgebraicGeometry.ProEtale.LocallyClosedComparisonAdjoints and its coordinates

## Reason

The remaining locally closed comparison proof needs separate invertibility and relative
Hom steps. Those steps must refer to the existing comparison coordinates without importing
the module whose theorem they prove. Move the coordinate declarations verbatim to
`Sheaf.AlgebraicGeometry.LocallyClosedComparisonCoordinates` and publicly reexport that
module from the original. No signature, definition body, declaration name, attribute or
instance changes. The docstring of the first structure gains the new definition-node tag.
There is no change to a target or to the meaning of a definition used by a target.

The relocated declarations are:

- `AlgebraicGeometry.ProEtale.LocallyClosedComparisonAdjoints`
- `AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension`
- `AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension`
- `AlgebraicGeometry.ProEtale.LocallyClosedComparisonAdjoints.etaleRight`
- `AlgebraicGeometry.ProEtale.LocallyClosedComparisonAdjoints.proetaleRight`
- `AlgebraicGeometry.ProEtale.LocallyClosedComparisonAdjoints.etalePasted`
- `AlgebraicGeometry.ProEtale.LocallyClosedComparisonAdjoints.proetalePasted`
- `AlgebraicGeometry.ProEtale.locallyClosedExtensionComparison`
- `AlgebraicGeometry.ProEtale.locallyClosedImageCompactification`
- `AlgebraicGeometry.ProEtale.locallyClosedEtaleSheafIso`
- `AlgebraicGeometry.ProEtale.locallyClosedEtaleSupportIso`
- `AlgebraicGeometry.ProEtale.locallyClosedImage_isLeftAdjoint`
- `AlgebraicGeometry.ProEtale.locallyClosedEtaleExceptional`
- `AlgebraicGeometry.ProEtale.locallyClosedEtaleRightIso`

## Old

In `Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison`:

```lean
/-- Coordinates for the two ambient closed right adjoints. Each functor is determined
up to the unique counit-compatible adjoint isomorphism, rather than freely chosen data.
Source: blueprint locally closed exceptional comparison, closed factor
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
structure LocallyClosedComparisonAdjoints (A : Type (u + 1)) [CommRing A]
    {S V : Scheme.{u}} (c : S ⟶ V) where
  etale : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
    DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
  proetale : DerivedCategory (Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A)) ⥤
    DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A))
  etaleAdjunction : (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor ⊣ etale
  proetaleAdjunction : (lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor ⊣ proetale

/-- The etale closed-then-open extension on ordinary derived categories.
Source: blueprint locally closed exceptional comparison, F_et
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
abbrev locallyClosedEtaleExtension (A : Type (u + 1)) [CommRing A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T) [IsOpenImmersion v] :=
  (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor ⋙
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory

/-- The pro-etale closed-then-open extension on ordinary derived categories.
Source: blueprint locally closed exceptional comparison, F_proet
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
abbrev locallyClosedProEtaleExtension (A : Type (u + 1)) [CommRing A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T) [IsOpenImmersion v] :=
  (lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor ⋙
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory

namespace LocallyClosedComparisonAdjoints

variable {A : Type (u + 1)} [CommRing A] {S V T : Scheme.{u}} {c : S ⟶ V}

/-- Open restriction followed by the ambient closed etale right adjoint.
Source: blueprint locally closed exceptional comparison, J_et
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
abbrev etaleRight (a : LocallyClosedComparisonAdjoints A c) (v : V ⟶ T)
    [IsOpenImmersion v] :=
  (Etale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ⋙ a.etale

/-- Open restriction followed by the ambient closed pro-etale right adjoint.
Source: blueprint locally closed exceptional comparison, J_proet
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
abbrev proetaleRight (a : LocallyClosedComparisonAdjoints A c) (v : V ⟶ T)
    [IsOpenImmersion v] :=
  (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ⋙ a.proetale

/-- The literal pasted etale adjunction, fixing its unit and counit.
Source: blueprint locally closed exceptional comparison, pasted adjunction
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
def etalePasted (a : LocallyClosedComparisonAdjoints A c) (v : V ⟶ T)
    [IsOpenImmersion v] : locallyClosedEtaleExtension A c v ⊣ a.etaleRight v :=
  a.etaleAdjunction.comp
    (Etale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) v).mapDerivedCategoryAdjunction

/-- The literal pasted pro-etale adjunction, fixing its unit and counit.
Source: blueprint locally closed exceptional comparison, pasted adjunction
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
def proetalePasted (a : LocallyClosedComparisonAdjoints A c) (v : V ⟶ T)
    [IsOpenImmersion v] : locallyClosedProEtaleExtension A c v ⊣ a.proetaleRight v :=
  a.proetaleAdjunction.comp
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) v).mapDerivedCategoryAdjunction

end LocallyClosedComparisonAdjoints

/-- Delta is the specified closed counit mate followed by open extension comparison.
Source: blueprint locally closed exceptional comparison, Delta
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
def locallyClosedExtensionComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] :
    DerivedCategory.Plus.ι ⋙ locallyClosedEtaleExtension A c v ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ≅
      DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory ⋙
        locallyClosedProEtaleExtension A c v :=
  Functor.isoWhiskerLeft
      (DerivedCategory.Plus.ι ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor)
      ((Functor.mapDerivedCategoryCompIso
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v)
        (comparisonUpperStar (ModuleCat.{u + 1} A) T)).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) v) ≪≫
        Functor.mapDerivedCategoryCompIso _ _) ≪≫
    Functor.isoWhiskerRight (fixedDirectImageComparisonIso A c)
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory

/-- The scheme-theoretic closure compactification of an immersion. No density or
nonemptiness assumption is imposed.
Source: blueprint locally closed exceptional comparison, closure factorization
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
def locallyClosedImageCompactification {S T : Scheme.{u}} (s : S ⟶ T)
    [IsImmersion s] [QuasiCompact s] : Compactification s where
  Z := s.image
  i := s.toImage
  g := s.imageι
  comm := s.toImage_imageι.symm
  isOpenImmersion := inferInstance
  isProper := inferInstance

/-- The unique identity-on-the-source sheaf comparison, oriented from closed/open
extension to closure extension. The existing theorem specifies uniqueness by the open
unit and closed counit, so this choice cannot introduce a scalar twist.
Source: Stacks 0GJ1; blueprint locally closed exceptional comparison, Step 7
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
def locallyClosedEtaleSheafIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] [IsNoetherian T] [QuasiCompact (c ≫ v)] :
    Etale.lowerStar (ModuleCat.{u + 1} A) c ⋙
        Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v ≅
      Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) (c ≫ v).toImage ⋙
        Etale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v).imageι :=
  (((((etale_locallyClosed_extension_comparison (A := A) T (𝟙 T) v).2 (c ≫ v)).choose_spec).1
    c v rfl).choose).symm

/-- The normalized identification with etale compact support at the closure
compactification. Both closed direct images are exact; the comparison is the
localization of the preceding uniquely normalized sheaf map.
Source: Stacks 0GJ1; blueprint locally closed exceptional comparison, Step 7
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
def locallyClosedEtaleSupportIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] [IsNoetherian T] [QuasiCompact (c ≫ v)] :
    locallyClosedEtaleExtension A c v ≅
      Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (locallyClosedImageCompactification (c ≫ v)) :=
  Functor.isoWhiskerRight
      (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorIsoMapDerivedCategory _ ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (locallyClosedEtaleSheafIso A c v) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((Etale.lowerStar (ModuleCat.{u + 1} A)
        (c ≫ v).imageι).rightDerivedFunctorIsoMapDerivedCategory).symm

/-- The existing Brown-adjoint theorem at the closure compactification. The
Noetherian and compact hypotheses it needs follow from the immersion into T; they
are constructed here rather than imposed on the statement as additional assumptions.
Source: blueprint locally closed exceptional comparison, Step 7
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
instance locallyClosedImage_isLeftAdjoint (A : Type (u + 1)) [CommRing A] [Finite A]
    {S T : Scheme.{u}} (s : S ⟶ T) [IsImmersion s] [QuasiCompact s] [IsNoetherian T] :
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (locallyClosedImageCompactification s)).IsLeftAdjoint :=
  letI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian s
  letI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace s
  letI : IsLocallyNoetherian s.image := LocallyOfFiniteType.isLocallyNoetherian s.imageι
  letI : CompactSpace s.image := QuasiCompact.compactSpace_of_compactSpace s.imageι
  Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A
    (locallyClosedImageCompactification s)

/-- The ordinary etale exceptional right adjoint in closure coordinates.
Source: blueprint locally closed exceptional comparison, s-times
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
abbrev locallyClosedEtaleExceptional (A : Type (u + 1)) [CommRing A] [Finite A]
    {S T : Scheme.{u}} (s : S ⟶ T) [IsImmersion s] [QuasiCompact s] [IsNoetherian T] :=
  (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    (locallyClosedImageCompactification s)).rightAdjoint

/-- The counit-compatible etale adjoint identification induced by the normalized
left-adjoint comparison, with no independently chosen right-adjoint isomorphism.
Source: blueprint locally closed exceptional comparison, Step 7
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
def locallyClosedEtaleRightIso {A : Type (u + 1)} [CommRing A] [Finite A]
    {S V T : Scheme.{u}} {c : S ⟶ V} (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] [IsNoetherian T] [QuasiCompact (c ≫ v)]
    (a : LocallyClosedComparisonAdjoints A c) :
    a.etaleRight v ≅ locallyClosedEtaleExceptional A (c ≫ v) :=
  (a.etalePasted v).rightAdjointUniq
    ((Adjunction.ofIsLeftAdjoint _).ofNatIsoLeft (locallyClosedEtaleSupportIso A c v).symm)
```

## New

The same declarations above, byte-identical except for the first blueprint tag, are in
`Sheaf.AlgebraicGeometry.LocallyClosedComparisonCoordinates`. The original module adds:

```lean
public import Sheaf.AlgebraicGeometry.LocallyClosedComparisonCoordinates
```

The original public imports are retained. The new module introduces no alternative
functor, no chosen witness and no new adjunction data beyond the existing coordinates.

## Users

`tools/downstream.py` found 573 transitive consumers. Its per-declaration queries and
an independent whole-library textual search find one external direct declaration user,
listed below. The remaining transitive consumers use the public reexport and their
signatures and definition bodies need no adaptation. No module held by another group
is changed by this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison | Z9 | Imports the same coordinates from the new module; its structure and both theorem signatures are unchanged. |
| Sheaf.AlgebraicGeometry.StratumHomComparisonMate | unclaimed at query time | Uses the adjoint structure and the two forward composites; all are publicly reexported with identical types and bodies. No adaptation. |
| Sheaf.AlgebraicGeometry.LocallyClosedComparisonCoordinates | new Z9 module | Owns the verbatim coordinate declarations. |
| Sheaf.AlgebraicGeometry.LocallyClosedCounitComparison | new Z9 module | Constructs the canonical counit mate and states component invertibility. |
| Sheaf.AlgebraicGeometry.LocallyClosedRelativeHomIdentity | new Z9 module | Uses exactly the retained named comparison maps and closure identification. |

## Status

landed 20261025T102119-L-3777722 2026-10-25 (merge of deliver/Z9/Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison)
