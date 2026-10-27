# AlgebraicGeometry.Scheme.SequentialVaryingRing.restrictionComp and derivedId

## Reason

The realization proof compares scalar restrictions, their complex functors and their
localization factors. Functor-wide `Iso.refl` forces elaboration to compare entire
restriction functors, including the module object construction. Use natural
isomorphisms with identity components and check naturality on sections instead.
Their components, signatures, universes, visibility, and mathematical meaning are
unchanged. The derived compositor and unit continue to be the canonical exact
localization comparisons for those same maps.

## Old

```lean
def restrictionComp {A B C : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : A ⟶ B) (b : B ⟶ C) (d : A ⟶ C) (h : a ≫ b = d) :
    reductionRestrict T b ⋙ reductionRestrict T a ≅ reductionRestrict T d :=
  by
  subst d
  exact Iso.refl _

def derivedId (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    reductionDerivedRestrict T (𝟙 A) ≅ 𝟭 (reductionDerivedCategory T A) :=
  exactDerivedRestrictionUnit (reductionRestrict T (𝟙 A)) (Iso.refl _)
```

## New

```lean
def restrictionComp {A B C : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : A ⟶ B) (b : B ⟶ C) (d : A ⟶ C) (h : a ≫ b = d) :
    reductionRestrict T b ⋙ reductionRestrict T a ≅ reductionRestrict T d :=
  by
  subst d
  refine NatIso.ofComponents (fun M ↦ Iso.refl _) ?_
  intro X Y f
  ext U x
  rfl

def derivedId (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    reductionDerivedRestrict T (𝟙 A) ≅ 𝟭 (reductionDerivedCategory T A) :=
  exactDerivedRestrictionUnit (reductionRestrict T (𝟙 A))
    (NatIso.ofComponents (fun M ↦ Iso.refl _) (by intro X Y f; ext U x; rfl))
```

Private proved helpers implement the roof induction, all composite transitions,
localization comparisons, and interchange of the sequence and complex indices.
The transition recursion uses `Nat.leRec` rather than repeatedly comparing whole
complex objects. Local irreducibility controls standard derived-category and exact
functor constructions; local reducibility of `reductionRestrict` and the three
`reduction*HasDerivedCategory` instances aligns the localization structures.
Local instance priorities and private evaluation exactness instances prevent
unnecessary inference through the full sheaf construction. These elaboration
commands affect only this module. There is no change to any other public definition
body or any existing declaration signature, and no target changes meaning.

## Users

`tools/downstream.py Sheaf.Paper.SequentialVaryingRingRealization --uses restrictionComp`
and the corresponding query for `derivedId` report zero downstream modules; the item
is their only textual user. The DAG's unfinished parents still require the realization
node, which is preserved. No consumer adaptation is necessary.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SequentialVaryingRingRealization | M3 | Identity-component restriction comparisons and complete realization proof; existing statements unchanged. |

## Status

landed 20261023T231831-L-3649480 2026-10-23 (merge of deliver/M3/Sheaf.Paper.SequentialVaryingRingRealization)
