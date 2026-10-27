# sfGraphWordProjection and sfCompactProjection

## Reason

Concrete graph-record reconstruction made the compiler repeatedly compare large
coefficient/derived-category structures. The original public definition is now the
`ModuleCat A` specialization of `sfGraphProjectionWord`. Its three graph morphisms and
coefficient category are parameters. The generic construction and its naturality API
therefore use the same structures before specializing. The complete generic prefix
calculation compiled in 9.9 seconds, its coefficient specialization in 9.5 seconds.
This repairs the construction rather than splitting a slow proof to evade a limit.

The new construction has precisely the original mathematical components: proper
projection for p, Rp of the inverse open projection for e, Rp De of the proper projection
for a, and Rp De Ra of M tensor the original composite pullback comparison. In the last
factor the original functor associator contributes the identity. The component of
whiskering the inverse compositor for (a,e) is its component at Lp K. Thus the original
`c.hom.app K` is exactly the inverse compositor for (a,e) at Lp K followed by the inverse
compositor for (a e,p) at K, as written by the generic construction. This identity uses
only `Iso.trans_hom`, `NatTrans.comp_app`, functor-associator and whiskering components,
and identity composition; it was also checked in a private expansion diagnostic.
No projection is inverted, and no existence witness is selected.

Scope removal of `CategoryTheory.catToReflQuiver` separately to the two projection
definitions, following existing projection repairs. These quivers are definitionally
equal copies of the same category structure. Existing public signatures, visibility,
declaration order and other bodies stay verbatim. Add the public import
`Sheaf.AlgebraicGeometry.SfGraphProjectionWord` because the public word definition uses
its generic constructor. The new module's tower/associativity imports are proof imports.

## Old

```lean
def sfGraphWordProjection
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (t : EtaleGraphPresentation f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj ((t.functor A).obj M)).obj K ⟶
      (t.functor A).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)) := by
  let B := ModuleCat.{u + 1} A
  let R := (lowerStar B t.p).rightDerivedFunctor
  let J := (openImmersionLowerShriek B t.e).mapDerivedCategory
  let S := (lowerStar B t.a).rightDerivedFunctor
  let Lp := (upperStar B t.p).leftDerivedFunctor
  let Le := (upperStar B t.e).leftDerivedFunctor
  let La := (upperStar B t.a).leftDerivedFunctor
  let c : (Lp ⋙ Le) ⋙ La ≅ (upperStar B f).leftDerivedFunctor :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarComp B t.a t.e).symm ≪≫
      (leftDerivedUpperStarComp B (t.a ≫ t.e) t.p f
        ((Category.assoc t.a t.e t.p).trans t.fac).symm).symm
  exact ((rightDerivedLowerStarProjectionMap B t.p).app (J.obj (S.obj M))).app K ≫
    R.map (((derivedOpenImmersionLowerShriekProjectionIso B t.e).inv.app
      (S.obj M)).app (Lp.obj K)) ≫
    R.map (J.map (((rightDerivedLowerStarProjectionMap B t.a).app M).app
      (Le.obj (Lp.obj K)))) ≫
    R.map (J.map (S.map (((derivedTensor B X).obj M).map (c.hom.app K))))

/-- The compactification projection with its tensor endpoints displayed once.
Source: `LowerShriekProjection.lean`, projectionMapOfCompactification
(blueprint: def-sf-etale-graph-word-projection). -/
def sfCompactProjection
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M)).obj K ⟶
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)) :=
  ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K
```

## New

```lean
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Successive proper, open and proper projection, with the canonical composite
pullback comparison. Source: Stacks Tags 0B56, 0GL1 and 0F7B;
node lem-sf-etale-compact-projection-coherence, steps 4--5
(blueprint: def-sf-etale-graph-word-projection). -/
def sfGraphWordProjection
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (t : EtaleGraphPresentation f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj ((t.functor A).obj M)).obj K ⟶
      (t.functor A).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)) := by
  exact sfGraphProjectionWord (ModuleCat.{u + 1} A) t.a t.e t.p f t.fac M K

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The compactification projection with its tensor endpoints displayed once.
Source: `LowerShriekProjection.lean`, projectionMapOfCompactification
(blueprint: def-sf-etale-graph-word-projection). -/
def sfCompactProjection
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M)).obj K ⟶
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)) :=
  ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K
```

## Users

Inventory: `tools/downstream.py Sheaf.AlgebraicGeometry.SfGraphProjectionData --uses
sfGraphWordProjection sfCompactProjection`, checked against whole-word source search.
No dependent theorem becomes weaker or stronger. The original canonical components
remain the data, including for identity or empty opens, zero coefficients and unbounded
complexes. No target text changes. This definition repair reopens semantic review for
every dependent target: the reader should check the componentwise equality above and
the unchanged interpretation of those target statements.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SfGraphProjectionData | unclaimed | Scoped instances; specialize the same explicit generic construction. |
| Sheaf.AlgebraicGeometry.SfGraphCompositionTailProjection | D9 | Assigned proof; signature unchanged. |
| Sheaf.AlgebraicGeometry.SfGraphWordProjectionSquare | unclaimed | Projection wrappers; no adaptation. |
| Sheaf.AlgebraicGeometry.SfGraphFirstProjectionSquare | C4 | Projection wrappers; no adaptation. |
| Sheaf.AlgebraicGeometry.SfGraphMiddleProjectionSquare | D2 | Graph-word projection; no adaptation. |
| Sheaf.AlgebraicGeometry.SfGraphSecondProjectionSquare | D3 | Graph-word projection; no adaptation. |
| Sheaf.AlgebraicGeometry.SfGraphCompactSupportCompositionProjection | unclaimed | Compact projection; no adaptation. |
| Sheaf.AlgebraicGeometry.SfEtaleCompactProjectionForward | unclaimed | Projection wrappers; no adaptation. |
| Sheaf.AlgebraicGeometry.SfEtaleCompactProjectionCoherence | unclaimed | Compact projection; no adaptation. |
| Sheaf.AlgebraicGeometry.SfGraphInterchangeProjection | D9, new | New Cartesian interchange square. |
| Sheaf.AlgebraicGeometry.SfGraphProjectionWord | D9, new | Generic construction and proved proper-prefix factorization. |

The final four-module packet and all seven existing explicit consumers compiled cleanly
in import order, each within 50.8 seconds. The consumers remained byte-for-byte identical
to the current shared source. Timings are recorded in `report.md`. No consumer adaptation
is included.

## Status

landed 20261026T065448-L-2996235 2026-10-26 (merge of deliver/D9/Sheaf.AlgebraicGeometry.SfGraphCompositionTailProjection)
