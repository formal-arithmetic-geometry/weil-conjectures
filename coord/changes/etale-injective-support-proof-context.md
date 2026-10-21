# AlgebraicGeometry.Etale.etale_injective_support_sequence proof context

## Reason

Server preflight classifies added or moved `section`, `variable`, `open` and local
`attribute` commands as a potential interface change and requests this record.
The delivery adds proved private helpers for derived-adjunction comparison algebra.
Their generic abelian-category variables are enclosed in an anonymous section, which
ends before the existing scheme variables. The extra irreducibility attributes are
local elaboration controls: they prevent expansion of chosen derived adjoints when
checking the specialized comparison maps. The complete file compiles in 46.4 seconds.

There is no statement or definition repair. All seven original public definition
bodies, all three theorem signatures and all public imports remain verbatim.
No private helper occurs in a public signature or public definition body. The new
private helpers occur only in theorem proofs. The assigned DAG node keeps its
statement and attachment and records the shorter proof route separately.

## Old

Original ordering of the common proof context, verbatim:

```lean
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Adjunction.mapHomologicalComplex
  _root_.DerivedCategory.Q _root_.DerivedCategory.Qh

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar lowerStar closedUpperShriek
  lowerStarClosedUpperShriekAdjunction upperStarLowerStarAdjunction
```

There was no anonymous section for the generic private comparison lemmas.
The existing scheme variable block and every public declaration are unchanged.

## New

The `open` commands move before the private helpers, verbatim:

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Functor
```

The private helpers are enclosed in `section` / `end`. Their two variable blocks,
verbatim (the first precedes the elementary comparison-isomorphism lemmas; the
second precedes the derived-adjunction lemmas):

```lean
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
```

```lean
variable [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions D]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)
```

After the section ends, the local attribute commands are, verbatim:

```lean
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Adjunction.mapHomologicalComplex
  _root_.DerivedCategory.Q _root_.DerivedCategory.Qh
  CategoryTheory.Functor.rightAdjoint CategoryTheory.Adjunction.ofIsLeftAdjoint
  CategoryTheory.Functor.rightDerivedFunctorObjQIso
  CategoryTheory.Functor.rightDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors
```

```lean
namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar lowerStar closedUpperShriek
  lowerStarClosedUpperShriekAdjunction upperStarLowerStarAdjunction
  derivedLowerStarClosedUpperShriekAdjunction mapDerivedUpperStarLowerStarAdjunction
```

These attributes have local scope. No notation, exported attribute, instance or
public declaration is added or changed. The public statements and definition bodies
are identical to the old versions.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.EtaleInjectiveSupportSequence --uses
etale_injective_support_sequence etaleSupportSequence_zero
etaleSupportSequence_boundary_naturality` reports zero downstream modules. Its only
textual uses are in the assigned module itself. The module remains necessary for
its unfinished DAG parents; it is not withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleInjectiveSupportSequence | Q4 | Three proofs filled; private proved helpers and local proof-context controls; public interface unchanged. |

No consumer needs adaptation and no other group's module is edited. The original
public imports are retained, so importers receive exactly the existing interface.

## Status

landed 20261021T111451-L-157262 2026-10-21 (merge of deliver/Q4/Sheaf.AlgebraicGeometry.EtaleInjectiveSupportSequence)
