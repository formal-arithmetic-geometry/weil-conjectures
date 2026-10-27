# WeilConjectures.PodHomChain transport presentation

## Reason

The planned child theorem `uncurried_transport` publicly imported its parent
`PodHomChainCounitFormula` only to access projection, internal Hom, and the source
functor value. This prevents the parent from using its stated child. The existing
`PodCtfPairingMaps` module already provides definitionally equal projection and
internal Hom constructions without importing the parent. Use those constructions
and spell out the ordinary direct image value in the child. No mathematical data,
object, morphism, binder, or hypothesis changes. The child is unclaimed (no current
claim file). This is an adaptation of an unclaimed Sheaf module, not an adaptation
of a held module or an adopted source-library module.

Repair of returned head `3b6ae8c077c`: start from the current child including
A7's proof in `245f936e9c4`. Keep all private helper proofs and the public
transport proof. Qualify their existing raw projection, projection isomorphism,
and projection references with `PodCtfPairing`, matching the shared definitions.
The helpers and public theorem remain fully proved; no hole is reintroduced.

## Old

```lean
public import Sheaf.Paper.PodHomChainCounitFormula
abbrev internalHomObject := (homX six s f c R M).obj (R.exceptional.obj N)
abbrev directHomObject := (sourceFunctor six s f c R M).obj N
variable (a : (tensorX six s f c R).obj M ⊣ homX six s f c R M)
```

`p` and the last two conjuncts of `uncurried_transport` use
`WeilConjectures.PodHomChain.projection six s f c R`.

The old affected definition and theorem signature, verbatim:

```lean
def p :
    ((tensorY six s f c R).obj (R.support.obj M)).obj
      (directHomObject six s f c R M N) ⟶ N :=
  projection six s f c R M (directHomObject six s f c R M N) ≫
    R.support.map (q six s f c R M N a) ≫ R.exceptionalAdjunction.counit.app N

theorem uncurried_transport
    (T : (PodCoefficientStage.domain six s Y).FullSubcategory)
    (t : T ⟶ directHomObject six s f c R M N) :
    (R.ordinaryAdjunction.homEquiv T
        (internalHomObject six s f c R M N)).symm t =
      R.pull.map t ≫
        R.ordinaryAdjunction.counit.app (internalHomObject six s f c R M N) ∧
    (a.homEquiv (R.pull.obj T)
        (R.exceptional.obj N)).symm
        ((R.ordinaryAdjunction.homEquiv T
          (internalHomObject six s f c R M N)).symm t) =
      ((tensorX six s f c R).obj M).map
        ((R.ordinaryAdjunction.homEquiv T
          (internalHomObject six s f c R M N)).symm t) ≫
        a.counit.app (R.exceptional.obj N) ∧
    (a.homEquiv (R.pull.obj T)
        (R.exceptional.obj N)).symm
        ((R.ordinaryAdjunction.homEquiv T
          (internalHomObject six s f c R M N)).symm t) =
      ((tensorX six s f c R).obj M).map (R.pull.map t) ≫
        q six s f c R M N a ∧
    (R.exceptionalAdjunction.homEquiv
        (((tensorX six s f c R).obj M).obj (R.pull.obj T)) N).symm
        ((a.homEquiv (R.pull.obj T)
          (R.exceptional.obj N)).symm
          ((R.ordinaryAdjunction.homEquiv T
            (internalHomObject six s f c R M N)).symm t)) =
      R.support.map
        ((a.homEquiv (R.pull.obj T)
          (R.exceptional.obj N)).symm
          ((R.ordinaryAdjunction.homEquiv T
            (internalHomObject six s f c R M N)).symm t)) ≫
        R.exceptionalAdjunction.counit.app N ∧
    projection six s f c R M T ≫
        (R.exceptionalAdjunction.homEquiv
          (((tensorX six s f c R).obj M).obj (R.pull.obj T)) N).symm
          ((a.homEquiv (R.pull.obj T)
            (R.exceptional.obj N)).symm
            ((R.ordinaryAdjunction.homEquiv T
              (internalHomObject six s f c R M N)).symm t)) =
      ((tensorY six s f c R).obj (R.support.obj M)).map t ≫
        p six s f c R M N a ∧
    projection six s f c R M T ≫
        R.support.map
          (((tensorX six s f c R).obj M).map (R.pull.map t)) =
      ((tensorY six s f c R).obj (R.support.obj M)).map t ≫
        projection six s f c R M (directHomObject six s f c R M N) := by
```

## New

```lean
public import Sheaf.Paper.PodCtfPairingMaps
abbrev internalHomObject := (PodCtfPairing.homX six s f c R M).obj (R.exceptional.obj N)
abbrev directHomObject := R.direct.obj (internalHomObject six s f c R M N)
variable (a : (tensorX six s f c R).obj M ⊣ PodCtfPairing.homX six s f c R M)
```

The same occurrences of projection use `WeilConjectures.PodCtfPairing.projection`.
Both projection definitions have identical constructed bodies (including the
same raw components, isomorphism evidence, and full-inclusion preimage); both
internal Hom definitions have identical bodies. `directHomObject` unfolds to the
same value of the composed functor. Thus all signatures and public definitions
retain their elaborated meanings by definitional equality. No target statement
or target definition is edited. Targets using this presentation retain exactly
their meanings; this record makes that fact available for independent review.

The corresponding new definition and theorem signature, verbatim:

```lean
def p :
    ((tensorY six s f c R).obj (R.support.obj M)).obj
      (directHomObject six s f c R M N) ⟶ N :=
  PodCtfPairing.projection six s f c R M (directHomObject six s f c R M N) ≫
    R.support.map (q six s f c R M N a) ≫ R.exceptionalAdjunction.counit.app N

theorem uncurried_transport
    (T : (PodCoefficientStage.domain six s Y).FullSubcategory)
    (t : T ⟶ directHomObject six s f c R M N) :
    (R.ordinaryAdjunction.homEquiv T
        (internalHomObject six s f c R M N)).symm t =
      R.pull.map t ≫
        R.ordinaryAdjunction.counit.app (internalHomObject six s f c R M N) ∧
    (a.homEquiv (R.pull.obj T)
        (R.exceptional.obj N)).symm
        ((R.ordinaryAdjunction.homEquiv T
          (internalHomObject six s f c R M N)).symm t) =
      ((tensorX six s f c R).obj M).map
        ((R.ordinaryAdjunction.homEquiv T
          (internalHomObject six s f c R M N)).symm t) ≫
        a.counit.app (R.exceptional.obj N) ∧
    (a.homEquiv (R.pull.obj T)
        (R.exceptional.obj N)).symm
        ((R.ordinaryAdjunction.homEquiv T
          (internalHomObject six s f c R M N)).symm t) =
      ((tensorX six s f c R).obj M).map (R.pull.map t) ≫
        q six s f c R M N a ∧
    (R.exceptionalAdjunction.homEquiv
        (((tensorX six s f c R).obj M).obj (R.pull.obj T)) N).symm
        ((a.homEquiv (R.pull.obj T)
          (R.exceptional.obj N)).symm
          ((R.ordinaryAdjunction.homEquiv T
            (internalHomObject six s f c R M N)).symm t)) =
      R.support.map
        ((a.homEquiv (R.pull.obj T)
          (R.exceptional.obj N)).symm
          ((R.ordinaryAdjunction.homEquiv T
            (internalHomObject six s f c R M N)).symm t)) ≫
        R.exceptionalAdjunction.counit.app N ∧
    PodCtfPairing.projection six s f c R M T ≫
        (R.exceptionalAdjunction.homEquiv
          (((tensorX six s f c R).obj M).obj (R.pull.obj T)) N).symm
          ((a.homEquiv (R.pull.obj T)
            (R.exceptional.obj N)).symm
            ((R.ordinaryAdjunction.homEquiv T
              (internalHomObject six s f c R M N)).symm t)) =
      ((tensorY six s f c R).obj (R.support.obj M)).map t ≫
        p six s f c R M N a ∧
    PodCtfPairing.projection six s f c R M T ≫
        R.support.map
          (((tensorX six s f c R).obj M).map (R.pull.map t)) =
      ((tensorY six s f c R).obj (R.support.obj M)).map t ≫
        PodCtfPairing.projection six s f c R M (directHomObject six s f c R M N) := by
```

## Users

`python3 tools/downstream.py Sheaf.Paper.PodHomChainUncurriedTransport` reported
zero downstream modules in the current repository. A direct source import search
also found none. The newly proved parent is the only added consumer. No other
consumer adaptation is necessary.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Replace upward public import and use definitionally equal existing constructions. |
| Sheaf.Paper.PodHomChainCounitFormula | H1 | Import the child for the assigned proof; all existing declarations retain their signatures and bodies except the theorem proof. |

## Status

landed 20261025T202144-L-2681991 2026-10-25 (merge of deliver/H1/Sheaf.Paper.PodHomChainCounitFormula)
