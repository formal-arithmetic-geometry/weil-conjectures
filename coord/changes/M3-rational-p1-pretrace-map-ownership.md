# AlgebraicGeometry.ProEtale.RationalP1 pretrace map ownership

## Reason

The two forward coherence statements must import the map definitions without importing
`second_pretrace`, whose proof imports those statements. Move the existing definitions,
with their signatures, attributes and bodies preserved, to the new module
`Sheaf.Paper.RationalP1SecondPretraceData`. Publicly reexport that module from the item.
The added maps are `secondExtractProjection` and the literal native exchange wrapper
`secondPretraceExchangeMap`. The former keeps q*K outside the second direct
image and has no inverse projection or exchange hypothesis.

No existing definition changes its mathematical meaning. No target statement changes.
The new file uses the same public imports, section visibility and noncomputability as
the old definitions. No source-library module is changed.

## Old

The item directly imported:

```lean
public import Sheaf.Paper.RationalP1SecondPullComparison
public import Sheaf.Paper.RationalP1AmbientTail
```

It directly declared `firstLineComparisonForTrace`, `secondTraceExchange`,
`secondTracePullMonoidal`, `secondTraceBraided`, `secondTraceUnitIso`,
`secondTraceTensorIso`, `secondTraceSwap`, `secondTraceStrength`,
`counitProjectionPart`, and `SecondPretraceEquation`. Their full signatures and bodies
are unchanged in the new data module; this is only a change of declaration ownership.
There was no declaration named `secondExtractProjection` or `secondPretraceExchangeMap`.

## New

The item imports the unchanged maps through:

```lean
public import Sheaf.Paper.RationalP1SecondPretraceData
```

The data module has the two old public imports verbatim and the added signature:

```lean
def secondExtractProjection
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    (moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K ⊗
      (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).obj
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y))
          0).obj (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧) ⟶
    (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).obj
      ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj
        ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
          ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
            K)))
```

The body is the forward p2 projection followed under Rp2* by the self-square
pullback comparison on K, tensorShiftIso.hom, and the inverse first pullTwistIso.
It uses no existence witness and contains no proof hole.

The other added signature is:

```lean
def secondPretraceExchangeMap (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
      ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M) ⟶
    (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)
```

Here Λ and Y are the existing section parameters. Its body unfolds only the two
functor aliases and uses `(condensedAmbientExchange Λ (square Y)).app M`.

The proved API lemmas `secondPretraceExchangeMap_isIso` and
`secondPretraceExchangeMap_inverse` transfer native invertibility to this wrapper
and identify its inverse with `ambientExchangeInverse`. They add no instance or
simp attribute; both proofs unfold the definitions and introduce no proof holes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.RationalP1SecondPretrace` | M3 | Same public signature and maps; proof imports the two forward lemmas. |
| `Sheaf.Paper.RationalP1ScalarChernMaps` | unclaimed | Same public reexports; no adaptation. |
| `Sheaf.Paper.RationalP1SecondScalarTrace` | unclaimed | Same public reexports; no adaptation. |
| `Sheaf.Paper.RationalP1SecondTraceReordering` | unclaimed | Uses unchanged reexported strengths and scalar exchange; no adaptation. |
| `Sheaf.Paper.RationalP1ScalarChernBaseChange` | unclaimed | Uses unchanged reexported line and exchange maps; no adaptation. |
| `Sheaf.Paper.RationalP1SecondExchangeProjection` | new in M3 | Uses the added untwisted forward projection. |
| `Sheaf.Paper.RationalP1SecondProjectionInterchange` | new in M3 | Uses that projection in the two-factor law. |

## Status

landed 20261027T210135-L-1662446 2026-10-27 (merge of deliver/M3/Sheaf.Paper.RationalP1SecondPretrace)
