# WeilConjectures.PurStrictScalar.scalar_compactification_composition

## Reason

Record the private proof additions and scoped local irreducibility commands that
preflight conservatively classifies as a command-interface change. The original
public signatures, definitions, instances, attributes and public imports remain
unchanged. The local commands prevent expensive unfolding of derived scalar maps
while the existing kernel-checked structural congruence tactic transports the
three compositor inputs. No target meaning changes.

## Old

The original theorem has the following unchanged signature and a `by sorry` proof:

```lean
theorem scalar_compactification_composition {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} (c : Compactification.Triangle f g)
    [QuasiCompact c.cf.i] [QuasiCompact c.cg.i] [QuasiCompact c.q]
    (N : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X) :
    (T l E F i Z).map
        ((compositionD (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) c).app N) ≫
        (comparison l E F i c.cfg).app N =
      (comparison l E F i c.cg).app ((image l E c.cf).obj N) ≫
        (image l F c.cg).map ((comparison l E F i c.cf).app N) ≫
        (compositionD (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) c).app
          ((T l E F i X).obj N)
```

The existing local irreducibility commands remain as before. There is no local
section folding the composition maps, and neither new compositor proof import is
present.

## New

The signature above is verbatim, with a complete proof from the central gamma
square and the open and proper compositor compatibility equations. The added
private imports are `Sheaf.Paper.StrictScalarOpenComposition` and
`Sheaf.Paper.StrictScalarProperComposition`. The latter is proved from the new
`Sheaf.Paper.StrictScalarPullComposition` statement. The open and pullback equations
are the two named smaller holes, with separate nodes and complete proofs in words.

The following command is confined to a section containing only the new composition
proof, so it does not change imported reducibility or any later local proof:

```lean
attribute [local irreducible] compositionD gamma jComp rComp proper openTensor strictScalarPull
```

The added categorical pasting lemma and equality-transport helpers are private and
proved. The theorem scopes transparency checking to `true`; no new disabled
transparency option is introduced. The original alpha hole is untouched.

## Users

A source search in both library roots finds no current direct Lean importer of
`Sheaf.Paper.CompactSupportStrictScalarRefinement`. Its unfinished DAG parents
remain attached and no unit route is withdrawn. There is no existing downstream
interface adaptation or consumer copy in this delivery. The item itself compiled
with the three new dependencies in 35.3 seconds, without warnings or errors.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompactSupportStrictScalarRefinement | S4 | Same public interface; new private compositor proof inputs. |
| Sheaf.Paper.StrictScalarProperComposition | S4 | New proved consumer of StrictScalarPullComposition. |

The new public statements are generic spatial compositor compatibilities and do
not change any existing data definition, target statement or target hypothesis.

## Status

landed 20261026T201404-L-3378672 2026-10-26 (merge of deliver/S4/Sheaf.Paper.CompactSupportStrictScalarRefinement)
