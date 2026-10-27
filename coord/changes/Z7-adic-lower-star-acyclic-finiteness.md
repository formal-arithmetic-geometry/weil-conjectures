# Adic finiteness proof imports below LowerStar

## Reason

Restore the proof archived in
`coord/preferred-upstream/WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar.lean`
without recreating the import cycle described by its accompanying note.
The dense-open and projective-space input modules currently contain only their
original theorem statements with `sorry`. Their private proof imports are unused
by these statements and bodies. Those imports nevertheless reach
`ProEtale.ScalarExtension`, then `PointPerfect`, `Adic.DerivedForget`, and
`Adic.LowerStar` after the upstream sync.

Remove these unused private imports from the two existing Sheaf modules. All
public imports, declarations, signatures, docstrings, attributes, and existing
proof bodies in those modules are preserved verbatim. Their mathematical proof
dependencies remain in the DAG for their future proofs. No lemma is duplicated,
moved, weakened, or withdrawn. The source module changes only by private proof
imports and filling its existing theorem proof.

## Old

`Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness` had these private imports:

```lean
import Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients
import Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.LisseEConstructibleIntegralLattice
import Sheaf.Paper.SfIntegralDirectImageConstructible
```

`Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness` had these private imports:

```lean
import Sheaf.AlgebraicGeometry.ProperBoundedConstructible
import Sheaf.AlgebraicGeometry.ProperCaseConstructibility
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.LisseEConstructibleIntegralLattice
import Sheaf.Paper.SfIntegralDirectImageConstructible
```

`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine` had its
original statement and a `sorry` body in `Adic.LowerStar`.

## New

Both lists of private imports above are removed. The complete theorem statements
and their `:= by sorry` bodies are unchanged. All public imports are unchanged.

The affine finiteness theorem now has the archived compactification proof: embed
the affine source in projective space, factor through its scheme-theoretic image,
apply the dense-open and closed-immersion finiteness results, extend projective
finiteness from sheaves to bounded complexes by truncation, and transport along
the two derived-composition isomorphisms. Its five new imports are private.

## Users

`tools/downstream.py <module> --uses <declaration>` found zero downstream modules
for each of the two changed Sheaf modules. Each declaration occurred only in its
own file. The restored source proof is their new direct consumer. The two Sheaf
modules had no claim files in the shared repository when inspected.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | Remove unused private imports; unchanged theorem and hole. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | Remove unused private imports; unchanged theorem and hole. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | Z7 | Restore the compactification proof using the same input declarations. |

No public interface or definition changes, so existing consumers need no
adaptations and target statement review is not reopened. An overlay source-graph
check found zero cycles; none of the three finiteness inputs reaches LowerStar
after these import removals.

## Status

landed 20261024T191847-L-523435 2026-10-24 (merge of deliver/Z7/WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar)
