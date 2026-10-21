## What changed

Restored `Sheaf.Algebra.Homology.AffineTildeDerivedTensorHomologyCoordinates`
as a compatibility module publicly importing the complete adopted
`WeilConjectures.Algebra.Homology.AffineTildeDerivedTensorHomologyCoordinates`.
The archived and adopted `affineTildeDerivedTensorToPushforward_homology`
signatures are byte-identical. Reuse the existing proof rather than redeclaring
its theorem and generic private helpers.

Updated the existing node's Lean attachment to the adopted owner and documented
this in its proof origin. Retained every existing statement dependency, proof
dependency and proof step; the unit route is unchanged. The quarantine archive
and all source-library files are untouched.

Adapted only the representative imports of the direct consumer
`Sheaf.Algebra.Homology.AffineBaseChangeTildeMateIdentityFactorization`,
retaining its original theorem statement and proof.

Change record:
`coord/changes/affine-tilde-homology-coordinates-adopted-interface.md`.

## Proved and sorry left

This is a listed quarantine repair with zero initial holes: closed 0, added 0,
left 0. No new statements or definitions are introduced.

`AlgebraicGeometry.affineTildeDerivedTensorToPushforward_homology` is supplied
by the complete adopted proof. Its supporting factorization and coefficient
coordinate theorems also already have complete source proofs. No proof is
split off. The restored wrapper compiled in 5.1 s. A fresh import probe
restated the complete archived theorem signature verbatim and applied the adopted
theorem, compiling in 8.4 s. Both the adopted theorem and that probe report only
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` is reachable.
The scratch probe is not part of the delivery.

## No longer needed

The restored interface needs no local copy of the archived theorem or its
private exact-homology/naturality helpers. It replaces the old public import
`Sheaf.Algebra.Homology.AffineTildeDerivedTensorMate` and the proof-only imports
`Sheaf.Algebra.Homology.AffineTildePushforwardHomologyFactorization` and
`Sheaf.Algebra.Homology.AffineTildeCoefficientPushforwardHomologyCoordinates`
with one public import of the adopted implementation. Their mathematical
counterparts remain used by the adopted proof; all corresponding DAG edges
are retained. No mathematical node or module is withdrawn or claimed pruned.
The consumer's old representative import is also replaced by its adopted source
counterpart, with the normalization compatibility import retained for its legacy
abbreviation. No new residual homology-coordinate item is needed.

## Where the brief, the DAG or earlier work was wrong

The route note predates adoption of the full reviewed calculation into
`WeilConjectures`. The current archive already contains zero sorries and the
current source library owns its exact declaration. Recovery therefore requires
a compatibility interface and corrected attachment, not a new calculation or
another open leaf. The current statement is sound; no hypothesis, universe,
conclusion or definition is changed.

The three required searches were run: LeanFinder returned general sheaf unit
and counit infrastructure; Loogle did not know the queried project-specific
exact-derived comparison name; grep located short-complex naturality and
natural-transformation homology APIs. Direct library search found the exact
complete theorem, which is the shortest available route.

## Forced adaptations

`Sheaf.Algebra.Homology.AffineBaseChangeTildeMateIdentityFactorization`
was unclaimed at adaptation. Compiling the original module against the restored
interface fails at its imports:

```text
import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeRepresentative failed,
environment already contains 'AlgebraicGeometry.affineBaseChangeTildeComplexIso._proof_18'
from Sheaf.Algebra.Homology.AffineBaseChangeTildeRepresentative
```

Replaced its public import of the Sheaf representative with the adopted source
representative and an explicit public import of the Sheaf pushforward
normalization compatibility module. This retains the `affineTildeFunctor`
abbreviation in the unchanged theorem signature and avoids loading the duplicate
representative definitions. The adapted consumer compiled in 34.1 s, and again
in 21.5 s when compiled together with a fresh consumer probe. That probe restates
the complete original consumer signature and applies its theorem; it compiled in
17.5 s. These two import lines are the only adapted lines.
No live module imports this parent according to `downstream.py`; DAG parents and
unit routes are preserved.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
