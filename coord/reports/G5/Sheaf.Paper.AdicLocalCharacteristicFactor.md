## What changed

Replaced the proof of `WeilConjectures.sfLocalCharacteristicFactor_existsUnique`
in `Sheaf.Paper.AdicLocalCharacteristicFactor`. All existing declaration signatures,
definitions and public imports are unchanged. The proof obtains a finite Weil model
from the identity-immersion `complex_descent` clause, constructs a compatible residue
embedding using the finite residue-field criterion and `IsAlgClosed.lift`, and evaluates
the finite-stage factor there. For another presentation it composes the presentation
isomorphisms, uses local-operator conjugacy at degree zero, and proves equality of the
factors by scalar extension and conjugacy invariance of characteristic polynomials.
Evaluating the universal formula at the initial model proves uniqueness.

Added two proved private linear-algebra helpers: `mapped_charpolyRev` follows from
`LinearMap.charpoly_baseChange` and injective `Polynomial.reverse_map`;
`charpolyRev_iso` converts the categorical intertwining equation into linear
conjugacy and applies `LinearEquiv.charpoly_conj`. These arguments also cover the
zero module. Declared the independent module universe needed by the first helper.

Added the operator comparison module `Sheaf.Paper.AdicLocalFrobeniusModelConjugacy`
with one named public theorem in every integer degree. It compares actual local
operators over the coefficient closure, before taking a determinant and without a
heart hypothesis. Its source is the separate local Frobenius conjugacy lemma, together
with the degreewise finite-model operator comparison. Its proof in words and DAG node
record the common-stage descent and the small-field interface needed to apply those
arguments. This theorem is not yet proved in Lean.

Current server verification: the comparison module compiled cleanly in 5.2 seconds and
the assigned module compiled cleanly in 19.5 seconds. An earlier profiled recheck took
6.0 seconds. The profiling option
was removed afterwards. An earlier assigned-module run reached the 60-second gate;
the subsequent profile showed no expensive declaration, and the unchanged proof
then compiled. The first full preflight requested the private-universe change record and reported
an axiom-probe timeout; both delivered files themselves compiled. The requested record
is now included. No push has been attempted.

Further proof work verified scratch lemmas for descent of a common-stage isomorphism
to an actual finite-stage isomorphism, naturality of rational pullback composition,
naturality of all iterated Weil maps, one-step point transport, and iterated point
transport. The return-comparison identification is still under development. These
scratch declarations are not part of the delivered library and add no holes there.
The previous compile-server outages recovered; they are not the present obstacle.

The dispatcher reference clock reset on resumptions (observed start timestamps
1792426893.226085 and 1792437809.6703236). The dry-run outputs consequently reported
15 minutes and later 11 minutes despite the retained work. No budget metadata was
edited, and no unchanged packet was retried to wait out that policy.

## Proved and sorry left

Closed the original hole `WeilConjectures.sfLocalCharacteristicFactor_existsUnique`
(node `def-wf-iota-real`); no `sorry` remains in the assigned module.

Added one hole: `WeilConjectures.sfLocalFrobenius_model_conjugacy` in
`Sheaf.Paper.AdicLocalFrobeniusModelConjugacy`, node
`lem-wf-adic-local-frobenius-model-conjugacy`. Its proof is exactly `by sorry`.
This is a decomposition (one original hole closed, one separate operator-comparison
hole added), not a net proof of the local-factor construction from standard axioms.
The determinant algebra, existence of an evaluating presentation and residue embedding,
and the uniqueness argument are completely proved from the stated declarations.
No axiom or sorry inside a definition was introduced.

The new theorem has no polynomial conclusion, asserts conjugacy in all degrees, and
has no sheaf-heart hypothesis. It does not provide finite-model existence, residue
embedding existence, characteristic-polynomial scalar compatibility, or uniqueness;
those are separate parts actually combined in the assigned theorem's Lean proof.
It therefore does not restate that theorem under another name.

## No longer needed

No original import, node or module was removed. The original node had no numbered
proof or declared proof dependencies to prune. Its new proof dependencies record
exactly presentation descent, finite residue fields and operator comparison.
No assertion that the old-framework conjugacy statements can be discarded is made:
they remain the sources of the new comparison's argument.
The private scalar-characteristic-polynomial proof needs no extra public imports;
the existing public charpoly module already exposes the base-change theorem.

## Where the brief, the DAG or earlier work was wrong

The assigned definition node had an empty proof and no proof dependencies, despite
its Lean module containing the nontrivial descent theorem. The sandbox node now gives
the three actual proof steps.

`localFrobeniusConjugacyClass` and `localWeilModelTraceIndependence` use a bundled
coefficient datum in the scheme universe and the unshrunk finite field `E.val`.
The assigned module instead uses `AlgebraicallyClosedCoefficients.Coefficient`,
which is a canonical small field model, and an independently sized coefficient
closure. Moreover, the latter comparison starts with an actual finite-stage
isomorphism and extension-valued points, whereas the assigned theorem supplies an
isomorphism in the common-stage category and a closed point. Their signatures
therefore do not directly close the comparison goal. The new node explicitly
records these transport and descent steps, rather than pretending to apply an
inapplicable declaration. The upstream `WeilSheaf` stalk conjugacy results use the
older category and likewise do not supply this bridge.

The identity-immersion descent theorem is present in
`Sheaf.Paper.ImmersionWeilLocalBehavior`, although the corresponding node's primary
Lean record currently names `Sheaf.Paper.ZlImmersionWeilLocalBehavior`; the proof
uses the former module's actual compiled `complex_descent` clause. No existing
module or interface has been altered to address that bookkeeping discrepancy.

Edge cases checked mathematically: equal coefficient stages and embeddings permit
identity conjugacy; zero cohomology has its unique automorphism; arbitrary degrees
are allowed because the point complexes have finite-dimensional cohomology in each
degree; closed residue fields have positive finite degree, including rational points.
The definition and all target signatures remain unchanged.

## New nodes

`lem-wf-adic-local-frobenius-model-conjugacy` states the separate operator comparison
needed before taking local determinants. Its source and proof in words identify
finite-diagram descent, the degreewise finite-model comparison, the Frobenius orbit
conjugacy argument, and scalar/cohomology tensor towers. It includes the verbatim
Lean signature and the actual LeanSearch, LeanFinder and source-grep results.
Blueprint searches for conjugacy and representative independence found the existing
finite-stage lemmas described above, but no statement with the actual small-field
and common-stage interfaces. Change record: `coord/changes/G5-adic-local-characteristic-private-universe.md`.
Preflight requested it for the additional universe used only in a proved private helper.
Existing statements and definitions are unchanged, and no consumer adaptation was made.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
