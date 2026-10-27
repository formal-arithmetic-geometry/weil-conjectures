## What changed

Kept the original signatures and the body of `compactSupportNativeOpenEvaluation` unchanged.
Replaced the proof hole in `compactSupportNativeOpenTransition` by exact localization of
an ordinary-module horizontal square. The private categorical proofs compare the two
exact-derived adjunction units, identify localization of inverse mates, and show that
postcomposing an ordinary square by `compactSupportOpenModel` gives the prescribed native
derived evaluation. The horizontal square is localized by cancellation of the exact
localization factors and natural-transformation extensionality; its horizontal maps
are the actual `compactSupportCoefficientTransition`, via their factorization equations.

Added `Sheaf.Paper.CompactSupportOrdinaryOpenTransition`. It constructs the ordinary
open-evaluation isomorphism from the native inverse mate, proves the mate invertible,
and states its horizontal compatibility before complexes or localization. The item uses
private proof imports of the varying-ring and exact-square implementations and of the
coefficient-transition factorization. The generic localization calculation is kept
private in the item, avoiding an import of the larger system-pushforward theorem.
Private local evaluation and open-extension instances supply the already proved properties
with the abelian structures inferred in the mixed native/coefficient presentation. No shared
instance registration or definition is changed. The standard derived-category construction
and the two localization-isomorphism constructions are protected from unfolding locally
during the final comparison. The specialization fixes the six coefficient-site categories
and their abelian and derived-category structures explicitly.

Validation: the new ordinary module compiled through `lcompile.py` in 39.1 seconds;
the final item compiled in 39.2 seconds without warnings. No diagnostic or profiling
options remain. The original definition and theorem signature were compared with the
current shared source and are textually unchanged. Only `proof`, `proof_deps`, and
`proof_origin` changed in the assigned node.

## Proved and sorry left

One original hole removed: `WeilConjectures.compactSupportNativeOpenTransition`
(node `lem-weil-compact-support-native-open-transition`). Its proof is complete from
the named ordinary-module step.

One hole added and left: `WeilConjectures.compactSupportOrdinaryOpenTransition`
(node `lem-weil-compact-support-ordinary-open-transition`). Its proof is exactly
`by sorry` in its own module. This is a decomposition, not a completed proof:
one hole closed, one added, net zero. It isolates original proof steps 1 and 2;
the exact-derived normalization and localization in step 3 are proved here.

Also proved `WeilConjectures.compactSupportOrdinaryOpenMate_isIso`. The ordinary
evaluation definition uses this proved proposition, not an arbitrary existence witness.
There are no other holes in the delivery and no holes inside definitions.

## No longer needed

No original public import was removed, and no existing module or declaration is withdrawn.
The item no longer directly needs `lem-sf-open-extension-scalar-restriction-coherence`
or `lem-sf-compact-support-restriction-of-scalars` as proof dependencies: the new ordinary
node retains these for its geometric normalization step. They are not globally pruned.
All other original proof dependencies remain used. No unit statement or unit step is bypassed;
the assigned unit has empty `realized.statement` and `realized.steps` records.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The listed declarations provide the operations and their
normalizations, but do not directly state the ordinary horizontal open square. That step
is now an explicit ordinary-module obligation. The native `evalJ` is defined by a derived
mate, rather than literally as localization of an ordinary open-evaluation isomorphism;
identifying those maps requires the unit-normalization proof supplied in this delivery.
The generic exact-square composition theorem addresses invertible comparison squares;
the extra calculation here handles the noninvertible horizontal coefficient maps.

The remaining statement was checked against the identity horizontal arrow, the zero system,
and the empty open: the two composites have the same type and their section-generator
interpretations agree. Its proof uses no flatness or cartesian-system hypothesis.

## New nodes

`lem-weil-compact-support-ordinary-open-transition` states original proof steps 1 and 2
on ordinary coefficient sequence-site modules. It has the specified native inverse-mate
normalization and the original `sfOpenRestriction`. It is strictly simpler than the item:
there are no complexes, derived functors, localization factors, or derived adjunctions.
The complete combination from this step to the assigned theorem is Lean code in the item.
Searches used LeanSearch, LeanFinder, Loogle, Mathlib grep, and the project and blueprint
indices; no ordinary native horizontal theorem was found. Source: Stacks 03DI,
`lemma-extension-by-zero`, its direct-sum generators and adjunction, with 03DA and 0941.
No existing interface changes or change records are needed.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
