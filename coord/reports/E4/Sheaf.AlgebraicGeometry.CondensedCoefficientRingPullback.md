## What changed

Proved `AlgebraicGeometry.ProEtale.IntegralModelsStacks.condensedSmallRingMap_pullback_isIso`
without changing its statement or `condensedSmallRingMap`. Added the proof-only import
`Sheaf.Paper.CartesianCoefficientTwists` to use the already proved
`AlgebraicGeometry.ProEtale.spCoefficientIso_existsUnique`, which supplies exactly the
ring inverse-image isomorphism on the original pro-etale sites and its sectionwise
adjunct normalization. Three private helpers transport that adjunction to the coefficient-sized
AsSmall models; a proved local instance fixes the existing sheafification theorem
at the required coefficient universe. Mathlib's uniqueness of left adjoints compares it
with the constructed model adjunction. Its unit equation and
`coefficientMap_existsUnique` show that the transported isomorphism has precisely
`condensedSmallRingMap` as adjunct.

Updated the item's DAG proof, proof dependencies and proof origin to record this
reuse. No other existing module or node is changed. No public interface is changed.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.condensedSmallRingMap_pullback_isIso`
(node `lem-sfb-condensed-coefficient-ring-pullback`). Zero holes remain in the item;
zero holes were added or split off. All new private helpers are proved or explicit constructions. The final single-file compile passed in 16.1 seconds with no warnings in the
item. The required delivery command also runs its declaration-axiom probe.

## No longer needed

No existing import was removed and no module is withdrawn. The item's proof no longer
needs a separate construction from `lem-weil-pbc-sheaf-pullback-forget-comparison`,
`lem-sfb-alpha-iso`, or `def-sfb-eta`: the existing proved
`spCoefficientIso_existsUnique` already carries out that argument and supplies its
required normalization. These three dependencies were removed from this node's
direct proof dependencies; they remain needed transitively by the reused theorem.
No claim of global pruning is made. The integral-models unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The DAG's proposed argument was mathematically sound but repeated a theorem already
proved in `Sheaf.Paper.CartesianCoefficientTwists`. The remaining AsSmall adjunction
transport can be completed using Mathlib without another split. Checked that this
import does not reach the item, and that the reused node's dependency closure does
not contain the item node. Read Stacks Sites 00YV and Modules on Sites 03D2 locally,
the unit record and its current blueprint text, and the relevant existing Lean
proof and normalization. The proof has no nonemptiness, nonzero coefficient, slice,
constant-coordinate or finiteness hypothesis; in particular it applies to empty
schemes and the zero ring. The strict equivalences and unit equations do not need
any such assumptions. Searches used LeanFinder for inverse image and forgetful
functors, Loogle for `Adjunction.leftAdjointUniq`, and grep for its unit theorem and
`restrictFullyFaithful_homEquiv_apply`.

Delivery validation: the required `deliver3.py E4
Sheaf.AlgebraicGeometry.CondensedCoefficientRingPullback` command exited 1 without
pushing. Its item compile succeeded in 12.3 seconds and printed `SHEAF-PROBED 2`.
The refusal was `COMPILES WITH WARNINGS (local), nothing pushed`; all three actual
warning locations were in an unpublished dependency,
`Sheaf.AlgebraicGeometry.SfP1ChartExchange`, lines 565--566, for unused simp arguments
`ordinaryFinitePullback`, `ordinaryFiniteLine`, and `ordinaryFiniteDegreeZero`.
No warning location was in this item. An additional long-line linter hint came from
the appended probe. The tool treats warnings in its dependency-overlay build as
warnings in the delivered file. The launcher tool was not modified and this
unrelated dependency was not changed. The complete zero-hole proof, node update,
and report remain ready in the sandbox for delivery once this gate is repaired.

Resumed-session validation on 2026-10-27: ran the required delivery check first
against the current shared sources. It again exited 1 with `COMPILES WITH WARNINGS
(local), nothing pushed`, after a successful 12.3-second item compile and
`SHEAF-PROBED 2`. The same three dependency warnings at
`SfP1ChartExchange.lean:565--566` remain the cause. Checked the import graph:
neither existing public import of this item reaches that module, while the
existing theorem `spCoefficientIso_existsUnique` is declared in
`Sheaf.Paper.CartesianCoefficientTwists`, whose transitive imports do reach it.
No narrower existing declaration of that theorem was found. The proved Lean
file and node update are retained unchanged; no launcher tool, unrelated module,
or warning setting was changed, and no delivery was pushed.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
