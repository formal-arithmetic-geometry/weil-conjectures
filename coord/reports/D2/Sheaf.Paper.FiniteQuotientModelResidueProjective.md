## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Scheme.finiteQuotient_model_residueProjective` by a complete
Lean assembly proof. Its statement and public imports are unchanged.

The proof obtains total derived scalar extension from the already proved
`ModuleCat.exists_baseDerivedExtension_resolution`, constructs the double-quotient
ring equivalence and checks its quotient square. It pulls back the residue covering
sieve and chooses a nonempty member using `mem_smallEtaleTopology_iff`. Proved private
helpers implement exact further slice restriction, using the same exact-functor
argument as the parent `FinitePerfectQuotientModels` module; that parent cannot be
imported because it depends on this item. After comparing the two constant residue
models, the proof transports the chosen projective complex along the ring equivalence.
It proves the support bounds and projectivity termwise, and assembles the final
isomorphism using derived functor composition and localization comparisons.

Added two proof-only imports with strictly separate intermediate statements:
`Sheaf.Paper.FiniteQuotientModelResidueComparison` and
`Sheaf.Paper.FiniteConstantSliceIsoReflects`. Added their nodes and updated only the
proof route of the item's node. No existing shared definition, statement, instance,
attribute or public import was changed; no consumer adaptation is needed.

Validation: both new modules and the item compiled through `lcompile.py`.
The item compiled without warnings in 14.6 seconds, below the 60-second limit.
The quotient equivalence and support transport require neither a nonzero ring nor
`a ≤ b`. The comparison statement permits empty charts; constant-value recovery
explicitly requires a nonempty chart. The unit's realized statements and steps are
unchanged, and the proof follows the original residue-identification route.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.finiteQuotient_model_residueProjective`
(`lem-weil-pbc-finite-quotient-model-residue-projective`): 1 of 1 original holes.
The item's module has zero remaining `sorry` occurrences.

Added exactly two named theorem holes:

- `AlgebraicGeometry.Scheme.finiteQuotient_model_residueComparison`, node
  `lem-weil-pbc-finite-quotient-model-residue-comparison`.
- `AlgebraicGeometry.Scheme.finiteConstantSlice_iso_reflects`, node
  `lem-weil-pbc-finite-constant-slice-iso-reflects`.

This is a decomposition, not a completed axiom-free proof of the residue theorem.
Both new holes have exactly `:= by sorry`, with their source and full proof in words
in the declaration docstring. No definition or private helper contains a hole.
The first new statement has no local projective-model hypothesis, support interval,
nonemptiness hypothesis or bounded-projective conclusion. The second has no adic
system or residue operation and concerns arbitrary algebraic constant values.
Neither restates the original bounded-projective residue conclusion. The proven
assembly supplies derived existence, the pointed cover choice, further restriction,
ring transport, projectivity and both bounds rather than delegating them again.

## No longer needed

Imports removed: none. Modules withdrawn or globally pruned: none.

For the item's derived-existence step, the planned direct uses of
`lem-pur-derived-change-of-rings` and `lem-weil-pbc-site-derived-tensor-descent` are
replaced by the already proved `lem-pc-base-derived-extension-resolution`.
Their modules are not imported directly by the item. They can still be needed by
constant scalar-extension infrastructure, so no global withdrawal is requested.

The item's direct geometric-point, constant-stalk and tensor-pullback work is now
confined to the two intermediate nodes. Thus the original direct dependencies
`lem-weil-proetale-weakly-etale-localization`,
`lem-weil-proetale-constant-sheaf-stalk`,
`def-sfb-site-derived-constant-module-functor`,
`def-weil-pbc-adic-coefficient-datum`, and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` are recorded under the new nodes
where their arguments belong, not claimed pruned from the whole target closure.
`def-weil-pbc-ringed-derived-restriction` remains a direct proof dependency.

## Where the brief, the DAG or earlier work was wrong

No false statement or source mismatch was found. The existing dependency declarations
provide the components rather than the entire compatibility square at the actual
coefficient and localization universes. `ConstantRealizationReflectsIsomorphismGeneral`
reflects a supplied algebraic map; it does not itself recover an algebraic isomorphism
from an arbitrary isomorphism between constant realizations. The separate
constant-value statement records precisely that missing step.

The ordinary-module derived extension already exists in the source library, so its
existence need not be split off again. The actual remaining work is coefficient
compatibility and constant-value recovery, independent of the interval and
projectivity assembly now proved here.

## New nodes

`lem-weil-pbc-finite-quotient-model-residue-comparison` records the coefficient-change
square, for arbitrary input complexes and charts, using the supplied universal
left-derived pair and a quotient-compatible residue-ring identification. Its source
is the iterated scalar-extension equality in Stacks Tag 094I, with derived pullback
and constant scalar-extension comparisons. The docstring gives the K-flat balancing
argument and exact slice restriction.

`lem-weil-pbc-finite-constant-slice-iso-reflects` records recovery of arbitrary algebraic
complexes from isomorphic changed constant realizations on a nonempty chart. Its
proof is exact geometric stalk, natural constant germs, and removal of universe lift
using small K-projective resolutions. It contains no residue-model assumption and
can be proved independently of the coefficient-change square.

No change record is needed: all existing public signatures and definitions are
unchanged, and only the item's existing node and the two new nodes are delivered.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
