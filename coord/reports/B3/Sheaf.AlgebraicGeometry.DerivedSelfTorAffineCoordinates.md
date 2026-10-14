## What changed

`lean/Sheaf/AlgebraicGeometry/DerivedSelfTorAffineCoordinates.lean` now proves
`AlgebraicGeometry.exists_derived_selfTor_affine_coordinates` from the chosen-lift
coordinate construction and the existing proved quotient tensor lift homotopy.
The declaration's signature, universes, visibility and docstring are unchanged.

The proof identifies the supplied quotient map with `Ideal.quotientMap` by
surjectivity of the quotient projection, rewrites the chosen augmentation and
tensor equations, obtains a homotopy between the chosen and supplied tensor maps,
and uses `Homotopy.homologyMap_eq` to transport the restriction equation.
It neither chooses data from an unproved existence theorem in a definition nor
asserts that restricted projective modules are projective.

A new module `Sheaf.AlgebraicGeometry.DerivedSelfTorChosenAffineCoordinates`
states the remaining geometric construction: affine coordinates compatible with
one augmented lift of the canonical quotient map on each basic inclusion.
Its natural-language proof records the coefficient normalization and the exact
homology, extension and tensor restriction comparisons. The parent DAG node now
records the actual quotient-surjectivity and homotopy argument.

Both delivered modules compile without warnings using `lcompile.py --all`, within
the single-file limit. The source checks were read at Stacks Tags
[08DX](https://stacks.math.columbia.edu/tag/08DX),
[06YH](https://stacks.math.columbia.edu/tag/06YH),
[01I9](https://stacks.math.columbia.edu/tag/01I9), and
[00LS](https://stacks.math.columbia.edu/tag/00LS).

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_derived_selfTor_affine_coordinates`
(node `new-p1-derived-self-tor-affine-coordinates`). Its proof has no `sorry`.

Added one hole:
`AlgebraicGeometry.exists_derived_selfTor_chosen_affine_coordinates`
(node `new-b3-derived-self-tor-chosen-affine-coordinates`), whose complete proof
is exactly `by sorry` in its own module.

This is a decomposition: one upper hole closed, one strictly smaller hole added,
net zero holes. The completed part is compatibility with EVERY supplied augmented
lift, including uniqueness of the quotient map and homology independence of the
lift. The new statement claims only existence of ONE compatible lift per basic
inclusion, with its quotient map explicitly fixed. It omits the universally
quantified lift-independence clause. No fully sorry-free geometric Tor comparison
is claimed. No other holes are added or left in the assigned module.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.AffineQuotientRestrictedIso`
- `Sheaf.AlgebraicGeometry.AffineDerivedTensorChartComparison`
- `Sheaf.AlgebraicGeometry.DerivedTensorOpenRestrictionNatural`
- `Sheaf.AlgebraicGeometry.AffineDerivedTildeHomologyComparison`
- `Sheaf.Algebra.Homology.BoundedFlatKFlat`
- `Mathlib.Algebra.Homology.Embedding.ExtendHomology`
- `Mathlib.Algebra.Homology.Embedding.CochainComplex`

Their geometric construction roles remain dependencies of the new chosen-lift
node and its module. Consequently they are not pruned from the targets' closure
by this decomposition. The former direct parent proof dependencies
`lem-sc-affine-quotient-restricted-iso`,
`lem-pc-affine-derived-tensor-chart-comparison`,
`lem-pc-derived-tensor-open-restriction-natural`,
`new-affine-derived-tilde-homology-comparison`,
`lem-pc-module-bounded-flat-kflat`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-spec-module-tilde-sections`, and
`lem-pc-affine-chart-total-tensor` likewise remain below that new node.
No module or node is claimed unnecessary globally. All public imports are kept.
The parent directly uses only the new chosen-lift module and
`Sheaf.Algebra.Homology.QuotientTensorResolutionLiftHomotopy`.

## Where the brief, the DAG or earlier work was wrong

No false statement or unit-route error was found. The existing affine chart
comparison gives only `Nonempty` object isomorphisms, not the normalized
cross-chart restriction square. Objectwise isomorphisms alone do not establish
that square. The new obligation records precisely the geometric normalization
and chosen-lift square that must still be built.

Existing self-Tor coordinate modules such as
`Sheaf.AlgebraicGeometry.SelfTorOrdinaryResolutionSections` and
`Sheaf.AlgebraicGeometry.SelfTorAmbientSectionCoordinates` already transitively
import the assigned module, so using them here would create a cycle.
`import_direction.py may` confirmed the former cycle. Their algebraic
lift-independence proofs helped identify the valid acyclic reduction.

The unit `sk-thm-picard-duality` is unchanged. Its Serre-duality statement and
single recorded step remain; its `realized.statement` and sole `realized.steps`
entry are empty in the repository. This refinement stays below the unit level
and separates the affine self-Tor tool's geometric construction from its
algebraic lift-independence argument. The original module refers to 00LS(1) in its source line although
lift independence uses 00LS(2); the updated proof origin records the latter.

## New nodes

`new-b3-derived-self-tor-chosen-affine-coordinates`, in
`dag/nodes/sec-picard-framework/`, states the affine geometric coordinate
construction and its restriction formula for one augmented lift of the
canonical quotient map. Its module is
`lean/Sheaf/AlgebraicGeometry/DerivedSelfTorChosenAffineCoordinates.lean`.
The source is Stacks 08DX(2), 06YH, 01I9(2), and 00LS(1), and the node and
Lean docstring carry the complete construction argument. Edge cases checked
mathematically: degree zero, zero quotient, zero ring/empty affine chart,
empty basic open, identity inclusion, and the zero ideal. None requires a
nonzero ring assumption or projectivity after restriction of scalars.
The searches are recorded in `searches.jsonl`; LeanSearch was unavailable,
while LeanFinder, Loogle, and grep returned only supporting tools.
No change record is needed: existing public interfaces are unchanged.


## Second reading by B3

1. Compared the assigned module against the repository with `diff` and an exact
   signature substring comparison: the existing declaration signature is byte
   identical. Its docstring and every public import are unchanged. There are no
   definitions added or altered and no change records or forced adaptations.
   Verdict: unchanged public mathematical statement.
2. Compiled both delivered modules in import order with `lcompile.py --all`:
   no errors or warnings (4.1 s and 12.5 s). Scanned the source: the only hole
   is the named new chosen-coordinate theorem, with proof exactly `by sorry`;
   no forbidden declaration forms or data definitions occur. A temporary scratch
   copy with `#print axioms` showed only `propext`, `Classical.choice`, `Quot.sound`
   and `sorryAx` for the two coordinate theorems. The tensor-lift homotopy theorem
   showed only the three permitted axioms. Verdict: valid reduction, with the
   reported geometric hole still open, not a sorry-free proof of the item.
3. Read the new statement and its full construction docstring, the augmented
   quotient-resolution comparison, and the affine derived comparison declarations.
   Checked degree zero, identity inclusion, zero ideal, top ideal/zero quotient,
   empty affine and empty basic opens: exact restriction of scalars and source
   projectivity suffice, with no projectivity claim about restricted target terms.
   Canonical quotient-map normalization makes the chosen lift statement true.
   It is strictly a part of the original argument: it omits arbitrary-lift
   independence, which the parent now proves from a separate sorry-free homotopy.
   It is not an alias with the same hypotheses and conclusion. Independently
   searched LeanFinder for sheafification of Tor and localization, Loogle for
   homology/tilde, Mathlib grep for Tor/localization and tilde/homology, and local
   `lean/Sheaf` by affine-coordinate and self-Tor concepts. The hits supply Tor
   and localization tools, not this normalized cross-chart square. Existing
   self-Tor coordinate users depend on the parent and cannot replace it here.
   Verified Stacks 08DX(2), 06YH, 01I9(2), and 00LS(1)-(2) against their pages.
   Verdict: true, needed geometric obligation with source, proof and node; it
   cannot be closed in a few minutes by applying an existing comparison alone.
4. Read the reduction top down: quotient surjectivity fixes psi, the existing
   tensor homotopy equates homology maps, and substitution proves the required
   restriction formula. No shorter complete route was found. Both new proof
   imports in the parent are plain imports; public imports supply statement
   notation, objects or instances. The eight removed old proof dependencies
   are all recorded above, and remain below the new construction node; no global
   pruning is claimed. The unit record and its source statement are untouched.
   Verdict: the unit route is preserved; decomposition with one hole closed,
   one added and net zero, rather than a completed geometric comparison.
5. Compared parent node JSON: only `proof`, `proof_deps`, and `proof_origin`
   changed. Checked both nodes' dependency sets against the union of their
   proof-step uses, and their verbatim Lean statement fields against the files.
   The new node has its source, searches, status, creation, blueprint, chapter,
   unit and Lean fields. Verdict: metadata matches the delivered argument.

Second-reading changes: corrected the report's inaccurate claim of three
realized unit steps: the repository has one recorded step and empty realization
entries. Added independent searches and this review. No Lean proof, statement,
definition or node required repair.
