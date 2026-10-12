## What changed

Proved `AlgebraicGeometry.minimal_component_dimension_maximum_data` by constructing the
finite nonempty set of minimal primes below `p` and combining two strictly smaller core
statements. Added proof-only import `Sheaf.RingTheory.MinimalComponentDimensionMaximumCore`.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.minimal_component_dimension_maximum_data`
(node `lem-weil-pbc-minimal-component-dimension-maximum-data`), by a decomposition.
Added two holes, both whole public named theorem proofs in the new core module:
`AlgebraicGeometry.minimal_component_dimension_maximum_bound`
(node `lem-weil-pbc-minimal-component-dimension-maximum-bound`) and
`AlgebraicGeometry.minimal_component_dimension_maximum_attained`
(node `lem-weil-pbc-minimal-component-dimension-maximum-attained`).
Thus 1 original hole closed, 2 new holes added; net -1. The dimension argument
remains open; this delivery proves the finite-set construction and packaging,
and does not claim an axiom-free proof of the dimension theorem.

## No longer needed

Removed proof-only imports from the item:
`Sheaf.RingTheory.FiniteTypeDomainDimensionLocalRing`,
`Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg`, and
`Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`.
The first two remain planned proof dependencies of the new core module and are
imported there. The localization/residue-field isomorphism theorem is unused;
its old dependency `lem-weil-pbc-localization-prime-residue-field-iso` is removed.
The old direct dependencies
`lem-weil-pbc-finite-type-domain-dimension-local-ring`,
`lem-weil-pbc-finite-type-domain-dimension-trdeg`, and
`lem-weil-pbc-localization-dimension-chains-below-prime` move to the core nodes;
they are no longer direct proof dependencies of the item. The three old
Noetherian/minimal-prime dependencies remain directly used as Mathlib lemmas.
No claim is made that any module becomes unreachable from every target.

## Where the brief, the DAG or earlier work was wrong

The DAG presented the entire prime-chain argument as one indivisible hole. It is more
useful to expose the bound and attainment portions as separate strictly smaller nodes;
the finite-set packaging is elementary once those are available.

## New nodes

`lem-weil-pbc-minimal-component-dimension-maximum-bound` is stated in
`Sheaf.RingTheory.MinimalComponentDimensionMaximumCore`.
`lem-weil-pbc-minimal-component-dimension-maximum-attained` is stated in the same module.

## Earlier second reading (a previous round; superseded)

Pending the independent second worker reading; the target compiles and the two added
statements are strict subclaims of its dimension argument.

## Second reading by S1

1. PASS: diffed the item's complete module against the repository. The existing
   theorem signature, universes, namespace, visibility, and public imports are
   byte for byte unchanged. Only its proof and proof-only imports change; there
   are no existing definitions or other existing declarations in this delivery.
2. PASS as a decomposition: compiled both modules in import order without errors
   or warnings. The only textual holes are the two reported core theorems;
   there are no definitions, axioms, unsafe declarations, opaque declarations,
   externs or implemented_by declarations. Scratch-copy `#print axioms` checks
   the item and both core theorems; sorryAx is expected through the two open
   subclaims. The finite set is constructed using proved Mathlib finiteness,
   not chosen from an unproved existence statement.
3. PASS after repair: read Stacks Tag 00P1 at
   https://stacks.math.columbia.edu/tag/00P1 and the statements of the domain
   dimension and maximal-chain dependencies. The two subclaims have respectively
   only the universal bound and only the attained equality; neither duplicates
   the finite-set target. Replaced incomplete chain sketches with the saturated
   chain argument, including why concatenation computes the whole component
   dimension. Checked k (d=r=0), k[x] at zero (d=0,r=1) and at (x)
   (d=1,r=0), and k[x,y]/(xy) at (x,y) (d=1,r=0).
   For unequal-dimensional components, S=k[x,y,z]/(xy,xz) at (x,y,z)
   has component dimensions 2 and 1 and d=2,r=0: the bound holds on both
   and attainment holds only on a largest component. A zero ring has no prime p,
   so supplies no counterexample. Re-ran recorded searches with different words:
   LeanFinder for affine height plus residue transcendence degree (height
   results, no direct formula); Loogle ringKrullDim/Ideal.Quotient (identifier
   unavailable, not counted as evidence); grep height/coheight/trdeg (order and
   height infrastructure); LeanSearch for finite-type maximal prime chains
   (HTTP 500, recorded unavailable). Searched both library roots for the same
   formula; upper dimension-at-point results depend on this item and would be
   circular. No quick existing theorem closes either subclaim.
4. PASS after repair: kept the working finite-set argument. Removed all three
   unused Sheaf proof imports from the item; retained the two domain lemmas in
   the core's proof plan. Added a proof-only Mathlib height import to the core
   for its localization/chain dependency. The report now distinguishes direct
   pruning from dependencies still needed below the core. Read sk-thm-p1's
   realized statement and all four realized step lists: this helper is below
   the unit level, and the unit route and records stay unchanged.
5. PASS after repair: added the missing existing item node to the delivery,
   changing only proof, proof_deps and proof_origin to match the packaging proof.
   Checked both new nodes' Lean signatures against their modules; made their
   prose statements self-contained with explicit field, finite type, prime,
   dimension and transcendence-degree assumptions, and complete statement
   dependencies. Replaced their proof sketches and search records with the
   reviewed arguments and actual searches. Their chapter/unit, new-node origin,
   status, creation record and Lean module/declaration records agree.

Changed in this second reading: pruned unused imports, moved domain proof-plan
imports to the core, completed both split-off docstrings and node proofs,
repaired self-contained node statements and search evidence, supplied the
item's missing proof metadata, and corrected the accounting to a decomposition.
