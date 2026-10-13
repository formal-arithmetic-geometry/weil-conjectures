## What changed

Proved `AlgebraicGeometry.Scheme.cechFirstSortingJunctionTailContribution` without changing
its signature or definitions. Added two proved permutation lemmas in
`Sheaf.AlgebraicGeometry.AlternatingCechPartialSortUnique` and
`Sheaf.AlgebraicGeometry.AlternatingCechPartialSortAdvance`, imported only for the proof.
The first constructs the unique partial sort with Mathlib `Tuple.sort`; the second
identifies the advanced sort with an inverse interval cycle and with the deleted junction.
Private proved helpers establish the unique deletion position, its integer coefficient,
presheaf transport in the thin category of opens, and the fixed-stage sum identity.
The parent node now records these actual proof dependencies.

All three modules compile cleanly with lcompile.py. The main proof closes its hole from
proved helpers; this is a proof, not a decomposition leaving lower holes. Independently
checked every permutation for n=0 through n=5 (719 tail stages): junction deletion,
interval-move orientation, unique tail position, and coefficient sign. The Lean proofs
also cover the empty type in the uniqueness lemma, the empty prefix, the empty advanced
tail, b=a, p=0, arbitrary repeated values of t, and empty I whenever an input tuple exists.

## Proved and sorry left

Closed the single original hole in
`AlgebraicGeometry.Scheme.cechFirstSortingJunctionTailContribution`
(node `lem-pc-alternating-cech-first-sorting-junction-tail-contribution`).
Also proved `AlgebraicGeometry.Scheme.cechPartialSort_existsUnique`
(node `lem-pc-alternating-cech-partial-sort-unique`) and
`AlgebraicGeometry.Scheme.cechPartialSort_advance`
(node `lem-pc-alternating-cech-partial-sort-advance`).
No sorry remains in any delivered module; no holes were added or split off.

## No longer needed

None. The original sorting-operator and SiteCechComplex dependencies are both needed.
No original imports or DAG nodes were pruned. Stable-sort existence or uniqueness,
restriction homotopy identities, and other junction cancellation statements are not used.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The original one-step proof plan needed its
partial-sort existence/uniqueness and interval-cycle argument made explicit. These are
now proved. Restriction-map composition is established directly by the subsingleton
hom sets of opens instead of comparing every fibre-product projection. Stacks 01FM
was read at https://stacks.math.columbia.edu/tag/01FM; its first-homotopy verification
is explicitly omitted. The new proofs supply the tail-labelled part of that verification.
LeanSearch returned Internal Server Error and is recorded as unavailable; Loogle,
LeanFinder and source grep supplied the sorting and cycle-sign ingredients.
The ancestor tool reports None for the original item's inherited blueprint chain;
the new nodes identify its existing blueprint ancestor
`lem-pc-projective-space-cohomology-bound` and the precise sorting-homotopy step.

## New nodes

`lem-pc-alternating-cech-partial-sort-unique`: existence and uniqueness of a permutation
with prescribed prefix and increasing tail, including the empty tail. Its new module
contains a complete proof using an injective numerical key and Mathlib tuple sorting.
No existence witness from an unproved theorem is used.

`lem-pc-alternating-cech-partial-sort-advance`: deletion of the tail junction copy gives
the next partial sort, which equals composition with the inverse interval cycle.
Its new module contains a complete proof by the four position cases and the proved
uniqueness lemma. Both nodes stay in the parent's chapter and unit. No change record
is required because every existing signature, definition and visibility is unchanged.

## Second reading by W2

1. **Interfaces: PASS.** Compared the main module with the repository using diff and
   checked the full existing theorem signature byte for byte. It is unchanged; no
   existing definition or visibility changed. The two additional modules are new.
   The existing node changes only proof, proof_deps, and proof_origin. No statement
   change or change record is needed.
2. **Proof and axioms: PASS.** Independently compiled all three modules in dependency
   order with lcompile.py, with no errors or warnings. Scratch copies with #print axioms
   checked both new public lemmas, the original theorem, and every private helper;
   each uses only propext, Classical.choice, and Quot.sound. No delivered module has
   sorry, axiom, unsafe, opaque, implemented_by, extern, or a hollow definition.
   The constructed sorting key and Mathlib Tuple.sort supply actual data; no arbitrary
   witness is selected from an unproved existence theorem.
3. **New statements: PASS.** Neither new theorem is left sorry or restates the item.
   They isolate unique partial sorting and its advancement by an inverse interval cycle.
   Read their complete docstring arguments and matching nodes against
   [Stacks Tag 01FM](https://stacks.math.columbia.edu/tag/01FM), where the homotopy
   verification is omitted. Independently exhaustively checked n=0 through n=6:
   all 5,039 tail stages satisfy the unique junction position, deleted tuple,
   inverse-cycle orientation, and coefficient sign. The n=0 uniqueness case,
   a=0, a=n, b=a, and final a are also covered by the Lean arguments. Tuple values
   are never assumed distinct; repeated values in t and empty I cause no added
   hypothesis. Additional Loogle search for Tuple.eq_sort_iff confirmed the ingredient;
   LeanFinder search for a bijection fixed on an initial segment with monotone complement
   returned generic initial-segment lemmas, not this result. Launcher grep for
   sort.*(prefix|initial)|cycleIcc.*symm returned no match. Source searches in both
   library roots and Mathlib found no existing replacement for either new theorem.
4. **Route and pruning: PASS.** Read the proof from the contribution identity down
   through the fixed-stage sum, transport, coefficient, position, and permutation
   lemmas. The Mathlib sorting and interval-cycle lemmas give the relevant direct route.
   Each import is needed for a signature or a used proof ingredient; new proof-only
   imports are plain imports. Both original proof_deps remain used, so No longer needed
   correctly says none. The unit sk-thm-picard-pn is unchanged, including its existing
   empty realized entries; this delivery completes a lower sorting-homotopy node and
   neither bypasses a unit nor claims to complete its realization.
5. **DAG: PASS.** Checked each recorded Lean signature against its declaration and
   each proof_deps against the union of proof-step uses. The parent records both new
   proved lemmas and the original definitions. New nodes contain the required source,
   searches, proof_origin, creation, blueprint ancestry, chapter, unit, and Lean records.

Second reading changed only this report: added the independent checks and verdicts.
No Lean or node repair was needed. One original hole is closed; zero holes are added,
zero statements are split off with sorry, and no modules are pruned.
