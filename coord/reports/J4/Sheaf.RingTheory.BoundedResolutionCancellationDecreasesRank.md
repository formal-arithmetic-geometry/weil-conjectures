## What changed

Replaced the original hole in `ModuleCat.bounded_resolution_cancellation_decreases_rank`
with a real reduction: choose finite bases, prove by two basis expansions that
nonminimality supplies a unit matrix coefficient, apply cancellation at that
supplied pivot, and compare finite sums with `Finset.sum_lt_sum`.

Removed the first worker's proposed `BoundedResolutionCancellationRankProfile`
module and node. Its same-input rank-profile statement still contained the entire
nonminimal cancellation problem. The new module
`Sheaf.RingTheory.BoundedResolutionUnitEntryCancellation` instead isolates removal
of a supplied unit pivot. It needs neither localness nor Noetherianity and does
not find the pivot. The existing signature and all its public imports are unchanged.
Its proof-only `UnitEntrySplits` import moves to the new construction module.

## Proved and sorry left

Closed the syntactic hole in
`ModuleCat.bounded_resolution_cancellation_decreases_rank`.
Added one named hole:
`ModuleCat.exists_bounded_resolution_unit_entry_cancellation`, node
`stage3-j4-bounded-resolution-unit-entry-cancellation`.
The proposed `ModuleCat.exists_bounded_resolution_cancellation_rank_profile`
hole was removed before delivery and is not part of the delivered accounting.

This is a decomposition, not a complete proof: one old hole closed, one new hole
added, net zero holes, zero of one original declarations proved without reachable
`sorryAx`. Unit-pivot extraction and the finite-sum comparison are proved;
construction of the complementary augmented projective resolution remains open.
No data definition was added or changed. In particular no arbitrary object is
chosen into a definition from an unproved existence theorem.

Both delivered modules compile in import order without errors or warnings.
Independent scratch-copy `#print axioms` checks of both declarations report exactly
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.

## No longer needed

Removed the direct proof import `Sheaf.Algebra.Homology.UnitEntrySplits` from the
item; it remains imported by the supplied-pivot construction module and is not
pruned from the target closure. Tested and removed an unnecessary proof import
of `Mathlib.LinearAlgebra.Dimension.Free`; `Module.finBasis` is already available
through the existing public imports.

Both old direct proof dependencies,
`lem-weil-pbc-free-complex-unit-entry-splits` and `def-weil-pbc-exact-sequence`,
are replaced in the item's `proof_deps` by
`stage3-j4-bounded-resolution-unit-entry-cancellation`. Both remain dependencies
of that construction, so no planned dependency module is pruned from the closure.
No unit realization is changed. The rejected rank-profile module and node were
unlanded proposals, not pruned library modules.

## Where the brief, the DAG or earlier work was wrong

The first worker's rank-profile theorem used the original nonminimality premise
and deferred the whole cancellation argument. Its parent node still recorded
the old proof instead of the proposed Lean dependency. Its search records lacked
independent evidence in this sandbox. The second reading replaces that proposal
with a supplied-pivot construction, proves pivot extraction, updates the parent's
proof route, and records new actual searches. No original mathematical statement
was changed. The decomposition's net-zero count is explicit.

## New nodes

`stage3-j4-bounded-resolution-unit-entry-cancellation` is stated in
`lean/Sheaf/RingTheory/BoundedResolutionUnitEntryCancellation.lean` and recorded in
`dag/nodes/sec-proper-base-change/stage3-j4-bounded-resolution-unit-entry-cancellation.json`.
It is the structural cancellation step after the upper proof has already supplied
bases, the degree and a unit pivot. Its complete proof in words covers integer
extension, splitting, restriction, augmentation, quasi-isomorphy, projectivity,
boundedness and finrank control. No change record is needed: no existing statement
or definition changes.

## Second reading by J4

1. Compared the original module with the repository using `diff -u`. Its existing
   declaration signature, hypotheses, conclusion, universes, visibility and
   docstring are byte-for-byte unchanged. Only proof text and proof imports differ.
   No definitions change and no existing declaration is added or removed. Pass.

2. Compiled both modules together in import order through `lcompile.py`, then
   compiled the item alone after removing the unnecessary Dimension.Free import.
   Probed both declarations using scratch copies with `#print axioms`. Only the
   allowed standard axioms and the declared remaining `sorryAx` occur. Scanned
   the delivered source for forbidden declarations and attributes: none occur.
   Exactly one `sorry` remains, in the named construction theorem; its docstring
   contains a complete natural-language proof. Pass as a decomposition.

3. Read Stacks Tags 00MT and 00OA online, and read the complete statement and proof
   of `ChainComplex.exists_splitting_of_isUnit_entry`. Tag 00MT supplies precisely
   the two rank drops at a known unit coefficient; Tag 00OA uses removal of this
   identity summand from a resolution. The new lemma omits pivot extraction,
   a strict part now proved above it, and assumes the actual pivot explicitly.
   Its nontrivial commutative-ring hypothesis gives invariant basis number;
   no locality or Noetherianity is needed for this part. For `d=0`, `j<d` is
   impossible, as is the original nonminimality premise. Empty source or target
   bases cannot supply pivot indices. For `j=0`, the augmentation kills the
   removed summand because it is a differential image; for `j>0`, its degree-zero
   term is zero. The case `j=d-1` stays within the bound. Over a field an identity
   disk gives the expected cancellation; the argument also allows zero divisors
   since the only inversion is of the supplied unit. The zero ring is explicitly
   excluded only in the new rank lemma and is already excluded by original
   localness. No minimality or iteration is asserted. Pass.

   Independent `msearch.py` searches used LeanFinder for removal of a supplied
   invertible coefficient, Loogle for `"toMatrix", "range"`, and grep for
   `contractible|splitting_of_isUnit|cancel.*unit`. LeanSearch was also attempted
   and returned Internal Server Error, recorded as unavailable. Hits are generic
   resolution maps and matrix lemmas, not the augmented cancellation construction.
   Local `rg` searches in both Lean roots located UnitEntrySplits and related
   splitting constructions, but no theorem with this supplied-pivot conclusion.
   The original rank-profile proposal was rejected and removed.

4. Reviewed the proof top downward. The two finite basis expansions now discharge
   the local-ring unit-extraction step; sum arithmetic uses Mathlib directly.
   The remaining hole is the supplied-pivot structural construction, whose plan
   uses the existing unit-entry splitting theorem. Inspected
   `dag/units/sk-thm-p1.json`, including its `realized` statement and steps: none
   of these unit-level realizations is replaced or bypassed. Original public
   imports support the unchanged signature; the new imports distinguish statement
   dependencies from the proof-only splitting dependency. The No longer needed
   section lists both removed direct DAG dependencies and explains that both
   remain transitively required, hence there are no pruned library modules. Pass.

5. Compared both node records against the delivered Lean. The parent now records
   pivot extraction, supplied-pivot cancellation and finite-sum comparison, with
   the supplied-pivot node as its sole direct proof dependency. The new node's
   statement matches its Lean signature verbatim, gives all hypotheses without
   referencing the parent as a statement dependency, and has its source, proof
   steps, their dependency union, origin, actual searches, creation metadata,
   blueprint ancestry, chapter, unit and Lean record. The old dependency nodes
   remain in the new node's plan. No cycle through the parent is introduced. Pass.

Changed during second reading: removed the restatement-like rank-profile proposal;
proved unit-pivot extraction in the original module; introduced the narrower
supplied-pivot construction hole with its full docstring and independent searches;
updated the parent DAG proof; corrected imports and hole accounting.
