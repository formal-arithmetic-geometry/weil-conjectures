## What changed

Replaced the sorry body of
`WeilConjectures.DerivedTotalResolution.total_resolution_column_zero_cycle_reduction`
with induction on an explicit finite column bound. Its signature, docstring, namespace,
visibility, and original public imports are unchanged. Added three proof-only imports:
`Sheaf.Paper.TotalResolutionCycleFiniteSupport`,
`Sheaf.Paper.TotalResolutionCycleSupportStep`, and
`Sheaf.Paper.TotalResolutionCycleSupportZero`.

The finite-expansion module imports only the total-complex, ModuleCat, and finite-sum
APIs needed by its statement. The target uses an explicit Finset.sum in its proof
to avoid adding a file-level notation scope.

The new modules state a finite expansion of an arbitrary total element, removal of one
outer column of a supported cycle by a boundary correction, and lifting a column-zero
cycle, respectively. The last statement is proved using Mathlib's split-monomorphism
instance for coproduct injections and `ShortComplex.cyclesMk` / `i_cyclesMk`.
The ModuleCat homology import used by this proof is plain `import`, not public.
No global definition or data object chosen from an unproved existence theorem is added.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.DerivedTotalResolution.total_resolution_column_zero_cycle_reduction`
(node `lem-pc-derived-total-resolution-column-zero-cycle-reduction`) by a real induction
and addition of successive boundary primitives. It still depends on the two holes below;
this is a decomposition, not a completed axiom-free proof of the original mathematics.

Also proved the new statement
`WeilConjectures.DerivedTotalResolution.total_resolution_cycle_support_zero`
(node `aux-total-resolution-cycle-support-zero`) without sorry dependencies.

Added exactly two named holes, each with a source and complete natural-language proof:

- `WeilConjectures.DerivedTotalResolution.total_resolution_element_finite_support`
  (node `aux-total-resolution-cycle-finite-support`). This is only the finite expansion
  of an element; it requires neither homology, the cycle condition, nor exactness.
- `WeilConjectures.DerivedTotalResolution.total_resolution_cycle_support_step`
  (node `aux-total-resolution-cycle-support-step`). This removes one column from an
  explicitly bounded cycle; it does not assert the final column-zero representation.

There are no other sorry bodies in the delivered modules. The syntactic hole accounting
is one old hole closed and two new holes added (net -1); the newly proved base statement
was not an old hole. No net progress is claimed. The maintainer's pinned sorry ledger,
including the actual target import closure, remains the authoritative measure.

## No longer needed

None from the library: the original node had no proof_deps, and all four original
Mathlib imports remain for its statement. No library module is claimed pruned.
The never-delivered `TotalResolutionCycleReductionAux` and its
`aux-total-resolution-cycle-reduction-measure` node were removed from this sandbox.
That discarded proposal is not counted as a library pruning or a closed hole.

## Where the brief, the DAG or earlier work was wrong

The first worker's existence of an unspecified measure with the complete target as
its base case and induction step was not a genuine reduction. Taking the measure
constantly zero makes that auxiliary statement the entire original target. Its
short docstring also did not supply a complete proof. The claimed proof was therefore
rejected in second reading and replaced by explicit finite expansion and a single
boundary-correction step, with the column-zero base actually proved.

The original source plan already contained these mathematical steps; it did not need
an extra measure theorem. The new proof follows that plan below the unit level.

## New nodes

`aux-total-resolution-cycle-finite-support`: arbitrary total elements are finite sums
of the actual column injections in columns 0 through -r. Zero elements admit r=0 and
all-zero coordinates. Horizontal differentials and homology play no role.

`aux-total-resolution-cycle-support-step`: for r>=0 a cycle supported from column
-(r+1) through 0 differs by a total boundary from a cycle supported from -r through 0.
Exactness is used at p=-r-2, which is strictly less than -1 even when r=0.
The correction degrees are n-1 and the outer vertical degree is n+r+1.

`aux-total-resolution-cycle-support-zero`: a cycle in the image of j.f(n) lifts to a
vertical cycle, using injectivity of j.f(n+1). This statement is proved. No change
record is needed: no existing signature or definition changes.

## Second reading by F3

1. Compared the item's module with the repository version by diff. The existing
   theorem signature is byte for byte unchanged, including every hypothesis and
   conclusion; only its proof and three private proof imports change. No existing
   definition, target statement, or other group's module is changed.
2. Compiled all four modules using lcompile.py in import order. Checked source for
   forbidden declarations and sorry in definitions. The only remaining sorries are
   exactly the two named auxiliary theorem bodies listed above. Explicit #print axioms probes
   found only propext, Classical.choice and Quot.sound for the base. The target and both
   open auxiliaries additionally use sorryAx, with no other axiom.
3. Rejected and removed the original measure wrapper. Read the replacement statements
   against Tag 09IZ (homology.tex, lemma-good-resolution-gives-qis, proof), using the
   locally available Stacks source copy. Checked zero ring, zero element, empty
   support, r=0, negative n, and the off-by-one exactness index. The finite expansion
   and one-step correction are true, independent parts of the argument. Repeated
   LeanSearch, leanfinder, loogle and grep searches with different terms; found generic direct-sum,
   coproduct and cycle-constructor tools, not these specialized statements. LeanSearch was attempted for each node
   and returned Internal Server Error; that unavailability is recorded without a
   mathematical verdict. Also searched
   lean/Sheaf and lean/WeilConjectures: the original reduction's downstream users do
   not supply either auxiliary. Complete verbal proofs and matching nodes are present.
4. Kept the finite-support route and proved the column-zero base directly from Mathlib.
   The unit sk-thm-picard-f-representable has no realized entry for this item, and its
   route is unchanged. Every original proof dependency (there were none) is accounted
   for under No longer needed. All added imports of the item are plain imports; the
   base module's additional homology implementation import is proof-only.
5. Rebuilt the existing node's proof, proof_deps and proof_origin from the actual
   induction; its original statement and all other non-proof fields are retained.
   The three new nodes contain verbatim Lean signatures, source, complete proof plan,
   search records, chapter, unit, blueprint origin, and F3 creation records. The two
   open statements and the independently proved base agree with their Lean modules.

Second reading changed the invalid measure wrapper into explicit finite-support
expansion and one-column reduction, proved the base, repaired dependent-index transport,
updated the DAG and corrected the report's progress accounting.
