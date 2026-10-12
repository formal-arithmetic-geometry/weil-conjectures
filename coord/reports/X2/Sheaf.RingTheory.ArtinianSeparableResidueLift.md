## What changed

The existing theorem `Algebra.exists_finiteEtale_artinian_residue_lift` keeps its
signature byte for byte. Its proof obtains the finite étale local Artinian construction
from `ArtinianSeparableResidueLiftCore`, proves the missing flatness with
`ArtinianSeparableResidueLiftFlat`, and assembles every original conjunct.

The new construction theorem needs no flatness hypothesis on D → S. Its complete
natural-language proof and DAG plan describe the finite separable residue extension,
henselian finite étale lifting, étale retraction, residue-element lifting and universe
transport. It is an existential theorem, and no definition extracts an arbitrary witness
from it. Its original proof-dependency cycle back to its parent was removed.

The second reader proved the new flatness theorem entirely from Mathlib. The map factors
as D' → S ⊗[D] D' → S. The first map is flat by flat base change; the second is an étale
section, hence smooth and flat. This avoids the open Noetherian fibre-flatness criterion.
Only proof imports changed in the existing module. All five original public imports
remain unchanged. The inaccurate provisional imports change record was removed because
no existing signature, definition or public import changes.

## Proved and sorry left

Original hole closed:
`Algebra.exists_finiteEtale_artinian_residue_lift`
(node `lem-weil-pbc-artinian-separable-residue-lift`).

New hole added and still open:
`Algebra.exists_finiteEtale_artinian_residue_lift_core`
(node `lem-weil-pbc-artinian-separable-residue-lift-core`, module
`Sheaf.RingTheory.ArtinianSeparableResidueLiftCore`).

The first worker also left
`Algebra.flat_of_finiteEtale_artinian_residue_lift_core`
(node `lem-weil-pbc-artinian-separable-residue-lift-flat`) with sorry. The second reader
closed it; the delivered theorem has no sorry and only standard axioms.

Thus one original hole is replaced by one new strictly smaller construction hole.
This is a decomposition, with net hole reduction zero against the repository version,
not a completed proof of the original theorem without sorryAx. There are no other new
holes, no definitions with sorry, and no new axioms. The construction separates the
entire flatness argument, and moreover no longer assumes flatness at all.

## No longer needed

All five old proof-only imports were removed from the existing target module:

- `Sheaf.RingTheory.FlatAndFlatOfFlatFibreNoetherian`
- `Sheaf.RingTheory.HenselianEtaleRetraction`
- `Sheaf.RingTheory.HenselianFiniteEtaleEquivalence`
- `Sheaf.RingTheory.LocalDimensionZeroHenselian`
- `WeilConjectures.Mathlib.RingTheory.Etale.Field`

The last four remain imports of the open construction theorem, preserving its route.
The fibre-flatness criterion module is no longer needed on this item's proof route.
This makes no claim that the module is globally unreachable from all other targets.

Every old direct proof dependency is replaced in the target node by the two intermediate
nodes. The following old nodes remain used transitively by the construction:
`def-weil-pbc-separable-algebraic-extension`,
`lem-weil-pbc-finite-separable-extension-etale`,
`lem-weil-pbc-artinian-local-noetherian-nilpotent`,
`lem-weil-pbc-artinian-local-unique-prime`,
`lem-weil-pbc-local-dimension-zero-henselian`,
`lem-weil-pbc-henselian-finite-etale-equivalence`,
`lem-weil-pbc-etale-ring-base-change`, and
`lem-weil-pbc-henselian-etale-retraction`.
`def-weil-pbc-flat-ring-map` remains used by the proved flatness subclaim.

Three old nodes are no longer needed on the route:
`lem-weil-pbc-criterion-flatness-fibre-noetherian`,
`lem-weil-pbc-finite-type-algebra-noetherian`, and
`lem-weil-pbc-noetherian-local-quotient-artinian-local`.
The last two are bypassed by the direct theorem `IsArtinianRing.of_finite`.
No unit realization or chapter route changes.

## Where the brief, the DAG or earlier work was wrong

The first worker's core node cited its own parent as both a statement and proof
dependency. That created a cycle and did not describe a genuine construction plan.
It now names the existing smaller dependencies of the original three construction steps.
Both original new docstrings were too short to let another worker reconstruct the proof.
They now give full proofs with sources. The original flatness hole was unnecessary:
Mathlib étale cancellation, smooth flatness and tensor-flatness suffice directly.
The old report incorrectly said that no imports were removed; the complete list is above.

## New nodes

`lem-weil-pbc-artinian-separable-residue-lift-core` is stated in
`lean/Sheaf/RingTheory/ArtinianSeparableResidueLiftCore.lean`. It isolates the unproved
construction without the flatness hypothesis or conclusion. Its DAG statement is
self-contained, its Lean statement is recorded verbatim, and its dependencies are acyclic.

`lem-weil-pbc-artinian-separable-residue-lift-flat` is stated and proved in
`lean/Sheaf/RingTheory/ArtinianSeparableResidueLiftFlat.lean`. Its DAG now records the
actual Mathlib tensor and étale-section argument, rather than the unused fibre criterion.
There are no interface change records.

## Second reading by X2

1. **Interface:** PASS. Compared every delivered module with the repository. Only the
   target module already exists; its signature is byte-for-byte identical, its original
   public imports are identical, and there are no altered definitions or forced adaptations.
   The two auxiliary modules and declarations are new. The construction theorem's
   unnecessary flatness hypothesis was removed before delivery.
2. **Proof and axioms:** PASS with the explicitly reported construction hole. All three
   files compile locally without errors or warnings. The target assembles every original
   conjunct. The sole sorry is the named construction theorem, with a full proof docstring
   and matching node. No axiom, unsafe, opaque, implemented_by or extern declaration occurs;
   no definition chooses data from an unproved existence theorem. A scratch copy prints
   axioms for all three declarations: the flatness lemma uses only standard axioms; the
   target and core also use sorryAx for the reported open construction.
3. **Split statements and searches:** PASS after repairs. For b in the base residue field
   (including b = 0), a universe lift of D itself is a witness of the core statement.
   For field extensions, D' = F(b) gives the expected finite separable extension. For
   nonreduced Artinian local rings, nilpotence makes the lifted field quotient the unique
   prime and henselianity supplies the prescribed residue map; no flatness is needed.
   Trivial rings are excluded by IsLocalRing's Nontrivial superclass. Flatness is verified
   by a kernel-checked proof that also works without locality, Artinianity or finiteness.
   Repeated searches with different wording using leanfinder, loogle and grep, and rg in
   lean/, found construction components but no duplicate complete capture theorem.
   Mathlib Etale.of_restrictScalars is the useful shorter route for flatness. The remaining
   core is a strict subargument, not the original assertion renamed: it omits flatness
   entirely and the delivered proof supplies that part independently with no new hole.
4. **Route and pruning:** PASS. Read the old proof plan and its imported declarations,
   and checked `dag/units/sk-thm-p1.json` and its realized statement and four steps.
   No realized unit step is bypassed or changed. Finite separable lifting and henselian
   factorization remain in the construction plan; only the below-unit flatness and
   Artinianity arguments are shortened. The complete removed-import and old-dependency
   inventory is above. New auxiliary imports in the target are plain proof-only imports.
5. **Nodes:** PASS after repairs. Existing-node edits are restricted to proof,
   proof_deps and proof_origin. New nodes have source, self-contained statement,
   statement dependencies, stepwise proof and its dependency union, proof origin,
   the required search records, creation and blueprint records, chapter, unit, and verbatim Lean
   signatures. The construction no longer depends on its parent. The flatness node agrees
   with its actual compiled proof, and the parent uses exactly the two new subclaims.

Second reading changed: closed the flatness hole; removed the core's unnecessary flatness
hypothesis; repaired the circular core node, proof plans, complete proof docstrings,
verbatim Lean records and search records; corrected the pruning and net-hole accounting;
removed the unnecessary provisional change record and local letI linter suppression.
Sources checked against [Stacks 07FI](https://stacks.math.columbia.edu/tag/07FI) and
[Stacks 04GK](https://stacks.math.columbia.edu/tag/04GK), together with the pinned Lean
sources. All checks and repairs were performed in this sandbox; no other agents were used.

The LeanSearch attempts for both new nodes returned Internal Server Error. They are
recorded as unavailable, without a search verdict; the working leanfinder, loogle and
grep searches and the direct pinned-source checks supplied the review evidence.
