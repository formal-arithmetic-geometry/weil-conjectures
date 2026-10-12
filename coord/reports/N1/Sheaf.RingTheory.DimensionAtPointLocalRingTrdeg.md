## What changed

Replaced the item's `sorry` with a reduction to the existing
`AlgebraicGeometry.dimension_at_point_components` and the new ring-theoretic lemma
`AlgebraicGeometry.minimal_component_dimension_maximum` in
`Sheaf.RingTheory.MinimalComponentDimensionMaximum`. The latter computes bounds and
attainment of the dimensions of minimal-prime quotients, without mentioning topological
dimension. The target combines the two sets of bounds by antisymmetry.

The finiteness witnesses now come entirely from Mathlib: finite type implies Noetherian,
a Noetherian local ring has finite Krull dimension, and an essentially finite type residue
field has finite transcendence degree (`FinTrdeg`, `trdeg_lt_aleph0`). The original public
imports and existing target signature are unchanged. Added proof-only imports for
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem`, `Mathlib.FieldTheory.FinTrdeg`, and the new lemma.
Updated the target node's proof route and added the new lemma's complete node.
No existing statement or definition changes; no change record is needed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.topologicalKrullDimAt_eq_ringKrullDim_add_trdeg`.
Added one hole:
`AlgebraicGeometry.minimal_component_dimension_maximum`, node
`lem-weil-pbc-minimal-component-dimension-maximum`, in the new module.
No other declaration in the delivered modules contains `sorry`.

This is a decomposition: one baseline hole closed, one hole added, net zero holes closed.
The topological reduction is complete, but it still depends on the open component theorem
and the new ring-theoretic chain lemma. It is not claimed as an axiom-free final theorem.
Relative to the first worker's sandbox, eliminated both auxiliary holes:
`AlgebraicGeometry.exists_ringDimAtPrime_and_residue_trdeg` is replaced by Mathlib proofs;
`AlgebraicGeometry.topologicalKrullDimAt_eq_add_of_local_and_residue` is replaced by a genuine
reduction using the existing component theorem and one strictly ring-theoretic hole.

## No longer needed

Removed the direct proof imports
`Sheaf.RingTheory.FiniteTypeDomainDimensionLocalRing`,
`Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg`, and
`Sheaf.RingTheory.LocalizationPrimeResidueFieldIso` from the target module.
They remain proof dependencies of the new ring-theoretic chain lemma and thus stay in
its import closure; no repository module or node is globally pruned.

Of the old target `proof_deps`, the following are no longer direct dependencies, and are
all retained inside the new lemma's chain argument:
`lem-weil-pbc-finite-type-domain-dimension-trdeg`,
`lem-weil-pbc-finite-type-domain-dimension-local-ring`,
`lem-weil-pbc-noetherian-finitely-many-minimal-primes`,
`lem-weil-pbc-prime-contains-minimal-prime`,
`lem-weil-pbc-localization-prime-residue-field-iso`, and
`lem-weil-pbc-localization-dimension-chains-below-prime`.
The target still directly uses `lem-weil-pbc-finite-type-algebra-noetherian` and
`lem-weil-pbc-dimension-at-point-components`.

Removed the undelivered `DimensionAtPointLocalRingTrdegAux` module and incomplete
`aux-dimension-formula` node. These are first-worker artifacts, not repository pruning.

## Where the brief, the DAG or earlier work was wrong

The first worker left two auxiliary holes but recorded only one, incomplete, new node;
both docstrings pointed to the target node instead of their own nodes. Its target node
still described the old proof rather than its applications of the auxiliary declarations.
Its formula auxiliary essentially rephrased the difficult conclusion after supplying
finiteness. The repair exposes a ring-only chain calculation and actually invokes the
already-stated component theorem to obtain the topological formula.

The first worker missed Mathlib's Noetherian-local finite-dimension instance and
`FinTrdeg` instance for essentially finite type field extensions. There is no need to
postpone either finiteness assertion. The source proof itself is correct; it was read in
`/home/ubuntu/work-bp/sheaf/literature/stacks-project/algebra.tex`, lines 28222--28267.

## New nodes

`lem-weil-pbc-minimal-component-dimension-maximum` records precisely the ring-theoretic
prime-chain part of Stacks Tag 00P1. Its docstring gives the full argument: identify r
using S/p, choose chains below and above p, compute the local maximum d, concatenate,
and apply the finite-type domain maximal-chain theorem. The node has its own blueprint
id, signature, source, proof steps, dependency union, origin, searches, creation record,
chapter, unit and Lean record. Searches were run through msearch.py: LeanSearch was
unavailable (HTTP internal server error), LeanFinder and grep returned height and
height/coheight results but no matching maximum formula; Loogle also returned no match.
No change records.

## Second reading by N1

1. Compared the delivered target module with the repository version using `diff` and
   an exact substring comparison of the declaration signature: byte-for-byte unchanged.
   No existing definitions changed; no other existing module is delivered. PASS.
2. Both modules compile locally in import order with lcompile.py, without errors or
   unexpected warnings. Exactly one `sorry`, as the whole proof of the public named new
   theorem. No definitions, axiom/unsafe/opaque/implemented_by/extern escapes, or data
   chosen from an unproved existence theorem. Scratch `#print axioms` checks of both
   declarations show only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   PASS as a decomposition with explicitly reported open dependencies.
3. Checked the new statement against the source chain proof and its edge cases:
   S=k gives d=r=0 and the zero minimal prime; S=k[t] at (0) gives d=0,r=1;
   at (t) gives d=1,r=0; nonreduced S=k[e]/(e^2) gives d=r=0.
   Components of different dimensions, e.g. a plane and a line meeting at a closed
   point, explain why a bound for every component plus attainment is required, rather
   than equality for every component. The zero ring has no prime and is excluded by
   p.IsPrime. The new lemma is true, strictly ring-theoretic, and exactly supplies the
   two inequalities the target needs. Searched Mathlib, upstream and lean/Sheaf by
   height, coheight, minimal component, localization and transcendence degree; no
   matching statement was found. The docstring and node now meet the contract. PASS.
4. Replaced the finiteness hole with the shorter Mathlib route. Kept the source's
   minimal-prime chain argument and the existing topological component theorem.
   Removed unused direct proof imports; listed every old dependency moved under the
   new lemma. Read dag/units/sk-thm-p1.json: this is a tool node below the unit's realized
   statements and steps. No unit step or chapter route is bypassed or changed. PASS.
5. Target proof/proof_deps/proof_origin now follow the Lean reduction. The new node's
   statement matches the Lean theorem; proof_deps is exactly the union of step uses;
   all required new-node metadata and genuine search records are present. PASS.

Changed on second reading: proved finiteness via Mathlib, replaced the two-hole auxiliary
wrapper with one ring-only chain hole and a real component-theorem reduction, corrected
all DAG and docstring metadata, pruned unused direct imports, and rewrote the report to
state the closed/added holes and decomposition honestly.
