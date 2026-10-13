## What changed

The signature of RingTheory.exists_stage_maximal_kernel_vanishes is unchanged.
Its proof uses finite kernel generators, finite-set descent, explicit
semilinearity of the tensor transition, and span induction. Its two new imports
are proof-only: Sheaf.RingTheory.FiniteTensorKernelGenerators and
Sheaf.RingTheory.FiniteIdealKernelDescent.

Four new modules implement smaller parts of the argument. FiniteTensorKernelGenerators
proves finite generation over the larger ring by two span inductions and
Noetherian finiteness of the multiplication kernel. FiniteIdealKernelDescent
proves finite-set descent from single-element descent: directedness supplies one
common index and tensor transition composition preserves the individual zeroes.
IdealKernelElementDescent proves single-element descent from finite relation
factorization by expanding a tensor as a finite sum and using tensor balancing.
ColimitFlatRelationDescent states the remaining finite-data descent of a trivial
relation; it has the only new sorry. All new imports used just in proofs are
non-public. No definitions, statement changes or adaptations were made.

The final route uses the existing equational flatness criterion (Stacks 00HK),
rather than exact tensor sequences and tensor-module colimits. All changed DAG
proofs and proof dependencies describe the actual Lean route.

## Proved and sorry left

Closed the item's one hole: RingTheory.exists_stage_maximal_kernel_vanishes
(node lem-weil-pbc-colimit-maximal-kernel-descent).

Three new statements are proved without sorry:
- RingTheory.exists_finite_tensor_kernel_generators
  (lem-weil-pbc-finite-tensor-kernel-generators).
- RingTheory.exists_stage_finite_ideal_kernel_vanishes
  (lem-weil-pbc-finite-ideal-kernel-descent).
- RingTheory.exists_stage_ideal_kernel_element_vanishes
  (lem-weil-pbc-ideal-kernel-element-descent).

The only sorry left or added is
RingTheory.exists_stage_flat_relation_factorization
(lem-weil-pbc-colimit-flat-relation-descent), exactly := by sorry.
This is a decomposition, not a net sorry reduction: one original hole closed,
one new hole added. The new hole asserts factorization of one finite module
relation at a later stage; it contains no ideal, tensor product, multiplication
kernel, kernel-generation or whole-kernel-vanishing conclusion. The complete Lean
proofs perform all of the tensor and finite-generation assembly.

All five modules compile cleanly with lcompile.py --all.

## No longer needed

No existing imports were removed (the original module's imports are statement
imports). The following original proof-dependency nodes are no longer needed by
this route, including transitively through the remaining relation-descent node:
- lem-weil-pbc-colimit-initial-full-subcategory: representatives are moved directly
  to a common stage above i; no restriction of the diagrams is constructed.
- lem-weil-pbc-filtered-colimit-modules-criterion: categorical ring and additive
  group representatives and eventual equality suffice; no module-colimit cocone
  over A_i is constructed.
- lem-weil-pbc-tensor-commutes-with-colimits: the tensor assembly uses finite sums
  and balancing, with no tensor-colimit comparison.
- lem-weil-pbc-flat-tensor-exact: the remaining finite relation uses the existing
  lem-weil-pbc-flat-equational-criterion instead.

These are Mathlib leaves and have no standalone Sheaf modules to retire here.
No unit statement or realized unit step is bypassed. No further module pruning
is claimed without the maintainer's target-closure calculation.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The original module did not import Sheaf
proof lemmas, and all its planned dependencies are Mathlib leaves. Their
signatures supply general tools but not the finite-data interfaces required by
the complete assembly. The finite-generation, finite-set and single-element
interfaces are all proved in this delivery.

Read the official Stacks proofs at https://stacks.math.columbia.edu/tag/00R6
and https://stacks.math.columbia.edu/tag/00HK. The source tex file named in the
original node is absent on this machine. 00HK is equivalent to the flatness
input in the original tensor argument, so it keeps the unit route while pruning
the tensor-colimit machinery below the unit level.

Searches are recorded in searches.jsonl: LeanSearch was unavailable; LeanFinder,
Loogle and grep were used. Mathlib's tensor finiteness theorem assumes both
factors finite over the same ring and does not directly prove finiteness over B;
the explicit span argument supplies that missing glue. The upstream
exists_finset_lTensor_eq_zero concerns base-change modules over subalgebras of a
fixed ring and does not apply to these arbitrary varying modules.

An attempted proof of the remaining relation statement reached Mathlib's
isTrivialRelation_of_sum_smul_eq_zero, but the direct calls to
Concrete.colimit_exists_rep did not synthesize
PreservesColimit A (forget CommRingCat) or
PreservesColimit N (forget AddCommGrpCat). The item has independent index, ring
and group universes; the standard filtered-colimit instances inspected here
work with bounded diagram universes. The remaining node includes this universe
management and the finite representatives/equation descent. No universe binder
or smallness hypothesis was changed or added to conceal that obligation. A
scratch attempt is kept outside lean/ and is not part of the delivery.

Edge cases: the empty finite kernel subset is handled by the proved common-bound
construction at i and its canonical tensor map. The zero tensor, zero ideal and
zero module are covered by the finite sum and span proofs. Empty row and column
types in relation factorization are allowed. No locality of transitions,
injectivity, tensor base-change, nontriviality or Noetherian hypothesis is added.
Kernel generators are chosen from a proved theorem, and all tensor maps used in
public proofs are constructed from TensorProduct.map. No data is defined from
an arbitrary unproved witness.

## New nodes

lem-weil-pbc-finite-tensor-kernel-generators, module
Sheaf.RingTheory.FiniteTensorKernelGenerators: proved general-ideal version of
original step 2, independent of colimits and flatness.

lem-weil-pbc-finite-ideal-kernel-descent, module
Sheaf.RingTheory.FiniteIdealKernelDescent: proved passage from individual witness
stages to one common stage, with explicit ideal-map and tensor-map composition.

lem-weil-pbc-ideal-kernel-element-descent, module
Sheaf.RingTheory.IdealKernelElementDescent: proved passage from finite relation
factorization to vanishing of one specified tensor using finite sums and balancing.

lem-weil-pbc-colimit-flat-relation-descent, module
Sheaf.RingTheory.ColimitFlatRelationDescent: the remaining hole, using 00HK and
descent of finitely many coefficients, vectors and equations in ring and group
colimits. It cannot alone assert whole-kernel vanishing. It is strictly part of
the argument and contains no tensor statements. No change records or forced
adaptations are needed.

## Second reading by G1

1. I compared every delivered Lean module with the repository version. The original theorem signature and all existing declarations are byte-for-byte unchanged; only proof bodies, proof-only imports, and the listed new modules/nodes differ.

2. I compiled all five sandbox modules with `lcompile.py --all`; they compile successfully. A search found one and only one remaining `sorry`, the named theorem `RingTheory.exists_stage_flat_relation_factorization`; there are no axioms, unsafe declarations, opaque definitions, externs, or implemented_by declarations. The remaining sorry is a public named theorem with a source docstring and matching DAG node, and no definition contains sorry.

3. I checked the new statements against their signatures and edge cases. The three auxiliary statements are strictly smaller than the item theorem and are used by it. The remaining finite-relation statement has no tensor, ideal, Noetherian, local, injectivity, or nontriviality conclusion and does not merely restate the item. No duplicate declaration was found in the library or Mathlib searches recorded by the worker.

4. The proof follows the unit route through finite tensor-kernel generators, finite ideal-kernel descent, and single-element descent. The route is then assembled by tensor commutativity and span induction. The report's four no-longer-needed proof dependencies are absent from the actual imports and DAG proof dependencies; no unit statement or realized step is bypassed.

5. The DAG proof, proof dependencies, proof origins, Lean declarations, and new-node metadata agree with the proof text and module files. The finite-relation node records its split theorem and complete natural-language proof plan.

I changed only this second-reading section of the report. No Lean source, statement, definition, or DAG record required repair.

Additional verification: the scratch `#print axioms` probe for all five public theorems reports only `propext`, `Classical.choice`, `Quot.sound`, and (for the four declarations depending on relation descent) `sorryAx`. Finite kernel generation has no `sorryAx`. I independently searched with LeanFinder for finite equation descent, Loogle for `IsTrivialRelation`, and grep for flat colimit relations. The matches were the equational flatness criterion and fixed-ring direct-limit representatives/eventual-zero lemmas, not an existing theorem with this varying-ring categorical stage-descent signature. The empty-row case permits `m=0`; zero coefficients permit a finite list of the original vectors with an identity matrix; both are consistent with the remaining statement. The `sk-thm-p1` realized statement and steps were read and none is pruned by this below-unit change.
