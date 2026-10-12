## What changed

Replaced the first worker's invalid whole-target replacement with a real reduction.
`ResidueFieldTowerSystem` now constructs the initial stage as `ULift R`, applies the
existing `flat_local_tower_directLimit` to each nonempty chain, adjoins the requested
field element by a one-element extension, and explicitly verifies the upper cocone,
flatness, maximal-ideal, kernel and composite conditions. A generic compatible-diagram
recursion theorem then assembles the tower, and the designated-stage witness proves
coverage. The existing target signature and public imports are unchanged.

Deleted the proposed `ResidueFieldTowerSystemData` and `ResidueFieldTowerSystemCoverage`
modules and their new nodes. Added proof-only imports of `FlatLocalMonogenicExtension`
and `CompatibleRingTowerRecursion`. Restored the original proof-only import of
`FlatLocalTowerDirectLimit`; its theorem is essential to the repaired proof.

## Proved and sorry left

Hole closed: `IsLocalRing.exists_residue_field_tower_system` has a complete Lean proof
term, conditional on the two strictly simpler statements below. This is a decomposition,
not a completed axiom-free proof: one existing hole closed and two new holes added,
for net -1 before any pruning is counted.

Holes added and left:
- `IsLocalRing.exists_flat_local_monogenic_extension`
  (`new-flat-local-monogenic-extension`): construction of one flat local extension
  containing a prescribed element, with no tower or recursion conclusion.
- `IsLocalRing.exists_compatible_ring_tower`
  (`new-compatible-ring-tower-recursion`): generic coherent recursion assuming an
  initial good object and the already established upper-extension operation for
  every nonempty chain. It makes no assertion of locality or flatness.

No other holes remain in the delivered sources. The deleted proposed data hole did
not occur in the repository baseline, so deleting it is not counted as a hole closed.
The first worker's coverage lemma was already proved; the old report incorrectly
listed it as sorry. Each remaining sorry is exactly a named theorem, with its source,
a complete natural-language proof, and its matching new DAG node.

## No longer needed

No repository import is removed. In particular `FlatLocalTowerDirectLimit` is retained.
The two proposed data/coverage imports, modules and nodes were removed before delivery.
The following old direct proof dependencies are no longer direct dependencies of the
item (several remain needed in the new monogenic/recursion nodes' proof plans):
- `def-weil-simple-field-extension`
- `def-weil-algebraic-element`
- `def-weil-polynomial-ring`
- `def-weil-pbc-localization-at-prime`
- `def-weil-pbc-free-module`
- `lem-weil-pbc-projective-module-flat`
- `lem-weil-pbc-localization-flat`
- `def-weil-pbc-separable-algebraic-extension`
- `lem-weil-pbc-monic-quotient-free`
- `lem-weil-pbc-simple-algebraic-extension-power-basis`
- `lem-weil-pbc-finite-algebra-local-radical`
- `lem-weil-pbc-filtered-colimit-algebras-elementwise`
- `lem-weil-pbc-well-ordering-theorem`
- `lem-weil-pbc-transfinite-recursion`

No module is claimed globally pruned: the downstream dependency closure still uses
the monogenic and transfinite ingredients.

## Where the brief, the DAG or earlier work was wrong

The first worker's data theorem repeated the whole item and strengthened its final
clause to a designated-stage preimage. Applying it and weakening that clause was not
a genuine reduction. Its claim to have isolated coverage was misleading, and the
coverage theorem had many irrelevant hypotheses. Both proposed modules were removed.
The repaired reduction follows the original plan's monogenic, direct-limit and
coherent-recursion steps. The stored unit `sk-thm-p1` and all its `realized` fields are
unchanged; this node is below that unit's designated statement/step nodes.

## New nodes

`new-flat-local-monogenic-extension` isolates Tag 03C3's first paragraph. The statement
asserts the single-step construction and records all compatibility needed by the
upper-cocone proof. Its natural-language proof treats both transcendental and algebraic
cases. No data definition is selected from its unproved existence assertion.

`new-compatible-ring-tower-recursion` isolates the coherent-recursion mechanism of
Tag 03C3's fourth paragraph, parametrized by an arbitrary predicate on ring stages.
Its hypotheses contain the already verified upper-extension operation. Its docstring
specifies fixed record choices, the default branch, well-founded recursion and the
induction proving coherence, including empty and initial-stage cases.

No existing statement or definition changed; no change record is required.

## Second reading by V2

1. Compared the delivered target module against the read-only repository with `diff`
   and independently checked its declaration signature as an exact byte string.
   Verdict: the existing signature, universe binders, namespace, visibility and public
   imports are unchanged. No public definition changed. The two new modules state
   new intermediate theorems; no change record or forced adaptation is needed.
2. Compiled every delivered module through `lcompile.py` in import order, without
   errors or warnings. Scratch copies with `#print axioms` showed only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The only textual sorries are the
   two named new theorems reported above. There are no data definitions, forbidden
   declarations or attributes, or inline proof holes. Verdict: valid conditional
   proof/decomposition, with the two remaining obligations explicitly identified.
3. Read both intermediate statements and their full docstring arguments against
   Stacks Tag 03C3. Checked x = 0 and x already in the image (degree-one quotient),
   algebraic and transcendental x, and the recursion's empty, singleton and limit
   index cases. Both are true: the monogenic lemma is just the successor construction;
   the recursion lemma assumes the chain-extension operation and only organizes
   coherent choices. LeanSearch was tried but returned Internal Server Error;
   independent LeanFinder/Loogle searches and source/blueprint searches found no
   matching theorem. Inspected Mathlib's WellOrderInductionData and DirectedInverseSystem
   interfaces: they supply machinery but do not specialize to the variable-carrier
   diagram assertion in one line. Verdict: strictly separate, needed intermediate
   obligations with sources, proofs in words, nodes and honest search records.
4. Read the original DAG plan and unit `dag/units/sk-thm-p1.json`, including `realized`.
   The repaired proof follows monogenic extension, the existing direct-limit result,
   and coherent transfinite recursion; it does not bypass a designated unit step.
   Checked imports and removed an experimentally added redundant Algebra.Equiv import.
   `No longer needed` now enumerates every old direct proof dependency omitted from
   the target node, while explicitly retaining dependencies of the new lower nodes
   and making no unsupported global pruning claim. Verdict: route retained and
   imports match the actual proof.
5. Checked node statement/signature records against Lean and the existing node's
   `proof`, `proof_deps`, `proof_origin` against the repaired proof. Both new nodes
   include the source, complete natural-language argument, dependency union, search
   records, creator, blueprint ancestry, chapter, unit and Lean record. Existing node
   changes are confined to stage-3-owned fields. Verdict: metadata agrees with Lean.

Changed: removed the whole-target data restatement and trivial coverage module/nodes;
replaced them with a genuine one-element-extension/coherent-recursion decomposition;
proved the initial lifted stage and chain upper-cocone properties in the target using
`flat_local_tower_directLimit`; restored that import; corrected the dependency pruning
list, hole accounting and report; removed a redundant proof import. No existing
statement or definition was altered.
