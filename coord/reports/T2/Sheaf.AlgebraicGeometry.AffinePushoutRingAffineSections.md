## What changed

The existing theorem `AlgebraicGeometry.Scheme.Modules.affine_pushout_ring_affine_sections`
keeps its signature and docstring verbatim. Its proof now constructs the canonical tensor
section map, proves surjectivity from finite-product generation, combines it with a separate
injectivity obligation, and transports `CommRingCat.isPushout_tensorProduct` across the resulting
ring equivalence. Its three new imports are proof-only.

Added `AffinePushoutRingSectionDelta` and `AffinePushoutRingSectionComm` for the explicit
second leg and the adjunction/naturality proof of section commutativity.
`AffinePushoutRingSectionMap` constructs the tensor map by `IsPushout.desc`, and
`AffinePushoutRingSectionMapTmul` proves its pure-tensor formula.
No data is chosen from an unproved theorem. The two remaining mathematical obligations are
stated in `AffinePushoutRingSectionMapInjective` and `AffinePushoutRingSectionProducts`.
Each has a source, complete proof in words, and a node.

## Proved and sorry left

Closed the original direct hole in
`AlgebraicGeometry.Scheme.Modules.affine_pushout_ring_affine_sections`.
Added exactly two direct holes:

- `AlgebraicGeometry.Scheme.Modules.affinePushoutSectionMap_injective`, node
  `stage3-affine-pushout-ring-section-map-injective`;
- `AlgebraicGeometry.Scheme.Modules.affinePushoutSection_products`, node
  `stage3-affine-pushout-ring-section-products`.

This is a decomposition, not a completed proof of the mathematical result: one baseline hole
closed, two holes added, direct net minus one. The target still depends on `sorryAx` through
these named obligations. The second leg, section-square commutativity, tensor map construction,
pure-tensor formula, finite-product-to-surjectivity reduction, and pushout transport are proved.
No other direct sorry occurs in the delivered modules. Closure and whole-library progress
figures remain the maintainer's pinned-baseline sorry ledger's responsibility.

## No longer needed

No original module import is removed, and no original dependency is mathematically pruned.
The old planned nodes `lem-weil-pbc-affine-module-tensor-base-change`,
`lem-weil-pbc-module-pullback-affine-sections`, and `pqf-lem-pushforward-qcoh` remain the
proof dependencies of both smaller obligations. They are not direct Lean proof imports of
the target. The target node's new proof dependencies are the constructed-map, commutativity, pure-tensor, injectivity,
and product-generation nodes; their uses agree with its new three proof steps.

The first worker's undelivered `AffinePushoutRingAffineSectionsComparison` module and
`stage3-affine-pushout-ring-affine-sections-comparison` node were removed from this sandbox.
They were never in the repository and their removal is not library pruning. Unused general imports were omitted from the new second-leg, commutativity, and tensor
modules; the two affine-specific theorem modules
import it publicly because their signatures need it.

## Where the brief, the DAG or earlier work was wrong

The first worker left an isomorphism with both leg equations as its sole new hole. This is
equivalent to the original ring pushout by uniqueness of pushouts, so its final transport
alone was not a valid split. The first report also called that a proved target, omitted net
hole accounting, and the new node had only one search kind and a placeholder Lean signature.
Its changed existing node was outside `dag/nodes/`, so deliver3.py would not deliver it; its
proof_deps also failed to equal the union of the listed proof-step uses. These faults are repaired.

The replacement obligations are individually strictly weaker: product generation asserts only
existence of additive product presentations, while injectivity asserts only uniqueness of tensor
preimages. Neither alone asserts the ring pushout or a comparison isomorphism. Their combination
is a decomposition, transparently recorded above. Mathlib and the upstream/project sources
were searched for the canonical tensor map, its kernel, and affine product generation.
LeanFinder found neighbouring scheme-section and spectrum results, grep found sheaf tensor
machinery and the commutative-ring tensor pushout, and LeanSearch returned Internal Server
Error. The existing `affine_pushout_ring_section_presentation` proves product generation for a
chosen leg and counit, but imports and applies this item; using it here would create an
import and proof cycle. No independent existing declaration states either remaining obligation. Both follow the original
regular-module and affine section route of Tags 01SB, 01I9, 01IA and 01HV.

## New nodes

`stage3-affine-pushout-ring-section-map` records the explicit tensor-map construction
from the proved section-square commutativity. Its Lean record names
the map declaration and contains its exact signature.

`stage3-affine-pushout-ring-section-map-injective` records only injectivity of that constructed
map, with the regular-module specialization and affine comparison argument written out.

`stage3-affine-pushout-ring-section-products` records only existence of finite sums of products
of the two legs, using surjectivity of the affine module comparison and finite pure-tensor
presentations. All six new nodes have real recorded searches of three kinds (LeanSearch was
unavailable), exact Lean signatures, inherited chapter/unit, and the original blueprint ancestor.
`stage3-affine-pushout-ring-section-delta`, `stage3-affine-pushout-ring-section-comm`, and
`stage3-affine-pushout-ring-section-map-tmul` record the second leg, the commuting-square theorem,
and the pure-tensor formula, respectively. Each new statement has its own module and node.
There are no interface change records because no existing signature, definition, or public import
changed.

## Second reading by T2

1. Compared the existing delivered module with the repository by diff and declaration parsing.
   Verdict: the existing statement is byte-for-byte identical; its existing docstring and public
   imports also remain identical. Only proof imports and the proof body change. No target or
   existing definition changes.
2. Read every delivered definition and proof. Verdict: constructions are explicit, with their
   required proofs named and proved; the only direct sorries are the two public named theorems
   listed above. No axiom, unsafe, opaque, extern, implemented_by, or kernel bypass occurs.
   All seven modules compile locally without errors or warnings. The scratch `#print axioms` inspection shows only propext, Classical.choice, and Quot.sound
   for the two definitions and two compatibility proofs; the two named obligations and the
   target additionally use sorryAx. The delivery tool also probes every declaration.
3. Read and checked both split statements and their source arguments. Verdict: each is true,
   needed, and strictly a part of the argument. Tested the identity morphism (the tensor map
   is multiplication C tensor_C C → C), zero rings, and empty affine opens (all relevant
   section and tensor rings are zero). No domain, nonzero-ring, finite-type, or nonempty
   condition is required. The finite-product claim makes no uniqueness assertion; injectivity
   makes no existence assertion. Independent alternate-word searches found no duplicate.
4. Checked the proof from the target down. Verdict: the formal ring pushout and transport use
   existing Mathlib; the remaining work is exactly the two sheaf-theoretic parts. There are
   no unused proof imports or unreported original dependencies removed. The record
   `dag/units/sk-thm-p1.json` and its realized statement/steps are untouched; the regular-module
   route remains in the lower nodes, and no unit step is bypassed.
5. Compared all node records with the Lean and proof. Verdict: the existing node is now in the
   delivered path; its proof_deps are exactly the union of its proof-step uses. Every new
   statement has its exact signature, source, proof in words, node, and search records. The
   two remaining theorem nodes retain the three original planned dependencies. No statement
   change or forced adaptation is claimed.

Second reading changed: replaced the equivalent comparison hole with an explicit tensor map,
proved its compatibility and pure-tensor formula, split injectivity and finite-product generation, separated each new statement into its own module,
and repaired node paths, dependency accounting, exact signatures, searches, imports, and report.
