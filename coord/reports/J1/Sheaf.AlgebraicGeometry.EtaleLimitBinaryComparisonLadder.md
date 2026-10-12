## What changed

Replaced the earlier degree-case renaming with a construction/algebra decomposition.
The existing signature, visibility, public imports and docstring of
`AlgebraicGeometry.Etale.etale_limit_binary_comparison_ladder` are unchanged.
The proof now obtains pointwise exact natural transformations on a directed tail,
proves exactness of their filtered colimit maps by representatives, transports the
middle term across the cofinality isomorphism, and applies continuity to certified
neighboring comparisons. The supplied bottom restriction remains the actual map
on the two inverse-image opens.

Added `StageCohomologyComparison.lean`, an inductive proposition recording canonical
comparison systems and their transports and products. Its system constructor includes
all the actual scheme-limit, coefficient-coherence, sheaf-colimit, stage-isomorphism,
and canonical-cohomology-cocone data. It contains no cohomology colimit proof.
Added `StageCohomologyComparisonBijective.lean`, whose theorem proves by induction
that continuity on the allowed stages makes every certified comparison bijective.
Added `EtaleLimitBinaryGeometricLadder.lean`, the remaining geometric construction:
it assumes no stage continuity and supplies pointwise exact diagrams, their cofinality
isomorphism, neighboring comparison certificates, bottom exactness and naturality
squares. It does not supply colimit exactness or bijectivity. These two parts are
proved in the delivery and are not restatements of its remaining hole.

The private `colimMap_apply_ι`, `exact_colimMap`, and `exact_transport_middle` helpers
are fully proved. The representative argument works with the index in universe u
and groups in universe u+1; it explicitly installs the smaller filtered-colimit
preservation instance rather than using an incompatible same-universe AB instance.
The existing node's proof route is updated, and every new node has its verbatim
signature extracted from the actual Lean declaration.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.Etale.etale_limit_binary_comparison_ladder`.

Proved without a new hole:
`AlgebraicGeometry.Etale.StageCohomologyComparison.bijective`, and the three private
helpers named above.

Added exactly one hole:
`AlgebraicGeometry.Etale.etale_limit_binary_geometric_ladder`, node
`lem-weil-pbc-etale-limit-binary-geometric-ladder`.
Its entire proof is `:= by sorry`, with the construction, literature source and edge
cases in its own docstring. No sorry remains in the item's module or in either
certificate module. This is a decomposition (one closed, one added, net zero), not
an independently complete proof of the geometric result.

The previous unlanded specialized zero and positive modules and nodes have been
removed from the sandbox's delivery set; neither is a dependency of this proof.

## No longer needed

Removed these direct proof imports from the item's module:

- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`
- `Sheaf.AlgebraicGeometry.EtaleMayerVietoris`
- `Sheaf.AlgebraicGeometry.EtaleMayerVietorisPullback`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

The first four remain proof dependencies of the geometric construction, so their
modules and corresponding nodes are retained through its imports. UpperLowerStar.Defs
is already available transitively through the public coefficient-system imports;
its inverse-image-composition node remains needed by the construction. No original
planned node or module is claimed globally pruned. The original node now depends
on the geometric construction and certificate bijectivity, with its algebraic
representative chase completely implemented locally. The failed unlanded nodes
`lem-weil-pbc-etale-limit-binary-comparison-ladder-zero` and
`lem-weil-pbc-etale-limit-binary-comparison-ladder-positive`, and their specialized
modules, are unused and not delivered.

The complete audit of the old direct `proof_deps` is:

- `def-weil-pbc-etale-cohomology-stage-continuity`: still used in the original signature and in certificate bijectivity.
- `def-weil-pbc-scheme-conventions`: moved to the geometric construction; still needed transitively.
- `lem-weil-pbc-cohomology-pullback-functorial`: moved to the geometric construction; still needed transitively.
- `lem-weil-pbc-colimit-initial-full-subcategory`: moved to the geometric construction; still needed transitively.
- `lem-weil-pbc-etale-inverse-image-restriction`: moved to the geometric construction; still needed transitively.
- `lem-weil-pbc-etale-mayer-vietoris`: moved to the geometric construction; still needed transitively.
- `lem-weil-pbc-etale-mayer-vietoris-pullback`: moved to the geometric construction; still needed transitively.
- `lem-weil-pbc-filtered-colimit-abelian-groups-exact`: replaced by the proved representative argument; this DAG dependency is no longer needed.
- `lem-weil-pbc-filtered-colimits-commute-finite-limits`: moved to the geometric construction; still needed transitively.
- `lem-weil-pbc-inverse-image-composition`: moved to the geometric construction; still needed transitively.
- `lem-weil-pbc-left-adjoint-preserves-colimits`: moved to the geometric construction; still needed transitively.
- `lem-weil-pbc-limit-cone-affine-projections-opens`: moved to the geometric construction; still needed transitively.

No module is globally pruned: the exactness node is a Mathlib match, not a separate Sheaf module.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's node signatures contained ellipses rather than actual Lean
signatures, its declaration docstrings carried the parent blueprint id, and its
new nodes cited the parent theorem, creating a circular proof route. Its report
also included a second-reading section written before an independent reading.
All of these artifacts are replaced; the second reader's section is left to that
reader. A degree split alone did not discharge geometric construction, continuity,
or colimit exactness. The replacement actually proves the latter two operations.

Read Tags 0A50 (lemma-mayer-vietoris) and 09YQ (theorem-colimit) in the available
local Stacks source at `/home/ubuntu/c1-stacks-review/etale-cohomology.tex`.
Their repository literature path is absent on this machine. The raw construction
is the parent node's agent-expanded geometric restriction argument; it is not
claimed to occur verbatim in Tag 09YQ's proof, which instead invokes affine sites.

For the raw node, checked degree zero, empty opens and coincident opens: degree
zero uses zero functors and initial restriction injectivity; empty opens give zero
factors; coincident opens give diagonal and difference maps. The raw node assumes
no ambient quasi-separatedness, and its intersection compactness comes from the
qcqs union stage. Connecting maps must be chosen as simultaneous natural
transformations, not unrelated existential witnesses at each stage. The three
allowed-stage continuity hypotheses enter only the proved certificate argument.
No unit statement or realized unit step is bypassed or changed.

The dependency audit found no cycle containing any delivered node. It also found
a pre-existing cycle between `lem-weil-pbc-sheaf-algebraic-structures-objects` and
`lem-weil-pbc-sheaf-algebraic-structures-abelian-component` in the inherited
cohomology-definition closure; both edges are already present in the read-only
base. Those nodes are outside this item's ownership and are unchanged. The Lean
import-cycle gate passes.

All four delivery modules compile without warnings. The delivery dry run passed
compilation, the axiom probes and static preflight; its only pending requirement
is the independent second reading, which its OK message explicitly leaves to
the second reader. No delivery was pushed.

LeanFinder and grep found related tools but no exact construction or certificate.
LeanSearch returned HTTP 500 and is recorded as unavailable, not as no match.
Blueprint searches for stage-cohomology comparisons and geometric ladders found
no duplicate blueprint node. There are no existing-interface changes or forced
adaptations and therefore no change record is required.

## New nodes

`def-weil-pbc-stage-cohomology-comparison` records the supplied-system certificate
proposition, in `Sheaf.AlgebraicGeometry.StageCohomologyComparison`. It makes no
choice of an object from an existence theorem and contains no sorry.

`lem-weil-pbc-stage-cohomology-comparison-bijective` records the fully proved
induction applying stage continuity and colimit universal properties, in
`Sheaf.AlgebraicGeometry.StageCohomologyComparisonBijective`.

`lem-weil-pbc-etale-limit-binary-geometric-ladder` records the only remaining hole,
in `Sheaf.AlgebraicGeometry.EtaleLimitBinaryGeometricLadder`. It is the independent
construction of the restricted geometric systems and their pointwise exact
Mayer--Vietoris diagram, before the two colimit-exactness and continuity arguments.

## Second reading by J1

1. **Existing interface: pass.** Read the complete diff against the read-only
   repository. The only existing declaration is
   `AlgebraicGeometry.Etale.etale_limit_binary_comparison_ladder`; its complete
   signature and docstring are byte-for-byte identical, and its visibility and
   three public imports are unchanged. The other three modules and their nodes
   are new. The existing node changes only `proof`, `proof_deps`, `proof_origin`.
   There is no interface change or forced adaptation requiring a change record.
2. **Proof and data audit: pass.** Read both directions of the representative
   exactness argument, its naturality rewrite and transport through the middle
   isomorphism, and the induction on comparison certificates. There is one
   explicit hole, exactly the named geometric theorem reported above. There
   are no forbidden declarations, options, attributes or holes in definitions.
   The inductive certificate records supplied data without choosing any witness;
   the geometric existential is eliminated only in a proof of a proposition.
   The original four-module compilation passed without warnings. Final
   compilation and axiom-probe results are recorded below.
3. **Split-off statement: pass as decomposition.** Independently checked the
   geometric statement against the natural-language node and construction in
   its docstring. It assumes no continuity and supplies pointwise exact natural
   transformations and comparison certificates; it supplies neither colimit
   exactness nor comparison bijectivity. Those two operations are proved in the
   delivery, so this is a real reduction, with one closed hole and one added
   hole, net zero. Read the local Stacks proofs of Tags 0A50 and 09YQ and the
   existing Mayer--Vietoris, pullback and canonical-cohomology-diagram modules.
   A future proof must construct the connecting transformations simultaneously
   from resolutions, with coefficient and pullback naturality; pairwise
   existential connecting maps cannot simply be chosen independently.
   For p=0 the first two stage functors and bottom groups are zero and the
   degree-zero restriction is injective. Empty opens give zero factors;
   coincident opens give diagonal/difference sequences. The intersection is
   compact inside the qcqs union stage, so no quasi-separatedness of X is
   silently required. A one-point index recovers the usual Mayer--Vietoris
   sequence. No small-case counterexample was found. Independent LeanFinder
   search `inverse system schemes open cover natural cohomology boundary
   comparison diagram`, Loogle search `Function.Exact`, and grep of the
   library and Mathlib found related constructions and universal-property
   tools, but no duplicate geometric statement or certificate. The remaining
   geometry is substantial and cannot be closed in a few minutes.
4. **Route and pruning: pass after report repair.** The proved helpers use
   Mathlib representatives and colimit equations directly. Mathlib's AB
   instance uses the same-universe index/category convention; the local proof
   explicitly handles the required groups in u+1 and indices in u.
   The remaining geometry retains the original restriction/Mayer--Vietoris
   dependencies. Read `dag/units/sk-thm-p1.json` and its `realized` mapping:
   no realized unit step is removed or bypassed. Added the complete list of
   old direct proof dependencies under `## No longer needed`, distinguishing
   relocation from the exactness node replaced by the proved helper. No
   globally unreachable module is claimed pruned.
5. **Node agreement: pass.** Checked all four nodes, their statements,
   source references, proof steps, Lean records and dependencies. Every
   `proof_deps` is exactly the union of step `uses`; every dependency resolves
   in the base plus delivery; no delivered node lies on a dependency cycle.
   New theorem signatures match the Lean after whitespace normalization;
   the definition record contains its complete inductive header, whose
   constructors were checked against its natural-language statement.
   All new nodes contain creation, blueprint, source and three search records.

Second-reading changes: replaced the certificate module's public import of
stage continuity by the direct upstream module needed for its geometric data;
imported stage continuity explicitly and publicly in the bijectivity module,
whose theorem signature actually needs it; removed the redundant public
continuity import from the geometric module. No theorem statement or proof
was changed. Completed the old-node pruning audit in this report. All Lean
lines remain at most 100 characters.

Final local validation: the corrected four-module set compiles without warnings
(49.0, 18.3, 9.5 and 23.9 seconds). One earlier run of the certificate module
hit the 60-second timeout; a single-file check and the final set both passed
without a code workaround. Explicit scratch-copy `#print axioms` probes passed:
`StageCohomologyComparison`, its `bijective` theorem and all three private
algebra helpers use only `propext`, `Classical.choice`, `Quot.sound` (or a
subset). The geometric theorem and original ladder also use `sorryAx`, exactly
as expected from the remaining geometric hole. No other axiom appears.
The scratch probes are retained under `scratchpad/probes`, outside the delivery
source set. Added the independent geometric search to its node's search records.

Second-reader dry run: `deliver3.py J1 Sheaf.AlgebraicGeometry.EtaleLimitBinaryComparisonLadder --no-push` printed OK; compilation, axiom probes and preflight passed. Review class CODEX because the delivery adds three nodes/modules and leaves one geometric theorem open.
