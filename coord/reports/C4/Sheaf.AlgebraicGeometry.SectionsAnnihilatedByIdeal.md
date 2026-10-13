## What changed

The signature and public imports of `AlgebraicGeometry.sections_annihilated_by_ideal`
are unchanged. Its proof now constructs the annihilator subsheaf, proves the affine
image formula, applies a separate quasi-coherence theorem, proves both stalk maps
injective from `RingedSpace.module_stalk_exact`, and proves the stalk image equivalence
by germ calculations and a separate local lifting theorem.

Four new modules carry the parts of the argument:

- `Sheaf.AlgebraicGeometry.AnnihilatorSubsheaf`: a proved construction, with explicit
  section submodules, restricted presheaf maps, gluing, subtype inclusion, and image formula.
  There is no choice of data from an unproved existence theorem.
- `Sheaf.AlgebraicGeometry.AnnihilatorAffineCriterion`: a proved affine criterion,
  valid for any module sheaf. `IdealSheafData.map_ideal` and the ideal map/comap
  adjunction show annihilation on smaller affine opens; sheaf separatedness handles
  all subopens. Neither finite type nor quasi-coherence of the module is needed here.
- `Sheaf.AlgebraicGeometry.AnnihilatorQuasicoherent`: the finite-generator principal-open
  localization argument, isolated as a theorem about an arbitrary mono inclusion
  with the specified affine image.
- `Sheaf.AlgebraicGeometry.AnnihilatorStalkLocalLift`: the finite-generator stalk
  localization argument, isolated as a theorem producing an annihilated local
  representative, independently of any global subsheaf or inclusion.

All five delivered modules compile in import order without compiler errors or warnings.
The original module contains no remaining hole. The public interface of every existing
module is unchanged; no adaptations or change records are needed.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.sections_annihilated_by_ideal`
(node `lem-weil-pbc-sections-annihilated-by-ideal`) by a complete Lean reduction.
This is a decomposition, not a complete proof without dependencies containing holes.

Proved outright:

- `AlgebraicGeometry.exists_annihilator_subsheaf`
  (`lem-weil-pbc-annihilator-subsheaf-construction`), including its private
  construction and gluing helpers.
- `AlgebraicGeometry.annihilator_affine_criterion`
  (`lem-weil-pbc-annihilator-affine-criterion`).
- The original theorem's forward stalk-image implication, reverse implication
  conditional on the local lifting theorem, and both stalk injectivity assertions.

Exactly two holes are added, each the whole proof of a named public theorem:

- `AlgebraicGeometry.annihilator_subsheaf_quasicoherent`
  (`lem-weil-pbc-annihilator-quasicoherent`).
- `AlgebraicGeometry.annihilator_stalk_local_lift`
  (`lem-weil-pbc-annihilator-stalk-local-lift`).

Each is strictly a part of the original argument. The quasi-coherence theorem
assumes the affine image identification and proves only quasi-coherence. The
stalk lifting theorem produces a local representative and does not mention the
subsheaf. Each has its complete finite-generator argument and source in its
docstring and DAG node. One original hole is closed and two lower holes are added;
the net hole count of this decomposition is -1, not +1.

Edge cases checked mathematically: zero ideal (use exponent zero and empty product one),
unit ideal (the subsheaf and annihilated stalk are zero), zero module, empty opens,
and empty schemes. The actual subsheaf gluing proof handles an empty cover by
separatedness. No nonemptiness, Noetherianity, or finite generation of F is assumed.

## No longer needed

Removed these original proof-only imports:

- `Sheaf.AlgebraicGeometry.Coherent`: no declaration from it occurs in the assembly.
  The quasi-coherence predicate in the statement is Mathlib's.
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`: finite-generation theory
  is not needed for the now-proved construction or affine criterion. Its node
  remains in the proof plans of the two localization theorems, so this is removal
  from the upper module, not a claim that it is globally unnecessary.
- `Sheaf.Topology.PresheafModuleStalkFunctor`: the proof uses the existing ringed-space
  module stalk functor and Mathlib's germ lemmas directly.

The original node's affine tilde/Gamma, finite-type affine, tilde sections,
localization-away, affine spectrum, coherence, stalk-localization, and localization
inputs are no longer direct dependencies of the upper theorem. Where genuinely
needed they are retained in the two new localization nodes. The affine criterion
itself prunes its original tilde/Gamma, finite-generator, and principal-localization
route in favor of ideal extension and an affine cover. The germ and stalk-exactness
inputs are retained. No unit statement or realized unit step is bypassed.
No claim is made that the removed modules become unreachable from all five targets.

The complete list removed from the original node's direct `proof_deps` is:
`def-weil-affine-spectrum`, `def-weil-pbc-module-localization`,
`def-weil-pbc-module-localization-away`, `def-weil-sheaf-of-modules-category`,
`lem-weil-pbc-affine-open-stalk-localization`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-quasi-coherent-finite-type-affine`,
`lem-weil-pbc-spec-module-tilde-sections`,
`lem-weil-pbc-spec-tilde-stalk-localization`, and `pqf-def-coherent`.
These are removed as direct proof edges, not all from the transitive argument.


## Where the brief, the DAG or earlier work was wrong

The original plan overstates the machinery needed for its affine criterion:
finite generation of the ideal and quasi-coherence of F are unnecessary for that
part. The stronger criterion is proved from quasi-coherent ideal data and sheaf
separatedness, without changing the original theorem's statement.

LeanSearch returned Internal Server Error on all four new-node searches. Those
attempts are logged and recorded as unavailable, with no absence verdict.
LeanFinder and source searches supplied the usable results; the exact ideal
extension lemma found by LeanFinder is used in the affine proof.

WANTED: `literature/stacks-project/properties.tex`, Tag 01PO and Definition 01PP,
for the original node and the four new nodes. This clone has no literature sources;
Tag 01PO was read on the official page https://stacks.math.columbia.edu/tag/01PO.
The expanded arguments and their Lean realization are marked agent-written.

## New nodes

`lem-weil-pbc-annihilator-subsheaf-construction` records the proved subsheaf
construction without finiteness or quasi-coherence assumptions on the module.
Its module is `Sheaf.AlgebraicGeometry.AnnihilatorSubsheaf`.

`lem-weil-pbc-annihilator-affine-criterion` records the proved equivalence between
local annihilation and annihilation by global ideal sections on an affine open.
Its module is `Sheaf.AlgebraicGeometry.AnnihilatorAffineCriterion`.

`lem-weil-pbc-annihilator-quasicoherent` records the remaining principal-open
finite-generator localization calculation and its sheaf identification.
Its module is `Sheaf.AlgebraicGeometry.AnnihilatorQuasicoherent`.

`lem-weil-pbc-annihilator-stalk-local-lift` records the remaining local representative
argument at a prime, with denominator clearing for finitely many ideal generators.
Its module is `Sheaf.AlgebraicGeometry.AnnihilatorStalkLocalLift`.

All four are in `dag/nodes/sec-proper-base-change/`, have unit `sk-thm-p1`, inherit
the original blueprint ancestor and chain, and carry their verbatim Lean statement.
The original node is updated only in `proof`, `proof_deps`, and `proof_origin`.

## Second reading by C4

1. Interface: PASS. Diffed the existing module against the repository. The entire
   existing theorem signature is byte for byte unchanged, as are its public
   imports, visibility, universe and variables. Only proof imports, private proof
   helpers and the proof changed. There are no existing definitions changed and no
   forced adaptations. The original node changes only proof, proof_deps and
   proof_origin; all four new node signatures match their Lean text exactly.
2. Proof and axioms: PASS as a decomposition. Independently compiled all five
   modules in import order without errors or warnings. Source inspection finds
   exactly the two reported named theorem holes, no forbidden declarations and
   no hollow definitions. A scratch module printed axioms for all five public
   theorems: the construction and affine criterion use only propext,
   Classical.choice and Quot.sound; the upper theorem and two open lemmas also
   use sorryAx, as expected. The construction makes its actual section submodules
   and sheaf; it chooses no arbitrary data from an unproved existence statement.
3. Split statements: PASS. Read both signatures, docstrings and complete node
   arguments against official Stacks Tag 01PO. The quasi-coherence theorem proves
   just quasi-coherence of an already specified mono subsheaf; the local lifting
   theorem constructs just a local representative, without any global subsheaf.
   Neither restates the original theorem. Finite generation permits a maximum
   exponent for principal localization and a product of denominators outside the
   prime for stalk localization. Checked the zero ideal, unit ideal, zero module,
   empty affine open, empty scheme and empty generator family. Independent
   LeanFinder searches for common kernels of finitely many scalar multiplications
   and neighborhood lifts of ideal-killed stalk elements returned only generic
   quasi-coherence, finite-type and tilde/stalk tools, not either statement.
   Independent msearch grep for commonKernel|common_kernel|annihilator|annihilated
   in Mathlib's module-sheaf geometry found no match. Repository searches found
   annihilator_affine_basicOpen, which concerns the annihilator ideal of a finite
   module, not the submodule killed by a finite ideal, and is not a replacement.
4. Route and pruning: PASS. Read the assembly from its original theorem downward.
   The affine criterion uses the shorter ideal-extension route; the construction
   uses Mathlib submodule presheaves and unique gluing; germ naturality is used
   directly. The two finite-generator arguments are not a few-minute closure with
   the available APIs. Every removed direct proof dependency is now listed
   explicitly above. The three removed imports are proof-only. The item is a tool
   below unit level: none of the realized statement or step nodes in
   dag/units/sk-thm-p1.json is bypassed or changed. No whole-module unreachability
   claim is made.
5. DAG: PASS. Checked all five node proofs and origins against the code or the
   remaining complete natural-language arguments. Every proof_deps list is the
   union of step uses. New nodes have creation, source, searches, blueprint chain,
   chapter/unit and exact Lean records. The original node retains all other
   fields unchanged. The upper proof keeps the stalk exactness and germ inputs;
   localization inputs remain on the two open localization nodes.

Second reading changed only documentation: replaced the upper theorem's obsolete
five-step docstring with the actual reduction and its two open inputs, and made
`No longer needed` enumerate every removed original proof-dependency node.
No Lean proof or signature required repair. One original hole is closed, two
strictly smaller holes are added: this is a decomposition with net holes closed
minus holes added equal to -1, not a fully closed proof.
