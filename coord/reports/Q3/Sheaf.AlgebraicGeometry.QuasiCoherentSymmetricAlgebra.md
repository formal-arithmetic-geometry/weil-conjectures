## What changed

Constructed the sectionwise symmetric-algebra presheaf explicitly, including its ring
restrictions, functor laws, structure morphism, ring sheafification and linear degree-one
map, in `Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction`. No data is selected
from an existence theorem. Proved the universal property in
`Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore`: sectionwise algebra lifts,
naturality, sheafification lift, scalar compatibility, existence and uniqueness.

Reduced the target to the affine comparison theorem. The target uses the concrete
sheaf and inclusion, the proved universal property, and `RingEquiv.ofBijective` applied
to the sheafification unit. Its scalar and degree-one compatibility are `rfl`.
Existing signatures and public imports of the target are unchanged.


Continuation check: all four sandbox modules compiled successfully through `lcompile.py`.
The previous compile log records an earlier failed version and is not the validation
result for this delivery. The fixed construction and complete universal-property proof
were checked again; only the named affine-comparison theorem contains `sorry`.

## Proved and sorry left

Closed `AlgebraicGeometry.exists_quasiCoherentSymmetricAlgebra` (one original hole).
The universal property `AlgebraicGeometry.exists_quasiCoherentSymmetricAlgebra_core`
is fully proved, as are all construction equations and functor laws.
One new hole remains:
`AlgebraicGeometry.quasiCoherentSymmetricAlgebra_affine_comparison`, node
`lem-weil-pbc-quasi-coherent-symmetric-algebra-affine`.
This delivery is a decomposition (one upper hole closed, one lower hole added), with
Steps 1--3 of the parent argument now implemented and proved. The remaining theorem
concerns the fixed concrete sheafification, does not claim a universal property or
choose an algebra sheaf, and isolates Steps 4--7.

## No longer needed

Removed the target's direct proof imports of
`Sheaf.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange`,
`Sheaf.RingTheory.SymmetricAlgebraBaseChange`, and
`Sheaf.Topology.PresheafModuleStalkFunctor`.
These modules and their nodes are still needed by the remaining affine comparison
argument; this is relocation of their use, not a claim they are globally pruned.
The original parent proof dependencies for sheafification, affine tilde and stalks are
now assigned to the appropriate new nodes. No mathematical ingredient is globally pruned.
The parent is not a realized unit statement or step; the unit route is preserved.
Removed the unused public import of `Coherent` from the new core module. The new
affine comparison imports `Coherent` and the construction directly, rather than importing
the unused universal-property core. No existing public import was changed.

Every former direct parent proof dependency is now indirect or a construction/statement
ingredient (none is claimed globally pruned):

- `lem-weil-pbc-symmetric-algebra-universal-property`
- `def-weil-sheaf-of-modules-category`
- `lem-weil-pbc-ring-sheafification-space-underlying-abelian`
- `def-weil-pbc-sheafification`
- `lem-weil-pbc-affine-open-spec-points`
- `lem-weil-pbc-module-restriction-open-immersion-colimits`
- `lem-weil-pbc-spec-module-tilde-sections`
- `lem-weil-pbc-affine-tilde-gamma-adjunction`
- `lem-weil-pbc-quasi-coherent-affine-section-base-change`
- `lem-weil-pbc-symmetric-algebra-base-change`
- `lem-weil-pbc-stalk-sheafification-space`
- `def-weil-pbc-module-stalk`
- `lem-weil-pbc-module-iso-on-stalks`
- `def-pc-scheme`
- `pqf-def-coherent`

## Where the brief, the DAG or earlier work was wrong

No false statement found. The original DAG describes the right construction but its
module had no explicit symmetric-algebra sheaf. The ring-level universal property is
available in Mathlib; no sheaf-level construction was found in the source library or
Mathlib searches. LeanFinder and Loogle returned only ring-level symmetric algebra and
tilde machinery. LeanSearch returned HTTP 500 and was recorded as unavailable.

Read Stacks `modules.tex`, labels `lemma-local-tensor-algebra`,
`lemma-stalk-tensor-algebra`, and `lemma-whole-tensor-algebra-permanence` (01CG,
01CH, 01CL), fetched read-only into the sandbox scratchpad. 01CG explicitly suggests
this presheaf sheafification construction; its proof is omitted. The new remaining
lemma records the parent node's full affine tilde/stalk proof. Edge cases include the
empty scheme (affine assertions are vacuous where appropriate), the zero module
(Sym is the structure ring), and zero rings: no nontriviality, finite-generation,
separatedness or nonemptiness assumptions were introduced.

## New nodes

`lem-weil-pbc-symmetric-algebra-sheaf-construction` records the explicit presheaf,
sheafification and degree-one map in `SymmetricAlgebraSheafConstruction`. Its Lean
construction and equations are proved; it carries no holes.

`lem-weil-pbc-quasi-coherent-symmetric-algebra-core` records the universal property
for that fixed concrete construction in `QuasiCoherentSymmetricAlgebraCore`.
It is proved with Mathlib's symmetric-algebra lift and ring sheafification API.

`lem-weil-pbc-quasi-coherent-symmetric-algebra-affine` records quasi-coherence and
bijectivity of the actual sheafification unit over affine opens, in
`QuasiCoherentSymmetricAlgebraAffine`. This is the only remaining hole. Its proof
uses the original parent Steps 4--7, recorded verbatim in the node and fully in the
Lean docstring. This node is strictly a local comparison, not the parent statement
under another name. No change records or forced adaptations.

## Second reading by Q3

1. Compared the item against the repository with `diff -u`: the existing theorem
   signature and all existing public imports are byte-for-byte unchanged. The only
   existing node changes are `proof`, `proof_deps`, and `proof_origin`. The three
   other Lean modules are new; no definition or statement change record is needed.
   Verdict: pass.
2. Compiled all four modules in import order with `lcompile.py --all`. Inspected
   every definition and proof: no forbidden declarations, no hollow definitions,
   and exactly one named `sorry`, the affine comparison. Scratch `#print axioms`
   checks for restriction, presheaf, structureMap, algebra, sectionMap, inclusion,
   and the core theorem show only propext, Classical.choice, Quot.sound. The affine
   theorem and target additionally show sorryAx, exactly as expected. Verdict: pass.
3. Read the remaining affine theorem and its complete tensor/tilde/stalk argument.
   It proves properties of a fixed construction, strictly less than the parent:
   neither construction nor universal property remains in this hole. The affine
   tensor identifications and cofinal affine neighbourhood argument establish its
   truth without extra assumptions; empty schemes, zero modules and zero rings
   introduce no exception. Independent LeanFinder search for "sheafification
   symmetric powers quasicoherent affine sections", Loogle search for
   "SymmetricAlgebra, Function.Bijective", and rg in Lean/Mathlib/upstream found
   no existing sheaf-level comparison. The hole cannot be closed in a few minutes
   with the available ring-level API. Verdict: valid decomposition, net zero holes.
4. Read the proof from the parent downward: concrete construction, generator-based
   universal property, then RingEquiv.ofBijective are the direct routes. The new
   imports are used by signatures/definitions or by the stated remaining proof;
   existing public imports are preserved. Checked sk-thm-p1.realized: this parent
   is not a realized statement/step, and no unit route is bypassed. Enumerated all
   old parent dependencies above; none is claimed globally pruned. Verdict: pass.
5. Checked all four node records, required new-node fields, statement correspondence,
   proof-dependency unions and proof origins. The parent reduction agrees with Lean.
   The affine node records the remaining argument and matches its single named hole.
   The construction node records actual data, not an arbitrary existence witness.
   Verdict: pass after the documentation repair below.

Changes made by second reading: restored the three planned proof-only imports in
QuasiCoherentSymmetricAlgebraAffine so their use really is relocated, as reported;
removed the unformalized functoriality claim from the proved core node's proof text;
explicitly listed every old parent proof dependency under No longer needed. No
Lean proof or statement was changed and no additional hole was introduced.
