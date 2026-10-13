## What changed

Proved `AlgebraicGeometry.exists_fibre_dimension_open_of_flat_restrict` from
constant relative dimension opens, in the existing item module. Added the proof-only
import `Sheaf.AlgebraicGeometry.FlatFibreDimensionStrata`. The already proved
`AlgebraicGeometry.fibre_dimension_eq_of_specializes_component_restrict` and all
existing signatures and docstrings are preserved. Updated the neighbourhood node's
proof and dependencies to match the Lean argument. The second reading also updates
the specialization node's stale proof plan to its existing Lean proof via the
neighbourhood theorem, and adds the source and blueprint to the new module header.

## Proved and sorry left

Closed one existing hole: `AlgebraicGeometry.exists_fibre_dimension_open_of_flat_restrict`
(node `lem-sbc-flat-fibre-component-dimension-specialization-open`). No sorry remains
in the item module. Added one hole:
`AlgebraicGeometry.exists_fibre_dimension_strata_of_flat_restrict`
(node `lem-sbc-flat-fibre-dimension-strata`). This is a decomposition, not a net
hole reduction: one closed, one added, net zero. The new statement is the
constant-dimension opens step of Tag 054T, rather than a renamed specialization or
neighbourhood assertion. The Lean proof chooses a dimension index and combines the
two equalities to that dimension. Both files compile without warnings.

## No longer needed

None. No imports removed; no existing nodes or modules are bypassed. The four public
imports support the unchanged signatures. The new module is needed by the proof.

## Where the brief, the DAG or earlier work was wrong

The checkout changed during this session: it now contains the previously added
neighbourhood theorem, and the specialization theorem is already proved from it.
The delivery preserves that work and closes the neighbourhood hole instead. The
neighbourhood node originally recorded no usable proof dependencies; the new node
makes its constant-dimension opens step explicit. There is no statement change or
mathematical dispute. The unit route stays unchanged.

Edge cases checked against the source: empty fibres give no generic points;
zero-dimensional fibres use n = 0; different component dimensions are assigned
different opens; arbitrary bases need no irreducibility or noetherian hypothesis.
The locally noetherian assertion concerns fibres, not the base or whole source.

## New nodes

`lem-sbc-flat-fibre-dimension-strata`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-flat-fibre-dimension-strata.json`, states
the constant relative dimension opens from Tag 054T after restriction to U, with
coverage of component generic points as explicitly used in Tag 054U. It has no
specialization hypothesis and no equality of two varying fibre dimensions. Its
source proof and the restriction/fibre identifications are documented in its
module. Searches found no exact existing declaration; LeanSearch was unavailable.
No change record is needed because existing interfaces are identical.

## Second reading by U2

1. Compared the complete delivered item module with the repository using diff.
   Both existing theorem signatures and docstrings are byte for byte unchanged;
   only the new plain proof import and the neighbourhood theorem body differ.
   There are no changed definitions, target statements or public imports.
2. Inspected both complete modules: the sole remaining sorry is the public named
   strata theorem documented above; there is no definition, axiom, unsafe code,
   opaque declaration, implemented_by or extern. Both files compiled locally without warnings, in import order, via lcompile.py
   --all. Scratch copies with #print axioms compiled successfully for all three
   declarations: precisely propext, Classical.choice, Quot.sound and the expected
   sorryAx from the strata hole were printed, with no additional axiom. The neighbourhood proof
   uses coverage once and combines hdim n y hy with the symmetric hdim n x hxn;
   specialization then uses Specializes.mem_open with the correct direction.
3. Read Stacks https://stacks.math.columbia.edu/tag/054T and
   https://stacks.math.columbia.edu/tag/054U. Flatness and local finite presentation
   are exactly those of the restricted morphism. Tag 054T supplies dimension-n
   opens with fibrewise dense union; Tag 054U explicitly places a component generic
   point in one of them. The new theorem states this underlying opens step, not
   the equality of dimensions at specialized points or the neighbourhood assertion
   under a new name. The two clauses serve distinct steps of the Lean reduction.
   Its docstring explains coverage using a noetherian neighbourhood, exclusion of
   the other components, density, and stability of opens under generalization;
   it also explains restriction and open invariance of local dimension.
   Checked empty U/source/fibres (empty opens suffice), zero-dimensional fibres
   (index zero), and disjoint components of unequal dimensions (different indices).
   No noetherian or irreducibility assumption on the base is used. New searches
   used the phrases "locus", "minimal primes", relativeDimension and fiber/dim;
   LeanFinder found openness of smooth/unramified loci and UniversallyOpen.of_flat,
   not this theorem. Loogle Flat with dimension had no hits (an earlier query with
   Topology had an identifier error and was not treated as evidence). Grep of the
   scheme Mathlib APIs, this library and upstream AlgebraicGeometry found no exact
   replacement. The remaining strata proof is substantial and was not closed.
4. All four public imports supply the existing scheme, fibre, flatness, finite
   presentation and local-dimension signature vocabulary. The strata import is
   plain because it is used only by the proof. No old proof dependency of the
   neighbourhood node is dropped: its former proof_deps was empty. The specialization
   node is now recorded as depending on its existing neighbourhood theorem.
   Read dag/units/sk-prop-normal-form.json: realized.statement and both realized.steps
   are empty; no recorded unit realization is bypassed or changed. The source route
   through 054T, then 054U, is retained. No imports or modules are pruned.
5. Checked the new node's verbatim Lean statement, module, declaration, source,
   definition dependencies, search records, creation and blueprint ancestry fields.
   The neighbourhood node now names precisely the strata declaration used by its
   body. Found and repaired a pre-existing stale specialization-node proof plan:
   the Lean body already uses the neighbourhood declaration, but proof_deps was
   empty. Only proof, proof_deps and proof_origin are changed in that existing node.
   The new node's non-elementary source theorem remains open, as its named sorry
   explicitly records; the delivery does not claim to have formalized Tag 054T.

Changes in the second reading: added source/blueprint information to the new
module header and repaired the specialization node's proof metadata. No Lean
proof or signature needed repair. One old hole is closed and one new hole remains:
a decomposition with net zero, not an axiom-free proof of either upper theorem.

Validation: lcompile.py --all passed for both modules. The first item scratch probe
ran before its new dependency finished compiling and reported that missing object
file; rerunning after the import-order build passed. The scratch strata probe and
both item #print axioms results were checked, and scratch files were removed.
