## What changed

Proved `ModuleCat.openStabilizerAdjunction` in
`lean/Sheaf/RepresentationTheory/OpenStabilizerAdjunction.lean`, preserving both existing
public signatures and the original public imports. Added the proof-only import
`Mathlib.Topology.Algebra.OpenSubgroup` for `Subgroup.isOpen_mono`.

Private constructions implement the three existing proof steps of
`lem-exc-rg-open-stabilizer-adjoint`. `vectorStabilizer` packages the stabilizer as a
subgroup. `openVectors` constructs the submodule of vectors with open stabilizer;
`openVectors_stable` proves invariance using continuous conjugation.
`openRepresentation`, `openInclusion`, and `openFunctor` construct the induced
representation, its inclusion, and the functor on objects and equivariant maps.
`openHomEquiv` restricts maps from discrete representations and inverts that restriction
by inclusion; `openAdjunction` supplies the two naturality identities.

The final proof obtains full faithfulness from the full-subcategory API. For
monomorphism preservation it constructs the kernel subrepresentation, proves that
it is discrete, and uses cancellation of the original monomorphism to force the kernel
inclusion to be zero. The counit is definitionally the constructed inclusion, so its
injectivity and exact range follow from the subtype construction.

The argument follows the original node's three steps and Stacks Project Tag 04JF
(https://stacks.math.columbia.edu/tag/04JF), whose proof was read. No route, statement,
definition of an existing declaration, or DAG dependency changed. The unit
`sk-prop-h2` has no realized step at this node that this argument bypasses.

## Proved and sorry left

Closed the sole original hole: `ModuleCat.openStabilizerAdjunction`
(node `lem-exc-rg-open-stabilizer-adjoint`). This is a complete proof, not a decomposition:
no new holes or modules were added, and every private helper is fully proved or
explicitly constructed. No `sorry` remains in the delivered module.

The module compiles through `lcompile.py`. The delivery dry run also checks the axioms
of its declarations. No data is chosen from an unproved existence statement.

## No longer needed

None. Both original public imports remain necessary for the existing statements.
The new proof-only Mathlib import is needed for openness of subgroups containing
an open subgroup. The node's original `proof_deps` is empty and remains empty.
No node or module was bypassed or pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The original plan can be implemented directly
using Mathlib's subrepresentation, full-subcategory, and adjunction APIs.
The local copy of the Stacks source is absent; the published Tag 04JF page was read.

## Second reading by E4

1. Interface preservation: PASS. Read the complete module and its diff against the
   repository version. Both existing public signatures are byte-for-byte unchanged,
   as is the body of `ModuleCat.forgetDiscreteGModule`; the existing docstrings and
   public imports are unchanged. The only additional import is proof-only. All new
   constructions are private, and no statement or definition change record is needed.
2. Proof and axioms: PASS. Independently compiled the delivered module with
   `lcompile.py` (no errors or warnings). Appended `#print axioms` for both existing
   declarations and all nine private helpers to a scratch copy, and compiled that
   copy: every declaration uses only `propext`, `Classical.choice`, and `Quot.sound`
   (the subgroup construction does not need choice). Inspected the explicit subtype,
   action, restricted linear maps, Hom equivalence, naturality, kernel cancellation,
   and counit range proofs. No forbidden declarations, hollow definitions, `sorry`,
   or data obtained from an unproved existence theorem occurs. Holes closed:
   `ModuleCat.openStabilizerAdjunction` (one). Holes added: none (zero).
3. Split-off statements: PASS, vacuous. There are no split-off holes or new public
   statements. The private helpers express strictly local, fully proved parts of
   the construction. Checked zero vectors/modules, trivial and discrete groups
   (the open-vector submodule is the whole module), and the indiscrete-group case
   (open stabilizers must be the whole group, so these are invariant vectors).
   No separation, commutativity, finiteness, or nonzero-ring hypothesis is introduced.
4. Route and pruning: PASS. Re-read Stacks Project Tag 04JF at
   https://stacks.math.columbia.edu/tag/04JF. The proof implements the node's kernel
   argument, open-submodule construction, and natural Hom bijection. A fresh
   Lean Finder search for a coreflection into smooth representations, using different
   terminology from the first worker, returned invariant/coinduction constructions,
   not this adjunction. Searched the local representation modules and Mathlib for
   open stabilizers and coreflections; no shorter applicable proved result was found.
   The full-subcategory API and `Rep.mono_iff_injective` are already used. Both
   original public imports serve the statement, and the new private import supplies
   `Subgroup.isOpen_mono`. The old `proof_deps` is empty, so `No longer needed: None`
   is complete. Read `dag/units/sk-prop-h2.json`: its realization lists are empty;
   the delivery bypasses no realized statement or step and changes no unit route.
5. DAG agreement: PASS. Read `lem-exc-rg-open-stabilizer-adjoint.json` in full. Its
   three elementary proof steps, empty `proof_deps`, and document `proof_origin`
   agree with the actual Lean proof. There are no new nodes or changed node files.

Second-reading changes: appended this review record only. The Lean proof and DAG
needed no repair. Scratch checks are outside the delivered `lean/` directory.
