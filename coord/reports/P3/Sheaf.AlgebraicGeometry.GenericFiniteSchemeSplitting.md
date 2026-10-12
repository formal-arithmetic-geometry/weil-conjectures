## What changed

Replaced the sorry in AlgebraicGeometry.Scheme.exists_dense_open_finite_scheme_splitting
with a compiling proof from exists_generic_finite_algebra_splitting and the new
finite_scheme_components_of_split_tensor_algebra. The existing signature is unchanged.
The proof establishes the affine finite global-section algebra, converts the factor
universal-homeomorphism encoding, proves density of D(c), and restricts the cover and
components to every smaller open by explicit pullback squares. Both private helpers
are fully proved. The new proof-only import is
Sheaf.AlgebraicGeometry.SplitTensorAlgebraSchemeComponents.

## Proved and sorry left

Closed: AlgebraicGeometry.Scheme.exists_dense_open_finite_scheme_splitting
(node lem-weil-pbc-generic-finite-scheme-splitting). No sorry remains in the item module.
Added: AlgebraicGeometry.Scheme.finite_scheme_components_of_split_tensor_algebra
(node lem-weil-pbc-split-tensor-algebra-scheme-components), the only sorry in this delivery.
This is a decomposition: one upper hole closed, one strictly smaller hole added;
net hole reduction is zero. The existing algebra splitting theorem remains an imported
sorry outside this delivery. The remaining theorem assumes the complete algebra
splitting data and proves only the passage to scheme components over one principal
open: it does not assert generic algebra splitting, density, or restriction to all opens.

## No longer needed

No existing imports removed and no modules globally pruned. The original direct dependency
lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism is no longer used
directly by the item; it moves into the new component-conversion node and is still
needed there. Restriction/base-change work is proved locally, not split into another item.

## Where the brief, the DAG or earlier work was wrong

The earlier proof plan omitted declarations implementing the scheme conversion and
component-restriction glue. The latter is now fully implemented; the former has its own
precise statement with actual algebra data rather than a repackaged generic existence
statement. The algebra theorem encodes universal homeomorphisms by universally
IsHomeomorph, whereas the item uses IsUniversalHomeomorphism; the private finite-map
conversion resolves this difference without a new hole.

Checked edge cases: n = 0 uses the empty spectrum of the zero product ring; V = bottom
is allowed by the pullback proof; nilpotents do not affect the lifted clopen components.
The conversion theorem does not require c != 0; density is proved separately in the item.
No statement or definition changed. No data definition chooses an arbitrary witness.
The unit record has no realized statement or steps, and the original algebraic route stays.
The local literature document is absent; the source and argument were read from the
existing module docstring and DAG proof; the new explicit glue is marked agent-written.

## New nodes

lem-weil-pbc-split-tensor-algebra-scheme-components is the geometric conversion of an
already supplied reduced tensor algebra decomposition. Its module is
Sheaf.AlgebraicGeometry.SplitTensorAlgebraSchemeComponents. Its statement needs no
integrality/Noetherianity of S and no generic existence/density claim. Searches found
Mathlib spectrum/coproduct and tensor-pullback ingredients but no exact theorem;
LeanSearch returned Internal Server Error, recorded as unavailable. There are no change
records because all existing statements and definitions are unchanged.


## Second reading by P3

1. Compared the delivered item module with the repository version using diff. The existing
   theorem signature and docstring are unchanged. The added component-module import is
   proof-only. There are no changed existing definitions or statements. Verdict: pass.
2. Compiled both modules through lcompile.py, without errors or warnings. Printed axioms in
   a temporary copy: both private helpers use only propext, Classical.choice and Quot.sound;
   the item theorem also uses sorryAx from its open dependencies, as expected. The split-off
   theorem has sorryAx. The only delivered sorry is that named theorem, with its docstring
   proof and node. No forbidden declarations or hollow definitions occur. Verdict: pass.
3. Checked the split-off statement mathematically: the supplied reduced tensor isomorphism
   gives clopen factors, reduction lifts them, and source-thickening invariance of integrality
   together with universal surjectivity of reduction gives universal homeomorphisms. This is
   strictly a part of the item, assuming the entire algebra-splitting data and asserting no
   generic existence, density, or all-subopen restriction. With r = 0 the reduced tensor is
   zero, hence its spectrum and the source are empty. With c = 0 the principal open and cover
   are empty. S and Z may be nonreduced: reduction and arbitrary-thickening integrality still
   apply. Searched the library with tensor, component and coproduct terms, and LeanFinder
   with "affine schemes decomposition of reduced coordinate ring product universal
   homeomorphisms"; only ingredients, no duplicate conversion result. Verdict: pass.
4. Read the entire proof top downward. It uses the existing generic algebra splitting,
   geometric conversion and explicit restriction by pullback. The conversion is substantial
   geometric glue and could not be closed in a few minutes. All imports support statement
   notation, typeclasses or proof ingredients; no additional pruning was identified. Checked
   sk-prop-sf-cbc.json: its realized statement and steps are empty; the original algebraic
   route is retained. The report now explicitly names the old direct dependency that moves
   to the split-off node. Verdict: pass.
5. Read both delivered DAG records, compared the item node with its repository version,
   and checked the referenced dependencies' declarations or Mathlib matches. The item proof
   and dependencies describe the actual Lean reduction; the split-off node's signature,
   source, natural-language proof, status and creation fields agree with the new theorem.
   Verdict: pass.

Second reading changed the report only: explicitly named the dependency moved out of the
item's direct proof_deps and added this review record. No Lean proof repair was necessary.
This delivery remains a decomposition, with one upper hole closed and one lower hole added.
