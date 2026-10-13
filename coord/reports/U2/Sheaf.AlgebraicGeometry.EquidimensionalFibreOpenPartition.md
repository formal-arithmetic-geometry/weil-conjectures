## What changed

Replaced the sorry in
`AlgebraicGeometry.exists_equidimensional_fibre_open_partition_of_depth_eq_ringKrullDim`
with a compiling proof. Its existing signature, public imports, visibility and docstring stay
unchanged. Two ordinary proof imports were added:
`Sheaf.AlgebraicGeometry.CohenMacaulayFibreDimensionNeighbourhood` and
`Sheaf.AlgebraicGeometry.ConstantLocalDimensionComponents`.

The partition is a real construction: V n is the interior of the set of points in W whose
local topological fibre dimension equals n. A local neighbourhood lemma supplies coverage;
interior membership supplies disjointness by injectivity of the natural-number casts.
The existing restricted-fibre noetherianity theorem is actually used. The proof identifies
arbitrary fibre points with asFiber of their images, then applies the component theorem.
For t outside U, nonemptiness of an irreducible component would contradict hW.

The component theorem is fully proved, including a private lemma deriving a global dimension
bound from constant finite local dimension. Its cover consists of all opens of dimension at
most n. The reverse component bound uses a canonical affine cover and Mathlib's nonempty
open subset of a noetherian irreducible component. No algebraicity assumption is needed.

The remaining geometric lemma is local at one point and assumes depth equals dimension only
at that point. Its conclusion gives one neighbourhood of constant fibre dimension, with no
partition, disjointness, global coverage or component-dimension conclusion. Its source is the
local openness theorem 00RH underlying 02NM; its complete affine proof is in its docstring.
This is a strict part of the original argument, not a renamed partition statement.

All three modules compile through lcompile.py --all without errors or warnings. Their lines
are at most 100 characters. The required deliver3.py --no-push dry run checks compilation,
axiom probes, declaration signatures and node/report structure before reporting readiness.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_equidimensional_fibre_open_partition_of_depth_eq_ringKrullDim`
(node `lem-sbc-cohen-macaulay-equidimensional-fibre-pieces`). This is a decomposition, because
its proof uses the following new holed geometric statement. Closed original holes: 1; added
holes: 1; net change in these delivered holes: 0. This is not a claim of an axiom-free proof
of the partition.

The sole sorry left anywhere in this delivery is
`AlgebraicGeometry.exists_constant_fibre_dimension_neighbourhood_of_depth_eq_ringKrullDim`
(node `lem-sbc-cohen-macaulay-fibre-dimension-neighbourhood`, new module
`Sheaf.AlgebraicGeometry.CohenMacaulayFibreDimensionNeighbourhood`). Its entire proof is
exactly `by sorry`, in a named public theorem with a source and full proof in words.

Fully proved the new declaration
`AlgebraicGeometry.topologicalKrullDim_component_eq_of_constant_local_dimension`
(node `lem-sbc-constant-local-dimension-components`, new module
`Sheaf.AlgebraicGeometry.ConstantLocalDimensionComponents`) and its private helper
`dimension_le_of_local_dimension_eq`. Neither contains nor directly uses sorry.

Edge cases checked in the argument: empty W has no neighbourhood obligation; empty fibres
have no components; points in pieces outside U cannot exist; a point of a noetherian component
has an affine neighbourhood meeting that component; no global quasi-compactness is assumed.
The finite n in the component theorem is essential to the infimum argument. In the local
geometric theorem W may contain non-Cohen-Macaulay points; 00RH provides a smaller suitable
neighbourhood. Fibre local dimension is topological dimension, not stalk dimension: for a
positive-dimensional irreducible fibre its generic stalk can have dimension zero while the
local topological dimension remains the component dimension.

## No longer needed

No existing imports, nodes or modules were removed or pruned. The planned dependency
`lem-sbc-restricted-fibre-locally-noetherian` remains needed and its module remains imported.
The proof avoids formalizing a global coproduct and transferring all its components: it
constructs interiors directly and proves their component dimensions separately. There is no
existing dedicated coproduct node or module to mark as pruned. The unit's realized statement
and proof-step lists are empty; no realized unit step has been bypassed or removed.

## Where the brief, the DAG or earlier work was wrong

The original single proof dependency proves only local noetherianity of restricted fibres.
It does not supply the central Cohen-Macaulay dimension openness/decomposition theorem.
The new local lemma isolates that missing geometric input; the rest is now real Lean.
The statement of the item is unchanged and is not disputed.

The original proof plan was correct but did not distinguish local openness from global
partition construction and component-dimension bookkeeping. The DAG proof now follows the
canonical-interior construction and the actual Lean dependency list.

Searches used msearch.py LeanFinder and Loogle, direct rg in Mathlib and both library roots,
and blueprint_refs.py. LeanSearch was attempted for both new statements and returned an
Internal Server Error; the unavailable attempts are recorded without an absence verdict.
No exact statement was found. Source tags 02NM, 02NJ, 00RH, 00RE, 00R7, 00RC, 00QE and 0A21
were read online. The local lemma follows the proof of 00RH, rather than assuming an entire
global partition. The component proof uses existing proved source-library and Mathlib facts.
The already proved node `lem-weil-pbc-dimension-bound-open-cover` is used as a general
open-cover tool; it does not replace any step of the unit's geometric route. The affine
noetherian and finite-component nodes used as tools are existing Mathlib leaves.

## New nodes

`lem-sbc-cohen-macaulay-fibre-dimension-neighbourhood` is the local 00RH geometric input in
`Sheaf.AlgebraicGeometry.CohenMacaulayFibreDimensionNeighbourhood`. It assumes Cohen-Macaulayness
only at the specified point and leaves one source-backed hole. It is strictly smaller than
the global equidimensional partition theorem.

`lem-sbc-constant-local-dimension-components` is a fully proved general theorem for an open
of a locally noetherian scheme in `Sheaf.AlgebraicGeometry.ConstantLocalDimensionComponents`.
It has no morphism, flatness, finite-presentation or Cohen-Macaulay hypothesis. It converts
constant finite local topological dimension to dimension of each component.

Both new nodes have complete proof steps, three kinds of searches, original chapter and unit,
blueprint provenance and exact Lean signatures. The existing item's node is updated only in
proof, proof_deps and proof_origin. No existing definition, statement or interface changed,
so there is no change record or forced adaptation.

## Second reading by U2

1. Interfaces: compared the delivered item with the repository using diff. The entire
   existing theorem signature, universes, visibility, public imports and definitions are
   byte-for-byte unchanged. The only code differences are two ordinary proof imports and
   the replacement of its proof. The other two modules are new. No change record is needed.
   The existing node differs only in proof, proof_deps and proof_origin. Verdict: pass.
2. Kernel checks: independently compiled all three modules through lcompile.py --all and
   scratch copies with #print axioms. The component theorem uses exactly propext,
   Classical.choice and Quot.sound; the neighbourhood and partition theorems also use
   sorryAx, as reported. Exactly one sorry occurs, the named neighbourhood theorem.
   There are no forbidden declarations or data definitions depending on existence holes.
   The partition is the explicitly constructed family of interiors. Verdict: pass as a
   decomposition, not an axiom-free proof of the original theorem.
3. New statements: read Stacks 00RH, 00QE, 00RE, 0A21 (10), 0052 (2),(3), and 0055.
   The local lemma uses flatness and local finite presentation only over U and
   Cohen-Macaulayness only at y; 00RH provides a neighbourhood even if W also contains
   non-Cohen-Macaulay points. Local topological dimension includes residue transcendence
   degree, so generic points of positive-dimensional fibres do not incorrectly give n=0.
   The component theorem is valid without finite type or global quasi-compactness:
   its upper bound uses all small-dimensional opens, its lower bound uses a nonempty
   open part of an affine noetherian component. Checked empty W, empty fibres, n=0,
   t outside U, and the finite n needed for the infimum argument. Repeated LeanFinder
   searches using different wording for both new statements and a Loogle search for
   topologicalKrullDimAt; the latter is not a Mathlib identifier. Direct rg in both
   library roots and Mathlib found no whole-theorem replacement. The one-point lemma
   is strictly simpler than the partition and carries a complete source-backed proof
   docstring. Its remaining scheme/ring transport is substantial and was not closed
   in a few minutes. Verdict: pass.
4. Route and pruning: read the proof from the partition downward. Coverage uses the local
   lemma, disjointness uses cast injectivity, and the component assertion uses the
   restricted-fibre noetherianity theorem and the proved component theorem. The cast and
   asFiber identification do not assume stalk dimension equals local topological
   dimension. No old proof dependency is unused: restricted-fibre noetherianity is
   applied explicitly. The new public imports support their signatures; the item's
   new imports are private to proofs. The sk-prop-normal-form realized statement and
   both realized step lists are empty, and no unit step or route is removed. Verdict: pass.
5. DAG: read all three delivered nodes against Lean and the repository. Their Lean
   signatures match exactly; chapter, unit, provenance and creation records are present.
   The item's proof and dependency list describe precisely its two-part Lean reduction.
   The component plan records the open-cover bound and affine component argument.
   Repaired the unresolved local lemma's plan to cite existing nodes for dimension
   finiteness, 00QE, miracle flatness, 00R7 and 00RC; these are source-plan dependencies,
   not a claim of a completed Lean proof. Verified these citations introduce no path
   back to the item. Marked unavailable LeanSearch entries explicitly unavailable.
   Verdict: pass after these repairs.

Changes by this reader: corrected the component docstrings from the section tag 0050 to
0052 and 0055; completed the local proof-plan citations and the missing unavailable-search
verdicts. No theorem statement or proof term changed, and no holes were added or closed
by the second reading. The delivered result remains one original hole decomposed into
one local geometric hole, plus a fully proved new component theorem; net holes closed: 0.
