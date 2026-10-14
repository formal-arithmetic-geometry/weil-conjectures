## What changed

Replaced the sorry in `AlgebraicGeometry.exists_flat_telescope_arrow_bar_data` by a
complete Lean assembly using `CochainComplex.exists_flat_truncation_tower` and two
successive applications of a new one-target refinement lemma. The existing theorem's
signature and visibility are unchanged. No definitions or existing interfaces changed.

The first refinement produces R -> E and a map from R into a presentation of P.
The second produces S -> R and a map into a presentation of P'. The final first
level map is the composite S -> R -> F. The final truncation map is S -> R -> E ->
truncLE P. Quasi-isomorphisms compose, and strict compatibility is proved by the two
naturality identities. The coproduct augmentation equations are proved by coproduct
extensionality. A proved private helper derives the telescope square from a level square.

The new module `Sheaf.AlgebraicGeometry.FlatTelescopeTargetRefinement` isolates the
single-target finite-piece construction. Its source input is an arbitrary bounded-flat
augmented tower, and its output includes levelwise quasi-isomorphisms back to that
input. It has no maps to good truncations and no simultaneous pair of targets. It is
used twice, with distinct input towers. Thus it is a proper subproblem, rather than
the original theorem under a new name. Its docstring and node give the generator-valued
relative resolution and one-target bar argument; this geometric proof remains to be
formalized.

Updated the item's proof, proof_deps, and proof_origin to record this route. Added the
new node and its Lean module. All files compile together with lcompile.py.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_flat_telescope_arrow_bar_data`
(node `lem-sc-flat-telescope-arrow-bar-data`), from the existing truncation tower and
the new one-target lemma, with no sorry in its body.

Added and left: `AlgebraicGeometry.exists_flat_telescope_target_refinement`
(node `lem-sc-flat-telescope-target-refinement`), whose proof is exactly `by sorry`.
There are no other new or remaining sorries in the delivered modules.

This is a decomposition: one original hole closed and one strictly smaller,
reusable one-target hole added. Net hole reduction is zero. The final statement is
not yet sorry-free, and no claim of an axiom-free geometric construction is made.

## No longer needed

Removed the item's direct proof import of
`Sheaf.Algebra.Homology.BoundedFlatReplacement` and its direct proof dependency
`lem-pc-kflat-bounded-flat-replacement`: the assembly uses the truncation-tower theorem
and the one-target refinement instead. BoundedFlatReplacement remains a proof-plan
dependency of the new geometric lemma and of the existing truncation tower. Therefore
no module is claimed to leave the targets' import closure.

Removed the redundant public import
`Mathlib.Algebra.Homology.Embedding.CochainComplex` from the new one-target
module: FlatTelescopeStageMap already supplies all of its signature types.
No existing public imports removed. No other existing nodes or modules pruned. The simultaneous
two-target bar enlargement is replaced by two one-target enlargements and explicit
composition; no blueprint unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof dependencies state ordinary flat replacements and flat truncation
towers. Their signatures do not supply a generator-valued split tower, compact finite
pieces, bar objects, or homotopy equivalences of target augmentations. Those extra
geometric assertions cannot be obtained by simply applying their stated conclusions.
The new lemma makes the missing single-target construction explicit, while the original
module now contains its actual two-target assembly.

The relative version of the generator construction is an agent-written extension of
the cone induction of Stacks 06XX, not the literal conclusion of 077J. I read Tags
03EW, 077J and 06XX on the Stacks website; the literature files listed in this clone
are not present locally. The source tower can be resolved relatively by taking a bounded
resolution of the cone of L_n -> E_(n+1), using the split extension triangle, and correcting
the augmentation by the lifted homotopy. Termwise surjectivity is not required in this
relative construction. The finite-piece bar argument is retained from the item's
original proof, rather than assuming that an entire source stage factors through one
finite target block.

Searches: LeanFinder returned Dold-Kan APIs and general complex factorizations, which do
not provide the stated bounded-flat one-target refinement. Loogle returned mapping-cone
constructors only. Mathlib grep found no telescope/bar refinement theorem. LeanSearch
returned HTTP Internal Server Error, recorded as unavailable. Searches of both Lean
roots and DAG nodes found no existing statement of the new refinement. Blueprint search
found no matching node; the original item's recorded ancestor `lem-sc-finite-duality`
is retained for the new node (the ancestor helper returned None for the existing item).

Edge checks for the new statement: zero augmentations still admit the target-chain
bar enlargement; a zero source tower may use the zero finite subcomplex. For the empty
scheme all module sheaves are zero. No nonzero-map, identity-map, finite-rank, projectivity,
uniform-bound, or quasi-coherence hypothesis is used. The upper bounds are per stage.
The finite-piece argument uses compact affine-open generators, not arbitrary flat
terms. The second refinement is allowed to replace the source again, and its strictly
commuting comparison d is exactly what preserves the first target identity.

## New nodes

`lem-sc-flat-telescope-target-refinement`, in
`dag/nodes/sec-picard-framework/lem-sc-flat-telescope-target-refinement.json`, states
refinement of one bounded-flat tower over one actual telescope, with a levelwise
quasi-isomorphism back to the supplied tower. It corresponds to
`AlgebraicGeometry.exists_flat_telescope_target_refinement` in the new module
`Sheaf.AlgebraicGeometry.FlatTelescopeTargetRefinement`. The proof plan resolves the
input relatively, takes its finite-piece bar tower, adjoins the one target's finite
cone-block filtration, and compares the bar augmentations by explicit homotopies.
No change records are needed: existing signatures and definitions are unchanged.

## Second reading by V4

1. Compared the existing module and DAG node with the read-only repository.
   The signature of `AlgebraicGeometry.exists_flat_telescope_arrow_bar_data`
   is byte for byte identical, including visibility and all hypotheses and
   conclusions. No existing definition changed, no other existing module is
   adapted, and no change record is required. The theorem docstring describes
   the new assembly; the public imports of the existing module are unchanged.
   Verdict: pass.

2. Compiled both delivered modules in dependency order using lcompile.py, with
   no errors or warnings. Checked every declaration: the one-target theorem is
   the only sorry, exactly a named public theorem with body `by sorry`; neither
   module has an axiom, unsafe/opaque declaration, external implementation, or
   holed definition. Scratch-copy `#print axioms` reports only propext,
   Classical.choice, Quot.sound and sorryAx for the two public theorems; the
   private sum-square helper has no sorryAx. The original hole is therefore
   closed conditionally, not axiom-free. Verdict: pass as a decomposition.

3. Independently read the new single-target statement and its proof against
   Stacks [03EW](https://stacks.math.columbia.edu/tag/03EW),
   [077J](https://stacks.math.columbia.edu/tag/077J), and
   [06XX](https://stacks.math.columbia.edu/tag/06XX). The arbitrary source tower
   requires the relative version of the cone induction, not a direct application
   of the truncation theorem. Expanded this induction, including the triangle
   comparison, degreewise extension of its homotopy, and the quasi-isomorphism
   argument. Also explained why the canonical augmentation itself is a homotopy
   equivalence; an arbitrary homotopy equivalence would not suffice for the
   strict sum identity. The compact-generator finite-support argument uses
   quasi-compact affine opens and each stage's own upper bound. Checked zero
   input towers, zero augmentations, identity augmentations, empty schemes, and
   increasing nonuniform bounds: the construction needs no additional hypothesis.
   The lemma handles one target and an arbitrary source, with no truncation
   maps or second target, and the assembly genuinely uses it twice. It is a
   proper reusable construction step, not a renamed copy of the original item.
   Independent LeanFinder query for strict sequential refinements returned
   derived-category fractions and injective factorizations, not this statement.
   Loogle Sigma.map search confirms the elementary sum identities used by the
   helper; searches of both Lean roots and Mathlib homology found no existing
   bounded-flat bar refinement. Its formalization is not a few-minute task.
   Verdict: pass; one documented geometric hole remains.

4. Read the full assembly top downward and checked both augmentation equations,
   both telescope squares, composition of all quasi-isomorphisms, and strict
   truncation compatibility. The existing truncation-tower declaration supplies
   the initial data; no shorter existing refinement was found. Removed the new
   module's unnecessary public Embedding.CochainComplex import: its statement
   has no good truncations and its remaining public import supplies its types.
   The existing module's removed direct bounded-replacement import and old
   proof dependency are already listed under No longer needed. No whole module
   leaves the target closure. The unit sk-thm-picard-duality has empty realized
   statement/step lists; the existing node is below the unit route and remains
   in place. Verdict: pass, with no unit bypass.

5. Compared both JSON nodes with the Lean statements and proofs. Only proof,
   proof_deps and proof_origin change in the existing node; the new node has its
   complete statement, dependency records, source, search records, creation,
   blueprint ancestry, chapter, unit, and verbatim Lean signature. The existing
   proof uses precisely the truncation tower and the one-target refinement.
   Synchronized the new node's natural-language proof with the expanded
   docstring. No node statement changed. Verdict: pass.

Second-reading changes: expanded the new lemma's relative cone induction and
canonical augmentation argument, synchronized its node proof, and removed its
redundant public Mathlib import. No Lean proof body, signature, definition, or
hole count was changed. Closed one original hole and added one lower hole:
net zero, a decomposition.
