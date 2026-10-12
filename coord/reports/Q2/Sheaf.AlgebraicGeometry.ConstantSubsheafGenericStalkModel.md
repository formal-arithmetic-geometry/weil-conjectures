## What changed

Replaced the sorry in `Sheaf.AlgebraicGeometry.ConstantSubsheafGenericStalkModel` by a complete
Lean proof from one strictly smaller comparison statement. The signature and existing docstring
are unchanged. The only added proof import is
`Sheaf.AlgebraicGeometry.GeometricStalkComparisonConstant`. The node copy now records this route.

Choose the separable-closure point at eta, take N to be its stalk of F, and map N monomorphically
into the constant value M of G. Applying the constant-sheaf functor constructs alpha and proves
its monomorphism. A comparison of stalk functors normalized on constants supplies e; naturality
for phi and the constant presentation, together with the constant-stalk naturality formula,
proves the required equality. Thus the new statement does not construct N or alpha, does not
assume a monomorphism, and does not assert the original conclusion under another name.

The comparison step covers separably closed fields and module coefficients; the nearby
`geometricPointMorphism_stalk_bijection` covers algebraically closed fields and set/abelian
coefficients, and `isZero_sheafFiber_iff_of_same_image` gives only simultaneous vanishing for
abelian sheaves. Neither signature supplies the comparison needed here.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.exists_constant_generic_stalk_model_of_mono_constant`
(node `lem-weil-pbc-constant-subsheaf-generic-stalk-model`). No sorry remains in the item.

Added and left: `AlgebraicGeometry.Scheme.exists_geometricStalkComparison_constant`
(node `lem-weil-pbc-geometric-stalk-comparison-constant`), exactly `:= by sorry` in its own
module. Its docstring gives the full residue-field/separable-closure, pointed-neighbourhood,
colimit, and constant-germ argument.

This is a decomposition: one upper hole closed, one strictly smaller geometric comparison
hole added, net zero holes. Both modules compile locally without warnings. The zero module,
zero stalk, identity comparison, and positive-characteristic separably closed nonperfect
fields cause no exceptional case; no finite-generation or Noetherian hypothesis is introduced.
The filtered-colimit-preservation instance in the new lemma is discharged in the original
proof by Mathlib's universe-shrinking theorem.

## No longer needed

No existing imports, nodes, or modules were removed. The explicit range-submodule construction
and range-factorization isomorphism in the original plan are unnecessary: N is the source
stalk, which is isomorphic to the range because its map is injective. Those constructions had
no separate dependency node or module to prune. The original proof dependencies on constant
sheaves, geometric stalks, and exactness of stalks remain used. No unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The plan's last step cited only definition nodes although it requires a nontrivial comparison
of geometric points and its normalization on constant sheaves. This missing interface is now
stated as a separate node. The field comparison is noncanonical, so the lemma asserts existence,
not a canonical choice. The original theorem and node statement remain unchanged.

The command `blueprint_refs.py ancestor` returns a broken created.item chain (the prior delivery
used a Lean module as created.item). The new node copies the existing item's explicit blueprint
ancestor and extends its via list; searches for “stalk functors” and “same point” found no
blueprint statement matching the new comparison. LeanSearch returned HTTP 500 and is recorded
as unavailable, not as a negative search. Loogle, LeanFinder and source grep actually ran.

## New nodes

`lem-weil-pbc-geometric-stalk-comparison-constant`, module
`Sheaf.AlgebraicGeometry.GeometricStalkComparisonConstant`: a natural isomorphism between
module-stalk functors at two separably closed geometric points with the same image, normalized
on every constant module sheaf. Source: Stacks Tag 04FN and the generic submodule paragraph
of Tag 09BH (3), with the separably closed module-valued details written by the worker.
No change record is required because no existing signature or definition changed.

## Second reading by Q2

1. Compared the delivered item against the repository with `diff -u`. The sole existing
   theorem signature and its docstring are byte-for-byte unchanged. Only its proof,
   a proof-only import, and a local elaborator transparency option changed. No target,
   definition, or declaration used by another module was altered; no change record is needed.
2. Both modules compile through `lcompile.py`. The item has no sorry; the new comparison
   theorem is the only new hole and is exactly `:= by sorry`. Scratch-copy `#print axioms`
   checks show only `propext`, `Classical.choice`, `Quot.sound`, and the permitted `sorryAx`.
   There are no prohibited declarations or hollow definitions. N is explicitly the stalk
   of F, j and alpha are explicit composites, and e is constructed inside a theorem proof;
   no definition extracts arbitrary data from the comparison existence theorem.
3. Read the comparison statement and its complete docstring proof against
   [Stacks 04FN](https://stacks.math.columbia.edu/tag/04FN) and the generic-submodule step of
   [Stacks 09BH](https://stacks.math.columbia.edu/tag/09BH). The additional separably closed
   case follows because every finite separable residue extension embeds into the chosen
   separable closure, and all its roots already lie there. The resulting bijections on
   pointed lifts are natural, preserve constant sections, and yield the stated module
   colimit comparison. Identity points, zero coefficients, zero stalks, nonperfect
   separably closed fields in positive characteristic, and an empty scheme introduce no
   counterexample (the empty scheme admits no such points). This is a strictly smaller
   comparison step, independent of the source sheaf, monomorphism, and constant model;
   it is not a restatement of the item. Independent LeanFinder search for an isomorphism
   induced by embedding separably closed fields, Loogle search for site points, and grep
   for geometric comparison and point equivalences found no direct replacement. Read the
   existing geometricPointMorphism_stalk_bijection, isZero_sheafFiber_iff_of_same_image,
   and Point.sheafFiberIso interfaces: the first restricts to algebraically closed fields
   and set/abelian coefficients, the second asserts only vanishing, and the third still
   requires an isomorphism of site points. None closes the field-comparison step in a
   few minutes.
4. The proof constructs the model directly from the chosen stalk and uses constant-stalk
   naturality; no range construction or additional existential model lemma is needed.
   All old proof dependencies remain used. Read `dag/units/sk-thm-p1.json`, including
   `realized`: this internal comparison keeps the curve-devissage route and bypasses
   no realized unit step. The item's existing public import remains necessary for its
   signature. In the new module, replaced the broad public import of ConstructibleSheaf.Defs
   by Mathlib.AlgebraicGeometry.Sites.EtalePoint and
   WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify; together with its existing
   Point.ConstantSheaf import these supply precisely the geometric-point and module-sheaf
   interfaces used by the statement. This removes an unnecessary constructibility import
   from the new module, but prunes no existing dependency node or module from the item.
5. Compared the existing node with the repository: only proof, proof_deps, and proof_origin
   changed, matching the construction and naturality calculation. Checked the new node's
   declaration and verbatim signature, source, proof steps and dependency union, searches,
   status, creator, blueprint ancestor, chapter, and unit. They match the Lean theorem.
   The filtered-colimit size hypothesis is the normalization interface's technical
   instance requirement and is discharged by universe shrinking in the caller.

Second reading changed only the new comparison module's imports and this report.
One original hole closed, one comparison hole added: decomposition, net zero holes;
no existing module pruned. No signature, definition, or DAG statement was changed.
