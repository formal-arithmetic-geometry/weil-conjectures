## What changed

Replaced the sorry in
`AlgebraicGeometry.surjective_structureSheafMap_stalk_of_proper_flat_fiber`
with a complete Lean reduction. The declaration's signature and public imports are unchanged.
The proof uses `perfect_derivedDirectImage_baseChange` on the structure sheaf, which is
finitely presented and relatively flat because it is invertible and f is flat.

Two new modules separate the missing parts of the original argument:
`PerfectLocalDegreeZeroUnit` supplies the local perfect-complex criterion;
`FlatDerivedStructureUnit` supplies the derived unit and its fibre/H0 comparisons.
The latter only assumes a quasi-compact separated flat morphism and does not assume
properness, finite presentation, or the fibre isomorphism when constructing the lift.
Its conclusion does not assert ordinary stalk surjectivity. The former has no morphism
f and applies to an arbitrary perfect complex and derived arrow at one point.

The existing theorem `tensorPullbackObjUnitToUnit_isIso` supplies the final identification
with the chosen adjunction unit. Transport through the H0 comparison square and cancellation
of the pushforward tensor-unit isomorphism are proved explicitly, using the abelian stalk
functor. A proved private helper cancels an isomorphism from a surjective composite.
All three modules compiled together without errors or warnings through lcompile.py.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.surjective_structureSheafMap_stalk_of_proper_flat_fiber`
(node `lem-sc-proper-flat-structure-sheaf-stalk-surjective`). Its module has no sorry left.

Added two holes, each the entire proof of a public theorem in a separate new module:

- `AlgebraicGeometry.surjective_stalk_homology_of_perfect_local_unit`
  (node `lem-sc-perfect-local-degree-zero-unit`, module
  `Sheaf.AlgebraicGeometry.PerfectLocalDegreeZeroUnit`).
- `AlgebraicGeometry.exists_flat_derived_structure_unit`
  (node `lem-sc-flat-derived-structure-unit`, module
  `Sheaf.AlgebraicGeometry.FlatDerivedStructureUnit`).

This is a decomposition, not an unconditional proof: one upper hole closed and two lower
holes added. No axiom or definition was added. No definition chooses data from either hole;
the existential derived lift is eliminated only inside the theorem proof.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel`
from the assigned module. Its node `lem-sc-perfect-finite-free-residue-model` remains needed
by `PerfectLocalDegreeZeroUnit`, so neither that node nor its module is pruned from the
transitive argument. All three dependencies in the original plan remain needed, directly
or through the new comparisons. No original node or module is claimed pruned from the closure.

New proof imports in the assigned module are `PerfectLocalDegreeZeroUnit`,
`FlatDerivedStructureUnit`, `TensorPullbackStructureSheaf`, and the source library's
`Algebra.Category.ModuleCat.Sheaf.LocallyFree`. Each is used by the written proof.
The general all-points `PerfectDegreeZeroFibreCriterion` was searched and read but is not
imported: its hypotheses do not follow from this one-point hypothesis.

## Where the brief, the DAG or earlier work was wrong

The original plan's two main modules supply perfectness/base change and a finite-free
representative, but they do not directly state the derived unit's H0/fibre compatibility or
the one-point degree-zero criterion. The new nodes expose precisely those remaining tasks.
The unit route is preserved: both new nodes carry sec-abelian-varieties/sk-prop-av-cube,
and the original base-change and minimal finite-free-model argument remains below them.

The existing all-points criterion cannot be applied with a single fixed-fibre hypothesis;
no condition on other fibres was introduced. The local criterion was checked on a
one-point local scheme with nilpotents: invertibility of the residue coefficient makes
it a unit and kills the outgoing differential, without any reducedness assumption.
For an empty scheme its pointwise statement has no input point. For an empty fibre the
canonical field-to-global-functions map cannot be invertible, so no invalid nonemptiness
conclusion is used. The derived-unit comparison itself also allows empty schemes and fibres.

Sources read: [Stacks Tag 0E62](https://stacks.math.columbia.edu/tag/0E62), first paragraph
and the local degree-zero argument, and [Stacks Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD),
the minimal finite-free local model. The finite-free chain-map argument expands the local
proof already documented in the assigned declaration. Mathlib searches found no exact
statement; LeanSearch returned Internal Server Error, recorded as unavailable.

`blueprint_refs.py ancestor` did not resolve the assigned module's node because its
created.item is a module name. Reading the explicit ancestry gives thm-sc-theorem-of-cube;
the new nodes record that ancestor and the intervening nodes. Whole-blueprint searches for
0E62, degree-zero, and structure unit found no exact substitute for either new statement.

## New nodes

`lem-sc-perfect-local-degree-zero-unit` records the local algebraic part of steps 1–2 of
the original plan. Its proof uses the existing finite-free residue model and affine
chain-map representative, then the local-ring unit argument. The hypotheses concern one
point only. It is a general perfect-complex result, not a renamed proper-flat stalk theorem.

`lem-sc-flat-derived-structure-unit` records construction of the derived unit and its
ordinary H0 and derived-fibre comparisons, combining the geometric part of step 1 with
step 3. It uses canonical relatively flat base change and the tensor structure-sheaf
identification. It neither asserts perfectness nor proves the local stalk criterion.
There are no change records or forced adaptations: every existing signature is unchanged.


## Second reading by N1

1. **Interfaces: pass.** Diffed the assigned module against the repository. Its sole
   existing public declaration has a byte-for-byte identical signature, docstring and
   public imports. Only its proof, private proof helper, local elaboration options and
   private imports changed. The other two modules are new; no definition or existing
   statement is altered, and no change record is required.
2. **Kernel and holes: pass.** Independently compiled all three modules in import order
   with lcompile.py, with no errors or warnings. Scratch copies with `#print axioms`
   show only propext, Classical.choice, Quot.sound and sorryAx. The latter is expected:
   both new named theorems and upstream dependencies remain open. There are exactly two
   delivered sorries, each a whole public theorem with its source, prose proof and node.
   No forbidden declaration or hollow definition occurs. The existential derived lift
   is eliminated in a proposition proof, never used to define arbitrary data.
3. **Split statements: pass.** Read the finite-free model, affine chain-map representative,
   canonical relatively flat base change, derived direct-image construction and tensor
   unit comparison. Checked Stacks [0E62](https://stacks.math.columbia.edu/tag/0E62),
   [0BCD](https://stacks.math.columbia.edu/tag/0BCD), and
   [0A1D](https://stacks.math.columbia.edu/tag/0A1D). The local criterion is true over
   nonreduced local rings: invertible residue makes the degree-zero coefficient a unit,
   and the chain-map identity kills the outgoing differential. The derived comparison
   needs no properness: quasi-compact separated relative-flat base change applies.
   Empty X is permitted in that comparison; its fibre-isomorphism premise then fails
   at any actual base point. Neither statement restates the assigned theorem: one is
   a local perfect-complex computation, the other constructs and compares the derived
   unit without asserting stalk surjectivity. New searches using Nakayama/zeroth
   cohomology and DerivedCategory.homologyFunctor (LeanFinder, Loogle, and Mathlib grep)
   and repository searches found no exact replacement. The existing all-points fibre
   criterion cannot be applied from a fixed-point assumption. Closing either new hole
   requires substantial derived/sheaf transport, not a short missing Mathlib application.
4. **Route and pruning: pass, with a pre-existing metadata limitation.** Checked the
   H0 comparison square and final cancellation explicitly: both comparison maps and the
   pushforward tensor-unit map remain isomorphisms under the abelian stalk functor.
   All three old proof dependencies are still used, the finite-free model transitively
   through the local criterion. Its removed direct import is listed above; no module is
   pruned from the closure. New proof-only dependencies are private imports. Tested
   removing PullbackFree from the new comparison module: Lean requires its public import
   because unitToPushforwardObjUnit occurs in the signature, so restored it. The cube
   unit and its general-cube route are unchanged. Its repository `realized.statement`
   and `realized.steps` lists are already empty; this delivery does not fill or bypass
   those pre-existing unit records.
5. **Nodes: pass.** Checked the new node fields, source and ancestry, verbatim Lean
   signatures, and union of step uses against proof_deps. The assigned node follows
   the actual perfectness, local-unit, H0-transport and tensor-cancellation proof. New
   nodes expose strictly intermediate tasks, with the same chapter/unit and full searches.

Second reading changed only the derived comparison module's source citation from
Tag 0B91 (proper finite-presentation base change) to Tag 0A1D (the relatively flat
quasi-compact separated base change actually used). Its node already cites 0A1D.
No proof or statement repair was necessary. Added this independent review and the
pre-existing empty unit-realization observation. Hole accounting remains one original
hole closed, two added: a decomposition with net -1, not an unconditional proof.
