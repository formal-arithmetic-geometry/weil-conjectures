## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.Curve.GenericTorsionFiniteStalk`
with a proof from the new finite-stalk coverage lemma. The original theorem's name,
universe, hypotheses and conclusion are unchanged.

The proof constructs the nonempty directed poset of finite-stalk subobjects, shrinks
it to universe u+1 using well-poweredness, forms its diagram of inclusions, and applies
Mathlib's subobject-colimit theorem. The proved private helpers `finite_fiber_sup`
and `torsion_of_mono` establish finite-stalk closure under sums and inheritance of
locally torsion sections by monomorphisms. Proof-only imports are
`Mathlib.Order.Shrink`, `WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject`, and
`Sheaf.AlgebraicGeometry.Curve.FiniteStalkSubobjectsCover`.

The new coverage lemma is stated for any field, so it does not assume a curve,
compactness or quasi-separatedness. The DAG now records the actual categorical
assembly. No existing definition or statement was changed; no change record is needed.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.exists_generic_torsion_finite_stalk_colimit`
(node `lem-sc-generic-torsion-finite-stalk-colimit-finite`) from the new coverage lemma.
The item's module has no sorry. Its two private helpers are fully proved.

Accounting: one original hole closed and one coverage hole added. This is a
decomposition, with net zero holes closed, not an axiom-free proof of the item.

One sorry is split off:
`AlgebraicGeometry.Scheme.torsion_finite_stalk_subobjects_iSup_eq_top`, in
`Sheaf.AlgebraicGeometry.Curve.FiniteStalkSubobjectsCover`, node
`lem-sc-field-torsion-finite-stalk-subobjects-cover`.
It states only exhaustion in the subobject lattice; it does not assert a small
filtered presentation or a colimit universal property. The construction and universal
property are proved in the assigned module.

Both modules compile cleanly with lcompile.py --all. The delivery dry run printed
OK, with only the second reading reserved for the second reader; nothing was pushed. Edge cases for the new statement:
the zero sheaf is covered by bottom; a finite sheaf is itself a member of the family;
for a separably closed field it is the union of finite subgroups of an arbitrary
torsion abelian group. An infinite torsion group requires no finite-generation
hypothesis. No axiom or sorry in a definition is introduced.

## No longer needed

Second reading also removed the redundant imports
`Mathlib.Algebra.Category.Grp.AB` and
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject` from the new coverage
module; both were redundant through the retained imports. No existing module is pruned.

No previous DAG dependency or library import is removed: the original node has
empty proof_deps, and the existing public statement imports are retained. Two
redundant proof imports tried during development were removed after compilation:
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject` and
`Mathlib.Algebra.Category.Grp.Biproducts`; both are already available through the
retained imports. No additional module was imported for general constructible
approximation, finite-coefficient module transport, or cohomology: this item needs
only finite-stalk subobject coverage, with categorical assembly in Mathlib.

## Where the brief, the DAG or earlier work was wrong

The node's proof consists of one prose sentence and has no numbered mathematical
dependencies. The finite Galois-stable subgroup construction was not yet a Lean
interface, so it cannot be applied as a supplied declaration. The delivery separates
its precise coverage consequence from the entirely proved diagram construction.

The blueprint and Stacks source trees are absent from this read-only clone. The
existing DAG supplies the blueprint paragraph reference; Stacks Tags 04JQ and 03SA
were read directly from the primary source. The proof remains the specified finite
stable subgroup route. The unit record `sk-prop-cd-affine` has no realized nodes,
and its statement and steps are unchanged. No mathematical statement was disputed.

Further scratch work verified the finite stable submodule step in Lean. Useful
premises for the next proof are `MulAction.orbitEquivQuotientStabilizer`,
`Subgroup.quotient_finite_of_isOpen`, `Submodule.fg_span`, `Module.Finite.of_fg`,
`IsAddTorsion.addSubgroup`, and `AddCommGroup.finite_of_fg_isAddTorsion`.
For a `Rep` carrier, fix its stored `Module ℤ` instance explicitly; the induced
submodule instance and the canonical integer action may require transport using
`Subsingleton.elim`. The uncompleted step is transporting those finite submodule
inclusions through the existing field/Galois equivalence and proving the supremum
inclusion is an isomorphism. This scratch work is outside the delivered Lean tree;
the delivery keeps one complete named coverage obligation rather than more splits.

## New nodes

`lem-sc-field-torsion-finite-stalk-subobjects-cover`:
`lean/Sheaf/AlgebraicGeometry/Curve/FiniteStalkSubobjectsCover.lean`.
It is the finite stable subgroup exhaustion part of the blueprint argument.
Its complete proof in words uses the existing abelian sheaf/Galois-module
equivalence and finite open-stabilizer quotients, followed by the finiteness of
finitely generated torsion abelian groups. The original node is updated to use it.


## Second reading by N1

1. **Interface preservation — pass.** Read the complete diff against the repository.
   The existing theorem's signature and docstring are byte-for-byte unchanged; no
   existing definition changes. Only its proof, proved private helpers and private
   proof imports are added. The coverage theorem is new, with its own module/node.
   No existing public import is changed and no change record is required.
2. **Proof and trust — pass as a decomposition.** Compiled both delivered modules
   locally in dependency order without errors or warnings. A scratch copy's
   `#print axioms` checks show only `propext`, `Classical.choice`, `Quot.sound` for
   `finite_fiber_sup` and `torsion_of_mono`. The original theorem and the coverage
   theorem additionally use `sorryAx`, as explicitly reported. There is exactly one
   delivered sorry, the whole proof of the named coverage theorem; no hollow
   definition, custom axiom or forbidden implementation device. Reviewed the
   supremum closure, shrinking equivalence, reindexing and cocone universal property.
3. **Split statement — pass.** The coverage obligation is the exhaustion step,
   strictly a part of the argument: it contains no chosen small filtered category,
   diagram, torsion assertions for its objects or colimit universal property. The
   original module proves all that assembly. Read its full proof docstring and DAG
   node, and checked Stacks [04JQ](https://stacks.math.columbia.edu/tag/04JQ) and
   [03SA](https://stacks.math.columbia.edu/tag/03SA). Open stabilizers have finite
   index by compactness; the orbit-generated subgroup is finite and invariant.
   Transported inclusions cover every element of the conservative stalk. Zero and
   finite sheaves, a separably closed field with an infinite torsion group, and an
   imperfect field all satisfy the statement (the geometric point is an algebraic
   closure, not a separable closure). Repeated LeanFinder, Loogle and grep searches
   with different queries: no existing coverage result; Loogle finds precisely the
   Mathlib subobject-colimit assembly theorem already used here. Direct searches of
   both library roots found no duplicate. The prior finite-submodule scratch proof
   addresses only the algebraic step; finishing equivalence transport is not a
   short local repair, so the one honest coverage obligation remains.
4. **Route and pruning — pass after import cleanup.** The finite stable subgroup
   route is retained; the unit `sk-prop-cd-affine` has empty realized entries, and
   its statement/steps are unchanged. The old node has empty proof_deps, so there
   are no obsolete old dependencies to list. Removed two redundant public imports
   from the new coverage module: `Mathlib.Algebra.Category.Grp.AB` and
   `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject`; scratch compilation
   established that both are already available through its retained imports. These
   are removals from a new module, not pruning of an existing reachable module.
5. **DAG agreement — pass.** The original node changes only proof, proof_deps and
   proof_origin. Its single actual dependency is the coverage node. The new node's
   statement/signature, source, full proof steps, union of uses, origin, searches,
   creation record, blueprint ancestry, chapter/unit and Lean record agree with the
   delivered declaration. The named existing Galois equivalence and torsion-stalk
   criterion provide the interfaces its future proof needs.

Second-reading changes: removed the two redundant imports above and explicitly
classified the delivery as one-hole-for-one-hole decomposition (net zero). No Lean
proof or statement needed repair. No existing module is pruned.
