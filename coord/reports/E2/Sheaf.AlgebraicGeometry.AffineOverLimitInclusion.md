## What changed

Proved `AlgebraicGeometry.isLimit_affineOver_inclusion` in
`Sheaf.AlgebraicGeometry.AffineOverLimitInclusion`, keeping its complete signature and
visibility unchanged. Defined a private, explicit contravariant structure-algebra functor
on all schemes over the base. Proved its Hom map bijective when the target is affine over
the base, including arbitrary source schemes. The local gluing helper adapts the existing proved private helper in
`AffineStructureAlgebraFullyFaithful`; it contains no holes. Extensionality is proved
directly inside the injectivity part of `structureAlgebra_bijective`.

The relative-spectrum anti-equivalence takes the given cone to a quasi-coherent algebra
colimit. `quasiCoherentAlgebra_colimit` and full-subcategory creation make it a colimit in
all algebra sheaves. A natural isomorphism identifies that cocone with the explicitly
constructed structure algebras. The Hom bijection then transfers the algebra universal
property to the requested scheme universal property, with explicit factorization and
uniqueness proofs.

Added the proof-only import `Sheaf.AlgebraicGeometry.AffineAlgebraLocalMaps`.
The second reader removed redundant direct imports of
`Mathlib.CategoryTheory.Limits.FullSubcategory` and
`Mathlib.CategoryTheory.Adjunction.Limits`; their needed declarations and instances
are already available through the remaining imports. Retained both original proof
imports and both public statement imports. Updated the node's proof, proof dependencies and proof origin.
No existing statement or definition changed, and no other module was adapted.

The source pages were read at [Stacks 01YX](https://stacks.math.columbia.edu/tag/01YX),
[Stacks 01SA](https://stacks.math.columbia.edu/tag/01SA), and
[Stacks 01LT](https://stacks.math.columbia.edu/tag/01LT), since the referenced local Stacks
TeX files are absent from this clone. Short-route searches used the required leanfinder,
loogle and grep services. Their relevant results were affine-scheme preservation
(which does not handle an arbitrary base) and full-subcategory colimit creation.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.isLimit_affineOver_inclusion`
(node `lem-weil-pbc-affine-over-limit-inclusion`). No `sorry` remains in the item and no
hole was added elsewhere: 1 hole closed, 0 added, 0 split off.

The proof uses the existing declarations `affine_morphism_relative_spec`,
`Scheme.quasiCoherentAlgebra_colimit`, and `affine_algebra_local_maps`, together with
Mathlib. Their existing downstream dependencies are not claimed to be axiom-free here;
the item's complete proof is from those recorded declarations, as stage 3 requires.
The private functor's data and laws are explicitly constructed. The scheme factorization
is chosen through a proved bijection, so its algebra map determines it uniquely.

## No longer needed

Removed the direct proof dependency `lem-weil-pbc-spec-colimit-limit`: the proof does not
construct spectrum charts of the cone or apply preservation of ring-colimit spectra.
This node is already a Mathlib leaf, so this does not remove a pending Sheaf module.
Removed the duplicate private declaration `AlgebraicGeometry.affine_over_ext`;
its local restriction argument now lives inside the strictly more specialized
structure-algebra injectivity proof. No import from the repository version was removed. The second reader removed the
redundant added imports `Mathlib.CategoryTheory.Limits.FullSubcategory` and
`Mathlib.CategoryTheory.Adjunction.Limits`. No Sheaf module is asserted to leave the
targets' import closure. The gluing dependency stays: its Mathlib realization is used directly.
The relative-spectrum and quasi-coherent algebra-colimit modules stay and are needed.
Added the used local-map node `lem-weil-pbc-affine-algebra-local-maps` to proof dependencies.

The item's node is absent from `dag/units/sk-thm-p1.json`'s `realized` statements and steps;
this shortening is below the unit level and leaves that unit's route intact.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned explicit spectrum-limit chart argument is
unnecessary: the structure-algebra Hom correspondence for arbitrary test schemes
already supplies the local universal property, and the algebra colimit gives the
factorization. This correspondence is obtained from existing local maps and Mathlib
gluing, without assuming quasi-separatedness or affineness of the source. The proof also
works for the empty base and empty inverse-image opens: the affine basis and its cover
extensionality include those cases.

The original theorem docstring described the longer chart argument; it now describes
the Lean proof actually delivered. Only the sandbox was edited. Compilation uses
`lcompile.py`; the final check uses `deliver3.py --no-push`.

Repair of return X-75186: the exact duplicate `affine_over_ext` declaration was removed.
The library's existing theorem is private, so importing its module cannot expose it.
Changing that module's visibility would violate the forced-adaptation rule. Instead,
the extensionality argument is incorporated into the existing Hom-bijection proof,
whose hypothesis is equality of structure-algebra maps. No duplicate statement or
new helper is left, and no existing public signature changes. The repaired file compiled
cleanly with `lcompile.py` (7.9 seconds). The earlier second reading below predates this
repair and must be refreshed by the next reader.

## Earlier second reading (a previous round; superseded)

1. **Unchanged interface: PASS.** Compared the entire delivered module and node with
   the repository using `diff`. Independently compared the existing theorem's signature
   as literal text: it is byte-for-byte identical, including all binders and the conclusion.
   There are no pre-existing definitions to change, no forced adaptations, and no change
   records. The only added declarations are private proof helpers and the explicit private
   structure-algebra constructions; existing visibility and both public imports are kept.
2. **Proof and data: PASS.** Independently compiled the delivered file with `lcompile.py`
   (9.9 seconds, no errors or warnings). A scratch copy with `#print axioms` for the main
   theorem and all six private declarations compiled (12.9 seconds). Every private
   declaration uses only `propext`, `Classical.choice`, and `Quot.sound`; the main theorem
   additionally reaches `sorryAx` through existing imported statements. No forbidden
   declaration or option, local `sorry`, or holed definition occurs. The functor's objects,
   morphisms and laws are explicit. The chosen scheme factorization is determined uniquely
   by the proved Hom bijection. The chosen algebra colimit is determined by its universal
   property; the equivalence's object and morphism clauses determine the forward functor
   used here, and the inverse functor is not used by this proof.
3. **Split statements and edge cases: PASS (none split off).** No new public statement,
   new node, or new hole is delivered. Read the existing `affine_algebra_local_maps` and
   the proved private helpers of `AffineStructureAlgebraFullyFaithful`. The duplicated
   private helpers are needed for arbitrary test schemes, whereas the existing public
   full-faithfulness theorem restricts both schemes to affine structure morphisms.
   Checked the empty base, empty inverse-image opens, singleton index diagram, and
   arbitrary nonaffine test schemes: the affine-basis cover, Gamma--Spec extensionality,
   and gluing handle these without additional hypotheses. Also checked nonaffine
   intersections: the local-map theorem covers them by smaller affine opens.
4. **Route and pruning: PASS.** Repeated searches with different words using leanfinder
   (relative spectrum as a right adjoint), loogle (`IsLimit` and `Functor.mapCone`),
   msearch grep (structure algebra, relative adjunction, affine limit preservation),
   and `rg` on both library roots. No existing arbitrary-base preservation theorem or
   public arbitrary-source structure-algebra Hom bijection was found. The Gamma--Spec
   adjunction results concern globally affine targets; generic faithful-functor transport
   still requires the Hom lifting proved here. The existing relative-spectrum and algebra
   colimit imports are used, as are the new local-map, colimit-creation and adjunction
   imports; all added imports are proof-only. The public imports supply the scheme,
   affine-morphism and limit-cone statement vocabulary. Compared old and new `proof_deps`:
   the sole removed dependency is `lem-weil-pbc-spec-colimit-limit`, already listed in
   `No longer needed`. No module is pruned. Read `dag/units/sk-thm-p1.json`: this item is
   absent from its realized statement and every realized step, so the unit route stays.
5. **DAG and source agreement: PASS.** The only changed node fields are `proof`,
   `proof_deps`, and `proof_origin`. Their four steps match the Lean construction:
   ambient colimit creation, natural-isomorphism transport, the arbitrary-source Hom
   bijection using local maps and gluing, and explicit factorization/uniqueness.
   Their dependency union is exactly `proof_deps`. Independently read
   [Stacks 01YX](https://stacks.math.columbia.edu/tag/01YX),
   [Stacks 01SA](https://stacks.math.columbia.edu/tag/01SA), and
   [Stacks 01LT](https://stacks.math.columbia.edu/tag/01LT) to check the cited construction
   and the arbitrary-test-scheme universal property. No new-node requirements apply.

**Second-reader changes:** Added this review and the explicit axiom-check qualification
above. No Lean proof, statement, definition, import, or DAG repair was necessary.
The delivery closes `AlgebraicGeometry.isLimit_affineOver_inclusion`, adds zero holes,
and splits off zero statements; its transitive imported holes remain open.

## Second reading by E2

1. **Interface: PASS.** Diffed the sole delivered module against the repository and
   compared the existing theorem signature as literal text: all binders, hypotheses,
   conclusion and visibility are unchanged. Both public statement imports remain.
   No existing definition changes, forced adaptations, or change records occur.
2. **Proof: PASS.** The repaired module compiled cleanly with `lcompile.py` (7.3 s).
   A fresh scratch copy printed axioms for the main theorem and all five private
   declarations (7.8 s): each private declaration uses only `propext`,
   `Classical.choice`, and `Quot.sound`; the main theorem additionally uses `sorryAx`
   from existing imported results. No local hole or forbidden construct occurs.
   The structure-algebra object, maps and functor laws are explicit constructions.
   The lift is chosen through the proved bijection and is uniquely determined by
   its algebra map. The algebra-colimit witness is fixed up to the universal-property
   equality used downstream. The equivalence's stated object and morphism clauses
   determine its forward functor; its inverse is unused here.
3. **Split statements and small cases: PASS.** No new public statement, node, or hole
   is added, so there is no split statement to close. Read the local-map theorem and
   the private helpers of `AffineStructureAlgebraFullyFaithful`. The removed duplicate
   `affine_over_ext` is absent; injectivity follows directly from the equality of
   algebra maps. The remaining gluing helper is private in the existing module and
   unavailable to clients. The public full-faithfulness theorem restricts the source
   to affine-over-base objects and cannot serve arbitrary test schemes here.
   Checked empty base, empty inverse images, singleton diagrams, arbitrary nonaffine
   test schemes and nonaffine overlaps: affine basis extensionality, the Gamma--Spec
   adjunction and cover gluing handle them without extra hypotheses.
4. **Route and pruning: PASS, with import repair.** Repeated leanfinder search for
   affine-over inclusion preserving directed limits, loogle for colimit transport
   (the successful fully qualified `IsColimit.mapCoconeEquiv` query), msearch grep
   for `structureAlgebra|relativeSpec|affineOver`, and `rg` across both library roots.
   No shorter public theorem for arbitrary base and arbitrary test scheme was found.
   Generic colimit transport is already used. The only old proof dependency removed
   is `lem-weil-pbc-spec-colimit-limit`, explicitly reported above; gluing remains.
   Read `dag/units/sk-thm-p1.json`: the item is absent from its realized statement and
   steps, so the unit route stays. Both added Mathlib imports were individually
   redundant; a scratch file with both removed also compiled cleanly (9.1 s).
   Removed both from the delivered file. All remaining proof imports supply the
   relative equivalence, ambient colimit or local maps; no module is claimed pruned.
5. **Nodes: PASS.** JSON comparison shows changes only in `proof`, `proof_deps`,
   `proof_origin`. The four steps match the Lean proof: ambient colimit creation,
   natural-isomorphism transport, arbitrary-source Hom bijection, then factorization
   and uniqueness. Their dependency union equals `proof_deps`. No new-node fields
   are needed. Checked the cited argument against
   [Stacks 01YX](https://stacks.math.columbia.edu/tag/01YX),
   [Stacks 01SA](https://stacks.math.columbia.edu/tag/01SA), and
   [Stacks 01LT](https://stacks.math.columbia.edu/tag/01LT).

**Second-reader changes:** Removed two redundant added Mathlib imports, corrected the
current report's import account, and refreshed this review after the X-75186 repair.
The proof and DAG needed no further repair. Closed one hole
(`AlgebraicGeometry.isLimit_affineOver_inclusion`), added zero holes, split off zero
statements, and pruned no module.
