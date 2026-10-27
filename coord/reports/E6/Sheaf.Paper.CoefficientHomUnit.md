## What changed

Returned-delivery repair (reviewer C-fcfa9, head `fcfa912c0fe`): the independent
review passed; landing failed while resolving a reviewer fix by a bare filename.
The evaluation change record is delivered at the repository-relative path
`coord/changes/E6-coefficient-hom-unit-evaluation.md`. The stage-3 landing tool's
flat reviewer-fix filename for that record is
`E6-coefficient-hom-unit-evaluation.change.md`, as specified by
`tools/batch_land.py:fixes`; the failed attempt used the record's ordinary `.md`
basename instead. The other records are
`coord/changes/E6-normalized-coefficient-comparison.md` and
`coord/changes/E6-product-hom-complex-data.md`.

Reconciled the retained packet with current `sheaf-dag`: preserved the newly
published `ringedCompletionHasSheafCompose`, the three
`ringedHomUnitEvaluationIso_hom_f`,
`ringedHomUnitEvaluationIso_hom_f_projection`, and
`ringedHomUnitEvaluationIso_naturality` theorems, their private proof import, and
their existing signatures. The two component proofs now use the proved evaluation
API; the naturality proof and the sheaf-composition helper are unchanged. These
declarations were absent from the returned packet and are now retained alongside its proved evaluation API.
The supporting module is currently unclaimed. No additional hole is closed or added.

Proved `CategoryTheory.exists_coefficientHom_unit` by constructing the localized
map `m ↦ (b ↦ b • m)` on presheaves and lifting it to sheaves, transporting
its B-linearity through the coefficient-Hom comparison, and lifting its degree-zero components to the product Hom complex.
Naturality and differential compatibility follow from the projection formulas.
Restriction, precomposition with the coefficient map, and evaluation at one give
the identity in every degree. The literal degree-zero identification is the
identity, so the final diagram uses the underived unit normalization and evaluation law directly. No general
transport theorem is needed. The assigned theorem's statement and both existing
public imports are unchanged.

Reused the existing restricted coefficient-Hom complex comparison. Its normalized comparison
helper now retains the projection equation that its product-universality proof
already establishes. Its public existence theorem keeps exactly its former
statement. The proof uses the named Hom bifunctor, eliminating the large local
functor definition that repeatedly unfolded during specialization. Its actual
projection has a typed API, proved equal by reflexivity to `homComplexπ`.
Its source uses the named complex bifunctor and its target the native internal
Hom. The underived comparison map is the original `i.hom.app`, with the same
native internal-Hom target. These matching endpoints avoid repeated conversion
through the concrete sheaf-module structures.
The seven documented comparison/projection helpers form a public API attached
to the same node. The unit uses an ordinary proof import rather than importing
all private declarations. The unit proof uses the pointwise naturality and
evaluation laws before passing them to the abstract product argument. The product
comparison is checked over abstract categories in that same existing module.
Change record: `coord/changes/E6-normalized-coefficient-comparison.md`.

Represented `ProductHomComplexSpecification` by `Nonempty ProductHomComplexData`,
with named projection, limit, differential and naturality fields.
`productHomComplexSpecification_iff` proves equivalence with the previous
existential proposition verbatim. The explicit product construction supplies
the same data and proved laws. The comparison and unit constructors consume
this data directly after unpacking the existence proposition once, rather than
repeatedly applying choice to that proposition. The two source categories of the specification
need only zero morphisms; its output category retains preadditivity. Under the
original assumptions the equivalence has exactly the previous right side.
Its two consumers are adapted together.
Change record: `coord/changes/E6-product-hom-complex-data.md`.

Refactored `CategoryTheory.ringedHomUnitEvaluationIso` in the unclaimed module
`Sheaf.CategoryTheory.RingedCompletionUnit`: its components are expressed
directly by the actual product projections. The new public component map and
its three proved API lemmas are attached to the existing definition node.
A private Lean theorem proves equality with the entire previous isomorphism.
Its functor presentation uses the same isomorphism with its source expressed by
`homComplexFunctor`, with proved inverse and component equations. This new
presentation abstracts the sheaf-composition instance proof, allowing its
consumer to use the same instance throughout the diagram. The final unit
identity uses this presentation and the normalized projection formula. A new
proved evaluation API removes the identity precomposition at literal zero.
The component definition retains its previous formula, including the existing
consumer equality proved by reflexivity.
The public import of `HomComplexComponents` supplies the projection definition.
Change record: `coord/changes/E6-coefficient-hom-unit-evaluation.md`.

The supporting comparison and evaluation modules locally prefer the
limit-preservation instance for sheaf composition. The unit module follows the
imported declarations' canonical instance choices, including zero objects.
Its product proof uses sheaf limits directly. The private unit construction
takes the actual ring complex, its degree-zero unit map and its vanishing
laws as input, avoiding repeated conversion through the single-complex definition. The explicit base-unit map and
its proved comparison law are exposed through an existential theorem; the
normalization determines the map because restriction is faithful.

The change records list the consumers. Target statement review is reopened
under the definition-change rule; the exact proposition equivalence and the
whole-isomorphism equality document preservation of meaning. No adopted
source-library module is changed.

Compatibility checks: the unchanged `RingedKoszulFiniteEvaluation` source
compiles against the repaired support in 8.8 seconds. The unchanged
`RingedKoszulSystem` source produced no Lean errors but exceeded the 60-second
file limit against the repaired support (87.6 seconds), as it did against the
original published library (81.7 seconds). No adaptation of that module is
included. The whole-isomorphism equality checks the semantic effect for every
listed user.


The rebased four-module set compiles without warnings; the assigned item takes
59.1 seconds and the rebased completion-unit support takes 26.4 seconds.
A separate compatibility check reproduces the existing consumer's
evaluation-component equality by `rfl` against this rebased set in 11.3 seconds.
The probe is archived outside the delivered `lean/` tree.


## Proved and sorry left

Closed the one existing hole in `CategoryTheory.exists_coefficientHom_unit`
(node `lem-weil-pbc-coefficient-hom-unit`). Added zero holes and zero split-off
statements. No `sorry` remains in any of the four changed Lean modules.
The supporting definition repairs and the strengthened comparison API add
zero holes; every new API lemma and equality certificate is proved.

## No longer needed

Neither existing public import of the item was removed. In
`RestrictedCoefficientHomComplex`, the private proof import of
`WeilConjectures.Algebra.Homology.HomComplexProjections` is replaced by a public
import of `WeilConjectures.Algebra.Homology.HomComplexComponents`, required by
the public typed projection definition. It publicly imports the projections
and supplies the component API. The projections node remains used.
All declared dependencies are used, including the restricted coefficient-Hom complex module's normalized comparison
API. No DAG node or module is pruned or withdrawn.

## Where the brief, the DAG or earlier work was wrong

The existing complex-comparison helper discarded its projection equation when
returning only an unspecified isomorphism. The final unit identity needs that
equation, so the existing proof now retains it for its consumer.

Specialization repeatedly unfolded the large existential product specification
and a local Hom-functor definition. Named structure fields and the existing
named Hom bifunctor provide the same mathematical data with a smaller interface.
The original evaluation isomorphism also forced repeated conversion through the
chosen Hom-complex construction. Its projection representation is identified
with the previous entire isomorphism by a proved equality.

No statement was found false or weakened, and no fixed blueprint unit step is
bypassed. No new DAG node is needed: the new data and API declarations are
attached to the existing product-complex and completion-unit nodes.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
