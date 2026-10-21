## What changed

Proved `WeilConjectures.point_sections_finite_reduction_iso` by an explicit ordinary
scalar-extension comparison, bounded-above flat replacements, invertible K-flat
counits, and naturality for derived morphisms represented by fractions. The mixed
total-tensor comparison includes a checked pure-tensor formula, not an arbitrary
choice of natural isomorphism.

Repaired and proved `WeilConjectures.point_sections_finite_reduction_complex`: it now
constructs a normalized family rather than asserting normalization of every family.
The parent `point_sections_finite_reduction`, the iso theorem and the bounded theorem
retain their signatures verbatim. The parent assembles this constructed family with
the boundedness theorem. The bounded sheaf clause is re-proved using flat models,
while the existing R1 module upper-bound theorem is retained unchanged.

`PointSectionsFiniteReductionData` extracts the existing data declarations to avoid
an import cycle with the new ordinary algebra lemma. It adds a typed universal
change-of-rings model, proved nonemptiness, a named counit and a typed natural sections
factor. The ordinary functor is fixed by its actual object and map equations, and the
derived pair by its universal property. This changes the presentation of chosen data,
not the tensor construction or its normalized meaning. Thin aliases become abbrevs;
no definition contains a hole. The change record explicitly requests semantic review
of targets using these definitions. All original public imports remain publicly
reexported. No adopted source-library declaration is changed.

`PointFiniteReductionSectionAlgebra` proves both preservation of flatness by point
sections and the ordinary scalar-extension comparison with its generator equation.
Every cover at the final algebraically closed point contains the identity, so local
flat relations are global and sheafification changes no final sections. This avoids
the DVR ideal argument entirely and works for the zero quotient and infinite modules.

The user table also covers all 49 transitive downstream modules because the public
sheafification instances moved with their signatures, attributes and bodies intact.
Their public reexports preserve access. The direct changed-choice consumer audit includes `PointReductionUnits`,
`PointReductionUnitNormalization`, and the newly present
`FixedStalkIdentificationReduction`. Two public proofs in `PointReductionUnits` are adapted
from the old existential projections to the typed witness fields. Its private
sheaf-adjunction proof also eliminates existential witnesses before applying the
cochain normalization, avoiding repeated reduction of nested choice projections. Their signatures,
visibility and public imports are unchanged. The private proof now destructs the
existing adjunction witness before applying the cochain lemma, avoiding repeated
conversion of its nested choice projections; its profiled prefix decreased from
29.3 to 13.7 seconds. The other consumers require no edits.
The ordinary-module and sheaf localization universes stay as previously published.
All four delivered modules compile, and the unchanged module-bound, fixed-stalk and
unit-normalization consumers were also compiled against this interface. The final
unit-consumer pair passed without warnings (47.4 and 32.1 seconds respectively).

Change records:
`coord/changes/T4-point-finite-reduction-typed-model.md` and
`coord/changes/T4-point-finite-reduction-normalized-existence.md`.

## Proved and sorry left

Original item: two holes. The unchanged statement of
`WeilConjectures.point_sections_finite_reduction_iso` is proved. The other original
hole, `WeilConjectures.point_sections_finite_reduction_complex`, had a false statement;
its corrected existential statement is proved. This is one proof of an original
statement plus one statement repair and proof, not a proof of the old false statement.
The current item contains zero `sorry`.

New public theorems, both fully proved:
`WeilConjectures.nonempty_pointFiniteReductionSheafModel` and
`WeilConjectures.pointFiniteReductionSectionAlgebra`. Every private helper is proved.
No holes are added and no unfinished result is split off. The copied module-bound
and unchanged consumer files are verification inputs, not new statements or holes.
The existing consumer holes are untouched. The proof uses the library's existing
stated dependencies as permitted by stage 3; this report does not claim the entire
transitive target closure is free of `sorryAx`.

## No longer needed

Removed proof imports from the original item:

- `Sheaf.Paper.ConstantModuleSectionProperties`
- `WeilConjectures.Algebra.Homology.BoundedFlatReplacement`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Sheaf.Algebra.Homology.RingedTensorCohomologicalBounds`
- `Mathlib.AlgebraicGeometry.Sites.ConstantSheaf`
- `Mathlib.RingTheory.Flat.Tensor`
- `Mathlib.Algebra.Homology.DerivedCategory.Plus`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`

The old planned DVR, principal-ideal and continuous-function routes are unused:
`lem-weil-l-adic-extension-integers-dvr`,
`lem-cbc-continuous-functions-fpqc-sheaf`,
`lem-weil-pbc-constant-module-section-properties`, and
`lem-weil-pbc-flat-fg-ideal-criterion` are unnecessary inputs to this proof.
The local equational flatness criterion and the final-point identity-cover fact
replace them. Thus their statement modules need not be added to prove this item.

`lem-pc-kflat-bounded-flat-replacement` and
`lem-pc-bounded-above-flat-kflat-site` have same-universe interfaces unsuitable for
the point site here. They are replaced by the existing independent-coefficient
functorial flat resolution and bounded-flat K-flat criterion. The flat-model
construction directly retains the termwise flatness needed by the normalized
comparison. `lem-weil-pbc-ringed-tensor-cohomological-bounds` is unnecessary: the
sheaf upper bound follows directly from this model's counit.

`lem-weil-pbc-bounded-below-cochain-localization` and the separately planned use of
`lem-weil-pbc-localization-universal-property` are unnecessary to the descent proof;
Mathlib's `DerivedCategory.right_fac` and cancellation of a quasi-isomorphism give
the required naturality directly. No opposite-category degree reversal is used.
The main assembly no longer needs a separate choice from the iso theorem: the
complex theorem constructs the same natural comparison with its normalization.
The iso theorem itself remains needed by the recorded complex route and is proved.

The new proof routes and their actual dependencies are recorded in all four item
nodes. No library module is withdrawn or deleted; in particular all adopted source
public declarations remain. This is pruning of this proof's dependencies, not a
claim that those modules are unreachable from every other target.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the old complex lemma's universal quantification over `e` was
false. Multiplication by -1 preserves a natural isomorphism but changes its
normalized counit square. For l=3, n=j=1, a degree-zero nonzero free coefficient
module detects the difference. The blueprint and unchanged parent need a constructed
normalized comparison. The corrected node records the old statement and audits its
only citer, `lem-trf-point-sections-finite-reduction`, whose use still holds.

The original same-universe flat replacement and site K-flat declarations do not fit
the independent site/coefficient universes of these point sheaves. The existing
independent-coefficient versions do. Also, a chosen derived functor is not
definitionally the functor chosen by a separate existence theorem. The typed model
and direct counit proof avoid relying on this accident of old choice expressions.

The generic complex statement assumed an arbitrary comparison was canonical; the
repair constructs the comparison from its counits. No hypothesis is added to the
parent and no target statement or unit route is changed.

## New nodes

`lem-trf-point-finite-reduction-section-algebra` attaches the proved ordinary
comparison and flat-sections theorem, including its generator normalization.

`lem-trf-point-finite-reduction-sheaf-model` attaches the proved nonemptiness of the
typed universal pair. Its selected data are fixed by actual ordinary equations and
the derived universal property, not by arbitrary existence.

`lem-trf-point-cover-identity` attaches the existing proved source declaration
`AlgebraicGeometry.Scheme.ProEt.id_mem_of_mem_topology_of_iso` without editing it.

`lem-trf-point-sheafification-final` attaches the existing proved source declaration
`AlgebraicGeometry.ProEtale.bijective_toSheafify_app_of_iso` without editing it.

`lem-trf-site-functorial-flat-resolution` attaches the existing proved declaration
`SheafOfModules.hasFunctorialFlatResolution_kfi`; this records the exact stronger
interface used to retain boundedness and termwise flatness in a total resolution.

All five nodes carry actual Mathlib searches from this session. None introduces a
new hole. Source and proof details are in their nodes and the two change records
listed above. The unit and chapter records are unchanged.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
