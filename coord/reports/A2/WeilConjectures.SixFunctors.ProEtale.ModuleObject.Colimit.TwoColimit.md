## What changed

Closed four of the five original holes of
WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit, without changing any existing
signature. The original Hom-surjectivity theorem is moved before the object-descent theorem because
the latter now uses it, as the planned Postnikov argument requires.

Added three fully proved helper modules:

- Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars: scalar extension preserves finite
  presentations, their pullback covers, and their stratifications; exactness then preserves
  boundedness and constructible cohomology.
- Sheaf.AlgebraicGeometry.SplitCoefficientDerivedFaithful: construct an algebraic E-linear
  projection Omega -> E, continuous on every finite subfield. It acts on the finite-subfield-valued
  condensed coefficient sheaf. Tensoring gives a natural splitting of the scalar-extension unit;
  localizing this splitting proves faithfulness on all unbounded derived complexes.
- Sheaf.CategoryTheory.DirectedTriangulatedImage: if morphisms between finite-stage images descend,
  their union is triangulated. Descend the first arrow of a triangle, complete it at a common stage,
  and compare third objects by a triangle isomorphism.

Object descent uses this triangulated-image lemma, the existing sheaf-descent statement, and the
already proved DerivedCategory.prop_of_bounded. The parent supplies the single-sheaf and ambient
subcategory glue. Its local triangulated structures are proved from the specific condensed-field
Serre statements via the already proved DerivedCategory.homologyProperty_isTriangulated, rather
than relying on the original unsupported arbitrary-coefficient instance (now corrected upstream). Zero constructibility is proved
directly from the rank-zero presentation and trivial stratification. Hom injectivity follows from
faithfulness, with no enlargement of the field.

The helper modules and sheaf-descent input are imported only for proofs. In the unclaimed module
Sheaf.Paper.CondensedFinitePresentationDescent, removed one unused proof import that otherwise
creates a cycle back to the parent. See coord/changes/a2-finite-presentation-import-cycle.md.

All five sandbox modules compile locally. A dependency traversal through the object-descent proof
(10,175 constants) confirms that it does not reference the original generic triangulation instance.
No new sorry, axiom, hollow definition, or target change.

Repair: the private helper in `Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars` that
transported finite presentations across an isomorphism had the same statement as the library's
`AlgebraicGeometry.ProEtale.finitePresentation_of_iso`. It is now the strictly more general iff
transport lemma `fp_iff_of_iso`, and its two uses select the needed direction. This removes the
duplicate declaration while preserving the proof and public theorem signature.
The existing Noetherian hypothesis on Hom injectivity is retained verbatim even though the new proof
works without it; its unused-section-variable linter is disabled for that theorem alone.

## Proved and sorry left

Closed original holes (4 of 5):

- AlgebraicGeometry.ProEtale.boundedConstructible_derivedExtendScalarsSubfield_obj.
- AlgebraicGeometry.ProEtale.boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj.
- AlgebraicGeometry.ProEtale.constructibleCocone_essSurjObj, using the existing Hom-surjectivity
  obligation and the existing sheaf-descent obligation.
- AlgebraicGeometry.ProEtale.constructibleCocone_homInj.

All four belong to prop-weil-pbc-qbar-condensed-two-colimit. The assembly theorem remains unchanged.

Original hole left in the item:
AlgebraicGeometry.ProEtale.constructibleCocone_homSurj
(prop-weil-pbc-qbar-condensed-two-colimit). No new holes are split off.

The adapted input retains its original, unchanged hole:
AlgebraicGeometry.ProEtale.exists_constructible_finiteCoefficient_model
(lem-weil-pbc-condensed-finite-presentation-descent). This is an existing planned dependency, not a
new declaration. The three new helper modules contain no sorry.

## No longer needed

For the completed Hom-injectivity clause, the filtered Hom comparison, the filtered-colimit
representative equality criterion, and the Postnikov/five-lemma argument are unnecessary: equality
already holds at the original field. Those ingredients remain in the DAG only for Hom surjectivity;
no global pruning of their modules is claimed.

Object descent uses the already proved DerivedCategory.prop_of_bounded, so it does not separately
formalize or import the separate truncation-triangle statement module or the planned
Hom-into-triangle/five-lemma nodes.
The generic triangulated-image proof uses Mathlib's distinguished_cocone_triangle and
isoTriangleOfIso12 directly. The parent proof_deps no longer includes
lem-weil-pbc-hom-into-triangle-exact or def-weil-size-convention. The former is unnecessary
for the cone comparison; the latter is already a convention of the existing definitions and
requires no separate proof step. Other consumers may still need these nodes.

Removed import Sheaf.Paper.CondensedFlatCoefficientCalculus from the sheaf-descent module because it
is unused by the current statement/proof and creates a cycle. This does not remove that module's
mathematical role in the remaining Hom-surjectivity plan. The scalar-preservation helper now publicly imports the narrower RingObjects.Ab module in
place of ModuleObject.Basic; its statement needs the abelian-group tensor structure, while the
point-pullback coefficient constructions are unused. A redundant explicit ExtendScalars import
was removed while developing the new scalar-preservation helper; its Monoidal and Biproducts imports
are proof-only. The redundant explicit TStructure proof import in the parent is removed, since
HomologyProperty publicly imports that module. Also removed the redundant direct
DerivedExtendScalars import from SplitCoefficientDerivedFaithful: Compatibility publicly
imports it through ChangeOfCoefficients. No original public import of the item was removed or changed.

## Where the brief, the DAG or earlier work was wrong

The intended finite-presentation descent module imported the parent indirectly through
CondensedFlatCoefficientCalculus -> CondensedCoefficientComparisons -> TwoColimit. The parent
could therefore not use its own stated sheaf-descent input until that unused proof import was
removed. This is an import graph problem, not a mathematical statement dispute.

The DAG's Hom-injectivity route is longer than necessary for this exact condensed Omega: an
algebraic projection is continuous on each finite subfield, which suffices because sections are
finite-subfield-valued. No global continuity of Omega -> E is asserted. This distinction is essential.
The projection is constructed with Mathlib's proved linear left-inverse API, not selected from a
sorried existence statement.

The first worker disputed the former generic
AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible instance in
WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory: it allowed arbitrary
commutative ring objects with no weak-Serre or coherence condition. For a constant ring
R = k direct-sum V with V infinite-dimensional and V squared zero, multiplication by a nonzero
v in V has kernel V, which is not finitely generated, although source and target are finite free.
Its cone consequently fails constructibility, even over a geometric point.

The second reader found that B4 has now corrected that upstream instance by requiring the
three coefficient-dependent closure properties explicitly. This delivery leaves B4's file
untouched and claims no current statement dispute. It replaces the historical warning in the
parent with an accurate comment. The delivered proof constructs the finite-field and Omega
instances directly from the stated condensed-field Serre closure; its zero and isomorphism
cases are proved from presentations. This remains valid after the upstream correction.

The finite Postnikov object-descent argument already exists in the source library as
DerivedCategory.prop_of_bounded. It applies after proving the finite-model objects triangulated and
checking single sheaves, which the parent now does. No unit statement or unit proof step is bypassed.

The remaining Hom-surjectivity proof still needs the strict coefficient-extension diagram over finite
overfields, identification of its termwise colimit with restricted Omega extension, and the natural
adjunction comparisons. The existing isIso_constructible_condensed_sheaf_hom_colimit covers the
single-sheaf base case once that diagram is supplied. Extending it to bounded first arguments uses
filtered exactness and the five lemma (the original parent plan, steps 3-4). These are not replaced by
another theorem with the original conclusion.

## New nodes

lem-weil-pbc-bounded-constructible-exact-scalar-extension attaches the proved generic scalar
preservation theorem in Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars. It generalizes the
two original preservation obligations and assumes precisely exact scalar extension.

lem-weil-pbc-condensed-coefficient-derived-faithful attaches the proved faithful derived extension
in Sheaf.AlgebraicGeometry.SplitCoefficientDerivedFaithful. Its algebraic projection and all derived
splitting glue are proved in the new module. It has no Noetherian or boundedness requirement.

lem-weil-pbc-directed-triangulated-image attaches the proved union-of-images theorem in
Sheaf.CategoryTheory.DirectedTriangulatedImage. Morphism descent supplies every common stage used;
no coherence or directedness is silently assumed beyond its actual signature.

Updated prop-weil-pbc-qbar-condensed-two-colimit's proof, proof_deps and proof_origin to record these
routes and the single remaining original obligation. All three new nodes include LeanSearch
(service unavailable), Loogle/LeanFinder, and Mathlib source searches. Change record: coord/changes/a2-finite-presentation-import-cycle.md.


## Earlier second reading (a previous round; superseded)

1. Compared the delivered module with the repository version. Existing declaration signatures are unchanged; the four closed proofs and proof-only imports are the declared changes, and the remaining `constructibleCocone_homSurj` hole is unchanged.

2. Compiled all sandbox modules with `lcompile.py --all`. The files compile without errors; the only remaining `sorry` in the item is the named Hom-surjectivity theorem, and the adapted finite-presentation input retains its pre-existing named hole. No definitions contain `sorry`, and no forbidden declarations were added.

3. Checked the added helper statements and their nodes. Scalar preservation, derived faithfulness, and directed triangulated-image closure are true, strictly narrower than the parent target, and used by the proof; they are not duplicate restatements. The helper proofs introduce no holes.

4. Read the proof from the target downward. The scalar-preservation proofs use the exact scalar-extension theorem; object descent uses the finite-model input, the local Serre closure, `prop_of_bounded`, and the directed-image lemma; Hom injectivity uses derived faithfulness at the original stage. The disputed generic triangulation instance is avoided, and the reported unused imports and dependency pruning agree with the code.

5. Checked the node metadata and unit route. The parent node records the four completed declarations, the one remaining obligation, all three helper nodes, and the actual proof dependencies; the unit's object and Hom route is retained. The import-cycle change record and forced adaptation are documented.

Changed during second reading: no Lean proof or statement changes; added this review record only.


## Second reading by A2

1. Compared every existing delivered module with the repository version and ran the declaration
   comparison. Verdict: no existing signature, definition, visibility, or target changed. Restored
   the original line layout of the Omega-preservation signature as well. The sheaf-descent module
   differs only by the declared unused proof import removal.

2. Read all five modules and compiled them locally through lcompile.py. The only local holes are
   the original constructibleCocone_homSurj and the unchanged imported
   exists_constructible_finiteCoefficient_model. No hole occurs in a definition and no forbidden
   trust mechanism occurs. Explicit scratch #print axioms checks show only propext,
   Classical.choice, Quot.sound, and existing upstream sorryAx where applicable; the generic
   scalar-preservation and directed-image helper theorems have no sorryAx. The coefficient
   projection uses Mathlib's proved linear left inverse, with no arbitrary witness from an
   unproved existence theorem.

3. Checked all three proved helper statements, their docstrings, and their nodes. Tested the
   rank-zero and empty-scheme constructions, the same-stage retraction, and the nonempty-index
   requirement in cone closure. They are true, used, and strictly smaller than the parent, with
   no new holes. Independent LeanFinder, Loogle, Mathlib grep, and library source searches found
   no replacement: the ordinary module finite-presentation API is not this internal-module API,
   and the standard essential-image theorem assumes a full individual functor. Corrected the
   new scalar-preservation node's prose to include S commutative, matching its actual Lean
   signature; no Lean statement was changed.

4. Traced the proof from the parent: exact extension preserves presentations and cohomology;
   sheaf descent and Hom surjectivity give the triangulated finite-model union; prop_of_bounded
   performs Postnikov induction; the split scalar-extension unit proves Hom injectivity at the
   original stage. Verdict: genuine reductions, no restatement. Replaced the unnecessarily broad
   public ModuleObject.Basic helper import by RingObjects.Ab, verified by compilation, and
   removed the redundant direct DerivedExtendScalars import from the faithfulness helper. Completed
   No longer needed with def-weil-size-convention. The other retained dependencies still serve
   the open Hom-surjectivity plan; no entire module is globally pruned.

5. Checked proof_deps against the union of each node's proof-step uses, proof_origin against the
   actual proofs, all required new-node metadata, and sk-thm-properbasechange's realized route.
   Verdict: consistent, and no unit statement or step is bypassed. Updated the parent node and
   this report to acknowledge the now-corrected upstream generic triangulation instance.

Changed during this second reading: narrowed one public import, removed a redundant import, corrected the scalar helper's
node prose, completed the pruning report, restored exact signature formatting, and updated the
historical triangulation warning. No proof argument or existing statement changed; four original
holes closed, zero new holes, one original item hole remains.
