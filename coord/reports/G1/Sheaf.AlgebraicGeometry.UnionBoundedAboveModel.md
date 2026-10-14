## What changed

Proved `AlgebraicGeometry.exists_boundedAbove_union_model` in
`Sheaf.AlgebraicGeometry.UnionBoundedAboveModel`, preserving its complete signature,
visibility and original docstring. Added five fully proved private helpers for relative
flatness under isomorphism and open restriction, restriction of a presentation,
extracting a bounded-above direct image from a presentation, and biproduct closure.
The first two helpers follow the already proved private calculations in
`StandardSingleFlatCounitUnionTriangles`.

The proof uses `standardSingle_union_ses_presentation p (𝟙 B) U V N`, only its first
short exact row and source-vertex identifications. The identity comparison from
`exists_derivedPullbackComposition` removes derived pullback of the identity.
Mathlib's triangulated bounded-above subcategory gives the union bound and
`DerivedCategory.exists_iso_Q_obj_of_isLE` gives the requested representative.
No witness is used to define library data. All choices are inside theorem proofs.
Updated the existing DAG node's proof, proof dependencies and proof origin accordingly.

Proof imports: added `StandardSingleUnionSESPresentation`,
`DerivedPullbackComposition`, and `Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
The existing public import is unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_boundedAbove_union_model`
(node `new-pc-standard-single-flat-counit-union-bounded-model`).
No `sorry` remains in the delivered module; no holes or new modules were added.
This is a proof from existing named library statements, including the still-holed
`AlgebraicGeometry.standardSingle_union_ses_presentation`
(node `new-pc-standard-single-union-ses-presentation`), which remains the next geometric
obligation. No claim is made that the full dependency closure is sorry-free.

The delivered module compiled cleanly through `lcompile.py`. The required delivery
dry run also checks declarations and axioms against the published library.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisPresentation`.
The node `lem-pc-kinjective-mayer-vietoris-presentation` is no longer a direct proof
dependency: the existing single-module short exact presentation is used instead.
That presentation's own DAG proof still uses the K-injective node, so this does not
claim that the node or module can be deleted project-wide.

No new explicit cohomological-vanishing or good-truncation modules are needed:
Mathlib already proves bounded-above subcategory closure and existence of strictly
bounded-above representatives. No unit statement or realized unit step is bypassed;
`dag/units/sk-thm-picard-coherence.json` has no realized statement or step nodes.

## Where the brief, the DAG or earlier work was wrong

The existing plan names the K-injective presentation but leaves all direct-image
composition, restriction and boundedness glue implicit. The unrestricted
`standardSingle_union_ses_presentation`, already in the library, provides the needed
short exact row without additional compactness hypotheses, after identity base change.
The more general `schemeDerived_mayerVietoris_directImage` cannot be used here directly:
it requires compact opens, which this item's signature does not assume.

The original node cites `literature/stacks-project/sites-cohomology.tex` for Tags
08BV and 0DJ9. The actual tags belong to Cohomology of Sheaves and Derived Categories
of Schemes respectively. The official pages were read:
https://stacks.math.columbia.edu/tag/08BV,
https://stacks.math.columbia.edu/tag/0DJ9,
https://stacks.math.columbia.edu/tag/0D5S.
The existing source field and theorem docstring were preserved; proof_origin records
the implemented route. Empty, repeated or contained opens and N=0 need no case split:
the existing unrestricted SES theorem covers them, and all categorical closure and
restriction arguments apply without nonemptiness assumptions. No signature or
interface change and no forced adaptation was needed.

## Second reading by G1

1. **Interface preservation: PASS.** Read the full delivered module and its diff
   against the repository. A byte comparison confirms the existing theorem signature
   and docstring are identical. Its visibility and sole public import are unchanged.
   Only proof imports, five proved private helpers and the theorem proof were added;
   no definition, target statement or other module was changed.
2. **Proof and axioms: PASS.** Independently compiled the delivered module through
   `lcompile.py`, cleanly, with no warnings. There is no `sorry`, axiom, unsafe,
   opaque, extern or implemented_by declaration in it, and no library data is
   defined by selecting witnesses. Existential complexes and the identity comparison
   are eliminated only within theorem proofs. A scratch copy with `#print axioms AlgebraicGeometry.exists_boundedAbove_union_model`
   also compiled and reported exactly `propext`, `Classical.choice`, `Quot.sound`
   and inherited `sorryAx`. The delivery probe checks every new constant's axioms;
   inherited `sorryAx` is permitted because dependencies remain open. This closes the item's hole, not all holes in its import closure.
3. **Split statements and edge cases: PASS (none added).** No new public statement
   or split-off hole exists. Read all five private helper proofs, the presentation
   predicate, the unrestricted SES statement and the identity comparison statement.
   Flatness transport uses section-module linear equivalences, and restriction uses
   affine images under open immersions with the correct composite scalar action.
   No step needs a nonempty open, distinct opens, a nonzero module or compact opens;
   empty, repeated and contained opens and zero coefficients remain covered.
4. **Route and pruning: PASS.** Independently searched with `msearch.py` for
   "bounded above derived direct image union" and searched the library for flatness
   restriction and Mayer--Vietoris statements. Existing matching flatness calculations
   are private, so cannot be imported as public lemmas. The generic direct-image
   Mayer--Vietoris theorem requires compact opens absent from this signature.
   Read Mathlib's `exists_iso_Q_obj_of_isLE`: it directly supplies the required
   representative. The delivered proof already uses triangulated bounded-above
   closure instead of adding cohomology or truncation holes. Every proof import has
   a concrete use; the original public import supplies the statement. The report's
   removed K-injective direct dependency is the complete old `proof_deps` pruning.
   The unit's `realized.statement` and its only `realized.steps` entry are empty;
   no realized unit node is bypassed.
5. **DAG agreement: PASS.** Compared both node JSON files: exactly `proof`,
   `proof_deps` and `proof_origin` changed. Read the four new proof steps against
   the Lean: restriction presentations, extraction of bounds, identity-base-change
   SES and bounded-above closure, then a strictly bounded representative. Their
   `uses` union is exactly `proof_deps`; existing statement and Lean records remain
   unchanged. No new node or change record is required.

Second reading changed only this report, adding the independent review. No Lean or
DAG repair was needed. Holes closed: `AlgebraicGeometry.exists_boundedAbove_union_model`.
Holes added: none; split off: none. The dry run and delivery checks are run after
this review section is written.
