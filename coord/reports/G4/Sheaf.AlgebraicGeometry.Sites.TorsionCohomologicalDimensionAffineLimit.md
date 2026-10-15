## What changed

Proved `AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_isLimit`
with its signature and visibility unchanged. The proof follows all three original
steps: reconstruction of a sheaf from pull-push approximations, continuity and
stagewise vanishing, and reduction of torsion to bounded exponents.

Added four fully proved modules under `Sheaf.AlgebraicGeometry.Sites`:
`AffineLimitSheafApproximation` constructs the diagram, transitions, counit cocone,
and comparison; `AffineLimitSheafApproximationEpi` proves epimorphy by descent and
adjunction; `AffineLimitSheafApproximationGermKernel` proves eventual vanishing of
kernel germs; `AffineLimitSheafReconstruction` proves the colimit universal property.
The diagram is an explicit construction. No definition chooses an arbitrary object
from an unproved existence theorem. Existence theorems are eliminated only in proofs.

Only proof imports of the existing module changed. Its public imports, declaration
signature, and all existing dependency statements are unchanged. The original DAG
node's proof, proof dependencies, and proof origin now describe the formal argument.
No existing module other than the assigned item was adapted; no change record is needed.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_isLimit`
(`lem-sc-cd-affine-limit`).

Added zero holes. No `sorry` remains in any delivered Lean file. This is a proof
from existing library declarations, not a decomposition into new unfinished statements.
The four new nodes and all their public definitions/API lemmas are proved.
In particular, the geometric kernel theorem was initially isolated during development
and then proved within this session; it is not handed on with a hole.

The proof uses the existing finite-diagram descent theorem
`AlgebraicGeometry.Etale.exists_etale_limit_finite_diagram_descent`, cohomology
continuity, the Sheaf.H/derived comparison, filtered-colimit commutation, and the
existing bounded-exponent reduction. Existing upstream unfinished proofs remain
upstream obligations; closing this item does not assert that every transitive axiom
has already been eliminated from the whole project.

Validation: all five sandbox modules compiled in import order with the prescribed
compiler and no warnings. The revised main proof also compiled separately. Empty
limit schemes cause no geometric-stalk obligation; the zero germ can use an identity
transition. The reconstruction and kernel statements require no torsion assumption.
The positive-exponent hypothesis is retained in the bounded-exponent argument,
including exponent one and cohomological bound zero.

## No longer needed

Removed these six direct proof imports from the item's module:

- `Sheaf.Paper.EtaleFiniteDataDescent`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`
- `Sheaf.AlgebraicGeometry.TorsionFilteredUnion`

The reconstruction proof uses `Sheaf.AlgebraicGeometry.EtaleLimitFiniteDiagramDescent`
in place of the broader `Sheaf.Paper.EtaleFiniteDataDescent` planned import. It checks
injectivity on geometric germs, so it does not need a separate finite affine covering
refinement theorem. Thus the direct proof dependencies
`lem-weil-pbc-etale-finite-data-descent` and
`lem-weil-pbc-etale-qcqs-cofinal-finite-coverings` are unnecessary for reconstruction.
The limit's quasi-separatedness follows from its affine projection; the separate
`lem-weil-pbc-quasi-separated-affine-cover-criterion` is unnecessary for this proof.

The inverse/direct-image definitions and filtered-colimit theorem remain in use
through the modules that expose the needed APIs. The factorial bounded-exponent
reduction already proves the torsion-union step, so its proof is reused rather than
reproved from `Sheaf.AlgebraicGeometry.TorsionFilteredUnion`. These are removals of
direct imports and planned proof edges; no claim is made that every listed module is
unreachable from all other targets or from the remaining library imports. A read-only
comparison of this item's library import closure (overlaying the sandbox) finds six
modules removed from that closure: `Sheaf.Paper.EtaleFiniteDataDescent`,
`Sheaf.AlgebraicGeometry.FiniteDiagramLiftOfModels`,
`Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings`,
`Sheaf.AlgebraicGeometry.TorsionFilteredUnion`,
`Sheaf.AlgebraicGeometry.EtaleFreeSheafDerivedSections`, and
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`.
The four new proved modules and the proved source module `GmGenericPoint` enter that
closure. No library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature repair was needed. The original proof's finite-cover
argument can be made shorter at geometric stalks: a single affine pointed
neighbourhood witnesses vanishing, so no finite cover must be descended. For its map
to the original stage neighbourhood, Mathlib's locally-finitely-presented morphism
factorization theorem suffices; that target neighbourhood need not be quasi-compact.

The finite-diagram descent interface is indexed by a directed preorder, whereas this
item allows an arbitrary small cofiltered category. Both uses explicitly perform a
final directed reindexing and transport the limit, including over a fixed stage.
The dimension predicate uses derived étale cohomology; the available continuity API
uses `Sheaf.H`. The existing natural isomorphism is applied explicitly in both places.
The general filtered-colimit API is exposed by the existing `Curve.Reductions`
module, whose proof uses `Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit`;
this route does not use the formerly planned `HigherDirectImage.FreeSheaf` module.

Mathlib searches were performed through LeanSearch (unavailable), LeanFinder, Loogle,
and grep; the records distinguish unavailable searches from absence of an exact match.
Whole-blueprint searches for sheaf/colimit/limit, counit, and approximation found
`lem-kun-descent-limit`, a related statement for torsion sheaves on directed limits
of affine schemes. It has no Lean attachment and is a specialization of the arbitrary
abelian-sheaf qcqs reconstruction proved here, not an interchangeable existing lemma.
The new nodes originate in this item's step 1 and bypass no unit-level statement.

## New nodes

`def-sc-affine-limit-sheaf-approximation`: explicit pull-push approximation diagram,
transition coherence, counit cocone, and comparison, in
`lean/Sheaf/AlgebraicGeometry/Sites/AffineLimitSheafApproximation.lean`.

`lem-sc-affine-limit-sheaf-approximation-epi`: epimorphy by joint faithfulness of
projection direct images and adjunction, in
`lean/Sheaf/AlgebraicGeometry/Sites/AffineLimitSheafApproximationEpi.lean`.

`lem-sc-affine-limit-sheaf-approximation-germ-kernel`: a counit-kernel germ dies at a
later stage, proved by representative descent and unit naturality, in
`lean/Sheaf/AlgebraicGeometry/Sites/AffineLimitSheafApproximationGermKernel.lean`.

`lem-sc-affine-limit-sheaf-reconstruction`: combines epimorphy and stalkwise
monomorphy to prove the approximation cocone is a colimit, in
`lean/Sheaf/AlgebraicGeometry/Sites/AffineLimitSheafReconstruction.lean`.

All four nodes carry source, full proof steps, search records, and exact Lean records.
All four are fully implemented and introduce zero new proof obligations.

## Second reading by G4

1. I compared the delivered target module with the repository version. The theorem
signature and visibility are byte-for-byte unchanged; the only existing declaration
change is its proof and proof-only imports. The four added modules and four node files
are new files listed by this delivery, with no accidental edits to other modules.

2. I compiled all five modules in import order with `lcompile.py --all`; compilation
completed without errors or warnings. There are no `sorry`, `axiom`, `unsafe`,
`opaque`, `extern`, or `implemented_by` declarations in the delivered files. Scratch
`#print axioms` checks for the five public results returned only `propext`,
`Classical.choice`, and `Quot.sound`.

3. I checked every added public statement against its node and searched the repository
and source library for duplicates. The approximation definitions, epimorphism,
germ-vanishing theorem, and reconstruction theorem are true at the stated generality,
with no added torsion or cohomology hypotheses. Their proofs use explicit constructions;
no definition chooses data from an undetermined existence proof. The new declarations
are recorded in the corresponding node `lean` records.

4. I checked the proof from the target downward and compared imports with actual use.
The target keeps the reconstruction, continuity, Sheaf.H/derived comparison, and
bounded-exponent route. The six removed direct imports and the corresponding unused
planned edges are documented above. The unit/chapter metadata and realized route are
unchanged, and the new nodes remain in the item's existing unit.

5. I checked the DAG metadata against the Lean declarations: each new node has its
statement, source, proof steps, proof dependencies, searches, and exact module and
declaration records; the target node records the revised three-step proof. No
statement-disputed marker or change record is needed.

I changed only this report section during second reading. No Lean proof, declaration,
node, or import required repair.
