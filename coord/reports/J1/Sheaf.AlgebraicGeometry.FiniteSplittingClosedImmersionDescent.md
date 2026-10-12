## What changed

Proved `AlgebraicGeometry.Scheme.finite_splitting_descends_surjective_closedImmersion`
with its original signature and public imports unchanged. Its two proof imports are
`Sheaf.AlgebraicGeometry.EtaleCoverThickeningLift` and
`Sheaf.AlgebraicGeometry.FiniteOpenPartitionThickeningTransport`.
Both new modules contain complete proofs, not postponed statements.

The first uses the already proved small etale site equivalence to lift each old cover
object, checks joint surjectivity on points, and constructs the source comparison via
restricted pullback squares and pasting. The second transports opens through a
homeomorphism, proves that the components are clopen and hence finite, and constructs
their restricted comparison morphisms. The main module proves universal injectivity
descent using arbitrary test pullbacks and a surjective precomposition, then combines
it with finiteness and surjectivity.

Validation: all three modules compile through lcompile.py. The dry run additionally
runs the declaration axiom probe. No global build was run; delivery is performed by the second reader.
Sources read: [Stacks 04DZ](https://stacks.math.columbia.edu/tag/04DZ) and
[Stacks 04DF](https://stacks.math.columbia.edu/tag/04DF), together with the existing
node proof and the source library implementation of topological invariance.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.finite_splitting_descends_surjective_closedImmersion`
(node `lem-weil-pbc-finite-splitting-closed-immersion-descent`).

Also proved the new declarations
`AlgebraicGeometry.Scheme.exists_etale_cover_thickening_lift` and
`AlgebraicGeometry.Scheme.exists_finite_open_partition_thickening_transport`,
and the private helper `universalHomeomorphism_of_surjective_precomp`.
No sorry remains in any delivered module; zero holes added or split off.
The existing site equivalence used here is already sorry-free.

The proofs include empty bases, empty old covering index types, n=0, and identity
thickenings. There is no Noetherian, affine, reducedness or density restriction.
All chosen cover objects occur locally within a proof of propositional existence;
no public data definition chooses an unspecified witness.

## No longer needed

The node `lemma-weil-pbc-universal-homeomorphism-coverings` is not needed by this
argument: the lifted cover is checked directly on points using Cover.exists_eq.
This prunes that proof dependency, not the equivalence dependency or its module.
The direct proof import of
`WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance` is removed from
the item's module and used in the proved cover-lifting module instead, so that module
is still required transitively. No library module can be claimed pruned here.
The other original proof dependencies remain used directly or through the new lemmas.
The unit's realized statements and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement needed correction. The planned proof works. Finiteness of
the partition is stronger than needed for clopenness: every member of any disjoint
open covering has open complement. The delivered statement retains Fin n as required.
The sieve-level covering compatibility theorem is unnecessary for this construction.
LeanSearch was attempted for both new nodes and returned Internal Server Error;
LeanFinder/Loogle, source grep, and blueprint searches supplied the other searches.

## New nodes

`lem-weil-pbc-etale-cover-thickening-lift` records the proved lift of an etale cover
and its arbitrary-source pullback comparison. It has no splitting or finite-source
hypothesis, and is exactly the geometric construction of steps 1 and 2 of the plan.

`lem-weil-pbc-finite-open-partition-thickening-transport` records the proved transport
of a partition and the restricted component comparison maps. It assumes and concludes
nothing about the structural component maps being universal homeomorphisms, so that
part of the argument is proved separately in the main module.

No interface change or forced adaptation; no change records.

## Second reading by J1

1. **Unchanged interface: PASS.** Read the complete repository/sandbox diff.
   The existing theorem signature is byte-for-byte identical, including `IsFinite f`,
   both assumptions on r, the fixed open U, the old etale cover, each finite disjoint
   partition, and every universal-homeomorphism component assertion. All original
   public imports, visibility, and the existing docstring are unchanged. The two new
   imports are proof-only. No definition or existing statement changes; no change
   record is required. The existing node changes only proof, proof_deps, proof_origin.

2. **Proof and axioms: PASS.** Independently compiled all three delivered modules
   through lcompile.py in import order: clean, approximately 3.5/2.4/2.4 seconds.
   Scanned the complete files: no sorry, forbidden declaration, hollow definition,
   or line longer than 100 characters. Scratch copies with `#print axioms` verified
   the main theorem, both new theorems, the private surjective-precomposition helper,
   and Hom.isEquivalence_etale: exactly propext, Classical.choice, Quot.sound.
   Removed all scratch Lean files before delivery. The helper pulls back the
   surjective a along every test square of g, pastes the squares to a base change
   of a followed by g, and cancels pointwise injectivity through that surjection.
   Finiteness supplies integrality and Surjective.of_comp supplies surjectivity.
   Thus this closes one original hole and introduces zero holes, not a decomposition.

3. **New statements: PASS.** Both new statements are fully proved and are strictly
   separate parts of the argument, not restatements of finite splitting descent.
   The cover-lifting lemma requires neither a finite f nor any splitting, and its
   restricted pullback/pasting construction proves both comparison maps are
   surjective closed immersions with the displayed projection equation. The
   partition lemma requires no etale cover or component universal homeomorphism:
   opensCongr transports cover and disjointness, the explicit complement union
   proves clopenness, and isoOfEq followed by restriction constructs a with the
   required inclusion equation. Their node statements agree with these clauses,
   and their recorded Lean signatures are verbatim. The docstrings give the full
   constructions and identify their sources. Checked n=0 (coverage forces an empty
   source), n=1 (the sole open is top), identity immersions, empty U and empty old
   cover indices; no nonemptiness or additional geometric hypothesis is used.
   Independent LeanFinder query about lifting etale covering families across a
   thickening returned general Etale API, and Loogle query
   `TopologicalSpace.Opens, Disjoint, IsClopen` found no combined theorem.
   Source searches also located FiniteEtaleThickeningLift (requires finite etale
   objects and finite-order thickenings), RefinementPreservesFiniteLisse and the
   upstream ConstructibleSheaf.UniversalHomeomorphism (cover lifting occurs inside
   proofs about sheaves, not an available geometric comparison theorem), and
   isClopen_of_disjoint_cover_open (a two-set topological fact). None states either
   new lemma; the existing etale equivalence and pullback API are already used.
   Re-read [Stacks 04DZ](https://stacks.math.columbia.edu/tag/04DZ) and
   [Stacks 04DF](https://stacks.math.columbia.edu/tag/04DF) against the constructions.
   All arbitrary object choices remain inside proofs of propositional existence.

4. **Route and pruning: PASS.** The top theorem first lifts the cover, then transports
   its partition, then descends universal injectivity and surjectivity of each finite
   component. This is the original three-step geometric route, with no unit bypass.
   Read dag/units/sk-thm-p1.json: no realized statement or step is removed.
   Of the old proof_deps, lemma-weil-pbc-universal-homeomorphism-coverings is unused
   and pruned; lemma-weil-pbc-universal-homeomorphism-site-equivalence moves from
   the parent's direct dependencies to the cover-lifting node and remains necessary
   transitively. The other four old dependencies remain used. The old direct
   EtaleTopologicalInvariance proof import likewise moves into the lifting module;
   no whole library module becomes unnecessary. Existing public imports are needed
   by the unchanged signature; new public imports support their own statements,
   and the equivalence/homeomorphism imports used only in proofs are plain imports.
   No shorter available theorem removes these constructions.

5. **DAG consistency: PASS.** Read all three delivered nodes and the original node.
   Each proof_deps list equals the union of its steps' uses. The parent records
   both proved helper lemmas and the explicit precomposition descent argument;
   the new nodes record the restriction/pasting and clopen/restriction constructions
   actually written in Lean. Checked source, proof_origin, three search kinds,
   status, worker/item/date/group creation records, inherited chapter/unit,
   blueprint ancestry, and verbatim Lean records on both new nodes. The pruned
   covering-compatibility node is not a realized unit step.

Second-reading changes: added this independent review and clarified the validation
paragraph's delivery status. No Lean or node repair was needed; the proved argument
is retained. No statement changed, no hole split off, no library module pruned.
