## What changed

Resumed the earlier sandbox attempt, checked its complete proof against the current
repository statement and projection interface, and retained the compiled proof.
Removed the stale second-reading section; the next reader must record a fresh review.

Proved `AlgebraicGeometry.homComplex_single_precomposition_iso` in
`Sheaf.AlgebraicGeometry.HomComplexSingleNaturality` without changing its signature
or its public imports. Added proof-only imports of
`Sheaf.Algebra.Homology.HomComplexProjections` and
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree`.

The proof uses the specified product projections, constructs their inverse when
all factors except source degree zero vanish, checks the differential formula,
assembles natural isomorphisms with `NatIso.ofComponents`, and verifies the
precomposition square by the componentwise map formula. The private
`soleFactorIso` construction follows the already proved single-source module;
it has no postponed proofs. The node's proof and proof dependencies now record
the projection interface actually used.

## Proved and sorry left

Closed the only hole:
`AlgebraicGeometry.homComplex_single_precomposition_iso`
(node `lem-sc-hom-complex-single-naturality`). No holes remain in the item, and
no holes were added anywhere. This is a proof, not a decomposition. The used
projection interface and Hom-complex construction are already proved.

The construction handles zero P or Q, zero coefficient complexes, empty schemes,
and arbitrary unbounded coefficient complexes. Each nonzero source degree is
eliminated by a zero-object argument, without any exactness assertion about
infinite products.

## No longer needed

No original imports were removed. The two public imports are required by the
unchanged statement. A trial proof-only import of
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero` was removed because
`InternalHomFree` already provides the zero-preserving internal Hom instances.

The old direct proof dependency `def-pur-hom-complex` is replaced by
`lem-sc-hom-complex-projections`. Its module remains a public statement import
and a transitive proof dependency, so no module is pruned. In particular, the pointwise
`lem-sc-hom-complex-single` / `Sheaf.AlgebraicGeometry.HomComplexSingle` is not
imported: its existential pointwise isomorphism does not fix a comparison whose
naturality can be checked. It remains a statement dependency, and it was not a
proof dependency of this item. The proof directly builds coherent comparisons
from `lem-sc-hom-complex-projections`. The unit record has no realized statement
or proof-step nodes, and its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface errors were found. The original prose plan was
usable; the existing projection interface avoids repeatedly unfolding the
large bifunctor construction. The node record now states that interface as the
proof dependency.

Searches run through msearch: LeanFinder for the degree-zero internal Hom
comparison returned related sheaf Hom and sheaf cohomology declarations, with
no exact comparison; Loogle for `NatIso.ofComponents` reported an unknown
identifier; grep for `homComplex_single_iso|singleObjXSelf|soleFactorIso` found
Mathlib single-complex identifications. Local rg and source reading found the
proved pointwise single-source argument and the proved unit-evaluation modules;
their product argument is reused, with the naturality calculations written here.


## Second reading by S4

1. Compared the entire delivered Lean file and node against the repository with
   diff, and checked declarations with the delivery declaration parser. PASS:
   the existing theorem signature and docstring are byte for byte unchanged;
   no existing declaration was removed, no public import changed, and no
   statement or definition used by others changed. The only new declaration
   is the private, fully constructed `soleFactorIso` helper.
2. Compiled the delivered module locally through lcompile.py without errors or
   warnings (39.9 seconds). Independently compiled a scratch copy with
   `#print axioms AlgebraicGeometry.homComplex_single_precomposition_iso` and
   `#print axioms CategoryTheory.homComplex_projections_exists` (38.6 seconds).
   PASS: both use exactly propext, Classical.choice, and Quot.sound; neither
   uses sorryAx. The delivered file has no sorry or forbidden declarations.
   The limit inverse is explicitly constructed, and the projection witness is
   chosen from a proved theorem, so there is no data from an unproved existence.
3. PASS: no statements were split off and no holes were added. Read the private
   product helper and checked both inverse identities, including the case when
   the surviving factor is itself zero. The nonzero source factors vanish by
   internal Hom additivity; the differential has zero source contribution.
   Nothing assumes boundedness, nonzero sheaves, or a nonempty scheme.
4. PASS: read the proof top down and checked the differential and both map
   specializations against HomComplexProjections. Searched the library also
   for single-source natural comparisons, and read HomComplexSingleNatural.
   Its public theorem gives an existential natural isomorphism in the coefficient
   variable but no specification of its projection components or compatibility
   in the source variable, so it does not replace this proof. The related
   product helpers there and in HomComplexSingle are private. Read Mathlib's
   product and zero-morphism interfaces; the present direct limit argument is
   appropriate. Both public imports support the signature; both added private
   imports are used (projection formulas and contravariant Hom additivity).
   The old proof dependency def-pur-hom-complex is fully accounted for under
   No longer needed, with its module retained for the statement. No modules
   are pruned. The unit's realized statement and step lists are empty and no
   unit route is bypassed or changed.
5. PASS: the node's five proof steps describe the actual projection, inverse,
   differential, coefficient naturality, and source naturality arguments.
   Their uses union is exactly the recorded proof_deps, namely
   lem-sc-hom-complex-projections. The proof_origin remains the original
   source with the implementation route recorded. All other node fields are
   unchanged; there are no new nodes or change records to review.

Second-reading changes: added this independent review and recorded the further
HomComplexSingleNatural and Mathlib interface checks. No Lean or DAG repair
was needed. Confirmed one original hole closed, zero holes added, and zero
holes left in the item.
