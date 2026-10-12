## What changed

Reduced `AlgebraicGeometry.schemeOpenModuleImageComplex_comparisons` without changing
its signature. Construct the three comparisons at `Q(I)` explicitly, postcompose with
restriction/direct image applied to the given isomorphism `e`, and prove the four
required identities using unit compatibility and naturality of the nested counit mate.
The resumed audit replaced broad rewrites with explicit associativity and congruence
steps, and enabled transparency-respecting backward elaboration for this theorem.
This avoids unfolding the large scheme functors while comparing the diagram arrows.

Added `Sheaf.AlgebraicGeometry.OpenImageComplexComparisonIso`: it proves
`AlgebraicGeometry.isKInjective_schemeOpenRestriction` from the existing open-site
restriction theorem and preservation of K-injectivity by an additive equivalence.
Its `AlgebraicGeometry.schemeOpenModuleImageComplexComparison` is actual data:
compose the inverse `rightDerivedFunctorObjQIso`, direct image of the inverse
`mapDerivedCategoryFactors`, and `rightAdjointUniq` from the canonical derived
adjunction to the supplied one. No existence witness is chosen.

Added `Sheaf.AlgebraicGeometry.OpenImageComplexComparisonUnit`: a generic proved
private calculation applies `derivedη_fac_app` and transports through the quotient
and exact-restriction localization isomorphisms; `unit_rightAdjointUniq_hom_app`
then identifies the supplied unit.

Added `Sheaf.AlgebraicGeometry.OpenImageComplexComparisonRestriction`: only the
compatibility of those fixed comparisons with one nested-open restriction is left
for the next worker. This is one arrow at `Q(I)`, with no pair of opens, no supplied
representative `E`, and no unit assertions. Its docstring states the full mate
calculation and normalization argument. The item itself performs the construction,
the two unit identities, and transport of both overlap identities to `E`.

The original unit `sk-thm-picard-duality` has empty realized statement/step lists;
no unit statement, step, or dependency route was bypassed. Updated the item's proof,
proof dependencies and proof origin to follow the delivered Lean.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.schemeOpenModuleImageComplex_comparisons`
(node `lem-pc-kinjective-mayer-vietoris-comparisons`). The item's module contains
no `sorry`.

Also proved `AlgebraicGeometry.isKInjective_schemeOpenRestriction`,
`AlgebraicGeometry.schemeOpenModuleImageComplexComparison_unit`, and the private
lemmas `unit_compute` and `mate_naturality`. The comparison definition contains
no proof hole and no data chosen from an unproved existence statement.

Added exactly one hole:
`AlgebraicGeometry.schemeOpenModuleImageComplexComparison_restriction`
(node `lem-pc-open-image-complex-comparison-restriction`), in its own module.
This is a decomposition: one original hole closed, one strictly smaller hole added;
the delivery does not claim a net decrease in holes or an axiom-free target.
The existing proofs used from imported modules retain their existing dependencies.

Validation: the complete four-module sandbox compiled in the delivery dry run,
and the preflight passed apart from the intentionally pending second reading.
The resumed audit rechecked the explicit construction, unit calculation, mate
naturality argument, unchanged original signature, node dependencies, and sources.

Checked edge cases: arbitrary unbounded K-injective complexes are allowed; there
is no cover or termwise-injectivity hypothesis. For repeated opens the canonical
identification is transported through both supplied adjunction comparisons; the
adjunctions need not coincide, so no literal identity mate is assumed.
For an empty smaller open the target module category is zero, so the remaining
compatibility is vacuous. Changing the supplied adjunction is handled by the
constructed right-adjoint comparison, rather than assuming its unit is canonical.

## No longer needed

Removed three direct proof imports from the item:
`Sheaf.Algebra.Homology.KInjectiveRestrictOpen`,
`Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps`, and
`Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`.
The first is used inside the new comparison-construction module; the other two
are already publicly available through `KInjectiveMayerVietorisData`.

No mathematical dependency node or module is pruned from the import closure.
All four original dependency nodes remain needed through the concrete data and
comparison construction. The new proof does not add dependencies for exactness,
a covering by U and V, or termwise injective resolutions.

## Where the brief, the DAG or earlier work was wrong

No false statement or forced adaptation was found. The original plan did not name
its comparison isomorphisms or isolate the derived mate computation. The delivery
makes the data explicit, proves K-injective transport and the unit computation,
and isolates just the nested mate computation. The resumed audit corrected the
repeated-open explanation: two supplied adjunctions may differ even when the opens
coincide. This correction changes no Lean statement or proof.

The search services found Mathlib `derivedη_fac_app`, `derivedε_fac_app`, and
right-adjoint uniqueness as generic ingredients. LeanSearch returned HTTP 500;
this is recorded as unavailable, not as no match. The logged grep and LeanFinder
searches and direct reads of Mathlib and both library roots found no existing
specialization to these fixed scheme complexes. Blueprint searches for
K-injective comparisons and nested restriction found no duplicate specialized node.

The local checkout lacks the Stacks TeX document. Read the same cited source at
[Tag 08BV](https://stacks.math.columbia.edu/tag/08BV) and
[Tag 08BS](https://stacks.math.columbia.edu/tag/08BS).
The source's first paragraph supplies the K-injective computation; the formal
unit/counit compatibility calculations spell out the original node's plan.

## New nodes

`def-pc-open-image-complex-comparison-iso` records the actual constructed
single-open comparison and the proved K-injectivity of restriction to the open
scheme. Module: `Sheaf.AlgebraicGeometry.OpenImageComplexComparisonIso`.

`lem-pc-open-image-complex-comparison-unit` records the proved unit factorization
for this specific comparison. Module:
`Sheaf.AlgebraicGeometry.OpenImageComplexComparisonUnit`.

`lem-pc-open-image-complex-comparison-restriction` records the one remaining
nested mate compatibility theorem at `Q(I)`. Module:
`Sheaf.AlgebraicGeometry.OpenImageComplexComparisonRestriction`.

There are no interface changes to existing declarations, no adapted modules,
and no change records.

## Second reading by X3

1. **Interfaces: pass.** Diffed the item against the repository module. The complete
   signature of `AlgebraicGeometry.schemeOpenModuleImageComplex_comparisons`, including
   all four derived-category instances, arbitrary K-injective I, arbitrary E and e,
   three independently supplied adjunctions, three existential isomorphisms, and all
   four equations, is byte-for-byte unchanged. Its existing docstring and public
   import are unchanged. The other three modules are new, and there are no adapted
   modules or interface-change records. Only proof bodies, private helpers, proof
   imports, and the three allowed proof metadata fields change in the existing item.
2. **Proofs and data: pass with the declared hole.** Compiled all four delivered
   modules in import order through lcompile.py; all passed without warnings. Scratch
   copies with `#print axioms` checked every public declaration and both private
   helpers. K-injective restriction, the explicit comparison definition, the unit
   theorem, `unit_compute`, and `mate_naturality` use only propext, Classical.choice,
   and Quot.sound. The restriction theorem and original theorem additionally use
   sorryAx, exactly as expected from the one declared remaining hole. Inspected
   all proof bodies: there is no forbidden declaration or option, no hollow
   definition, and no arbitrary choice from an unproved existence statement.
   The comparison is composed from the inverse K-injective computation,
   right-derived image of the inverse restriction factorization, and the
   rightAdjointUniq component. The unit calculation cancels these same comparisons.
3. **Split statement: pass.** Read the restriction theorem and its node against
   the concrete underived mate in KInjectiveMayerVietorisData and the derived mate
   in DerivedOpenRestrictionMaps. Its single equation at Q(I) is strictly a part
   of the original argument: it supplies neither comparison data, the two unit
   identities, nor transport to E. The docstring gives the localization,
   unit/counit factorization, nested restriction factorization, and supplied
   adjunction normalization argument. Equal opens still allow distinct supplied
   adjunctions, handled by rightAdjointUniq; empty W has zero target objects;
   unbounded I requires neither a cover nor injective individual terms.
   Rechecked Stacks Tags [08BV](https://stacks.math.columbia.edu/tag/08BV) and
   [08BS](https://stacks.math.columbia.edu/tag/08BS): the computation and restriction
   facts used here do not require the cover and termwise injectivity needed for
   the separate short exact sequence argument. Fresh LeanFinder search for
   localization of adjunction mates and grep for derived counit factorization
   found generic derivedη_fac_app and derivedε_fac_app, already used in the plan.
   Direct searches in both Lean roots found no existing specialization. Read
   Adjunction.derivedPresentation_mate: it requires exact right adjoints and
   treats localized left adjoints, so it does not apply to these generally
   nonexact open direct images. Also read rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv:
   it treats a composition isomorphism of right adjoints, rather than this arrow
   between restriction/direct-image composites. These results do not close the
   remaining statement by a short application. No additional hole was added.
4. **Route and pruning: pass.** Reviewed the explicit witnesses, both unit
   equations, and both overlap equations. The private mate_naturality theorem
   proves naturality of the actual whiskered unit/counit transformation; applying
   it to e.hom transports each overlap equation correctly. Proof-only imports
   of the new unit and restriction modules are plain imports. Public imports
   in the new construction module expose the constructions its public definition
   uses; the new unit/restriction signatures use the comparison definition.
   The three old direct imports removed from the item are listed above.
   The old dependency nodes lem-sc-derived-k-injective-restrict-open,
   def-pc-derived-direct-image, and def-pc-kinjective-mayer-vietoris-data are
   replaced as direct proof dependencies by the three new nodes, but all remain
   necessary transitively; def-pc-derived-open-restriction-maps remains direct.
   No node or module is pruned from the closure. Read the unit record:
   realized.statement = [] and realized.steps = [[]]; no realized unit route
   is bypassed. One old hole is closed and one smaller hole added, a decomposition
   with net zero, not a claim of an axiom-free original result.
5. **DAG: pass after metadata repair.** Read all four node files. Their Lean
   statements match the corresponding declarations, and each proof_deps is the
   union of proof-step uses. The item's new steps track construction, unit
   naturality, and nested-mate naturality. Its only changed fields are proof,
   proof_deps, and proof_origin. Each new node has its source, dependencies,
   search records (including the unavailable LeanSearch service), split status,
   creation record, blueprint ancestry, chapter/unit, and complete Lean record.
   Added the missing lean_audit records with master/slopmaster2 state none to
   all three new nodes; this records the absence of an upstream audit without
   claiming one was performed.

Second-reading changes: completed the three new nodes' lean_audit metadata and
added this independent review and nearby-lemma search findings. The Lean proofs,
statements, definitions, and imports needed no repair. Scratch axiom-check copies
were removed before delivery.
