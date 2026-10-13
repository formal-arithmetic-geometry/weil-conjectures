## What changed

Replaced the sorry in `resolution_unitTwist_comparison` with a complete Lean proof
from an untwisted resolution comparison and a tensor-unit morphism calculation.
The original declaration, its universes, and its public imports are unchanged.
The proof defines the pulled-back section explicitly, transports the untwisted
additive equivalences through cohomology of the unit-power isomorphisms, uses
restriction naturality, and cancels these isomorphisms to prove the transition
identity. All three delivered modules compile without warnings.

Added `Sheaf.AlgebraicGeometry.TensorUnitPowerScalar`, with the fully proved
`tensorUnitPower_scalar`. Its private recursive unit-power isomorphisms are actual
constructions. A proved private induction computes their action on powers of the
section. Equality on sections after precomposition with the inverse right unitor
then proves the numerator/scalar identity as an equality of sheaf morphisms,
before applying cohomology.

Added `Sheaf.AlgebraicGeometry.ResolutionOpenScalarComparison` with the remaining
untwisted comparison. Updated the original node's proof route and dependencies.
This is a decomposition with a proved tensor calculation, not a sorry-free proof
of the original result's entire dependency closure. There are no statement or
definition changes and no forced adaptations.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.resolution_unitTwist_comparison`
(`lem-pc-resolution-unit-twist-comparison`). Its module has no sorry left.

Fully proved the new declaration:
`AlgebraicGeometry.Scheme.Modules.tensorUnitPower_scalar`
(`lem-pc-tensor-unit-power-scalar`), and its private helpers `unitPowerIso_section`
and `unitPowerIso` contain no sorry.

Added exactly one hole:
`AlgebraicGeometry.Scheme.Modules.resolution_open_scalar_comparison`
(`lem-pc-resolution-open-scalar-comparison`). It is the only sorry in the delivery.
This statement removes all tensor powers from the original comparison and only
concerns the raw resolution/derived-section identification. Its docstring and
node give the resolution construction, restriction naturality, principal-open
identification, and scalar argument. The existing proved
`resolutionSectionsHomology_scalar` is a useful input to its remaining proof;
it is not a complete derived-section comparison by itself.

Hole count: one closed, one added; this is a decomposition. The tensor calculation
and the Lean combination are complete.

## No longer needed

Removed the direct proof import `Sheaf.Topology.RestrictInjectiveResolution` from
the item's module. Its node `lem-sc-ringed-space-restrict-injective-resolution`
is still needed below the untwisted comparison, so this does not prune that
module from the eventual target closure. No original public imports were removed.
`def-weil-pbc-flat-base-change-open-choices` is no longer a direct proof dependency of the target node, but remains a statement dependency and is needed by the split comparison. `def-sc-open-module-cohomology` remains a direct proof dependency. No additional nodes or modules can be declared globally unnecessary on this route.

The existing `Sheaf.AlgebraicGeometry.SectionCohomologyUnitComparisons` was inspected
but is not imported: its scalar assertion concerns the principal open, whereas the
present theorem requires the scalar identity on the whole inverse-image open.
No affine, qcqs, quasi-coherence, localization, torsion, or fraction-presentation
modules are needed by the proved tensor calculation or the combining proof.

## Where the brief, the DAG or earlier work was wrong

No false statement or changed signature was found. The DAG's unit-power step can
be proved independently of all resolution, cohomology, and scalar-comparison
machinery. This delivery extracts and completes that step rather than leaving it
inside the unresolved comparison. The raw section/derived-cohomology comparison
still requires the compatibility of one fixed resolution comparison with both
restriction and scalar maps; merely choosing unrelated additive equivalences
would not establish either assertion.

The new statements were checked on n=0, q=0, b=0, invertible b, empty opens/schemes,
and zero coefficients in the mathematical arguments. The unit-power induction
starts with the identity, so n=0 uses the ordinary right unitor. Zero and unit
scalars require no division. The raw comparison excludes no such cases.

Searches: LeanFinder returned general monoidal/tensor-power facts for other tensor
structures, Loogle could not resolve tensorPowSection, and local searches found
and used the source tensor-section formulas. For the raw comparison, inspected
RestrictInjectiveResolution, ResolutionSectionsHomologyScalar,
SectionCohomologyUnitComparisons, FlatBaseChangeOpenChoicesExist, and the general
isoRightDerivedObj machinery. LeanSearch was unavailable (Internal Server Error);
this is recorded in both new nodes. No duplicate of either new statement was found.

## New nodes

`lem-pc-tensor-unit-power-scalar`, in
`dag/nodes/sec-picard-framework/lem-pc-tensor-unit-power-scalar.json`, records the
fully proved morphism-level tensor-unit identity in
`Sheaf.AlgebraicGeometry.TensorUnitPowerScalar`. It is independent of resolutions,
scheme morphisms, and cohomological degrees; its source is the tensor-unit
specialization of the numerator maps of Stacks Tag 09MR.

`lem-pc-resolution-open-scalar-comparison`, in
`dag/nodes/sec-picard-framework/lem-pc-resolution-open-scalar-comparison.json`,
records the strictly untwisted remaining comparison in
`Sheaf.AlgebraicGeometry.ResolutionOpenScalarComparison`. Its sources are Tags
01E1 and 01E4, with the already stated resolution-homology scalar lemma and
nonvanishing/local-generation lemma supplying steps of the planned proof.
The latter is used as a tool to identify the principal open; the former is used
as a tool for semilinearity of the pinned section-complex comparison. Neither
bypasses a blueprint unit statement or realized step. No change record is needed.

## Second reading by B2

1. **Visible declarations.** Compared the delivered resolution module with the repository version; the theorem statement and all existing signatures are byte-for-byte unchanged. The two added modules contain only the split statement and its supporting proved declaration.

2. **Proof validity.** Compiled all three modules with `lcompile.py --all`; there are no compiler errors, no forbidden declarations, and no `sorry` in the proved modules. The sole remaining `sorry` is the named `resolution_open_scalar_comparison` theorem and has a matching node and proof docstring. `#print axioms` in a scratch module confirms that `tensorUnitPower_scalar` uses only `propext`, `Classical.choice`, and `Quot.sound`. The resolution target and its split comparison additionally use `sorryAx`, as expected from the single remaining named hole. The tensor-unit theorem is fully proved by explicit recursive constructions.

3. **Split statements.** Checked the new untwisted comparison and tensor-unit scalar statements against the source formulas and edge cases (degree zero, zero/unit scalar, empty opens, and zero coefficients). Read Stacks Tags [01E1](https://stacks.math.columbia.edu/tag/01E1) (restriction of injectives and locality of cohomology), [01E4](https://stacks.math.columbia.edu/tag/01E4) (evaluation of the pushed-forward resolution), and [09MR](https://stacks.math.columbia.edu/tag/09MR) (the numerator-map context). The untwisted comparison uses only the resolution evaluation/locality portion, and the tensor statement is the unit specialization of the numerator maps, not the qcqs localization conclusion of 09MR. Its explicit induction supplies the calculation without those hypotheses. The tensor statement is strictly lower-level than the target; the untwisted comparison is the remaining strictly simpler resolution comparison. Independent searches used the query "cohomology of sections on inverse image open using an injective resolution natural in scalar multiplication" in LeanFinder and the fully qualified `CategoryTheory.InjectiveResolution.isoRightDerivedObj` in Loogle. Loogle found the genuine general resolution and naturality machinery; it does not identify the scheme inverse-image section complex or its semilinearity. Read `resolutionSectionsHomology_scalar` and `sectionCohomology_unit_comparisons` in full: the former needs a pinned restricted resolution and does not supply c/d; the latter gives scalar compatibility on U, not on Y. Local searches of resolution and unit modules found no duplicate. The remaining comparison is not closable by those results in a few minutes.

4. **Pruning and route.** The target proof uses `resolution_open_scalar_comparison` to pin c, d and the pulled-back section, and `tensorUnitPower_scalar` to remove the tensor powers. The restriction equation is naturality for `(i 0).inv`; the transition equation cancels the cohomology images of `i 0` and `i n` before applying the scalar equation. The unit record `sk-thm-picard-coherence.json` has empty realized statement/step lists: neither this item nor either new lemma replaces a realized unit node. The original resolution and tensor-unit steps are retained in this reduction. The direct `RestrictInjectiveResolution` proof import is no longer used by the target module and was removed; its node remains a dependency of the split comparison. No unnecessary public import was removed.

5. **DAG agreement.** Updated proof routes and `proof_deps` match the Lean imports and applications. The new nodes have sources, proof steps, searches, Lean records, chapter/unit, and split status required by the stage contract. No definition or target statement was changed.

Changed during second reading: added this review record and clarified the old dependency pruning and empty unit realization record; no Lean proof or statement changes were needed.
