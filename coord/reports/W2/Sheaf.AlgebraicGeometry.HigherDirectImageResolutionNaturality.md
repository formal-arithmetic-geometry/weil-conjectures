## What changed

Proved `AlgebraicGeometry.higherDirectImage_resolution_naturality` in
`Sheaf.AlgebraicGeometry.HigherDirectImageResolutionNaturality`, with its original
signature and specified section map unchanged. Two proved private helpers establish
the naturality of the sheafification comparison before choosing resolutions.
Mathlib's augmentation-preserving resolution lift, derived comparison naturality,
exact-evaluation homology naturality, and adjunction naturality provide all steps.
The existing node's proof and proof_origin record this implementation. Its
proof_deps are unchanged. No imports, definitions, public signatures, or other
modules changed.

The source is Stacks Project, Cohomology, Lemma 20.7.3,
[Tag 01E4](https://stacks.math.columbia.edu/tag/01E4). Its comparison is computed
by the presheaf homology of a direct-image injective resolution. The proof here
checks naturality of that exact construction. The argument applies in degree zero,
to zero coefficient maps, and to empty opens without extra hypotheses. The unit
`sk-thm-picard-duality` has no realized nodes or proof steps bypassed by this proof.

## Proved and sorry left

Closed: `AlgebraicGeometry.higherDirectImage_resolution_naturality`
(node `lem-pc-higher-direct-image-resolution-naturality`). This is 1 of 1 original
holes closed, with 0 holes added and 0 split off.

Also proved the private helpers `adjoint_homology_naturality` and
`sectionCohomologyTheta_naturality`. No `sorry` remains in the delivered module.
This proves the assigned theorem from existing Mathlib declarations, rather than
replacing it with an unproved intermediate statement. The existing imported
library may still contain its own holes; none were added by this delivery.

Validation: the module compiled using the mandated local launcher with no warnings.
The delivery dry run performs compilation and the axiom probe again.

## No longer needed

None. The sole original public import
`Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices` is required by the unchanged
section-map definition. No additional proof imports were needed. All three planned
proof dependencies remain used: `def-sp-injective-resolutions`,
`def-weil-presheaf-modules-sheafification`, and
`def-weil-pbc-flat-base-change-open-choices`. No nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface errors found. The existing plan is sufficient.
Identity restriction of scalars in the sheafification adjunction needs explicit
functor arguments for efficient elaboration. Short-complex and complex homology
are definitionally identified using `erw`; the final evaluated direct-image
section map identification is `rfl`. These are proof elaboration details, and no
definition or statement repair was necessary.

## Second reading by W2

1. **Interface preservation: pass.** Read the complete module and compared it
   with the repository using `diff -u`. The existing definition
   `higherDirectImageResolutionSectionMap`, including its body, is byte for byte
   unchanged. The signature of `higherDirectImage_resolution_naturality` is
   unchanged: arbitrary schemes X and Y, morphism f, degree p, open V,
   coefficient morphism a, and specified resolutions I and J. Only its proof,
   two proved private helpers, and local heartbeat settings were added. There
   are no other delivered modules or change records. Read Stacks Tag 01E4,
   Lemma 20.7.3: the definition uses precisely its sectionwise direct-image
   resolution homology followed by sheafification. Naturality is proved for
   that specified map, rather than for an unspecified comparison.
2. **Proof and trust: pass.** Independently compiled the delivered module
   cleanly (47.8 seconds). Compiled a scratch copy with `#print axioms` for
   the section-map definition, both private helpers, and the assigned theorem
   (45.4 seconds). All four use only `propext`, `Classical.choice`, and
   `Quot.sound`; none uses `sorryAx`. Scanned the delivered Lean for forbidden
   declarations and holes: none. The only chosen resolution morphism is
   Mathlib's `InjectiveResolution.desc`; its augmentation equation is supplied
   by `desc_commutes_zero`. No data is chosen from an unproved existence claim.
3. **Split statements and small cases: pass.** No split-off statements or new
   holes. Read both private helper proofs: the generic helper first commutes
   exact sheafification with homology using the inverse mapHomologyIso square,
   then applies homology to counit naturality and takes adjoints. Its
   specialization unfolds exactly `sectionCohomologyTheta`. No exactness of
   the forgetful right adjoint is assumed. The arguments admit arbitrary p,
   including zero; zero coefficient maps and empty opens need no exception,
   since every step is a functorial equality. There is no cancellation of a
   section-class map or assertion that taking sections is exact on sheaves.
4. **Route, existing results, and pruning: pass.** Read Mathlib's two
   `isoRightDerivedObj` naturality lemmas, both mapHomologyIso naturality
   lemmas, and `Adjunction.homEquiv_naturality_left_square`. Searched both
   library roots and Mathlib for theta/homology-adjunction naturality and ran
   Loogle with `"homEquiv", "naturality"` (12 generic adjunction hits).
   No already proved specialized theorem replaces the four squares here.
   The analogous flat-base-change resolution proof concerns different maps
   and would not shorten this argument. The sole public import is needed by
   the unchanged definition's use of `sectionCohomologyTheta`. There are no
   proof-only public imports or unused imports. All three old proof_deps
   remain used, so `## No longer needed` is complete. Read the unit record
   `sk-thm-picard-duality`: its realized statement and step lists are empty;
   this below-unit naturality argument bypasses no realized unit step.
5. **DAG agreement: pass.** Compared the node JSON with the repository. Only
   `proof` and `proof_origin` changed; the statement, Lean signature record,
   and proof_deps are unchanged. Its three steps describe the code: the
   augmentation-preserving source resolution square; evaluation and theta
   naturality; the target inverse-resolution square and definitional
   direct-image section identification. The dependency union is exactly
   `def-sp-injective-resolutions`,
   `def-weil-presheaf-modules-sheafification`, and
   `def-weil-pbc-flat-base-change-open-choices`. No new nodes need checking.

Second reading changed only this report by adding the independent review.
No proof repair was necessary. Confirmed holes closed: 1; holes added: 0;
split off: 0; pruned: none.
