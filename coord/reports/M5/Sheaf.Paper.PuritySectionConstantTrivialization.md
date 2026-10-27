## What changed

Replaced the proof of
`WeilConjectures.PurityFiniteSetting.SectionRestriction.section_constant_trivialization`.
The statement, `lineCounit`, and existing public imports are unchanged.

Constructed the actual extended-Rees deformation datum and applied the existing
ordinary-etale family-constancy theorem. Private proved helpers transport its model
through the fixed site comparison and check the composition, identity, and section
constraints. Specializing the published DNC normalization predicate to identity
base change proves the zero reading. For arbitrary target objects, lift the ratio
of two comparisons to an endomorphism of the bounded-below etale family; the
existing invertible-object detection theorem then proves equality at one suffices.
This uses comparison full faithfulness only with a bounded-below target.
Private helpers cache the canonical `Sheaf.instHasColimitsOfShape` proofs to avoid
repeated broad instance searches. Their local instance scope covers only the private
proof helpers, ending before the public theorem. No shared definition is changed.

Added proof imports of `Sheaf.Paper.ComparisonPullbackDerivedCoherence`,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarCompCoherence`,
and `WeilConjectures.EtaleCohomology.TateTwist.Normalized`.
Updated the item's DAG proof, proof dependencies, and proof origin accordingly.
No existing shared module or other node is changed.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.PurityFiniteSetting.SectionRestriction.section_constant_trivialization`
(node `lem-pur-section-constant-trivialization`).

One hole closed, zero holes added, zero holes left in the delivered module.
No statement is split off and no additional assumption is introduced.
The final single-file server compile passed without warnings in 36.2 seconds.
The public theorem statement and `lineCounit` definition were checked unchanged;
all added proof imports passed the import-direction check.

## No longer needed

None. No existing import, declaration, module, or DAG dependency is withdrawn.
All the original geometric and site-comparison dependencies are retained.
The existing normalized etale constancy theorem is used directly, so no new local
chart, gluing, or lisse-automorphism obligation is introduced.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The DAG's ordinary-etale
constancy route applies to the actual constructed deformation datum. Its general
pro-etale target clause requires the bounded-below comparison Hom bijection for
an automorphism of the family; it does not require faithfulness on arbitrary
derived Hom. The DAG now records this point and the formal identity-base reading
calculation explicitly.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
