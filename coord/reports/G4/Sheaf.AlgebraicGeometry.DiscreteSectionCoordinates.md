## What changed

Proved `AlgebraicGeometry.ProEtale.IntegralModelsStacks.discrete_section_coordinates` in the assigned module, preserving its statement and the definition of `discretePointScalarSection`. The proof constructs an explicit coordinate equivalence, proves its scalar normalization and restriction compatibility, and chooses the inverse coordinate of the given section. All added constructions and lemmas are private and fully proved. Added proof imports for the existing constant-coefficient comparison, monoidal localization, lifted-integer corepresentability, and small-site equivalence. Updated the item's proof plan and dependencies. The private constructions become irreducible after their comparison lemmas, so subsequent proofs use that API instead of unfolding large sheafification terms.

Validation: the server compile passed in 53.3 seconds, including an axiom probe. `#print axioms discrete_section_coordinates` reports exactly `propext`, `Classical.choice`, and `Quot.sound`. The final file removes the probe and all profiling/debug commands. Both original public signatures and the scalar-section construction are unchanged.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.ProEtale.IntegralModelsStacks.discrete_section_coordinates` (`lem-sfb-discrete-section-coordinates`). Added zero holes. There are no remaining `sorry`s in the delivery and no split-off statements.

## No longer needed

The separate planned dependency `lem-weil-proetale-weakly-etale-localization`, implemented by `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`, is not needed by this proof. The existing source-library localization adjunction computes inverse image as restriction, and Mathlib's continuous/cocontinuous sheafification comparison supplies the constant-ring localization directly. No original public import is removed, and no module or upstream declaration is withdrawn. The other declared dependencies are used.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The terminal coefficient comparison already has a proved private generalization for arbitrary abelian coefficients; importing that existing proof avoids reconstructing its inverse-image composition calculation. The proof checks empty schemes and the zero ring through uniform adjunction and sheafification identities, without extra hypotheses.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
