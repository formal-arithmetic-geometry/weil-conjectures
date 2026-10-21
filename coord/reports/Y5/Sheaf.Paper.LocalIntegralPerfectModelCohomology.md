## What changed

Proved `AlgebraicGeometry.Scheme.local_integral_perfect_model_cohomology` in
`Sheaf.Paper.LocalIntegralPerfectModelCohomology`, preserving its complete statement,
definitions, instance, universes, and public imports. Added two proved private helpers:
`localIntegral_constant_exact` establishes exactness on the original site with independent
object and morphism universes, and `localIntegral_coefficient_iso` transports the existing
finite-ring tower comparison to the actual adic ring diagram, including every projection.

The scalar ring is Noetherian by the coefficient DVR theorem. Positive coefficient
quotients are finite by `Padic.finite_coefficientExtensionRing`. The existing profinite
coefficient inverse-image theorem therefore provides the coefficient isomorphism directly.
The specified ring-module pullback and slice restriction are exact. Constant module
presheaves preserve limits and colimits sectionwise; module sheafification is exact.
Completion flatness gives exact scalar extension. Their composite is the scalar realization.
For cohomology, the displayed morphism is a composite of isomorphisms. The abstract module
homology is identified with the quotient of the outgoing differential's kernel by incoming
boundaries; Noetherianity makes that quotient finite and hence finitely presented.

Updated the existing node's proof, dependencies, and proof origin to reflect this argument.
The unit statement and its realized steps are preserved. In the exactness helper, the
locally bijective constant-ring sheafification unit is retained, rather than replacing the
coefficient sheaf by a different presentation. The finite-ring tower result is
used as a generic coefficient-comparison tool; the current immersion-limit statement is not
needed for this finite-quotient argument. Constant-module exactness is reproved at the actual
unequal site universes by the sectionwise argument of
`lem-weil-pbc-finite-type-constant-exact`, since its published small-category signature does
not directly apply to the original pro-etale site. The proof uses the Mathlib
`PresheafOfModules.sheafification` exactness instances recorded by
`lem-weil-pbc-ringed-site-module-sheafification-exact` at that locally bijective unit.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.local_integral_perfect_model_cohomology`
(node `lem-sfb-local-integral-perfect-model-cohomology`).

One of one existing holes closed; zero holes added; zero split off; no sorry remains in
the delivered module. The two private helpers are fully proved. Zero and torsion cohomology are included; neither
boundedness nor termwise projectivity is needed for this cohomology calculation, and both
original hypotheses are retained verbatim. Imported declarations
remain the independent existing items of their respective nodes.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`
  (`lem-weil-pbc-proetale-immersion-limit-preservation`): preservation of arbitrary inverse
  limits is unnecessary; the finite quotient tower has its own proved comparison.
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`
  (`lem-pe-constant-left-module-inverse-image`): the profinite comparison already includes
  normalized constant inverse-image maps and their projection equations.
- `Sheaf.Paper.ConstantModuleSectionProperties`
  (`lem-weil-pbc-constant-module-section-properties`): exactness of constant module
  realization follows directly from sectionwise presheaf limits and colimits followed by
  module sheafification. No assertion about sections of arbitrary constant sheaves is used.

Removed those same three obsolete `tool_uses` entries from the node. No module is withdrawn:
other consumers can still need these nodes. All public imports are retained because they
provide the public statement's existing objects and comparison interfaces.

## Where the brief, the DAG or earlier work was wrong

The planned coefficient argument was longer than necessary. The finite quotient ring
interface and `lem-weil-pbc-profinite-coefficient-inverse-image` give the required normalized
comparison for any scheme morphism. The theorem keeps its immersion hypothesis verbatim.
The specified pullback already has additive and exact instances in `ProEtaleOperations`.

No statement, definition, target, upstream declaration or other group's module changed.
No new nodes were introduced. The original docstring is preserved; the revised node and
this report record the actual shorter proof route.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
