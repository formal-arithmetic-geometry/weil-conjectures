## What changed

The item proves coefficient_construction_coherence by assembling normalized ring scalar
laws, explicit counit-transpose calculations, rational left laws, common representative
laws, and ring-to-rational-to-common refinement descent. Its existing signature and all
four coherence records are unchanged. The main module compiled in 42.5 seconds after
replacing concrete comparison projection matching with proved generic field wrappers;
all timing diagnostics and temporary heartbeat settings were then removed.

ConstructibleExceptionalCoefficientConstructionData now retains literal rational object
and integral-arrow localization and the common representative-arrow formula required by
the reviewed coherence node. The generic localizedAction and representativeAction
predicates keep these normalizations independent of implementation reductions. This is
a definition repair and requires renewed statement review of target-reachable definitions.
The newly landed A3 construction proof and its stage/refinement split are preserved;
their module documentation records the repaired normalization contract.

NormalizedRingCompactScalarCocycle is generalized to independent site and algebraic-closure
universes. The old equal-universe specialization is included. No target signature changes,
and no source-library declaration is removed or changed.

Change records: coord/changes/D6-coefficient-construction-morphism-normalization.md and
coord/changes/D6-normalized-ring-universe-interface.md.

## Proved and sorry left

The item's one original hole, coefficient_construction_coherence, is closed by a complete
assembly proof. normalized_common_coefficient_laws is proved, including the left law from
identity representatives and the right law by adjunction counits. Private proved helpers
transfer left scalar identity/composition to the right adjoints and descend ring refinement
identity/composition to rational and common coefficients.

Two new holes remain: normalized_rational_left_laws
(lem-sf-normalized-rational-left-laws) and normalized_ring_refinement_laws
(lem-sf-normalized-ring-refinement-laws). They are strictly separate parts of the original
argument: rational LEFT scalar identity/composition, and ring-stage LEFT refinement
identity/composition. Neither restates the bundled theorem, a right law, a common law,
or refinement descent. This is a decomposition, not a net proof of the target closure.

Existing retained dependency holes are normalizedRingCompactScalarCocycle
(lem-sf-normalized-ring-compact-scalar-cocycle), exists_coefficient_stages
(lem-sf-constructible-exceptional-coefficient-stages), and
exists_coefficient_left_refinements (lem-sf-constructible-exceptional-left-refinements).
No hole is inside a definition. ConstructionData and the item have zero holes.

## No longer needed

The item does not use CommonTransitionCoefficientMates: the common representative action
at the identity and direct counit calculation give both common laws. It does not directly
use RationalLeftCoefficientLocalization, IntegralRefinementDiagramAdmissibility,
IntegralNormalizedRefinementPasting, ProetaleConstructibleOrigin, or
CompactificationCoherence; the rational and ring-refinement helper nodes retain the
corresponding separate obligations and their declared dependencies. None of these shared
modules is withdrawn. No WeilConjectures declaration is pruned. The unit sk-thm-sf-compatibility
retains its own statement and proof steps; its realized lists are empty and are unchanged.

Removed direct tool-use entries: lem-pur-ringed-coefficient-projection-cocycle, lem-sfb-successive-derived-quotient-normalization, lem-weil-pbc-mate-pasting, lem-weil-finite-free-completed-scalar-comparison, lem-weil-scalar-extension-composition, lem-sf-proetale-constructible-origin, prop-compactification-coherence-detailed, lem-trf-open-ctf, lem-kun-dimension-finite-type, cor-sf-direct-image-ctf-proetale, lem-coef-integral-compact-support, lem-sf-ambient-proper-open-pasting.

The generic mate-pasting theorem import is unnecessary: the explicit counit calculations
prove the required right identity and composition. Removed stale direct tool-use approvals
for ring projection cocycles, quotient normalization, mate pasting, completed scalar
comparison, scalar composition, constructible origin, compactification coherence, open
Tor preservation, dimension bounds, constructible direct image, integral compact support,
and ambient proper/open pasting; their needed mathematical uses remain in helper nodes.

The provisional primitive-refinement extraction and source adaptations are absent from
the packet because the delivered assembly does not import them. The three new helper
modules publicly import ConstructionData, the actual owner of their statement records.

## Where the brief, the DAG or earlier work was wrong

The reviewed coherence statement already requires rational object/arrow and common
representative-arrow normalization, but the original Lean construction records contained
only individual component normalization. That does not determine a functor's action on
arrows between different labels of the pair category. The repaired records state the
intended construction on those arrows without assuming coherence. The rational scalar
argument needs only localized integral arrows, not an unsupported reflection of equality
through localization.

During this session A3 landed the ConstructionData extraction and proved existence
assembly. The packet rebases onto it, retaining that proof and the independent stage and
left-refinement obligations. The old single-universe ring scalar helper could not be
instantiated at the item's independent universes; its uniform generalization repairs this.

## New nodes

lem-sf-normalized-common-coefficient-laws records the proved common left/right transition
argument from representative action and counits. Its module also defines the two literal
predicates used to keep the heterogeneous equations readable.

lem-sf-normalized-rational-left-laws records the localization of integral left scalar
composition and identity. It retains no right/common/refinement conclusion. The complete
source argument and edge cases appear in its docstring and node.

lem-sf-normalized-ring-refinement-laws records ring-stage proper/open normalization and
identity/transitivity. Its source proof uses finite witnessed compactification coherence
and integral normalized refinement pasting on the admissible finite-Tor domain. Rational
and common descent are proved in the item and are not included in this helper.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
