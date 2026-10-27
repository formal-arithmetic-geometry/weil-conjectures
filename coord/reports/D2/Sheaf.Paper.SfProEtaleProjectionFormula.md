## What changed

Updated `Sheaf.Paper.SfProEtaleProjectionFormula`, reducing `WeilConjectures.sf_proetale_projection_formula` along the current blueprint route: the finite clause uses the source library's proved finite pro-etale projection formula after transporting the retained origin and intrinsic Tor witnesses. The integral clause is a composite of the ordinary projection and invertible completion units. Its ordinary projection is detected by finite scalar reductions. The rational and common-stage clauses use functorial preservation of isomorphisms.

Added `Sheaf.Paper.SfIntegralReductionConservative`, proving `WeilConjectures.sfIntegralReduction_conservative` by a distinguished cone, exact finite reduction, and the augmented Roos completeness triangle. Added `Sheaf.Paper.IntegralOrdinaryProjectionReduction` for only the finite-reduction assertion about the specified ordinary projection arrow. It is strictly a step of the adic argument: it asserts invertibility after finite reduction, and supplies neither integral invertibility nor the completion-unit and field arguments.

The main theorem statement is preserved. No source-library or coefficient definitions are edited. The finite proof uses private generic interfaces for the named projection property and bifunctor whiskering, and preserves the finite coefficient instance already selected in its statement. Local irreducibility settings keep the constructed maps folded. The existing tensor-domain proof uses named projections of its supplied presentation and explicit universe annotations. These are elaboration changes only; the map and tensor models are unchanged.

Validation: all three modules compile together in import order with no errors or warnings. Both existing public theorem signatures and all seven existing definition bodies are unchanged. The item module has no remaining hole.

## Proved and sorry left

Original hole closed by decomposition: `WeilConjectures.sf_proetale_projection_formula` (one of one original holes).

New hole: `WeilConjectures.integralOrdinaryProjection_finiteReductions`, in `Sheaf.Paper.IntegralOrdinaryProjectionReduction`, node `lem-sf-ordinary-projection-finite-reductions` (one split-off hole).

New theorem proved without a hole: `WeilConjectures.sfIntegralReduction_conservative`.

This is a decomposition with one hole closed and one added, not a claim of net hole reduction. The item module has zero remaining holes; the packet has one.

## No longer needed

The direct application of `thm-sf-pf-adic` is replaced by its finite-reduction/cone argument on the actual completed coefficient sheaf. `thm-sf-pf-field` is unnecessary for the literal localization and common-stage maps in this statement: both are images of the integral map under functors. No module is withdrawn.

The finite clause uses the already proved source fixed-scalar compactification projection theorem and the precise intrinsic Tor transport, so it does not need to reconstruct the finite comparison theorem through `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula` or `Sheaf.Paper.ComparisonTorAmplitude`. The retained witnesses directly give constructibility, so no new origin existence theorem is needed there. The split-off reduction lemma still records the origin/residue-Tor/comparison steps it needs.

Removed direct proof imports: `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`, `Sheaf.Paper.ComparisonTorAmplitude`, `Sheaf.Paper.ExchangeProjectionSuppliedDomains`, `Sheaf.Paper.IntegralResidueTor`, `Sheaf.Paper.ProEtaleConstructibleOrigin`, `WeilConjectures.Compactification.Noetherian`, `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, `WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational`, and `WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative`. The reduction bridge still records residue Tor and coefficient compatibility in its own proof plan. The source projection theorem may retain some of these transitively; no transitive source declarations are removed.

The revised top-node proof dependencies no longer directly cite `def-exchange-projection`, `def-sf-pf`, `def-weil-derived-complete-integral-detailed`, `def-weil-finite-tor-amplitude`, `lem-coef-integral-residue-tor`, `lem-fix-operation-reduction`, `lem-sf-comparison-tor-amplitude`, `lem-sf-proetale-constructible-origin`, `lemma-nagata-open-immersion-qc-over-separated-target`, `sk-thm-nagata-sketch-noetherian`, `lem-exc-comparison-tor-interval`, `lem-pur-projection-comparison-etale-origin`, `lem-sf-proetale-pf-admissible-models`, `thm-weil-pbc-site-comparison`, `thm-sf-pf-adic`, or `thm-sf-pf-field`. The finite branch uses the supplied origins, the exact intrinsic Tor transport and the source projection theorem. The integral branch uses the concrete coefficient operations and the two new reduction lemmas. Its domains use the existing finite-type/noetherian, tensor, pullback and support interfaces directly. Completeness and residue/comparison facts remain dependencies of those interfaces or of the reduction bridge where used. This removes these entries from the direct top-node route, not from any source declaration or from a still-needed lower proof.

## Where the brief, the DAG or earlier work was wrong

The recorded `thm-sf-pf-adic` Lean attachment is about discrete etale coefficient modules. It cannot be specialized to the completed pro-etale coefficient sheaf used by `integralMap`. The proof therefore realizes the same adic unit argument directly: finite reductions, constructibility of the cone, and derived-complete conservativity. No target or coefficient definition is weakened or replaced.

The completed integral map and field clauses are stated for every integral constructible representative. The existing ordinary tensor and pullback constructibility/completion-unit results establish the necessary domains without assuming the structure maps of X or Y separated. The new finite-reduction lemma keeps exactly this geometry.

## New nodes

`lem-sf-intrinsic-reduction-conservative` attaches the proved general cone/Roos conservativity lemma on integral constructibles. Source: the current blueprint adic projection proof, conservativity step, and the existing derived-completeness definition.

`lem-sf-ordinary-projection-finite-reductions` states the remaining finite-reduction substep for the actual ordinary proper-counit/open-extension composite. Its docstring and node give the reduction squares and finite projection argument, including tensor-model normalization and the absence of structural separatedness assumptions.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
