## What changed

Completed `AlgebraicGeometry.ProEtale.CondensedRing.proper_image_localizing_proper_coefficients`
in `Sheaf.SixFunctors.ProperImageLocalizingProper`. All six coefficient cases use the
existing finite, integral and rational theorems. The previously proved conditional
restriction theorem and every existing public signature and definition are unchanged.

Private proved helpers transport the two hypotheses through condensed ring
isomorphisms, construct the bottom-field Q_l and Z_l identifications as explicit isomorphism data and the finite
ULift coefficient identification, deduce bounded preservation by truncation induction,
and extend preservation from Hom-universe sums to all existing larger coproducts by
the small nonzero-support argument. The geometric-fibre bound is derived from the
existing ordinary-fibre bound and field-base-change dimension theorem.

Updated the existing node proof and proof dependencies to match these arguments.
No new public declaration, new module, new node, or adapted consumer is introduced.
The local elaboration commands and private variable section are documented in
`coord/changes/K2-proper-coefficient-private-proof-context.md`; the complete consumer
audit records identical public signatures, definitions and exports.
The sandbox copy of `CondensedCoefficientIsoConstructible` was identical to current
sources and was removed from the delivery; its existing theorem is imported.

## Proved and sorry left

Closed one of the one original remaining holes:
`AlgebraicGeometry.ProEtale.CondensedRing.proper_image_localizing_proper_coefficients`
(node `det-proper-image-localizing-proper`).

The conditional `proper_image_localizing_proper` remains proved.
The first required dry run compiled the module and its axiom probe cleanly; its
preflight requested the administrative change record for local proof commands.
After the duplicate-private-helper cleanup, the module again compiled cleanly
in 41.4 seconds through `lcompile.py`. There are zero
`sorry` occurrences in the delivered Lean module and zero holes added or split off.
This is a proof from existing declared dependencies, some still open elsewhere.

Resumed validation on 2026-10-19: the required `deliver3.py --no-push` passed
against current sources (dry-run commit `46fcc3bac2`), including compilation and
the axiom probe. The packet is classified CODEX for the node update and recorded
local proof commands; independent review is performed by the delivery workflow.

## No longer needed

Removed proof-only imports `Sheaf.Paper.IntegralProperBaseChange`,
`Sheaf.Paper.CondensedModuleDerivedPushpull`, and
`Sheaf.Paper.LocalizingAdmissibleCoefficients`.
The direct dependency `det-thm-sfb-proper-base-change-integral` is unnecessary:
the heart clause of `integralProperDirectSums`, followed by a complete bounded
truncation induction, proves the required bounded preservation. The integral
base-change theorem may remain needed by other modules or by that dependency.
The other two modules contribute no declaration used by this proof; the canonical
pushforward is the existing `lowerStar.rightDerivedFunctor` and the closure is
provided by the unchanged public imports. No entire module is withdrawn.

The proof does not use the stronger all-ambient-sums
`det-proper-image-localizing-principle`; it keeps the unit's restricted-sums argument.
All other originally listed proof dependencies are retained. Additional existing
nodes used are `sk-thm-sfb-qlbar-two-colimit`,
`lem-sfb-integral-constant-model-heart-closure`,
`lem-sfb-condensed-coefficient-iso-constructible`,
`def-sfb-derived-comap-lower-star-iso`, and `lem-pc-dim-base-change`.

## Where the brief, the DAG or earlier work was wrong

The retained attempt was incomplete at typeclass elaboration, not at the coefficient
case split. Rational finiteness uses the locally free bounded predicate whereas the
item uses finite constant models: the existing equality clause of finite coefficient
descent bridges them. The fibre-bound theorem bounds ordinary fibres, while both
sum theorems request geometric fibres: pullback associativity and the existing
field-extension dimension theorem supply that bridge. Integral bounded preservation
can be obtained from its already stated heart clause and the existing Serre closure
of integral constant-model constructibles. These are interface bridges in the
source's route, with no weakened statement or altered target.

The extra static import-pruning check identified four private helper statements
already stated privately in other modules, so none could be imported as an API.
The final proof constructs the two canonical bottom-field isomorphisms as explicit
data at that fixed field, and proves the zero-model clause directly where needed
on the qcqs target. It adds no duplicate zero-model theorem or existential helper.

Edge cases checked in the constructed helpers: the zero finite ring (use exponent
n+1), empty schemes (the one-stratum zero model), empty families, zero summands,
inverted cohomological intervals, and the bottom finite intermediate field.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
