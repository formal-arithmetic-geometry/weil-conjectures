## What changed

Restored the assigned quarantined module from
`quarantine/Sheaf/Paper/WContractibleCondensedScalarEvaluation.lean`, preserving its
existing public declaration signatures, definition bodies and public imports.
Replaced the proof of
`AlgebraicGeometry.ProEtale.wContractible_condensed_scalar_evaluation` with a complete
Lean reduction to ordinary affine scalar evaluation. Added the private, proved helpers
`scalarSections_tExact` and `scalarSections_leftDerived`.

The first helper identifies the recorded right-derived section functor with the exact
termwise evaluation functor and transports both truncation bounds through restriction
of scalars. The second constructs the natural derived comparison from the ordinary
comparison, the fixed change-of-rings model, and flat-term K-flat resolutions. Its
universal left-derived comparison is proved invertible on resolutions and then on
every derived object. It handles the independent localization universes in the
unchanged original statement.

Added `Sheaf.Paper.CondensedAffineOrdinaryScalarSections` with the separate ordinary
module result used by that argument. Updated the original node's proof and dependencies
to match the implemented route. No existing statement, definition or target changed;
no forced consumer adaptations or change records are required.

The first preflight requested a change record for a local instance-attribute command.
Removed that command and replaced it with explicit composition instances inside the
private proof; no module-scope command is added.

Validation: both sandbox Lean modules compile through `lcompile.py --all`. All added
proof imports are private. The new ordinary theorem has its own public statement
imports. No definition contains a hole.

## Proved and sorry left

Closed the original proof body of
`AlgebraicGeometry.ProEtale.wContractible_condensed_scalar_evaluation`
(node `lem-zl-wcontractible-condensed-scalar-evaluation`). The two private helpers
`scalarSections_tExact` and `scalarSections_leftDerived` have complete Lean proofs.
The assigned module contains zero `sorry` tokens.

Added one remaining hole:
`AlgebraicGeometry.ProEtale.condensed_affine_ordinary_scalar_sections`, in
`Sheaf.Paper.CondensedAffineOrdinaryScalarSections`, node
`lem-zl-condensed-affine-ordinary-scalar-sections`. Its proof is exactly `by sorry`;
its docstring gives the source and the full ordinary-module proof by the balanced
comparison, coproducts and free presentations.

This is a decomposition: one original hole closed and one ordinary-module hole added,
net zero holes. It is not claimed as a net proof completion. The remaining statement
has no derived category, universal derived functor or t-exactness assertion, so it is
strictly the degree-zero geometric part of the argument, rather than a renamed copy
of the original theorem. Existing imported theorems are used as stated; their own
holes are not changed by this packet.

## No longer needed

Removed these direct proof imports from the restored item:

- `Sheaf.Paper.CondensedPointBasisEvaluation`
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`
- `WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`
- `Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsExact`
- `WeilConjectures.RingTheory.ProEtale.WContractible`

The exact-section and ring weak-contractibility APIs remain available through imports
actually used by the proof. Point-basis evaluation, colimit-preserving affine
evaluation and module adjunction remain mathematical dependencies of the new ordinary
lemma; they are not claimed globally pruned.

The implemented derived argument no longer needs these original proof dependencies:
`lem-pc-kflat-resolution`, `lem-weil-pbc-ringed-pullback-preserves-kflat`,
`lem-weil-pbc-site-derived-tensor-descent`,
`lem-weil-proetale-weakly-etale-localization`, and `det-pe-wc-sections-derived`.
Removed their entries from the original node's top-level `tool_uses`, preserving the
remaining order. The argument instead uses source module K-flat resolutions, exact
constant-module K-flat preservation, and the universal normalized left extension.
Evaluation is the functor already used in the definition of derived sections, so no
slice-site identification or separate derived tensor-descent construction is needed.
These are route-level removals; no Lean module or DAG node is deleted and no claim is
made that another target no longer uses any of them. The unit's realized route is
unchanged.

## Where the brief, the DAG or earlier work was wrong

The item's live Lean path is absent because it was quarantined for rework. Its rework
row names the preserved source used here; this is a restoration, not evidence for a
withdrawal. Its Lean attachment and public declarations are preserved.

The planned coefficient evaluation and tensor comparison do not directly supply a
typed ordinary comparison for the actual internal-ring reconstruction and the fixed
ordinary change-of-rings functor. The new lemma states precisely that interface.
The rest of the planned derived descent can be replaced by the existing universal
left-derived extension and K-flat-resolution APIs. No false statement was found.

## New nodes

`lem-zl-condensed-affine-ordinary-scalar-sections` is in chapter `sec-zeta-weil`,
with the original item's unit and blueprint ancestry. Source: Hemo–Richarz–Scholbach,
Section 3, equation (3.2), Remark 3.2, Lemma 4.1(1) and Proposition 4.3(1). The
statement is the ordinary coefficient-ring identification together with the natural
ordinary scalar-extension comparison. Its proof uses point-basis ring evaluation,
the canonical balanced tensor map, preservation of coproducts, and free presentations.
It covers the empty affine, zero coefficient ring, and arbitrary nonflat modules;
flatness is needed only later in the already implemented derived argument.

Mathlib searches using Leansearch, Leanfinder and text search found ordinary
extension/restriction and tensor APIs, but no theorem expressing this comparison for
the project's internal/sectionwise module equivalence and point inverse image.
There are no definition-change records.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
