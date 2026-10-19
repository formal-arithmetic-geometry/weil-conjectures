## Worker report

This repairs the returned head 662026aead2e. The initial saved packet passed the required
dry run (temporary commit 1de9e99baa), but its mathematical self-check confirmed the
returned defects. The packet is therefore substantively repaired, not re-pushed unchanged.
Only the owning module and its lean record are changed. All auxiliary records below package
conclusions of this node, not assumptions. Dependent data and their equations are separated
into Finite/FiniteCoherent, DualityData/DualityProperties and
ExceptionalData/ExceptionalProperties to avoid repeated kernel unfolding when generating
dependent structure projections. Duality and Exceptional extend these data with their full
equations. The finite operation aliases finiteLeft, finiteRight, finiteAdjunction,
finiteLeftScalar and finiteRightScalar are exactly the published System projections with
cached category endpoints; they introduce no alternative operations. The only postponed
theorem is WeilConjectures.coef_qbar_verdier.

Hypotheses and clauses, matched against the DAG statement:

- The global finite-field datum is D : FiniteFieldDatum.{u}; the coefficient prime   is l
  with Fact l.Prime and hl : l ≠ D.p. Ω : Type v has Field, Algebra (Padic l)   and
  IsAlgClosure instances. No equation between u and v is imposed.
- X is a Scheme.{u} over Spec D.k. Its structure morphism has IsSeparated,
  LocallyOfFiniteType and QuasiCompact, exactly separated finite type over k.   Y and f have
  the same geometric hypotheses, and f.IsOver supplies k-linearity.
- The finite intermediate fields are AlgebraicallyClosedCoefficients.Index l Ω.   Their
  Coefficient.{u} models use Shrink.algEquiv, so every finite subfield of   the given Ω is
  covered even when its universe differs from that of X.
- Finite.omega, Finite.datum and Finite.hom use the actual integral dualizing   datum,
  RationalVerdier.Datum and RationalOperations.HomIdentification.   Finite.scalar and
  normalized use RationalVerdier.Extension and   ExtensionProperties, including the actual
  integral-origin omega, beta,   evaluation and biduality squares. FiniteCoherent retains
  identity   and tower equations for those same comparisons.
- Duality.duality is one SfClassDuality, so exactness, anti-equivalence and its   natural
  bidual isomorphism concern the very same .dual. The literal object clause of
  DualityProperties   specifies (E,K) maps to (E,D_E K). The natural inclusion comparisons,
  the comparison-normalization, scalar-comparison and bidual clauses of DualityProperties
  identify its actual arrows   and delta with those finite data; no unrelated dual functor
  is quantified.
- DualityData.linearCategory is normalized by the scalar-action clause of DualityProperties
  on every finite-stage   included arrow, using the actual embedding of Coefficient E into
  Ω.   The same properties assert Additive and D(c f) = c D(f) for that action; the opposite
  action is   not an independently chosen Linear structure. Algebraic exhaustion and
  finite representatives determine the action on every arrow and scalar.
- The dualizing object has omegaComparison at every finite field and the   omega-scalar
  equation in DualityProperties. Dualizing additionally identifies it with the descended
  exceptional pullback of the constructed coefficientUnit at a_X. The latter   is the
  completed regular module localized at the base finite coefficient   field, not an
  arbitrary object. The same finite dualizing data are identified   with exceptional
  pullback by RationalOperations.DualizingIdentification.
- InternalHom uses commonStageDerivedInternalHom on pairs (K,omega), with a
  natural functor isomorphism from the same duality functor. Its universal field
  states bijectivity of the explicit evaluation transpose h maps to
  tensor(id_K,h) followed by B.evaluation K, for every P and K. Naturality of
  evaluation makes these bijections natural; this is exactly internal Hom into
  omega. Evaluation is fixed at every finite field through tensorInclusion by
  the evaluation-stage equation in DualityProperties. The evaluation-naturality
  equation is the full dinaturality equation. No existence assertion for
  internal Hom into unrelated objects is added at the common stage.
- Exceptional.system is the published coefficient-compatible System, whose   rationalLeft
  identifies compact support and whose right operation retains   its etale-origin finite
  construction and integral/rational normalizations.   Its auxiliary small closure is
  AlgebraicClosure (ULift (Padic l)); only its   finite rational stages are used. All
  common-stage categories, arrows,   comparisons and scalar fields remain indexed by the
  original Ω : Type v.
- ExceptionalProperties specifies the pair object formulas;   its inclusion comparisons are
  normalized to identities, commute with the   actual finite scalar comparisons, and
  preserve the actual finite unit and   counit. Thus its adjunction is the descended
  constructible adjunction.
- ExceptionalFormula uses the correct variance:   D_Y.rightOp ⋙ (CoefQbarPullback f).op ⋙
  D_X. The finite comparison is   RationalOperations.ExceptionalIdentification for the same
  X and Y dual data.   The normalized square identifies the displayed global isomorphism
  itself   with those finite comparisons, using the canonical pullbackInclusion.
- The last three clauses of DualityProperties state restriction of   evaluation, delta and
  delta inverse along i : P → K, p : K → P with   i ≫ p = 1_P. Other descended maps are
  natural transformations, so their   corresponding restriction equations follow by
  naturality in each variable.

Dependency declarations used (module, name):

- Sheaf.Paper.FiniteFieldFiber, WeilConjectures.FiniteFieldDatum.
- Mathlib.AlgebraicGeometry.Morphisms.Proper, AlgebraicGeometry.IsSeparated.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType, LocallyOfFiniteType;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact, QuasiCompact.
- Sheaf.Paper.SfRationalizationKaroubi, sfRationalConstructibleCategory,
  sfRationalConstructibleLocalization and sfRationalCoefficientEquiv.
- Sheaf.SixFunctors.RationalVerdier, RationalVerdier.units, tensor, Datum,   Extension and
  ExtensionProperties, and coef_rational_verdier.
- Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients, Stage, transition,   stageSystem,
  inclusion, unitor and associator; the public category is
  generalAlgebraicallyClosedConstructibleCategory.
- Sheaf.Paper.DerivedPullbackTensorHom, commonStageDerivedTensor,
  commonStageDerivedPullback, commonStageDerivedInternalHom,   commonStageHomPairs,
  rationalTensorScalarComparison and   operationStageTransitionIso, including the specified
  object formulas.
- Sheaf.Paper.QcqsCompactSupportRealization, sfQcqsCompactSupportRealization;   the existing
  exceptional System retains its rationalLeft compact-support   identification and imports
  the normalized finite compact-support functor.
- Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients,
  ConstructibleExceptionalCoefficients.FieldStage and System, including its   ring.operation
  and fields.rationalComparison with actual units/counits.
- Sheaf.SixFunctors.RationalOperations, HomIdentification, coefficientUnit,
  ExceptionalIdentification and DualizingIdentification.
- Sheaf.Paper.SfBidualityClass, SfClassDuality and   SfClassEvaluationCompatible, reused as
  generic records rather than assuming   the downstream biduality-class theorem.

The generic SfClassDuality records live in SfBidualityClass, whose theorem cites
this item as a proof dependency. A reverse proof import into that module would
close an import cycle and must be omitted under stages/2-statements.md §3(7).
This delivery uses its generic records, not its downstream theorem.

Edge cases checked: identity finite field inclusions occur in FiniteCoherent and in all
universal scalar clauses. Repeated-field towers occur in composition. The base finite
coefficient field is the explicit Padic.finiteCoefficientBase. The empty scheme, zero
objects and zero arrows are retained; there is no nonemptiness assumption on X. Identity
morphisms and identity retracts are included. General retract equations concern evaluation,
delta and its inverse, not just the functor law D(p)D(i) = 1. Ω may have a universe
different from X; finite fields alone are transported to Type u, and the auxiliary closure
is never substituted for Ω in the asserted common-stage category.

Searches: the previous saved packet records LeanFinder, Loogle and grep searches with no
exact existing theorem. Rechecked with msearch.py NO thm-coef-qbar-verdier: LeanFinder query
"Verdier duality on a common finite coefficient stage algebraic closure with scalar
comparison and biduality" returned generic Ext, derived category bounds and finite-
dimensional rigid-category results, none this theorem. Loogle query "CategoryTheory.Functor,
CategoryTheory.Adjunction" returned the standard adjunction API used here. Mathlib grep
"Qbar.*[Vv]erdier|qbar_verdier" returned zero hits. rg of the source WeilConjectures tree
and lean/Sheaf for thm-coef-qbar-verdier, CoefQbarVerdier and coef_qbar_verdier found only
the biduality-class docstring citation, no existing declaration. The small-closure and
tensor/transition searches found the published coefficient models and canonical comparison
API, reused above. No new DAG notion is introduced.

## Second reading by NO

This is the author's required repair self-check; no independent worker is claimed. The
earlier second reading incorrectly claimed that the contravariant order and finite
comparisons were checked. F1: the old formula was D_X² f* D_Y², which collapses by biduality
to f*, and did not express exceptional inverse image. It is replaced by D_Y.rightOp ⋙
(f*).op ⋙ D_X with the actual finite comparison square. F2: the old SfClassDuality was
unrelated to Dfun. The new statement uses only one Duality.duality.dual throughout, tied to
each RationalVerdier.Datum by literal object formulas, normalized natural comparisons, their
scalar square and the evaluation-compatible biduality equation.

The remaining returned defects are also checked against concrete fields: the finite
comparisons retain unit and composition equations in FiniteCoherent; omega is tied to the
specified exceptional image of the actual unit; evaluation is normalized to finite
evaluation and the explicit universal evaluation transpose; exceptional functors and their adjunction maps are
descended from one specified System, and Y has the same full duality assertion; the scalar
action is fixed by actual finite embeddings; the retract assertions concern the maps
themselves. The vacuous outer forall E and unused _l parameter are removed. Every
declaration now has a source and blueprint docstring, and the theorem docstring contains all
ten DAG proof steps (renumbered by the maintainer's reviewer; see below). The node's natural-language statement and dependency lists are
unchanged.

Validation: the final delivery module compiles cleanly through scompile.py at
both paths (sandbox 35.0 s, library module 37.1 s), without errors or warnings.
The synchronized delivery passed deliver2.py --no-push: temporary commit
9feed10394 passed server preflight and per-file compilation. The node differs
from the shared base only in lean; its theorem signature is copied verbatim,
and all 27 listed declarations are present. The final module contains one
sorry, in the requested theorem, and no diagnostic options.

## Maintainer review note (cc reviewer, 2026-10-18)

FIX, docstrings only: the node's proof has ten steps, while the theorem docstring said
"nine steps" and merged node steps 7 (Hom-group descent) and 8 (adjunction from the
natural bijection). The theorem docstring now carries all ten steps in order, and the
module and declaration docstrings cite the matching step numbers. No declaration,
signature or lean record changed.
