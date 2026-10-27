## Worker report

Item: lem-sf-general-hom-comparison-cocycles. Module:
`Sheaf.Paper.GeneralHomComparisonCocycles`; main declaration:
`WeilConjectures.generalHomComparisonCocycles`. Only the final theorem has a
postponed proof. The ten auxiliary definitions are actual mate constructions,
an evaluation transpose, or explicit predicates spelling out this node's clauses.
There are no new nodes, dependency replacements or statement changes.

Source read: current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md`.
The source has moved from the older `sk-thm-sf-package` path in the DAG source
record. Its general-Hom sentence says that these three comparisons use the same
evaluations as operation reduction; its final sentence restricts coherence to the
stated domains and adds no preservation or biduality assertion. The node's full
seven-step proof is expanded in the theorem docstring.

Hypotheses and coefficient conventions:

- The finite field, its characteristic and algebraic closure are `D : FiniteFieldDatum`.
  `C : D.CoefficientDatum` supplies the prime `C.l`, `Fact C.l.Prime`, `C.different`
  and the algebraic closure `C.Qbar` of the coefficient field. These are the same
  global data as `SixFunctorOperationDatum`, whose module is publicly imported.
- A finite extension of Q_l is `E : Type u`, `Field E`, `Algebra (Padic C.l) E`,
  `FiniteDimensional (Padic C.l) E`. Its existing coefficient ring, valuation ring
  and uniformizer constructions are used; no additional choice of ring is made.
- `X : Scheme.{u}`, `[X.Over (Spec (.of D.k))]`, `IsSeparated`,
  `LocallyOfFiniteType` and `QuasiCompact` on its structure morphism express exactly
  separated finite type over k.
- All finite indices in the interfaces mean exponent n+1. Thus `n : ℕ` covers every
  positive exponent and `h : m ≤ n` includes equality. The finite categories are
  `normalizedDVRDerived`, the completion category is
  `DerivedCategory (scalarReductionSource ...)`, and the ring sheaves are the
  existing `integralCoefficientCommRingSheaf` and `completedIntegralCommRingSheaf`.
- Internal Hom is the recorded `derivedInternalHomOfUniverses`, publicly retained
  by `DerivedInternalHomMixedUniverses`. `coefficientFiniteInternalHom`,
  `coefficientIntegralInternalHom` and `IntegralHom.hom` are the existing wrappers
  for that very bifunctor, not replacement internal Homs.
- The general statements below involve no compact-support functor or compact-support
  input, so no etale-origin witness is required of these Hom-only ambient variables.
  The constructible finite and integral domains are the recorded intrinsic ones;
  rational Hom uses the existing permitted-pair category. Nothing here alters the
  witness/domain conventions of the six-functor datum.

Clause-by-clause rendering:

1. `GeneralHomComparison.finiteLaws` first states the identity-quotient equation
   for both `finiteTorConstructible` inputs. `finiteUnit` is the canonical left
   adjoint mate of `normalizedDVRResUnit`, using the actual quotient adjunction.
   The displayed Hom-map uses its inverse on the contravariant input and its
   forward map on the covariant input. Hence the equation is v_nn = identity
   under the canonical tensor identity, not an equality with ill-typed endpoints.
   The second part reuses `FiniteHomIntrinsicCocycle` from the finite-Hom theorem.
2. `integralLaws` quantifies all ambient integral K,M and assumes exactly that
   their reductions at n are finite-Tor constructible. It asserts
   alpha_H ; c_m = F_nm(c_n) ; v_nm ; H(alpha_K inverse, alpha_M).
   Here `integralAssoc` is the actual left-adjoint composition mate of
   `normalizedDVRResCompletedComp`. This is precisely the displayed c_m cocycle
   with all successive tensor identifications retained. There is no completeness,
   boundedness or site-perfectness assumption on either ambient integral object.
3. `elementaryAgreement` has the finite overlap's two finite-Tor hypotheses and
   the additional site-perfect first-variable hypothesis. The equality is
   definitional in this published interface: both named arrows are the same
   `finiteIntrinsicReductionHom`. Its second conjunct identifies the elementary
   integral transpose `integralMap` with `IntegralHom.comparison` for a jointly
   chosen source presentation a and, for every n, a chosen reduction presentation
   m, with the comparison invertible as in the integral reduction theorem.
   The quantifier order is `∃ a, ∀ n, ∃ m, ∀ K M`; the equality still holds for
   EVERY ambient K,M. The presentations are chosen with the natural closed
   adjunction on every input in the construction underlying `integralHomReduction`.
   Thus its c_n agrees with the fixed `integralMap` used throughout `integralLaws`;
   this does not redefine c_n as an unrelated arbitrary arrow. The opposite tensor
   orders agree by the canonical symmetry and the signed evaluation.
   `scalarAgreement` states `∀ L ι, ∃ a b, ∀ K M hK hM, ...`: the source and target
   presentations underlying `coef_integral_finite_extension` are jointly chosen
   with invertibility of `IntegralFiniteExtension.v` as in the finite-extension
   theorem and agreement with `scalarHomCompleteInputs`. Their equality is on exactly two `sfIntegralConstructible` inputs, with all
   completion units and the inverse contravariant unit retained. Neither equality
   is asserted for all presentations, nor for an arbitrary witness extracted from
   a dependency theorem. The existential equalities pin the actual comparisons
   on all stated inputs without adding a presentation as a hypothesis.
   `fieldTransport` first identifies `rationalHomScalarComparison` with raw
   localization of `integralHomScalarComparison` on its permitted pair category.
   Its `commonStageInternalHomRepresentativeLaws` conjunct uses the published
   all-common-stages formula for the SAME rationalized comparisons. Thus the
   finite, integral, rational and common-stage overlaps are all covered.
4. `evaluationCoherence` uses `CoefficientEvaluationCompatible` (naturality,
   arbitrary tensor-Hom transposes and INTERNAL composition), `FiniteHomEvaluation`
   (the explicit reduced evaluation and its unique transpose), and the spelled-out
   three-factor `tensorReassociation` square. It gives these for finite quotient
   change, integral reduction and ordinary finite-field extension. The completed
   scalar maps are their conjugates through the canonical completeness units,
   as in `scalarAgreement`. No choice of a bare comparison isomorphism is used.
   These square equations paste under category composition, so preserve every
   well-typed finite expression made from the maps named in the node. The remaining
   `fieldTransport` conjuncts assert preservation of arbitrary parallel-arrow
   equations under raw localization, finite scalar transition and common-stage
   inclusion. They apply to the evaluation/transpose/associativity equations above
   and to the cited identity/composition equations. The common-stage representative
   condition ensures these equations concern the prescribed operations.

Dependency declarations read and used (public statement imports):

- `Sheaf.Paper.SixFunctorOperationDatum`: `WeilConjectures.SixFunctorOperationDatum`
  and its finite-field coefficient/domain conventions.
- `Sheaf.Algebra.Homology.DerivedInternalHomMixedUniverses`: the publicly retained
  `CategoryTheory.derivedInternalHomOfUniverses`, also used by `IntegralHom.hom`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `WeilConjectures.scalarReductionDerivedExtension`, its restriction and adjunction.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`:
  `WeilConjectures.integralScalarExtensionOfUniverses` and normalized completion model.
- `Sheaf.Paper.FiniteCoefficientHomChange`:
  `WeilConjectures.finiteCoefficient_derivedHom_change`, `FiniteHomIntrinsicCocycle`,
  `FiniteHomEvaluation`, and its publicly retained canonical finite arrows.
- `Sheaf.Paper.IntegralHomReduction`: `WeilConjectures.integralHomReduction`,
  `IntegralHom.TensorPresentation`, `IntegralHom.ReductionPresentation`,
  `IntegralHom.comparison`. No presentation is selected from mere nonemptiness.
- `Sheaf.SixFunctors.CoefIntegralFiniteExtension`:
  `WeilConjectures.coef_integral_finite_extension`, `IntegralFiniteExtension.v`.
- `Sheaf.Paper.BasicOperationsCoefficientReduction`:
  `WeilConjectures.basicOperationsCoefficientReduction`,
  `commonStageInternalHomRepresentativeLaws`, and the publicly retained elementary
  finite/integral/scalar/rational comparison declarations.

All already stated proof dependencies are imported, including the closed-structure,
monoidal-comparison, site-perfect scalar-Hom, finite-free completed-scalar,
semilinear localization, rationalization and common-stage modules. The composition
node's minimal `lean` record is resolved through `lean_audit.slopmaster2.decls`:
`CategoryTheory.Functor.LaxMonoidal.ihomComparison_comp_app` in
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic` (and its
`ihomComparison_app_eq_curry` normalization). That module is imported for the proof.

Edge cases checked: positive exponent one is n=0; n=m and m=r are included by
reflexive inequalities; zero K or M and the empty scheme introduce no nonzero or
nonempty hypotheses; integral K,M may be unbounded and not complete; only their
specified n-reductions are restricted in clause (2); the scalar extension may be
identity or ramified; all arbitrary common finite coefficient stages are retained.
No finite reduction is formed from a rational object, no site-perfect tensor-dual
formula is asserted for general constructible inputs, and no site universe is
collapsed: the small site retains object universe u+1 and morphism universe u.

Searches for an existing statement:

- `msearch.py leanfinder`, query `Internal Hom coefficient change identity composition
  and evaluation transpose under iterated reduction`: eight categorical closed-Hom
  hits, including `ihom.coev_ev`, `MonoidalClosed.coev_app_comp_pre_app` and
  `compTranspose`; none states this geometric finite/integral/rational package.
- `msearch.py loogle`, query `Functor.map_comp, Adjunction.homEquiv`: zero hits,
  unknown unqualified identifier `Functor.map_comp`. Direct source inspection
  supplied the adjunction and comparison signatures used instead.
- `msearch.py grep`, query `internalHom.*[Cc]oefficient|[Hh]om.*reduction.*cocycle`:
  zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, queries
  `GeneralHom|generalHom|general_hom|comparison.*cocycle|hom.*cocycle` and then
  `CoefficientEvaluationCompatible|integralHomReductionComparison|scalarHomCompleteInputs`:
  found the cited finite and integral components and `SpecifiedHomScalarEvaluation`,
  but no declaration containing the four clauses together. The scalar-only module
  does not include finite quotient identities or the integral-to-finite cocycle.
- Node-id search in `lean/WeilConjectures` and `dag/lean_names_upstream.json`: no match.
  Direct declaration/docstring reads confirmed the reusable maps listed above.

Validation of the original delivery: prescribed server-only `scompile.py` passed
sandbox and library-mode checks, 12.3 and 11.6 seconds, with no errors or non-sorry
warnings. Repair validation is recorded below. The scratch
probes were module-mode files too; none is part of the delivery. No global build,
live source edit, direct Git mutation or extra agent was used.

No STATEMENT-DISPUTED issue or source statement correction was needed.

## Repair of returned delivery 843f62ac9913

The independent maintainer review identified two false universal claims (H3).
Both have been repaired in the retained sandbox rather than re-pushed unchanged:

1. `elementaryAgreement` formerly quantified over every a and m. It now supplies
   one source presentation and a reduction presentation for each exponent, jointly
   with invertibility and equality to `integralMap` for every ambient K,M. This keeps the displayed
   integral cocycle tied to the c_n in the integral-Hom reduction construction.
2. `scalarAgreement` formerly quantified over every a and b. For each extension
   it now supplies jointly chosen source and target presentations with equality
   on the full stated constructible domain. The completion maps are unchanged.

The theorem docstring steps 4 and 5 and clause 3 above explain these choices.
The original error was to infer global adjunction normalization from normalization
only on K-flat representatives. At a non-flat degree-zero K0 = O_E/t, changing the
sign of the adjunction's unit and counit is permitted by those presentation fields;
for odd l it negates a nonzero comparison. This tests and rejects the old universal
claims. The repaired existential claims allow the canonical fully natural
adjunctions, and make no claim about the sign-twisted presentations. They retain
n=0, m=n, arbitrary ambient integral objects, zero objects, empty X, identity and
ramified coefficient extensions. No source/DAG statement correction is needed:
this repairs its Lean rendering, not the mathematical source statement.

The maintainer's advisory about `lem-sfb-integral-hom-comparison-normalization` is
recorded here: its universal-presentation claim has the same sign-twist defect.
This delivery does not use that lemma. The three functorial equation-transport
conjuncts of `fieldTransport` are indeed immediate congruence statements; they
express the source's preservation of already established equations and do not
replace the nontrivial HEq or common-stage representative clauses.

Repair validation: `scompile.py Q55 lem-sf-general-hom-comparison-cocycles`
passed on the final revised module in both sandbox mode (59.4 seconds) and
library mode (9.6 seconds), without errors or non-sorry warnings. The only
postponed proof remains the main theorem. A server-source comparison was attempted
with `scompile.py --source Sheaf.Paper.GeneralHomComparisonCocycles`; it reported
that the module source was unavailable, consistent with this returned module not
being landed. All non-lean node fields match the current shared read clone.
The delivery wrapper performs the final rebase and preflight against current main.

## Second reading by Q55

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
