## Worker report

The module `Sheaf.SixFunctors.RamifiedScalarExceptionalLimit` states
`WeilConjectures.RamifiedScalarExceptionalLimit.ramifiedScalarExceptionalLimit`.
Its sole theorem has proof `sorry`. `Realization` is a structure collecting the
node's conclusion, with actual functors, natural isomorphisms, and equations;
it constructs no data from a bare existence assertion.

Source read: the item's complete statement and six proof steps; the current
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/`
`det-prop-scalar-six-exceptional.proof.md` (definition/formal-properties paragraph)
and `det-prop-scalar-six-compact-support.proof.md` (ordered proper/open comparison,
independence and composition). The item's original supporting statement remains
unchanged. Its old source path is historical metadata, not a second blueprint used
as the current source. There is no repair-note entry for this item.

### Hypotheses and objects

* The global finite-field datum is `D : FiniteFieldDatum.{u}`. Its fields supply
  the finite base field and chosen algebraic closure, prime p, positive exponent,
  and q=p^a. `l`, `[Fact l.Prime]`, and `hl : l ≠ D.p` render the prime conditions.
* E and L are fields, finite-dimensional algebras over `ℚ_[l]`.
  `i : E →ₐ[ℚ_[l]] L` is the inclusion (field algebra homomorphisms are injective).
  The valuation rings, chosen uniformizers and quotients remain the published
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and
  `coefficientExtensionRing`. No new coefficient definition is made.
* `e`, `he : PurCompactSupport.Ramification l E L i e`, and `hp : 1 ≤ e`
  express pi S=v^e S and positivity. `retainedIndex e n + 1 = e*(n+1)` is the
  published positive-level convention. Index 0 denotes exponent 1, never exponent 0.
* `X Y : Scheme.{u}`, their Over instances, locally-finite-type and quasi-compact
  structure morphisms, and separated structure morphisms give exactly the
  separated finite-type k-schemes. `f.IsOver`, `IsSeparated f`,
  `LocallyOfFiniteType f`, and `QuasiCompact f` give the specified k-morphism.
  `c : Compactification f` supplies the actual open/proper factorization.
* Sites and completed sheaves are those already used by the calculus:
  `Scheme.ProEt.topology`, `completedIntegralCoefficientSheafUnrestricted`,
  and `scalarReductionSource`. They retain the site's object/morphism sizes;
  no equality of the two site universes is imposed.
* `Context` supplies the simultaneous calculi, their normalized finite-Tor system
  domains, and the canonical proper/open support functors and finite adjunctions.
  `FiniteAdjunctionDiagram.domain` is normalization plus ctf separately at every
  level, with no uniform interval hypothesis. Its scalar extension `a.TX/a.TY`
  is the existing exact-localized sequence-site scalar extension, not a newly
  specified family of maps.
* The integral categories are `sfIntegralConstructibleCategory`; `a.TIX/a.TIY`
  are exactly restrictions of `integralScalarExtensionOfUniverses`.
  `a.GR/a.GS` are right adjoints to the fixed recorded integral support functors.
  Their comparison with the system exceptional functors is required by
  `adjunctionR/adjunctionS`, including unit and counit identities. Thus there is
  no extra assumption of existence of any of the adjoints or preservation proofs:
  the theorem concludes existence of the entire Context and Realization.

### Every conclusion clause

| Node clause | Lean rendering |
| --- | --- |
| First displayed natural isomorphism | `Realization.source` |
| Second displayed natural isomorphism | `Realization.target` |
| Third displayed natural isomorphism | `Realization.scalarY` |
| Fourth displayed natural isomorphism | `Realization.supportSource` |
| Fifth displayed natural isomorphism | `Realization.supportTarget` |
| Actual reduction/limit units | `completeRX`, `completeRY`, `completeSX`, `completeSY`; the units are those of the recorded calculus |
| Actual reduction/limit counits | `scalarReductionX/Y_normalization` uses `integralComparisonScalarCounit`; its definition is the scalar realization followed by the actual reduction/limit counit |
| Specified integral/system adjunction maps | `adjunctionR`, `adjunctionS` are the published `SemilinearSections.AdjunctionEvaluation`, including both unit and counit equations |
| First and second isomorphisms are the specified ones | `source_normalization`, `target_normalization`, using the preceding comparisons and actual inverse completion units |
| Third isomorphism is the specified one | `scalarY_normalization`, using the cochain-normalized existing scalar model |
| Fourth and fifth isomorphisms are the specified ones | `supportSource_normalization`, `supportTarget_normalization`, via the actual system adjunction and published support realization |
| Compact support realizes the specified projections | `a.supportR/a.supportS.projections`, supplemented by `supportR/S_normalization` against the completion unit |
| N has a uniform finite Tor interval | `uniformReduction`, with one ordered integer interval preceding `∀ n` |
| E_R N has a uniform finite Tor interval | `uniformExceptional`, again one interval preceding `∀ n` |
| T_Y M and T_X G_R M are in C_S | `a.integralY`, `a.integralX`, used by `a.TIY/a.TIX`; all displayed composites are typed functors on those full categories |
| Retained scalar levels are tensor A_n to B_n | `finiteX/Y`, `scalarEvaluationX/Y`, with `finiteTensor` at `retainedIndex e n` |
| Composite quotient transitions | `scalarTransitionX/Y`, using the actual quotient tensor square and retained monotone index |
| Full/retained limit identification | `cofinalX`, `cofinalY` and their normalization fields |
| Preserve the total-limit projections | `IsCofinalRoosMap` fixes BOTH signed Roos coordinates, by selection and block sum, not merely an unspecified cofinal iso |
| Preserve scalar-extension adjoints | reduction counits in `scalarReductionX/Y_normalization` together with the calculus's `counit_projection`, and the unit/counit equations of `adjunctionR/S` |
| Limit of alpha^sys is exactly alpha at G_R M | `comparison`, an equation using the actual `a.alpha` and `a.integralAlphaComponent` |
| Fixed compactification and finite-free normalization | `Context.alpha` is the proper projection followed by open tensor comparison in its fixed support presentation; `integralAlphaComponent` conjugates that same completed proper/open map by `IntegralFiniteExtension.completion` (exactly `asIso completedScalarComparison`, chi) and the fixed support realization |
| Natural in M, on morphisms | all five displays are `≅` between composed functors; each component equation quantifies over the actual full-subcategory input, not chosen representatives |

The published Context uses the full upper uniformizer tower. This is a presentation
of the node's retained tower: `retainedLimit` restricts the strict completed-coefficient
tower BEFORE taking the total right derived limit. `scalarEvaluationX/Y` and
`scalarTransitionX/Y` explicitly identify its retained values and transitions with
A_(n+1) to S/v^(e(n+1)), and the signed Roos equations identify the retained limit
with the full one. No limit of a diagram in the triangulated category is substituted
for a total derived limit of strict systems.

### Dependency declarations used

The direct statement imports are the landed Context owner, the recorded scalar
transpose module, and the recorded cartesian-section mate module. Their transitive
public interfaces provide the following recorded declarations, read in source:

* `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
* `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
* `def-weil-scheme-morphism-properties`: convention only; the named component definitions are used.
* `def-weil-integral-rational-qbar-compact-support`: `Sheaf.Paper.QcqsCompactSupportRealization`, `WeilConjectures.sfQcqsCompactSupportRealization`.
* `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
* `def-weil-size-convention`: convention only; the named component definitions are used.
* `lem-coef-derived-system-evaluation-calculus`: `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`, `WeilConjectures.coefficientDerivedSystemEvaluationCalculus`.
* `def-coef-normalized-dvr-tower`: `Sheaf.Paper.NormalizedDVRTower`, `WeilConjectures.NormalizedDVRTower`.
* `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites`, `WeilConjectures.finiteTorConstructibleEtale`.
* `def-weil-finite-torsion-constructibility`: `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`, `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
* `lem-coef-finite-adjunction-diagram-realization`: `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization`, `WeilConjectures.FiniteAdjunctionDiagram.finiteAdjunctionDiagramRealization`.
* `lem-coef-cartesian-section-adjoint-mates`: `Sheaf.Paper.CartesianSectionAdjointMates`, `WeilConjectures.CartesianSectionAdjoint.cartesianSectionAdjointMates`.
* `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, `WeilConjectures.integralConstantToCompletionOfUniverses`.
* `def-weil-derived-complete-integral-detailed`: `Sheaf.Paper.SfIntegralConstructible`, `WeilConjectures.sfIntegralConstructible`.
* `def-weil-integral-scalar-extension`: `Sheaf.Paper.IntegralScalarExtensionUniverses`, `WeilConjectures.integralScalarExtensionOfUniverses`.
* `lem-weil-finite-free-completed-scalar-comparison`: `Sheaf.Paper.FiniteFreeCompletedScalarComparison`, `WeilConjectures.finiteFreeCompletedScalarComparison`.
* `prop-coef-integral-exceptional-adjoint`: `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients`, `AlgebraicGeometry.Etale.boundedConstructibleIntegral_rightDerivedUpperShriek`.
* `lem-coef-ramified-scalar-system-transpose`: `Sheaf.Paper.RamifiedScalarSystemTranspose`, `WeilConjectures.RamifiedScalarSystemTranspose.ramifiedScalarSystemTranspose`.
* `lem-pur-compact-support-integral-coefficient-comparison`: `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`, `WeilConjectures.PurCompactSupport.integralCoefficientComparison`.
* `def-coef-finite-scalar-mate-data`: `Sheaf.SixFunctors.FiniteScalarMateData`, `WeilConjectures.FiniteScalarMate.Context`.

The upstream integral-exceptional attachment points at an older module location;
the current source explicitly redirects those declarations to IntegralExceptionalAdjoint
and LocalizationIntegral. I read the live source with `scompile.py --source` and
read the actual preservation signature in LocalizationIntegral. For this statement
we use the existing pro-etale Context's right adjoints to the fixed support functors,
with the explicit adjunction-evaluation normalization, so no arbitrary étale map
is silently treated as a pro-etale completed-coefficient map.

The additional `stmt_deps` entry is only the already landed
`def-coef-finite-scalar-mate-data`, whose Context defines all of the interfaces
just listed. This is the authorized addition of a landed definition owner.
No new node and no dependency module are introduced. Proof imports retain the
recorded residue-Tor, normalized effectivity, scalar Tor bounds, K-flat change
of rings, integral support constructibility, scalar constructibility, and arithmetic
restriction modules; the remaining proof dependencies are publicly imported by
statement dependencies.

### Edge cases

Checked before writing: M=0 admits any ordered interval, so no nonzero condition
appears. Empty X or Y is allowed (no positive dimension or nonempty scheme
binder). e=1 retains every positive level; identity coefficient extensions and
identity f are included. Equal quotient indices use the recorded identity
quotient maps. All positive n occur as n+1; intermediate S-exponents not divisible
by e occur in the Context's full upper tower and in its constructibility witnesses.
Uniform intervals are conclusions for integral reductions and exceptional
reductions only, not imposed on every normalized system. Scheme/site sizes and
ULift coefficient sizes follow the recorded interfaces.

### Searches actually run

* `msearch.py ... leanfinder`: “Cofinal ramified coefficient towers realize completed
  scalar extension of integral exceptional inverse images and compact support”.
  Eight results on adic completion algebra, ramification, and strict-mono extension;
  none states this derived sheaf/system comparison.
* `msearch.py ... loogle`: `CategoryTheory.Functor.Initial, CategoryTheory.Limits.limit`.
  Four hits: Initial.limitIso, limit_pre_isIso, limitIso_inv, limitIso_hom. Ordinary
  categorical limits do not supply total derived strict-system realization.
* `msearch.py ... grep`: `cofinal|derived.*limit` in RingTheory/AdicCompletion.
  Zero matches.
* `msearch.py ... leansearch`: “Derived inverse limits of ramified normalized
  coefficient systems realize completed scalar extension and exceptional inverse image”.
  Eight hits, primarily InverseSystem.limit and its natural equivalences, plus
  adic completion and direct-limit lemmas; none states this result.
* `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `ramifiedScalar.*[Ll]imit|ramified-scalar-exceptional-limit|boundedConstructibleIntegral_rightDerivedUpperShriek`:
  no declaration for this node; the upstream integral preservation theorem found.
  Further source searches found the landed `FiniteScalarMateData.Context` and
  `FiniteScalarMateRealization.Realization`. The latter is the downstream mate
  theorem, with a different conclusion, and is NOT imported or used circularly.
  The shared definition Context is reused; this module packages this node's five
  realizations and additional uniform-interval assertions.

No statement correction and no STATEMENT-DISPUTED finding.

## Second reading by O4

A separate pass of this sole worker's reading checked the node against the file;
no independent agent was started, as the dispatcher's brief forbids that. The
maintainer's independent review remains the independent review of this delivery.

The five iso types were checked in the exact order of the displays. In particular,
`supportSource` ends at F_S T_X G_R, whereas `supportTarget` ends at T_Y F_R G_R;
`comparison` has precisely the corresponding direction. The initial draft used
only the full-tower presentation without spelling out retained scalar evaluations;
the final version adds scalarEvaluationX/Y and both quotient-transition equations.
The cofinal condition fixes the shifted Roos coordinate as well as the ordinary
projections. Scalar and support normalizations use the actual adjunctions, not
unconstrained level isomorphisms. The structure is supplied in the conclusion;
none of the preservation facts or comparisons is an added hypothesis.

Every binder is explicit, both automatic-implicit options are false, all Lean
lines are at most 100 characters, and the sole theorem is sorry-only. The module
compiled with scompile.py in both sandbox and library-name mode, clean apart
from the expected sorry warning. The revised retained-scalar version compiled
again cleanly. Dry-run and delivery results are recorded below when available.

Validation: `deliver2.py O4 lem-coef-ramified-scalar-exceptional-limit --no-push`
printed `OK (dry run): commit b3914a25a02 passes the preflight and compiles; nothing pushed`.
