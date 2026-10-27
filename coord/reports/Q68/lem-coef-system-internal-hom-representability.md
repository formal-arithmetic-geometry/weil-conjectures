## Worker report

The module states `WeilConjectures.SystemInternalHom.systemInternalHomRepresentability`.
Its conclusion is the existence of the canonical presentations and comparison properties
for both X and Y. The theorem alone is postponed by `sorry`; every definition has real
data and every structure spells out its data and equations. No statement correction,
dependency repair, private notion of strict systems, or new axiom is introduced.

The recorded pro-etale evaluation calculus already defines the fiberwise system I as
`coefficientSequenceInternalHom`, and its mapping tower as this internal Hom followed by
exact `coefficientSequenceDerivedRestriction` and total `coefficientTowerSections`.
`fiberComparison` therefore transposes that very system evaluation. This uses the
recorded realization of I; it does not replace I by an arbitrary family of fibers.

Hypothesis and clause correspondence:

- Finite field and its fixed algebraic closure: `D : FiniteFieldDatum`. The prime is
  `l` with `[Fact l.Prime]`; `_hl : l ≠ D.p` is the distinct-characteristic assumption.
  The finite extension is `E` with `Field`, `Algebra ℚ_[l] E`, and `FiniteDimensional`.
  `coefficient` and `quotient` use the recorded Padic integer-ring quotient and actual
  quotient transition, with its canonical ULift. Index n means exponent n+1.
- The k-scheme structures are `X.Over` and `Y.Over`; separation, locally finite type
  and quasi-compactness are on each actual structure map. The same properties on f
  render separated finite type, `f.IsOver` renders k-linearity, and `_c` is its
  actual `Compactification`. The two factors of the conjunction are exactly W=X,Y.
  All system constructions also apply to the compactification's middle scheme.
- Strict etale systems and their ordinary unbounded derived category are the existing
  `Etale.SystemProjection.Modules` and `.Derived` instantiated at `coefficients`.
  Pro-etale systems are the existing `coefficientSequenceModules` and `.Derived`.
  No full subcategory of normalized systems replaces either ambient category.
- `EtData` and `Representability.proetale` are instances of the recorded semilinear
  `Data`. Its `scalar`, `reduction`, and `Normalized` use the scalar-extension
  adjuncts of actual transitions for every n≤m, including equality. `EtNormalized`
  specializes this. `pro_normalization` identifies the same condition with the
  existing `IsNormalizedCoefficientSequence` universal Hom criterion.
- On both sites, `Data.homEvaluation` is the natural isomorphism for normalized first
  argument and arbitrary second argument; `Data.homEvaluation_evaluation` is the
  tensor/evaluation normalization. Thus the first Hom clause has no hypothesis on N.
- On normalized pro-etale M,N, `fiber_iso` states invertibility of the evaluation
  transpose. `fiber_identity` conjugates its actual evaluated map by the recorded
  `system.fiberHom` isomorphism and asserts identity of finite RHom.
- The site-comparison structural ring map is `ComparisonRing.structural` on the
  actual product inclusion `(𝟭 ℕ).prod Scheme.toProEt`; `constants` fixes it on
  sheafification generators. `ComparisonRing.push` is actual module-sheaf
  pushforward. `ComparisonImage` supplies its exact left adjoint and its canonical
  unbounded derived adjunction. These are conclusion presentations, not hypotheses.
- `ComparisonTensor.model` fixes derived tensor comparison on K-flat total complexes;
  `pure` fixes its ordinary adjunct on pure tensors to the tensor of the two units.
  `pullHom` is exactly `coefficientBaseChangeHom`, the transpose of pulled-back
  evaluation. `Representability.transpose` states preservation of every actual tensor-Hom transpose,
  including evaluation as its counit instance, before evaluating any level.
- `EtFinite` uses `finiteTorConstructibleEtale` separately for every positive level.
  Boundedness, constructibility and Tor intervals are inside that per-level predicate.
  `pull_normalized` gives normalization of inverse images; `pull_iso` assumes exactly
  normalization and levelwise bounded constructible finite Tor for both inputs.
- `representingObject` is actual structure-map derived pushforward of etale system
  RHom. `representingEquiv` is the reverse structure adjunction followed by reverse
  tensor-Hom transpose. It is defined for every M,N,P without any finiteness or
  normalization hypotheses. `representing_evaluation` gives the stated forward
  counit/evaluation word, and `representing_naturality` gives contravariant naturality
  in the test P.
- `pointSections` is actual terminal sections at every level, retaining transitions.
  `PointSections` gives its exactness as conclusion data over Spec of the closed
  field; `.derived` is exact termwise localization to D(Tow(Ab)).
- `SectionsComparison.ordinary` compares actual sections with scalar restriction then
  Hom from the completed-ring unit; `sections` fixes it by evaluation at 1. Its
  derived comparison is fixed on whole complexes by the full composed derived-unit
  equation `unit`. `exactThenRightUnit` and `twoRightThenExactUnit` construct these
  unit words generically, so no arbitrary derived natural isomorphism is substituted.
- `mappingComparison` first uses the actual site-comparison adjunction unit at etale
  RHom, then pushes `pullHom`, then uses `SectionsComparison.derived`. Its codomain
  is the recorded `coefficientSequenceGlobalHom` at the two actual inverse images.
  `mapping_iso` states invertibility under the same levelwise hypotheses.
  All maps are formed in unbounded derived categories before coefficient evaluation.

Dependency declarations read and used:

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `def-weil-scheme-morphism-properties`: the recorded convention has no declaration;
  use Mathlib `AlgebraicGeometry.IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`.
- `def-weil-compactifications-refinements`: `WeilConjectures.Compactification.RefinementCategory`, `AlgebraicGeometry.Compactification.Refinement`.
- `lem-pur-coefficient-system-derived-comparison`: `Sheaf.Paper.CoefficientSystemDerivedComparison`, `SheafOfModules.coefficientSystemDerivedComparison`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`.
- `def-weil-derived-tensor`: `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`, `AlgebraicGeometry.ProEtale.derivedTensor`.
- `def-coef-normalized-dvr-tower`: `Sheaf.Paper.NormalizedDVRTower`, `WeilConjectures.NormalizedDVRTower`.
- `lem-coef-derived-system-evaluation-calculus`: `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`, `WeilConjectures.coefficientDerivedSystemEvaluationCalculus`.
- `def-pur-derived-internal-hom`: `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`, `CategoryTheory.ordinaryModuleDerivedInternalHom`.
- `def-weil-pbc-site-comparison-morphism`: `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`, `AlgebraicGeometry.Scheme.proEtaleSiteComparison`.
- `def-weil-finite-torsion-constructibility`: `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`, `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites`, `WeilConjectures.finiteTorConstructibleEtale`.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`, `AlgebraicGeometry.Scheme.smallEtaleTopology`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
- `lem-coef-semilinear-derived-sections`: `Sheaf.Paper.SemilinearDerivedSections`, `WeilConjectures.SemilinearSections.semilinearDerivedSections`.
- `def-pur-etale-system-projection-data`: `Sheaf.Paper.EtaleSystemProjectionData`, `AlgebraicGeometry.Etale.SystemProjection.Theory`.

The extra landed dependency `def-pur-etale-system-projection-data` is added to
stmt_deps because its actual etale system categories, evaluation, and normalized
structure-morphism image presentations are used, rather than copied.

The proof imports also include the recorded closed symmetric monoidal theorem,
ringed pullback-Hom evaluation comparison, finite constructible Hom comparison,
finite constructible Hom closure, site comparison, abelian-sheaf/Galois equivalence,
etale sections/invariants comparison, exact-functor localization, derived pushforward
composition, coefficient sequence global-sections evaluation, and the Mathlib
bounded-below injective representative / K-injective facts. The theorem docstring
retains all six natural-language proof steps and the separate-level boundedness argument.

Edge cases checked before finalizing the statement:

- n=0 means A_1, so the zero quotient A_0 is never inadvertently included.
- m=n and identity coefficient maps occur in the full normalization criterion.
- Zero M or N, the empty scheme, and W=Spec k are allowed; no nonemptiness or
  positive-rank hypothesis appears. Hom transposition and unit words retain their
  ordinary values in these cases.
- Both M,N may be unbounded for representability; P ranges over the full ordinary
  unbounded derived category at the point. The finite comparison uses a separate
  interval at each n and imposes no common cohomological or Tor interval.
- The pro-etale site's object universe is u+1 and its morphism universe u. It is
  retained; the coefficient ULift supplies the existing u+1 coefficient convention.
  Fixed smallness instances are Mathlib's `essentiallySmallSelf`, not extra size
  hypotheses or an equality of site universes.

Searches performed:

- msearch leanfinder: "Internal Hom of normalized strict derived coefficient systems
  evaluated at a level and punctual representation of mapping towers". Eight hits
  about generic Hom-complex evaluation / Dold-Kan normalized complexes; no match.
- msearch loogle: "ihom, Adjunction.homEquiv". No match (unqualified ihom unknown).
- msearch loogle: "CategoryTheory.Adjunction.homEquiv". Twelve generic adjunction
  hits, including `homEquiv`, its counit formula and representability specializations.
  These justify the construction of the Hom bijection, but not this whole theorem.
- msearch grep: "internalHom|internal_hom|representab" in CategoryTheory/Monoidal.
  Generic closed-category and representability declarations; no varying-ring theorem.
- rg in WeilConjectures and Sheaf for the node id, systemInternalHom, mappingSystem,
  internalHomRepresent and punctual. Existing results concern finite-coefficient or
  Weil/condensed Hom comparisons and unrelated punctual weights. The exact declaration
  is absent. Targeted final rg for `systemInternalHomRepresentability` and the node id
  in the published source found no existing implementation of this item.
- Read `EtaleSystemProjectionData`, `SemilinearDerivedSections`,
  `CoefDerivedSystemEvaluationCalculus`, and all dependency declaration signatures and
  docstrings. The relevant sequence-site and mapping-system constructions already
  exist, so no additional independent definition node is necessary.

The latest blueprint six-functor section and finite-exceptional proof were read.
The node explicitly retains the ordinary-system refinement of the older integral
exceptional-adjoint proof paragraph. Its source allocation and six retained proof
steps are unchanged. No STATEMENT-DISPUTED issue was found.

## New nodes

None. The declarations in this module specify the canonical maps and presentations
belonging to this item's own internal-Hom / punctual-representation statement, as
permitted by brief-stage2 §1(A) for owning-module helpers.

## Validation

All compilation uses the prescribed scompile.py server wrapper. Temporary prefix and
profiling files are scratch diagnostics outside lean/ and are not delivery modules.
The final full-file compile, delivery preflight and push results are recorded below
once completed.

The final full module compiled cleanly through scompile.py against current server sources
in 45.3 seconds (60-second limit, nice 19, two threads). All scratch profiling and
#check commands are absent from the delivered module. The single theorem uses `sorry`,
as required by stage 2. The ordinary and derived comparison definitions have no `sorry`.

The first deliver2.py dry run timed out during its repeated compile. The three
derived comparison maps now have explicit source and target signatures, and their
termwise source complex is named `composedSectionsComplex`. This preserves every map
and equation while avoiding repeated kernel unfolding of coefficient presentations.
The dry run will be repeated on this final version.

## Second reading by Q68

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
