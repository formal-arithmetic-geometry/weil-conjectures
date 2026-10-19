## Worker report

The module `Sheaf.Paper.AdicSmoothBaseChange` states
`WeilConjectures.adicSmoothBaseChange`, with exactly one `sorry`, and defines the
coefficient-presentation helper `WeilConjectures.sbcAdicFiniteCohomology` by actual
restriction of scalars applied to derived cohomology. No proof is supplied and no
other DAG node is stated. The item statement and dependency lists are unchanged.

Source read: the complete item record and its eight proof steps; blueprint
`sec-smooth-base-change/sk-rem-rest/sbc-thm-adic-smooth-base-change.md`, order 1443.
The DAG has already corrected the blueprint's S landing to X and supplied the
finite-dimensional-domain hypotheses. This delivery follows that corrected record.

Hypotheses and objects, clause by clause:

- Prime: `(l : ℕ) [Fact l.Prime]`.
- Finite extension: `(E : Type u) [Field E] [Algebra ℚ_[l] E]` and
  `[FiniteDimensional ℚ_[l] E]`.
- The fixed ring of integers and chosen uniformizer are precisely the dependency's
  `Padic.coefficientExtensionIntegers l E` and
  `Padic.coefficientExtensionUniformizer l E`. The canonical completed-operation
  interface uses their published harmless size lift `PbcIntegralRing l E` and
  `pbcUniformizer l E`, through `pbcIntegralDatum l E`. This is the existing
  specialization, not a new coefficient datum. Its ideal is the singleton span of
  that uniformizer. No ring, ideal, or generator is supplied arbitrarily.
- The datum includes Noetherianity, finite generation, torsion residue coefficients,
  finiteness of each quotient and its perfectness over the integral ring. Thus no
  stronger coefficient predicate is assumed. `ProEtale.PbcQuotient ... n` is the
  actual quotient by exponent `n+1`, starting at `n = 0`.
- The four schemes and arrows are the explicit binders `X S T Y`, `f g h e`.
  `sq : ChosenCartesianSquare h e f g` includes commutativity and the chosen
  pullback identification respecting both projections.
- The four `[IsNoetherian ...]` instances match all four noetherian hypotheses.
  `[Smooth f] [QuasiCompact g] [QuasiSeparated g]` match exactly the specified
  morphism properties. No properness, separatedness, or finiteness of f is added.
- `_hl : IsUnit (l : Γ(S, ⊤))` says l is invertible on S.
  `_horder` says for every n the cardinality of that finite quotient is an
  invertible global section at S, X, T, and Y, exactly the coefficient-order
  assumption in the item. Finiteness and perfectness already belong to the datum.
- `_hT` is finite topological Krull dimension of T, expressed by a natural-number
  upper bound. X's finite dimension occurs only in the conditional conclusion.
- `K : PbcIntegralConstructible l E T` is the published
  `PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)`: its membership is
  intrinsic completeness, uniform bounded constructible canonical reductions,
  and compatible bounded-below etale origins, with all ambient morphisms retained.
  This uses the original specialization reexported by the recorded
  `IntegralUniformCoefficient` module; that module's additional larger-coefficient
  convenience specialization is unnecessary for the published exchange interface.
- `sbcReduction l E T n` is exactly derived scalar extension along the completed
  coefficient projection, hence K tensor^L (A_n)_T with its quotient action.
- `_horigin` quantifies over EVERY n and asks for a bounded constructible etale
  object `L` with an isomorphism from its comparison inverse image, then its
  canonical associated-module realization, to this actual reduction of K.
  It imposes neither chosen origin data nor extra compatibility on these witnesses.

Conclusions, clause by clause:

- The first conjunct is `IsIso (sbcExchangeApp l E sq ... K)`, in
  `PbcComplete l E X`. Its input is the existing full constructible-to-complete
  inclusion. `sbcExchangeApp` is the actual completed unit/theta/counit mate of
  the recorded dependency, never a freely chosen morphism or isomorphism.
- In that map, `sbcPull f` after `sbcPush g` is the left endpoint, and `sbcPush h`
  after `sbcPull e` the right endpoint. Completed push is ordinary derived direct
  image restricted to complete objects; completed pull uses the strict canonical
  reduction tower and derived inverse limit from the dependencies.
- The second conjunct assumes X finite dimensional and `∃ a b : ℤ, a ≤ b` with
  `∀ n : ℕ, ∀ i : ℤ`. Its four conjuncts concern, respectively, finite
  `Rg_* K_n` on S, `Lf* Rg_* K_n` on X, `Le* K_n` on Y, and
  `Rh_* Le* K_n` on X, in exactly that order.
- Every output uses `IsConstructibleProEtaleCoefficientModuleSheaf` on its
  i-th cohomology. `sbcAdicFiniteCohomology` changes presentation along
  `pbcLevelConstantComparison.hom`, the canonical constant-to-continuous-function
  coefficient isomorphism, so the dependency predicate applies to this very
  cohomology sheaf with its actual quotient action. It does not replace intrinsic
  constructibility by etale origin or require a common stratification.
- For each of the same four outputs, `(i < a ∨ b < i) → IsZero ...` expresses
  precisely vanishing outside the shared closed interval, with no bound on n.
- The conclusion produces `hB` and `hD`, membership proofs for the ACTUAL ambient
  left and right endpoint objects in `PbcIsBoundedConstructibleComplete` on X.
  It then asserts `IsIso` of `ObjectProperty.homMk` of the same exchange morphism,
  between these objects equipped with those proofs. This explicitly states
  invertibility in the full subcategory, not merely existence of unrelated
  constructible objects isomorphic to the endpoints.

Dependency declarations used (the modules are imported):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionRing`, and `finite_coefficientExtensionRing`.
- `Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso`:
  `AlgebraicGeometry.ChosenCartesianSquare` and its recorded inverse-image comparison.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`;
  the scheme conventions use Mathlib's `Scheme`, `IsNoetherian`, `QuasiCompact`,
  `QuasiSeparated`, global sections, and `topologicalKrullDim`.
- `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficientDatum`, finite quotient,
  completed ring, canonical projection and reduction tower interfaces.
- `Sheaf.Paper.IntrinsicCompletionCompleted`:
  `IsCompletedIntrinsicallyDerivedComplete`, used by the published full categories.
- `Sheaf.Paper.CompletedPullback`: `AdicCoefficientDatum.completedPull` and the
  strict-tower normalization interface, reexported with the completed operations.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`: reexports ordinary
  ringed-site operations; `sbcFinitePull`/`sbcFinitePush` use those ringed operations
  on the canonical finite coefficient sheaves. The small-coefficient convenience
  `sfIntrinsicDerivedPullback` is not substituted for those functors.
- `Sheaf.Paper.SbcCompletedOperations`: `PbcIntegralConstructible`, `PbcComplete`,
  `pbcConstructibleInclusion`, `sbcReduction`, `sbcFinitePull`, `sbcFinitePush`,
  `sbcPull`, `sbcPush`, `sbcExchangeApp`, and its recorded finite-mate compatibility.
- `Sheaf.Paper.IntegralUniformCoefficient`: reexports
  `PbcIsBoundedConstructibleComplete`, `PbcBoundedConstructibleComplete`,
  `pbcIntegralDatum`, and the original specialization used by completed operations.
- `Sheaf.Paper.RefinementCoefficientRealization`: reexports the canonical finite
  coefficient realization; `pbcDerivedFunctionRealization` supplies its exact
  constant/function coefficient presentation, and `ProEtale.comparisonUpperStar`
  supplies the etale comparison inverse image.
- `Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf`:
  `IsConstructibleProEtaleCoefficientModuleSheaf`, applied after the canonical
  `pbcLevelConstantComparison` restriction.

All recorded proof-dependency modules with Lean records are imported without
`public`, except those already public statement imports. The finite pro-etale
smooth theorem has no Lean record yet and its module is therefore omitted under
stage 2 rule 7; its use remains explicit in the proof docstring. This does not
prevent stating the present theorem. The proof docstring follows all eight steps,
including quotient-linearity, construction of compatible etale witnesses, their
cocycle, and fullness in the final step.

Edge cases checked: n=0 means exponent 1, never quotient by the zeroth ideal power;
all positive levels are included. Zero K and zero finite outputs satisfy the
vanishing predicates. a=b is allowed and there is no bound on a or b. Empty schemes
are allowed: the constructibility predicate permits a positive number of empty
strata, and no geometric point or nonempty scheme is required. No properness-based
constructibility preservation is presumed. The small pro-etale site's object
universe u+1 and morphism universe u remain distinct; the E : Type u specialization
and its ULift are the exact published completed-operation convention.

Searches actually run:

- `msearch.py`, leanfinder, “Smooth base change for derived adically complete pro
  etale sheaves with finite coefficient etale origins”: 8 hits, all ring-theoretic
  etaleness/smoothness and base-change properties, no completed exchange theorem.
- `msearch.py`, loogle, `AlgebraicGeometry.Smooth, CategoryTheory.IsIso`: 1 hit,
  `Scheme.Hom.instIsIsoNormalizationPullbackOfSmooth`, about normalization.
- `msearch.py`, grep, `smooth.*baseChange|completed.*exchange|adic.*base.change`:
  21 hits, concerning smooth ring maps and their base-change stability, no match.
- `rg` over upstream WeilConjectures and project Sheaf for the item id and
  adic/smooth names: the rational-coefficient successor cites this theorem in its
  proof, but no declaration states this integral theorem.
- `rg` over `dag/lean_names_upstream.json`, upstream WeilConjectures, project Sheaf
  and Mathlib for `sbcAdicFiniteCohomology|adicSmoothBaseChange`: no existing names.

No new nodes, dependency repairs, statement correction, or unresolved statement
faults. Compilation uses only the prescribed scompile.py wrapper; no global build
or direct Git operation was performed. The final `deliver2.py N5
sbc-thm-adic-smooth-base-change --no-push` printed OK: the module compiles without
warnings and passes preflight except for the independent second reading, which
is intentionally reserved for the next worker. Nothing was pushed. A sandbox
check also confirmed that only the node's `lean` field changes, its recorded
signature is exact, every Lean line has at most 100 characters, and the only
postponed proof is `adicSmoothBaseChange`.

## Second reading by N5

Independent reading on 2026-10-16. I read the node's complete statement and eight
proof steps before comparing the module. I opened the blueprint source at order
1443, Stacks `etale-cohomology.tex`, `theorem-smooth-base-change` (0EYU), and
`proetale.tex`, `lemma-naive-completion` (099M),
`lemma-pushforward-Noetherian-case` (099N),
`lemma-compare-constructible-derived` (09AL), and `definition-Dbc` (09C1), including
the surrounding section hypotheses. The completion section assumes a Noetherian
coefficient ring and an ideal; the specialized datum supplies these. The smooth
theorem assumes smooth f, qcqs g, and torsion orders invertible on S. The Lean
retains all additional hypotheses explicitly required by this node. Stacks 09C1
is a comparison source, not a replacement for the project's three-clause category.
The original blueprint's final S is already corrected to X in the base DAG node;
the four arrows force X. No statement correction is made in this delivery, and
there is no `statement_change` in the node copy.

The following is my independent inventory of the node, matched to the Lean.
Every row has verdict **match**.

| Node object, hypothesis, or conclusion | Lean rendering and check |
| --- | --- |
| Prime ell | Section variable `l : ℕ`, `[Fact l.Prime]`; these are parameters of the theorem. |
| Finite extension E/Q_ell | `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`. |
| Its integers A and fixed uniformizer, I=(varpi) | `pbcIntegralDatum l E` has actual ideal `Ideal.span {pbcUniformizer l E}` in the size lift of `Padic.coefficientExtensionIntegers l E`; the uniformizer is the lift of the recorded choice. |
| Positive quotient A_n=A/I^(n+1) | `ProEtale.PbcQuotient (pbcIntegralDatum l E) n` is definitionally that quotient, with n ranging over all naturals. |
| Every quotient finite and perfect over A | `pbcIntegralDatum` supplies `quotientFinite` and `quotientPerfect`, as proofs about these actual quotients. No extra coefficient instance is assumed by the theorem. |
| Completed coefficient sheaf and ambient derived category at each W | `pbcAdicCompletion W ...` is the actual inverse limit of `pbcAdicRings W ...`; `PbcCompletedDerived` is the derived category of its module sheaves. |
| Four schemes, arrows, and cartesian square | `{X S T Y : Scheme.{u}}`, `{f : X ⟶ S}`, `{g : T ⟶ S}`, `{h : Y ⟶ X}`, `{e : Y ⟶ T}`, `sq : ChosenCartesianSquare h e f g`. Its pullback isomorphism respects both projections and includes commutativity. |
| All four schemes noetherian | Four instances `[IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]`. |
| f smooth, g qcqs | `[Smooth f] [QuasiCompact g] [QuasiSeparated g]`; no further morphism property is imposed. |
| ell invertible on S | `_hl : IsUnit (l : Γ(S, ⊤))`; a global inverse is equivalent to invertibility on the scheme. |
| Every quotient order invertible at every corner | `_horder : ∀ n : ℕ, ...` has four `IsUnit (Nat.card ... : Γ(W, ⊤))` conjuncts for S, X, T, Y. |
| T finite dimensional | `_hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞)`. |
| K in the specified integral constructible complete category | `K : PbcIntegralConstructible l E T`, an alias of `PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)`, retaining all ambient morphisms. |
| Canonical reduction K_n | `(sbcReduction l E T n).obj K.obj`; this is `pbcCompletedReduction`, derived extension along the actual completed limit projection. |
| Every K_n has a bounded constructible etale origin | `_horigin : ∀ n, ∃ L : Etale.BoundedConstructibleDerivedCategory ... T, Nonempty (... ≅ (sbcReduction ...).obj K.obj)`; the left side is the actual derived comparison inverse image followed by canonical coefficient realization. No compatibility or chosen witness is added to this assumption. |
| Completed pullback and restricted ordinary direct image | `sbcPull` uses strict reduction, tower pullback, and derived inverse limit; `sbcPush` restricts `sbcAmbientPush`, the ordinary derived module direct image. |
| Canonical completed exchange is an isomorphism in D_comp(X,A) | First conjunct `IsIso (sbcExchangeApp l E sq ((pbcConstructibleInclusion ...).obj K))`. I opened its definition: unit for h, theta on Rg K, then the e-pullback of g's counit, all pushed along h. Its endpoints are exactly `sbcPull f (sbcPush g K)` and `sbcPush h (sbcPull e K)` over X. |
| Conditional X finite dimension | The implication starts with `∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞)`; it does not assume a dimension bound on S or Y. |
| One interval a<=b, for every n and degree i | The next implication assumes `∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ, ∀ i : ℤ, ...`; the same a,b bind all four outputs at all levels. |
| Rg_n,* K_n constructible, vanishing outside the interval | First pair applies `IsConstructibleProEtaleCoefficientModuleSheaf S` and `(i < a ∨ b < i) → IsZero` to the cohomology of `sbcFinitePush g n (sbcReduction T n K)`. |
| Lf_n^* Rg_n,* K_n with the same properties | Second pair uses `sbcFinitePull f n` of that direct image, on X, in the same n,i binders. |
| Le_n^* K_n with the same properties | Third pair uses `sbcFinitePull e n` of K_n, on Y. |
| Rh_n,* Le_n^* K_n with the same properties | Fourth pair uses `sbcFinitePush h n` of that e-pullback, on X. |
| Both actual completed endpoints belong to Dbc(X,A) | Existential `hB` and `hD` prove `PbcIsBoundedConstructibleComplete` of the underlying objects of exactly those two endpoints. |
| The same alpha is an isomorphism in that full subcategory | Final `IsIso (ObjectProperty.homMk ... (sbcExchangeApp ...).hom)` uses those membership proofs and the original exchange's underlying morphism. It does not assert isomorphism of unrelated representatives. |

Dependency-interface checks: I opened all recorded statement-dependency modules
and their relevant underlying declarations. In particular:

- `CoefficientExtensionFinite` reexports the actual integer ring, uniformizer,
  ideal powers and quotients from `CoefficientExtension`; its finiteness theorem
  applies at every positive exponent. `BoundedConstructibleComplete` specializes
  these with ULift, and its datum fills only proof fields from
  `pbcCoefficientDatumProperties`.
- `BaseChangeInverseImageIso` reexports `ChosenCartesianSquare`; I read the
  structure in `ChosenCartesianSquare.lean`. Mathlib `Smooth`, `IsNoetherian`,
  `QuasiCompact`, and `QuasiSeparated` give the recorded notions. The scheme
  conventions node is explicitly a pointer bundle, with no missing declaration.
- `AdicCoefficientDatum` and `BoundedConstructibleTower` build finite coefficient
  sheaves by sheafifying continuous functions on connected components; their
  completed ring is their inverse limit. `PbcIsIntrinsicallyComplete` transports
  the recorded intrinsic predicate through the normalized completed comparison.
  Its generator tuple and complex representative are existential proof witnesses.
- `CompletedPullback.completedPull` and `SbcCompletedOperations.sbcPull` both
  retain reduction/tower/derived-limit operations. I read the latter's coefficient
  isomorphism, ordinary comparison normalization, complete-category lift,
  `sbcFinitePull`, `sbcFinitePush`, `sbcReduction`, theta, and exchange definitions.
  The ordinary operations in `ProEtaleOperations` are exact termwise pullback and
  K-injective derived direct image. The smaller-coefficient
  `sfIntrinsicDerivedPullback` reexport is not incorrectly applied here.
- `IntegralUniformCoefficient` reexports `BoundedConstructibleComplete`. Its
  newer convenience wrapper with E in Type (u+1) is not another membership
  notion. The published E in Type u specialization used by the completed
  exchange already supplies exactly the required category. I read
  `PbcIsBoundedConstructibleComplete`: intrinsic completeness, uniform canonical
  reductions including transitions, and compatible bounded-below etale origins.
- `RefinementCoefficientRealization` reexports the exact finite coefficient
  realization. `pbcDerivedFunctionRealization` uses the specified constants map
  into the function-sheaf presentation, not an arbitrary equivalence.
- `ProEtaleConstructibleCoefficientSheaf` uses finite constructible locally closed
  strata and the existing `IsRelativelyFiniteLisseModule` on each actual
  inverse-image module. I opened that predicate: a covering sieve trivializes it
  by finite constant modules over the inverse-image constant ring. This is the
  required intrinsic local constancy and finite-stalk condition.
- The only helper in this delivery, `sbcAdicFiniteCohomology`, is the literal
  composite of `DerivedCategory.homologyFunctor` and restriction along
  `pbcLevelConstantComparison.hom`. I read that comparison's constant-section
  characterization and `pbcRestrict`. Restriction along this ring isomorphism
  preserves and reflects zero objects and changes only the coefficient
  presentation of the very same cohomology. It adds no new notion or hypothesis.

Edge cases: n=0 is exponent 1, and every positive quotient is present. There is
no empty level-index set hidden in a hypothesis. Empty schemes are admitted:
their topological dimension is bottom, all dimension bounds permit this, and the
constructibility predicate explicitly admits one empty stratum. No nonemptiness
or geometric point is required. Zero K and zero cohomology are permitted; no
interval endpoint is forced positive, and a=b is allowed. Residue characteristic
ell on a nonempty base is excluded precisely by the stated invertibility
hypotheses, while every allowed characteristic remains covered. The small
pro-etale site keeps object universe u+1 and morphism universe u, with modules
and finite quotient coefficients in u+1. The published size lift of the finite
p-adic coefficient extension changes its representation only; the theorem adds
no site-universe equality, smallness instance, or field assumption beyond E/Q_l.
No independent lower test-object universe makes a hypothesis vacuous.

Independent searches, with different wording from the worker's:

- LeanSearch via `msearch.py`: “Smooth base change for derived adically complete
  sheaves over the ring of integers of a finite p-adic field extension”. Eight
  results concern smooth ring maps, their base change, or formal smoothness of
  adic completion; none states this theorem.
- LeanFinder via `msearch.py`: “Derived complete integral l-adic sheaf smooth
  pullback commutes with derived direct image”. Eight results concern ordinary
  module pullback/direct-image adjunctions and composition, with no completed
  exchange theorem.
- Loogle via `msearch.py`: `AlgebraicGeometry.Smooth, CategoryTheory.IsIso`.
  The sole result is normalization pullback under smooth base change, unrelated
  to these derived categories. A preliminary unqualified query was rejected as
  an unknown identifier; the qualified query above succeeded.
- `rg` in Mathlib, the read-only slopmaster2 WeilConjectures tree, current
  `lean/Sheaf`, current `lean/WeilConjectures`, and upstream name records for
  adic/smooth, completed exchange, and cohomology presentation terms. I opened
  upstream `ProEtale.isIso_derivedBaseChangeMap_app_of_smooth`: it concerns
  finite fixed coefficients and bounded constructible etale origins, not this
  integral completed theorem or its conditional landing. I also opened
  `completeProetale_isIso` and `constructibleComplete_properBaseChange`; they
  impose properness and do not state this smooth/qcqs result. The rational
  successor refers to this node, and `SbcCompletedOperations` constructs the
  map without asserting its invertibility. No existing exact statement or
  named copy of the cohomology-presentation helper was found.

H5/H6/H8/H9 checks: the helper contains real data, and the sole postponed proof
is the named `adicSmoothBaseChange` with `by sorry`. All eight proof steps occur
in its source/blueprint docstring, including the coefficient-linear comparison,
compatible origin construction and cocycle, and fullness for the final landing.
Every declaration has its source and blueprint id; there are no private helpers,
file-local instances or notation, unbound variables, or overlong Lean lines.
Every recorded proof-dependency module is imported; the finite pro-etale smooth
node still has no Lean record, so its import is correctly omitted at this stage.
There are no new nodes or dependency modules in this delivery to review under
H12/H13. The node copy differs from the base only in `lean`, and its
`lean.statement` equals the theorem signature verbatim.

Mismatches found: none. Changes made: appended this independent second reading
only; the module, node statement, signature, and dependency lists remain as read.
The prescribed `scompile.py N5 sbc-thm-adic-smooth-base-change
lean/Sheaf/Paper/AdicSmoothBaseChange.lean`, run from the sandbox, compiled the
sandbox and module cleanly, with no warnings, in 4.5 s and 6.2 s respectively.
