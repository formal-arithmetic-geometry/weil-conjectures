## Worker report

Item: `lem-sf-complete-residue-cohomology-bounds`, group Q11, stage 2.
Module: `Sheaf.Paper.CompleteResidueCohomologyBounds`.
Declaration: `WeilConjectures.complete_residue_cohomology_bounds`.

This delivery states the cohomology bounds for an arbitrary derived-complete complex over the actual inverse limit of constant quotient coefficient sheaves. Its only proof is `sorry`. It introduces no coefficient sheaf, reduction functor, tensor product, or completeness predicate. The theorem docstring reproduces all seven proof steps, including the identification of the Milnor cone with the derived limit using products in the derived category and rotation of the cone triangle.

### Statement correspondence

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Prime ell | `(l : ℕ) [Fact l.Prime]`. |
| Finite field extension E/Q_l | `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. |
| Valuation ring, uniformizer, residue field | Existing `Padic.coefficientExtensionIntegers`, chosen uniformizer and `Padic.coefficientExtensionRing l E n`; at `n = 1` the latter is exactly the quotient by the uniformizer ideal. They are the recorded coefficient extension constructions, rather than new parameters or copies. |
| Quasi-compact scheme, small pro-etale site | `(X : Scheme.{u}) [CompactSpace X]`, and `X.ProEt` with `ProEt.topology X`. No Noetherian, separatedness, characteristic or invertibility condition is added. |
| B_X is the inverse limit over positive exponents of constant quotient ring sheaves | `integralTowerModules.{u, u} l E X` is `SheafOfModules` over `completedIntegralCoefficientSheafUnrestricted l E X`. The latter is the categorical limit of `integralCoefficientSheafSystem`, whose index `n : ℕ` means exponent `n+1`. It is not the constant sheaf of the valuation ring. |
| K in the ordinary unbounded D(Mod B_X) | The binder uses `DerivedCategory (integralTowerModules.{u, u} l E X)` with the existing standard localization. |
| Derived completeness through canonical quotient transitions, all reductions restricted to B_X, and the canonical quotient augmentation | `_hcomplete : IsDerivedCompleteUnrestricted.{u, u} l E X K`. Expanding the recorded predicate gives a K-flat representative, `integralReductionTower` with actual tensor quotient maps, restriction along the limit projections, and `IsDerivedLimitTriangle` whose first map is `Pi.lift` of `integralReductionTowerCone`'s canonical quotient maps. This is not mere existence of an unrelated derived-limit object. |
| No auxiliary characteristic condition | The unrestricted completeness predicate existentially hides a finite-field presentation datum that none of its coefficient constructions uses. Such a datum with characteristic different from `l` always exists (characteristic 2 or 3). There is no hypothesis on `X` coming from it. |
| Integers a <= b | `(a b : ℤ) (_hab : a ≤ b)`. |
| K_1 = K derived-tensored over B_X with k_X | `((scalarReductionDerivedExtension.{u, u} l E X 0).obj K)`. Level zero of this API is positive exponent one. The functor is the existing universal derived change of rings along the completion projection to this quotient. |
| Every site object V -> X | `_hTor : ∀ V : X.ProEt, ...`. Its structure map is `V.hom` and its scheme is `V.left`. No quasi-compactness condition is imposed on V. |
| Restriction K_1 to V | `proEtaleRingDerivedPullback V.hom` with the constant residue sheaves on X and V, using the existing `StrictTower.constantRingIso (ULift (Padic.coefficientExtensionRing l E 1)) V.hom`. This is the canonical constant-section identification, not an arbitrary supplied coefficient isomorphism. |
| Every sheaf N of k_V-modules, all degrees outside [a,b], derived tensor over k_V | `HasProEtaleTorAmplitude V.left (Padic.coefficientExtensionRing l E 1) (...) a b`. Its full definition quantifies over every module sheaf in degree zero and all K-flat resolutions of all representatives of the specified object; it requires the homology of the recorded `derivedTensor` to be zero when `i < a ∨ b < i`. Thus the local quantifier over V and the universal quantifier over N are both retained. |
| Conclusion H^j(K)=0 outside [a,b] | `∀ j : ℤ, j < a ∨ b < j → IsZero ((DerivedCategory.homologyFunctor ... j).obj K)`. The homology is taken in the same completed-coefficient module category as K. |
| No constructibility or local constancy required | There is no such binder and no predicate that embeds either assumption. In particular the completeness predicate is the unrestricted one, not bounded constructible derived-complete membership. |

The category and homology functor explicitly supply `SheafOfModules.instAbelian` using `integralCoefficientAbSheafify.{u, u}` and `integralCoefficientAbLocallyBijective.{u, u}`, together with the existing `integralTowerHasDerivedCategory.{u, u}`. This avoids ambiguous max-universe instance search; it is Mathlib's original abelian structure and standard localization, not a new instance or category. All variables and universes are explicitly bound; `autoImplicit` is false. The small site retains objects in universe `u+1` and morphisms in universe `u`; the module-value and lifted coefficient universe is `u+1`. No equality between the site's object and morphism universes is assumed.

### Dependency declarations used

The original statement dependencies were read, including their full recorded source declarations and docstrings (Mathlib leaves were resolved through their `mathlib_match`). They are used as follows:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: the recorded coefficient extension constructions are publicly imported; `Padic.coefficientExtensionRing` gives the finite positive quotient and its exponent-one residue field. The recorded finiteness theorem is `Padic.finite_coefficientExtensionRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`; `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`, with the original small site and intrinsic constant-ring module encoding.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`, used by the quotient coefficient sheaves and constant residue sheaves.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the transparent alias of `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and `HasDerivedCategory.standard`.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`: `AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude`.
- `Sheaf.Algebra.Homology.DerivedTensor`: `AlgebraicGeometry.Scheme.derivedTensor`, used inside the recorded Tor predicate, with its canonical sheafified tensor and K-flat representative.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`: `DerivedCategory.homologyFunctor`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `CategoryTheory.Limits.limit` and `limit.π`, used by the existing completion.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`: `CategoryTheory.IsDerivedLimitTriangle`, as used by the existing completeness predicate.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`: `SheafOfModules.restrictScalars`, used in the canonical reduction tower.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`: `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`, which constructs the recorded reduction functor without identifying the site's two universes.

The item gains only three already-landed statement dependencies under standing brief §5:

- `def-weil-derived-complete`: `Sheaf.Paper.DerivedCompleteUnrestricted`, `WeilConjectures.IsDerivedCompleteUnrestricted`.
- `def-weil-integral-derived-reduction`: `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`, `WeilConjectures.scalarReductionDerivedExtension`.
- `def-cbc-strict-constant-tower-operations`: `Sheaf.AlgebraicGeometry.StrictConstantTowerOperations`, `AlgebraicGeometry.ProEtale.StrictTower.constantRingIso`. Its canonical constant-section map realizes the restriction in the local Tor hypothesis; strict tower operations themselves are not assumed as extra hypotheses.

The completed-ring and module construction is reused from `Sheaf.Paper.CompletedIntegralCoefficients` and `Sheaf.Paper.IntegralReductionTowerUnrestricted`, publicly available through the recorded completeness module. In particular, `completedIntegralCoefficientSheafUnrestricted`, `integralCoefficientSheaf`, and `integralTowerModules` have real construction data.

The recorded proof-dependency modules are imported for stage 3: `KFlatResolutionIndependentCoefficients`, `FlatOnSite`, Mathlib's `DerivedCategory.ShortExact` and `DerivedCategory.HomologySequence`, `ProEtaleMilnorSequence`, `ProEtaleProductsDerived`, `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`, and `ProEtaleMilnorEpimorphic`. These supply the representative, coefficient-sequence tensor exactness, triangle, long exact sequence, product comparison, derived-limit uniqueness and epimorphic-tower Milnor vanishing needed by the seven-step proof.

### Sources and edge cases

Read the local Stacks source for proetale.tex Tag 09C2, including its proof of (1) and (2); proetale.tex Tag 099Q; sites-cohomology.tex Tags 0942 and 0947; and algebraization.tex Tag 099I. The bounds portion of 09C2 uses completeness and the residue Tor interval; constructibility enters other assertions, so it is correctly absent here. The proof docstring keeps B_X as the coefficient sheaf throughout the Milnor argument.

Checked: K=0; empty X (no nonemptiness assumption); a=b (including arbitrary shifts); arbitrary positive and negative a,b; all site objects, including the identity and empty object; exponent one as API level zero; and primes equal to residue characteristics of X. The theorem excludes a>b exactly through the stated ordered-interval hypothesis. For nonempty X, the coefficient sheaf itself is a nonzero test in interval [0,0]. Completeness is essential: without it a uniformizer-inverted object can have zero residue reduction and nonzero cohomology. No assertion here replaces completeness by residue vanishing alone. No statement fault or `STATEMENT-DISPUTED` flag was found.

### Searches

- `msearch.py`, LeanFinder: “A derived complete complex of proetale sheaves whose reduction modulo the uniformizer has Tor amplitude a to b has cohomology in a to b”. Returned eight generic t-structure/complex bounds hits (`DerivedCategory.IsGE`, `IsLE` comparisons, zero criteria, and `cm5b`), not the claimed residue-to-complete theorem.
- `msearch.py`, Loogle: `"DerivedCategory", "complete"`. Zero hits.
- `msearch.py`, Mathlib grep: `derived.?complet|complete.*cohomology|cohomology.*complete` in `Algebra/Homology`. Zero hits.
- `msearch.py`, LeanSearch: “A derived complete complex of sheaves over a complete discrete valuation ring has cohomology bounded by the Tor amplitude of its residue reduction”. Eight hits: generic derived-category bounds, DVR cotangent-space dimension, module-sheaf colimits, and a valued-field completeness criterion; none states this theorem.
- `rg` on upstream `WeilConjectures/`, side `lean/Sheaf/`, and `dag/lean_names_upstream.json` for the item id and proposed declaration name: no existing declaration. A proof-plan reference in `ResidueLisseProjectiveModels.lean` is a consumer, not an implementation.
- `rg` for derived completeness, residue Tor and related bounds in upstream and side modules found the reusable completed coefficients, reduction and completeness APIs. `IntegralResidueTor.lean` assumes constructible completed membership and states finite-level Tor/constructibility equivalences; it does not state this general cohomology bound.

## New nodes

None.

## Dependency modules

None. All reused declarations are already published. No other DAG node is stated or repaired in this delivery.

## Validation

The final module was compiled with the prescribed `scompile.py` wrapper, both as the isolated sandbox input and as `Sheaf.Paper.CompleteResidueCohomologyBounds`. Both passes succeeded without errors or warnings. No global build or direct live-source edit was run. Diagnostic `#check` commands are confined to the sandbox scratchpad and are absent from the delivered module.

## Second reading by Q11

Independent second reading, 2026-10-17. I opened the sandbox node and module, the
base node, every statement-dependency record, and the source declarations behind
the coefficient rings, ringed-site modules, completeness, reduction, Tor amplitude,
constant-coefficient pullback, derived limits and cohomology. There is no repair
note for this item, no `statement_change`, no new node and no dependency module in
this delivery. The three added dependencies are already published interfaces;
none adds a mathematical assumption.

My inventory of the node, matched against the actual signature, is as follows.

| Object, hypothesis or conclusion | Lean rendering and second-reader verdict |
| --- | --- |
| A prime ell | `l : ℕ` and `[Fact l.Prime]`; exact. No prime is excluded. |
| A finite field extension E/Q_ell | `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`; exact finite-dimensional extension, not a finite-type algebra assumption. |
| Its valuation ring R and one chosen uniformizer | `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer` in the imported coefficient construction; exact dependency data. The spectral absolute value fixes the ring of integers and the recorded uniformizer generates its maximal ideal. |
| k = R/(varpi) | `Padic.coefficientExtensionRing l E 1`; its definition is the quotient by `(Ideal.span {uniformizer}) ^ 1`. This is exactly the quotient specified by this node, even though the separately named residue-field construction uses the maximal ideal. No field structure is assumed on a new arbitrary coefficient ring. |
| A quasi-compact scheme X | `(X : Scheme.{u}) [CompactSpace X]`; exact. I opened `CompactSpace`: it has no Hausdorff axiom. No Noetherian or separatedness hypothesis occurs. |
| The small pro-etale site | `X.ProEt`, `ProEt.topology X`, and `V : X.ProEt`; these are the recorded small site, not the big site or the category of only affine objects. |
| B_X = lim of the constant positive quotient sheaves | The category `integralTowerModules.{u, u} l E X` expands to `SheafOfModules` over `completedIntegralCoefficientSheafUnrestricted`. The latter is `limit (integralCoefficientSheafSystem l E X)`; its terms are constant sheaves of `ULift (coefficientExtensionRing l E (n+1))` and its maps are induced by quotient transitions. Exact completed coefficient sheaf, with real construction data. |
| Arbitrary K in ordinary unbounded D(Mod B_X) | The explicit `@DerivedCategory` binder uses this module category, Mathlib's `SheafOfModules.instAbelian`, and `integralTowerHasDerivedCategory = HasDerivedCategory.standard`. Exact, with no boundedness or constructibility implicit in K's type. |
| Completeness for the canonical reduction tower, including the quotient augmentation | `_hcomplete : IsDerivedCompleteUnrestricted.{u, u} l E X K`; I expanded it through `IsDerivedComplete`, `integralReductionTower`, `integralReductionTowerMap`, and `integralReductionTowerCone`. It asks for a K-flat representative and a distinguished Roos triangle whose first map is the product of the canonical maps `[q]⁻¹` followed by `[x ↦ x tensor 1]`, transported along the representative isomorphism. The transitions come from tensoring the actual quotient maps. It is exactly the required augmented derived-limit condition. |
| All tower terms viewed over B_X | The reduction tower uses `integralTowerComplex`, obtained by restriction along the completion projections, before localization; it is a tower in the single completed-module derived category. Exact. |
| No auxiliary characteristic condition | The unrestricted predicate existentially hides `D : FiniteFieldDatum.{0}` and `l ≠ D.p`; none of the coefficient, transition or augmentation constructions depends on D. Choose characteristic 2 when l differs from 2 and characteristic 3 otherwise. Thus this existential restricts neither X nor l; exact unrestricted completeness. |
| Integers a <= b | `(a b : ℤ) (_hab : a ≤ b)`; exact order and arbitrary integer endpoints. |
| K_1 = K tensor-derived over B_X with k_X | `(scalarReductionDerivedExtension.{u, u} l E X 0).obj K`; exact. I opened `scalarReductionExistence` and the independent-coefficient derived-change-of-rings theorem: the functor is the universal derived extension along `completedIntegralCommRingProjectionUnrestricted ... 0`, computed by K-flat tensor. Level zero here means exponent one. Its choice is constrained by that universal property. |
| Every V -> X and the restriction K_1 on V | `_hTor : ∀ V : X.ProEt, ... (proEtaleRingDerivedPullback V.hom ...).obj ...`; exact unrestricted object quantifier. The coefficient identification is the existing `StrictTower.constantRingIso (ULift ... k) V.hom`, whose map is the canonical constant-section comparison. This exact inverse-image descent is the restriction used by the node. No arbitrary map or coefficient isomorphism is supplied as a hypothesis. |
| Every k_V-module N, and every degree outside [a,b], in the derived tensor test | `HasProEtaleTorAmplitude V.left (Padic.coefficientExtensionRing l E 1) (...) a b`; I opened its definition and `derivedTensor`. It quantifies over every sheaf M in degree zero, all cochain representatives isomorphic to the argument, all K-flat resolutions, and every i with `i < a ∨ b < i`, requiring the tensor cohomology object to be zero. Existing K-flat resolutions make this the stated invariant predicate, not a vacuous test or a test restricted to locally free sheaves. |
| H^j(K) = 0 outside [a,b] | `∀ j : ℤ, j < a ∨ b < j → IsZero ((DerivedCategory.homologyFunctor ... j).obj K)`; exact conclusion in the same completed-module category. No clause about reduction alone replaces integral cohomology vanishing. |
| No constructibility or local constancy requirement | Neither appears as a binder nor in the expanded completeness, derived-category or Tor-amplitude predicates; exact. |

Source reading: I read `proetale.tex` at `definition-Dbc`,
`lemma-describe-constructible-complexes` (09C2), and
`proposition-enough-weakly-contractibles` (099Q), including the proof of 09C2(1),(2).
The surrounding coefficient ring is Noetherian; the chosen valuation ring is a DVR,
so this holds automatically, rather than becoming an extra assumption on X. The
bounds argument uses completeness and a common residue Tor interval. Constructible
cohomology is used for the other conclusions of 09C2, not the conclusion stated
here. I also read `sites-cohomology.tex` at `lemma-bounded` (0942) and
`proposition-enough-weakly-contractibles` (0947), and `algebraization.tex` at
`lemma-restriction-derived-complete-equivalence` (099I). In particular 0947 applies
to an arbitrary ring sheaf, so the Milnor argument retains B_X throughout. I checked
the module docstring against all seven node proof steps: residue-unit test, single
K-flat resolution, coefficient exact sequence, triangle and long exact sequence,
induction plus top-degree epimorphy, product/cone identification with the same
canonical tower, and final Milnor vanishing are all present with their dependencies.

Edge cases: K=0 and the empty scheme are admitted, as are the identity and empty
site objects. There is no index set parameter that would exclude an empty family;
the quotient tower is the prescribed nonempty sequence of positive exponents.
API index n=0 is its residue level, not the zero coefficient ring at exponent zero.
Intervals with a=b, negative endpoints, and endpoints zero are admitted; a>b is
excluded exactly as in the node. Neither ell=2 nor residue characteristic ell on
X is excluded. The uniformizer is the dependency's chosen one, as stipulated by
the node. All universes are bound: the small site has object universe u+1 and
morphism universe u, with ring and module values in u+1. The common ambient
universe for E and X does not identify those two site universes or add an instance
hypothesis. No finiteness condition on test sheaves or site objects is hidden.

Independent H4 searches, using different wording from the worker's report:

- LeanFinder, via `msearch.py`: “Derived completion is t exact on complexes whose
  reduction modulo the maximal ideal has bounded Tor dimension”. Eight hits,
  including `AdicCompletion.map_exact`, ordinary localized-module exactness and
  `CategoryTheory.Tor`; none is this sheaf-complex residue-to-completion theorem.
- Loogle: `"AdicCompletion", "IsLE"`; zero hits.
- LeanSearch: “The homotopy limit of quotient reductions of a complete sheaf complex
  has the cohomological bounds of its reduction modulo the maximal ideal”. Eight
  generic homological-complex limits, localization and homology-factorization hits;
  none states the required implication.
- Mathlib grep through `msearch.py`: `adic.*[Tt][Ss]tructure|[Dd]erived.*[Aa]dic|[Aa]mplitude`;
  only two irrelevant Lie-derived-series text hits. Direct `rg` for derived
  completeness and completion/cohomology combinations in Mathlib's homology tree
  returned no result.
- Direct `rg` on upstream `WeilConjectures/` and side `lean/Sheaf/` for the item,
  declaration name and residue/bounds wording found no existing theorem. I opened
  `IntegralResidueTor.lean`: its theorem starts with constructible completed
  membership and concludes finite-level Tor amplitude and an equality of
  constructible object predicates; it is not this general cohomology bound.
  `ResidueLisseProjectiveModels.lean` cites this node in its proof plan and does
  not already supply it. The copied pro-etale framework was checked using
  `coord/pefw-upstream-framework.md`; its condensed-coefficient target interfaces
  do not replace the completed intrinsic module category used here.

Mismatches and changes: none found in the statement, definitions used, proof
outline, imports or node binding. I left the correct Lean and node unchanged;
this independent reading is the only content I added. No additional definition,
helper theorem, statement correction or citer audit is needed.

Validation: reran the required `scompile.py Q11
lem-sf-complete-residue-cohomology-bounds
lean/Sheaf/Paper/CompleteResidueCohomologyBounds.lean`; sandbox and module passes
both succeeded with no diagnostic output (1.9 s and 2.0 s). A separate text check
confirmed the node's `lean.statement` is verbatim equal to the full signature,
all lines are at most 100 characters, and the only theorem proof is `sorry`.
The node changes only `lean` and the three already-published `stmt_deps` additions.
