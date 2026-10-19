## Worker report

This delivery states `AlgebraicGeometry.ProEtale.InternalHomDualModels.internalHomDual_constructible_models` in `Sheaf.Paper.InternalHomDualConstructibleModels`. The node's natural statement is unchanged. The scalar realization data is now owned by the added definition node `def-sfb-finite-constant-model-data`; the item cites that node, while the two-term resolution theorem remains a separate dependency whose module imports the data module. A read-only reachability check found no dependency cycle.

The auxiliary `Assertion` is an explicit Prop abbreviation of this item's quantified local-model statement. Its functor parameter only shares syntax: the main theorem substitutes six concrete canonical functors and never assumes a functor with arbitrary properties. `scalarDual` gives real degreewise Hom-module data and the ordinary signed dual differential. The Qbar scalar map consists of literal constant functions in the finite-subextension subsheaf, followed by the sheafification adjunction. No arbitrary map, arbitrary chosen isomorphism, or existence-chosen object replaces a canonical construction.

Hypothesis and conclusion correspondence:

| Node phrase | Lean rendering |
| --- | --- |
| Prime ell | `(l : ℕ) [Fact l.Prime]` |
| Field k, characteristic p>0, p different from ell | `(p : ℕ) (k : Type u) [Field k] [CharP k p] (hp : 0 < p) (hpl : p ≠ l)` |
| Separated finite-type k-scheme S | `(S : Scheme.{u}) [S.Over (Spec (.of k))]` and `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on its structure morphism |
| Finite commutative A annihilated by a power of ell | First conjunct: `∀ (A : Type u) [CommRing A] [Finite A], (∃ n : ℕ, (l : A)^n = 0) → ...`; `finiteCoefficients` fixes the discrete topology |
| Z_l | Second conjunct: `ULift.{u} ℤ_[l]`, `baseIntegralCoefficients`, `baseIntegralModel` |
| O_E, finite E/Q_l | Third conjunct: all fields E with `Algebra ℚ_[l] E` and `FiniteDimensional ℚ_[l] E`, using `Padic.coefficientExtensionIntegers`, `FiniteConstantModel.integralCoefficients`, `integralModel` |
| Q_l | Fourth conjunct: `ULift.{u} ℚ_[l]`, `baseRationalCoefficients`, `baseRationalModel` |
| E, finite E/Q_l | Fifth conjunct: the same finite-extension binders, `FiniteConstantModel.rationalCoefficients` and `rationalModel` |
| Condensed Qbar_l | Sixth conjunct: `Profinite.padicAlgClRingObj l`, with `algebraicModel`; its sections take values in a finite subextension |
| R=Lambda(*) | The scalar coordinates are A, Z_l, O_E, Q_l, E, Qbar_l, respectively. Evaluation on the singleton identifies the existing coefficient sheaf's point ring with these coordinates. `ULift` only changes universe coordinates for the Type-0 base rings; inverse is `ULift.down`. It does not restrict the coefficient fields. |
| B=Lambda_S, ordinary unbounded D(B) | `condensedRingObj Λ S` and the ambient `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u+1}) ...)` in `Assertion` |
| A pro-etale cover U_i→S | `𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S`; no finiteness or nonemptiness assumption |
| Given bounded complexes F_i of finite projective R-modules | `F : 𝒰.I₀ → CochainComplex (ModuleCat.{u+1} A) ℤ`; for each i there exist a,b with `IsStrictlyGE a ∧ IsStrictlyLE b`; every term has `Module.Finite A` and `Module.Projective A` |
| P restricted to U_i is B tensor constant F_i, termwise | Given `Nonempty` isomorphism between exact `upperStar.mapDerivedCategory` of P and `DerivedCategory.Q.obj` of `C(U_i).mapHomologicalComplex` applied to the exact given F_i |
| P-dual=RHom_B(P,B) | `((CondensedRing.derivedHom Λ S).obj (op P)).obj (𝟙_ _)`; the derived tensor unit is B[0] |
| Scalar dual F_i=Hom_R^bullet(F_i,R[0]) | `scalarDual (F i)` has degree q equal to `Module.Dual A ((F i).X (-q))`; differential is `-q.negOnePow` times precomposition with the original differential |
| First cohomology isomorphism, every original i and every integer q | First `Nonempty` isomorphism in `∀ (i : 𝒰.I₀) (q : ℤ)`: restriction of `DerivedCategory.homologyFunctor` of P to `C(U_i)` of scalar homology of F_i |
| Second cohomology isomorphism, same i and q | Second `Nonempty` isomorphism, with the actual derived internal dual on the left and scalar homology of `scalarDual (F i)` on the right |
| Both scalar cohomology modules finitely presented | Two `Module.FinitePresentation A` conjuncts in that same i,q block; not projectivity of cohomology |
| P and its dual have bounded cohomology and lie in Dbc | Two `constantModelBoundedConstructible Λ S` conjuncts. The existing predicate expands to boundedness plus constructibility of every integer cohomology sheaf, using finite constant scalar local models. |
| Includes the completed integral sheaf O_E,S=lim_n(O_E/pi^n)_S | Integral functors use the pulled-back continuous condensed ring, not the discrete constant integral ring. The imported `sfb_integral_coefficient_limit` identifies exactly that ring object with the actual positive quotient tower, with projection normalization. `completed_constant_sheaf_reduction` is the imported proof input establishing flatness. No completion condition is imposed on P or on D(B). |

The scalar complex bounds need not agree between charts. The conclusion keeps the original covering index throughout. The finite affine refinement occurs only in the natural proof for a uniform global bound.

Dependency declarations read and used:

| Dependency | Module and declaration/interface |
| --- | --- |
| sk-def-sfb-dc-setting | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, `CondensedRing.compactificationOverField`; its explicit field/scheme setting is used in the theorem binders, without imposing a compactification on this local-model assertion |
| sk-def-localizing-closure | `Sheaf.Paper.LocalizingClosure`, `localizingClosureProEtale`; the node supplies the coefficient convention, with the individual ring constructions imported and instantiated. No localizing-closure membership is asserted here. |
| def-weil-pbc-proetale-site | `Mathlib.AlgebraicGeometry.Sites.Proetale`, `Scheme.ProEt`, `Scheme.ProEt.topology`, `Scheme.proetalePrecoverage` |
| def-pc-perfect-ring-complex | `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`, `DerivedCategory.IsPerfectRingComplex`; the assumption supplies the concrete bounded finite-projective representative itself, rather than adding a redundant perfectness hypothesis |
| def-weil-pbc-strict-perfect-coefficient-package | `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`, `SheafOfModules.StrictPerfectCoefficientRepresentationOfUniverses`, and its imported `StrictPerfectCoefficientPackageOnSite`; proof input for the degreewise summand argument, not an additional hypothesis |
| sk-def-sfb-derived-tensor-hom | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`, `CondensedRing.derivedHom`; the relative B-linear closed structure, on the unbounded ambient category |
| sk-def-sfb-constructible | `Sheaf.Paper.CondensedConstantConstructibility`, `constantModelBoundedConstructible` and its underlying `HasFiniteConstantLocalModel` / `IsConstantModelConstructible` |
| lem-weil-pbc-completed-constant-sheaf-reduction | `Sheaf.Paper.CompletedConstantSheafReduction`, `Scheme.CompletedConstantReduction.completed_constant_sheaf_reduction` |
| det-prop-sfb-qlbar-colimit-x-integral-limit | `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`, `sfb_integral_coefficient_limit` |
| Scalar-model definition owner | `Sheaf.Paper.FiniteConstantModelDefinitions`, `FiniteConstantModel.scalarModules`, `scalarToContinuous`, `modelFunctor`, `integralModel`, `rationalModel`, and the coefficient abbreviations. No two-term-resolution assumption is added. |

All other currently stated proof-dependency modules are imported without `public`; the main theorem docstring contains all ten node proof steps and their mathematical arguments. `sk-prop-sfb-cartesian-coefficients` has no lean record but its upstream audit names `isIso_condensedPullbackHom`, `condensedPushforwardHom_id` and `condensedPushforwardHom_comp` in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, already exported by the imported framework. `lem-sfb-local-model-cohomology-descent` has no recorded declaration or module, so that proof import alone is omitted; its interface is not needed to TYPE the theorem and its role remains named in the full natural proof. The old ordinary-sheaf Hom interfaces are proof inputs only; the statement itself retains module objects and their relative derived internal Hom.

Named postponed well-definedness lemmas are `scalarDualDifferential_laws` (shape and square zero), `scalarModules_additive`, `constant_mem_finiteIntermediateFieldValued`, `algebraicScalarMap_isMonHom`, and `realization_additive`. Each has the item's blueprint tag and its complete natural proof. All definitions have actual data; all theorem proofs are `sorry`. The additive instances are direct applications of the named lemmas, not independently proved mathematical statements.

Edge cases checked mathematically before writing and again against the file: S empty (empty cover allowed, bounded zero objects); zero complex and zero scalar cohomology; rank zero and arbitrary shifts, including negative q; finite nonregular coefficient ring such as Z/4 (cohomology is finitely presented but need not projective); zero finite coefficient ring (n=0 allowed exactly in that case); variable chart bounds and infinite original covers; no nonempty cover-index assumption; torsion O_E modules; and genuine condensed Qbar coefficients rather than all continuous Qbar-valued functions. No counterexample or statement correction was found.

Searches for existing declarations:

- `msearch.py ... leanfinder "locally scalar perfect complex and its internal dual have constructible cohomology on pro etale sites"`: eight K-projective/K-injective and generic derived-bound hits; none states both scalar cohomology formulas with all coefficients.
- `msearch.py ... loogle "Module.dual_projective, Module.dual_finite"`: zero hits.
- `msearch.py ... grep "dual_projective|constructible.*dual|dual.*constructible"`: only `Mathlib/LinearAlgebra/Dual/Lemmas.lean:145`, the scalar projective-dual instance.
- `msearch.py ... leansearch "cohomology scalar models of locally perfect complexes and internal duals on pro-etale sites"`: eight Hom-complex scalar-action / unrelated etale-algebra hits; no match.
- `rg` over the upstream `WeilConjectures` and side `lean/Sheaf` for the item id and constructible/dual phrases: generic perfectness, Verdier duality and lisse-object results, none this statement. Searches for scalar realization located the existing declarations in `FiniteConstantModelResolution`; they were moved into the new owning `FiniteConstantModelDefinitions` module without changing signatures.
- `rg` of Mathlib Hom-complex/opposite APIs and upstream monoidal `rightDual`: the latter requires prechosen categorical duals of every term; it does not define the ordinary Hom_R(F,R[0]) for arbitrary scalar module complexes. The degreewise scalar dual here explicitly uses the existing `LinearMap.dualMap`.
- `rg` of proposed helper names in `dag/lean_names_upstream.json`, Mathlib/source and side files: no same-namespace declarations. Existing unrelated `Assertion` names are in other namespaces.

## Second reading by Q108

Second pass by this worker, with the node and file open; the dispatcher brief prohibits starting another agent and assigns the independent review to the maintainer. No independent review is claimed here.

Matched every row in the correspondence table against `Assertion` and the six-conjunct theorem. Checked that the first and second homology isomorphisms use the same GIVEN F_i and original U_i, that the scalar dual differential has the Hom sign rather than an unsigned reverse, and that both finite-presentation clauses are conclusions. The two Dbc predicates include boundedness in their existing definition, so no boundedness clause is silently lost. Checked all finite-extension binders, the finite ring's annihilation condition, and positive/different characteristic. The coefficient functors in the theorem are fixed constructions, not hypotheses.

The first compiler pass found missing discrete-topology and additivity interfaces plus scalar homology type inference; these were repaired explicitly. A subsequent pass exposed a surplus parenthesis edit, which was corrected to keep the entire derived-dual homology object on the left of the second isomorphism. Discrete constant-ring commutativity is supplied from the existing named lemma with the discrete topology made explicit. Checked that no construction of derived duality or constructibility has been duplicated.

## New nodes

`def-sfb-finite-constant-model-data` is the required definition node in
`sec-six-functors-basics`. It records ownership of the canonical `scalarModules`,
`scalarToContinuous`, `modelFunctor`, `integralCoefficients`, `rationalCoefficients`,
`integralModel`, and `rationalModel` data (plus their supporting scalar-action and
ring-map declarations) in `Sheaf.Paper.FiniteConstantModelDefinitions`. The statement
is sourced from the scalar local-model constructions in paragraphs 2--3 of the
blueprint internal-Hom proof. The grep, LeanSearch, LeanFinder, and Loogle searches
recorded in the node found no separate combined declaration. The declarations already
exist with the exact signatures in `Sheaf.Paper.FiniteConstantModelResolution`; this
node records them as definitions without copying or redeclaring them, so the theorem in
that same module uses the canonical data directly.

There is no dependency-module repair in this packet: the old two-term theorem node is
removed from the item's statement dependencies, and its published module remains
unchanged. The new definition node points to the existing data declarations that the
theorem module already exposes; no theorem conclusion or `HasResolution` is used.

Validation: `scompile.py Q108 lem-sfb-internal-hom-dual-constructible-models` passed the
three split modules (`FiniteConstantModelDefinitions`, `FiniteConstantModelResolution`,
and `InternalHomDualConstructibleModels`) with no errors or warnings. The required
`deliver2.py Q108 lem-sfb-internal-hom-dual-constructible-models --no-push` is run again
after the packet preflight checks this repair.

## Maintainer review fix (cc reviewer, 2026-10-18)

- Qbar_l coefficient corrected. The node takes Lambda from the admissible coefficients of
  [sk-def-localizing-closure], which give the topology of the l-adic absolute value. The
  condensed ring of a topological ring is C(-,T) [sk-def-sfb-condensed-ring], and the landed
  `IsLocalizingAdmissibleCoefficient` (Q89) uses `continuousMapRingObj (PadicAlgCl l)`. The
  delivery's `Profinite.padicAlgClRingObj` is instead the finite-subextension colimit object,
  which is a different condensed ring: a convergent sequence in Qbar_l can generate an
  infinite extension. The sixth conjunct now uses
  `algebraicCoefficients l = continuousCoefficientRingObj (ULift (PadicAlgCl l))` (norm
  topology, checked by `rfl`) and `algebraicModel l = FiniteConstantModel.modelFunctor`. This
  removes `constant_mem_finiteIntermediateFieldValued`, `algebraicConstantFunctions`,
  `algebraicScalarMap` and `algebraicScalarMap_isMonHom`. Step 3's field-splitting argument
  covers this coefficient unchanged. The worker report's edge-case line about "genuine
  condensed Qbar coefficients rather than all continuous Qbar-valued functions" is superseded.
- Report and record wording. No module `FiniteConstantModelDefinitions` exists or was
  delivered. `def-sfb-finite-constant-model-data` binds the existing declarations of
  `Sheaf.Paper.FiniteConstantModelResolution` with `existing: true`; nothing was moved. Its
  grep search entry is corrected accordingly.
