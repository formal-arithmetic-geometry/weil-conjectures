## Worker report

The module `Sheaf.Paper.NoetherianStratifiedModelProductEmbedding` states
`AlgebraicGeometry.ProEtale.noetherian_stratified_model_product_embedding`.
Its proof is `sorry`. The six preceding declarations are real specializations and
index constructions belonging to this product construction; none chooses data from
an unproved existence result. No additional node or dependency repair is needed.
The original statement and every original dependency and proof step are unchanged.

The previous attempt's stage-1 “already split and reviewed” refusal does not require
a new split: this is the stage-2 Lean statement of that already reviewed split.
The preserved sandbox had no module or node packet when this attempt began.

Hypotheses and clauses, in the node's order:

- The fixed scheme bound is `Scheme.{u}`, with morphisms in universe `u` and
  scheme codes in `Type (u + 1)`. The larger universe is `u + 1`, as in the
  published pro-etale framework. `Scheme.FiniteLocallyClosedStratification X`
  is itself in `Type (u + 1)`: this is the node's H, with no quotient or choice
  of isomorphism representatives. `StratifiedModelIndex X I : Type (u + 1)`
  is exactly its dependent sum of finite dependent label products, the node's J.
  These universe annotations express membership in the larger universe directly;
  no vacuous Small hypothesis or redundant Small conjunct is introduced.
- `X : Scheme.{u}`, `[CompactSpace X]`, and `[IsLocallyNoetherian X]` render
  respectively the scheme, quasi-compactness without a separation condition,
  and local Noetherianity. No reducedness, nonemptiness or separatedness is assumed.
- `(l : ℕ) [Fact l.Prime]`, `(E : Type u) [Field E] [Algebra (Padic l) E]`,
  and `[FiniteDimensional (Padic l) E]` render the prime and finite field extension.
  `integralModelCondensedCoefficients l E` is precisely the recorded condensed
  valuation ring, with the spectral absolute value topology. The abbreviation
  `integralStratifiedModelModules` uses `condensedRingObj` to pull this coefficient
  ring from the point, and uses the existing internal module category `Mod`.
- `LocallyClosedModelDomain X` is the subtype of bounded schemes T with
  `∃ a : T ⟶ X, IsImmersion a`. Thus the supplied families have exactly the
  domain requested in the statement. An immersion is only an existential proof;
  the family does not depend on a chosen immersion into X. Proof irrelevance
  identifies its eligibility proofs. `I : LocallyClosedModelDomain X →
  Type (u + 1)` gives the arbitrary small label sets, and `F : ∀ T, I T →
  integralStratifiedModelModules l E T.val` supplies the arbitrary modules.
  There is no finite-generation, local-model, or constructibility hypothesis on F.
- The recorded `Scheme.FiniteLocallyClosedStratification` supplies `n`, the
  domains, immersions, local closedness, disjoint images, and coverage. The helper
  `stratificationModelDomain h s` uses its actual domain and immersion only to
  establish eligibility. `StratifiedModelIndex` is `Σ h, ∀ s : Fin h.n, I (...)`.
- `stratifiedModelFactors l E X I F j s` is exactly the specified
  `CondensedRing.lowerStar` of the labelled module along the actual stratum
  immersion. `∃ c : Fan ..., Nonempty (IsLimit c) ∧ ...` supplies the product
  P_j and its actual product projections for every j. This is an existence
  assertion with the universal property; it is not an arbitrary-map hypothesis.
- `integralStratifiedModelSections` is the functor of the dependency's
  `sectionModuleEquivalence`, followed by the existing `SheafOfModules.evaluation`.
  For every pro-etale V, `Function.Bijective (fun x s ↦ ...map (c.π.app ⟨s⟩) x)`
  identifies sections of P_j with the product of the factor section modules.
  The map is the tuple of the actual linear projection maps. Thus it is the
  module product comparison, not an arbitrary bijection of sets. Naturality of
  the projection sheaf morphisms gives the product restrictions. All these
  section carriers are in `Type (u + 1)` by the section functor's ModuleCat
  universe, so the displayed formula includes the requested section-size bound.
- `(j.1.n = 0 → IsZero c.pt)` states the zero empty product explicitly.
- The final universal quantifiers range over every internal R_X-module M and
  every tuple `φ s : (CondensedRing.upperStar ...).obj M ≅ F ... (j.2 s)`.
  They assert `∃ f : M ⟶ c.pt, Mono f ∧ ...`. Each projection equation reads
  `f ≫ c.π.app ⟨s⟩ = (CondensedRing.upperStarLowerStarAdjunction ...).unit.app M ≫
  (CondensedRing.lowerStar ...).map (φ s).hom`. This is exactly the specified
  unit followed by direct image of φ_s. No arbitrary adjunction or unit is used.
  The product universal property ensures that the displayed components determine
  this arrow uniquely, so the existential map is the node's canonical u.
- The final “equivalently” sentence follows directly from these quantifiers:
  given h and the local representation witnesses, choose each label and its
  isomorphism, form `j = ⟨h, labels⟩`, and apply the theorem. Conversely such a
  j and tuple φ give exactly the representation witnesses. There is no
  unconditional nonemptiness assertion for J.

Dependency declarations read and used (full signatures and relevant docstrings
were opened in the local published sources):

- `def-weil-size-convention`: the recorded metatheoretic convention, implemented
  by the explicit universe levels just described; it names no Lean declaration.
- `Mathlib.Topology.Defs.Filter`, `CompactSpace`;
  `Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, and its public imported coefficient
  constructions; these enter through the coefficient-ring module below.
- `Sheaf.Paper.IntegralModelSurjectiveClosedReflection`,
  `AlgebraicGeometry.ProEtale.integralModelCondensedCoefficients` and its
  `integralModelCondensedCoefficients_isCommMonObj` instance.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`, and the
  transported commutative monoid instances (publicly imported by UpperLowerStar.Defs).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`,
  `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar`, `upperStar`, and
  `upperStarLowerStarAdjunction`.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`,
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`,
  `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence`;
  `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`
  (the latter is exactly Mathlib's sectionwise `SheafOfModules` category).

All stated proof dependencies are imported. The generic finite-lower-star source
is already publicly imported by the module-object functors. The plain proof imports
are `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits` (sectionwise limits),
`Sheaf.Paper.CartesianCoefficients`, `Sheaf.AlgebraicGeometry.NoetherianStratumDetection`,
and `Sheaf.CategoryTheory.JointAdjunctionModelEmbedding`. Their recorded declarations
are respectively `SheafOfModules.hasLimitsOfSize` and evaluation preservation,
`AlgebraicGeometry.ProEtale.cartesianCoefficients`,
`AlgebraicGeometry.Scheme.proEtale_isZero_of_stratum_cover`, and
`CategoryTheory.mono_pi_lift_adjunction_models`. The docstring preserves every
proof step and notes that finite locally closed strata on a Noetherian space
are constructible when using the detection theorem's older stratification encoding.
There is no import cycle.

Edge cases checked before writing:

- Empty label sets: stratifications requiring such a label have no point in J;
  nothing asserts J is inhabited for a nonempty X.
- Empty strata are permitted by the dependency structure and by our Fin index.
- For empty X, `n = 0` is admitted; its dependent label product is a singleton
  regardless of I. The product is zero, and every module is zero by empty-stratum
  detection, so the asserted map is monic. No `Nonempty` on X or the Fin index
  has been introduced.
- One identity stratum reduces the embedding to the given isomorphism under
  the identity adjunction. Zero modules and repeated scheme codes are allowed.
- Nonreduced strata and several immersion codes of the same domain are retained.
- The site object universe is `u + 1` and its morphism universe is `u`; the
  section equivalence is used with coefficient universe `u + 1`. No extra
  universe-equality hypothesis is imposed.

Searches for existing declarations (2026-10-22):

- `msearch.py leanfinder`, query “A finite stratification of a Noetherian scheme
  gives a monomorphism from every module sheaf to the product of pushforwards
  of its restrictions”: eight hits, including unrelated sheaf monomorphism and
  locally injective facts; no stratified model product assertion.
- `msearch.py loogle`, query `CategoryTheory.Adjunction, CategoryTheory.Mono`:
  six hits, including `Adjunction.unit_mono_of_L_faithful`; none supplies the
  geometric joint detection or labelled products.
- `msearch.py grep`, query `(stratif|stratum).*(product|mono)|joint.*adjunction|unit_mono`
  in Mathlib/CategoryTheory: 25 generic adjunction hits, no exact match.
- `msearch.py leansearch`, query “Small labelled finite stratifications and
  products of direct images of module sheaves with monic adjunction unit
  components”: eight generic pullback and unit hits, no exact match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for stratified products,
  model/product embeddings and joint adjunctions located the generic
  `JointAdjunctionModelEmbedding` dependency and the private proof
  `stratifiedModelsSmall` in `CoefficientHeartSmall`. The latter asserts essential
  smallness of finite-constant models, without this arbitrary-family product
  construction or sectionwise/empty-product clauses; it is not an existing match.
- `grep -rn` for the node id in `lean/WeilConjectures` found no declaration.
  `rg` for every newly declared full-name stem in both source roots and
  `dag/lean_names_upstream.json` found no name collision.

Validation: the prescribed `scompile.py Q36 <item> <module>` compiled the sandbox
and its final library-module form cleanly, respectively in 15.4 s and 9.3 s,
within the unchanged 60-second limit. No global build or live source mutation
was performed. Every variable and universe is explicitly bound, with
`set_option autoImplicit false`. The sole postponed proof is the named main
node theorem. There are no statement corrections or disputed assertions.

## Second reading by Q36

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
