## Worker report

The delivery states `AlgebraicGeometry.ProEtale.CondensedRing.integralExtensionByZero`
in `Sheaf.Paper.IntegralExtensionByZero`. Its only theorem proof is `sorry`.
The mathematical statement is unchanged. A new definition node `def-sfb-integral-derived-coefficient-data` owns canonical aliases
for the coefficient ring, derived category, and reduction functor. The aliases delegate
without copying the existing `DerivedNakayama` constructions. The item now cites this
definition node in `stmt_deps`; `det-pe-derived-nakayama-resolution` remains only a
proof dependency.

Source checked: the current main-20261015 blueprint file
`sec-six-functors-basics/sk-cor-int-compactness-ii/sk-cor-int-compactness-ii-extension-zero.md`.
Its three clauses are exactly the item's statement. The resolved stage-1 maintenance
note was read: it asks to retain the statement and the split proof route. The module's
docstring carries all five current proof steps, including the derived product-existence
input and the product/kernel argument for preservation of every existing small limit.

Hypothesis and clause correspondence:

- The implicit prime ell is `(l : ℕ) [Fact l.Prime]`.
- The integral coefficient extension is `(E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. This permits any finite
  extension, rather than just a chosen embedded finite subfield. Its integer ring is
  the canonical alias `integralCoefficientRing l E` (definitionally the recorded
  `DerivedNakayama.integerRing l E`): continuous functions on profinite
  sets with values in the spectral-absolute-value valuation ring. On X this is exactly
  `condensedRingObj (integralCoefficientRing l E) X`.
- The standing setting of `sk-def-sfb-dc-setting` is explicit: `(k : Type u) [Field k]`,
  `[Fact (ringChar k).Prime]` and `[Fact (ringChar k ≠ l)]` give characteristic p>0,
  p different from ell. Both schemes have `Over (Spec (.of k))`,
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on their structure maps.
  Thus they are separated of finite type over k. `j.IsOver` makes j a k-morphism.
- The specified quasi-compact open immersion is `(j : U ⟶ X)
  [IsOpenImmersion j] [QuasiCompact j]`. No nonemptiness, smoothness, or properness
  hypothesis is imposed.
- In clause 1, the exact module-sheaf extension is the dependency's
  `openImmersionLowerShriek`; `PreservesHomology` expresses its exactness. The
  triangulated exactness of its termwise derived descent is also stated as
  `Functor.IsTriangulated ...mapDerivedCategory`.
- All direct sums are `∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)`
  for the termwise derived functor. This is the fixed small coefficient universe.
- All existing small categorical limits are
  `PreservesLimitsOfSize.{u + 1, u + 1}` for that same derived functor. This asserts
  preservation when a diagram has a limit, without an extra existence assumption
  or a claim that the ordinary derived category is complete.
- Commutation with reduction is `∀ n : ℕ, Nonempty (j_! ⋙ integralReductionFunctor X n ≅
  reductionFunctor U n ⋙ j_!)`. These are natural isomorphisms of functors, not
  merely objectwise isomorphisms. `integralReductionFunctor` is the canonical alias for the actual
  uncompleted derived tensor with the continuous finite quotient in degree zero,
  with its restricted integral action. The quotient is by the nth power of the
  chosen uniformizer ideal, rather than ell powers or a replacement coefficient ring.
- Clause 2 quantifies over every `K : DerivedNakayama.Derived l E U` and sends
  `constantModelBoundedConstructible (integralCoefficientRing l E) U K` to
  `constantModelBoundedConstructible ... X (j_!.obj K)`. This is the precise Dbc
  predicate recorded by `sk-def-sfb-constructible`; it uses bounded cohomology and
  finite constant scalar local models. No Tor-amplitude or completeness hypothesis
  is imposed on K.
- Clause 3 uses `CategoryTheory.localizingClosure` of those exact same Dbc predicates
  on U and X, and asserts the corresponding objectwise implication. In particular
  it is Loc(Dbc), with no substitution of Dctf or a complete derived subcategory.

Recorded dependency declarations read and used:

- `sk-def-sfb-dc-setting`: the setting and compactification interface in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and the
  bounded-constructible definitions. The theorem has the setting's explicit binders;
  no compactification is needed in the open-immersion statement itself.
- `sk-def-sfb-module-lower-shriek`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`,
  `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek`,
  its linearization, coefficient restriction, exactness instances, and adjunction.
  The full source and module docstring were read in the published side framework,
  as required by `coord/pefw-upstream-framework.md`; the derived open-immersion
  adjunction/descent source was also read.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `HasFiniteConstantLocalModel`, `IsConstantModelConstructible`, and
  `constantModelBoundedConstructible`. The definition source was read in full.
- `det-def-localizing-closure-existence`: `Sheaf.Paper.LocalizingClosureExistence`,
  `AlgebraicGeometry.ProEtale.localizingClosure_exists`, together with the imported
  `CategoryTheory.localizingClosure` intersection definition in
  `Sheaf.Paper.LocalizingClosure`. Their complete declarations/docstrings were read.
- `def-sfb-integral-derived-coefficient-data`: `Sheaf.Paper.IntegralDerivedCoefficientData`,
  `integralCoefficientRing`, `integralDerived`, and `integralReductionFunctor`; these
  aliases are the declarations used in the item signature.
- `det-pe-derived-nakayama-resolution`: `Sheaf.Paper.DerivedNakayamaResolution`,
  `integerRing`, `quotientRing`, `quotientModule`, `pullback`, `Derived`, and
  `reductionFunctor`. It remains a proof dependency only; its full resolution theorem
  and proof docstring were read. The underlying `Padic.coefficientExtensionUniformizer`,
  `coefficientExtensionIdeal` and `coefficientExtensionRing` were checked in their source.

All stated proof dependencies are imported privately, including the exact Mathlib
product/equalizer, exact-functor descent, adjoint-colimit, and sheaf-limit modules.
Statement dependencies are publicly exposed. There are no private notions, local
notations, file-local instances, extra axioms, or auto-bound variables/universes.

Edge cases checked against the definitions before writing:

- U empty, X empty, and K zero: extension is zero, reductions and both closure
  predicates contain zero; no `Nonempty` scheme hypothesis excludes these cases.
- j the identity: the two reduction composites agree with the identity extension;
  preservation statements specialize to those of the identity functor.
- Empty sums and empty limits are included. Sums use every I, and the limit class
  includes the empty category, hence the terminal/zero object.
- n=0 is included: the zeroth power ideal is the unit ideal and its quotient is zero;
  both reduction composites therefore vanish. n=1 is the residue-field reduction;
  all larger n are genuine uniformizer powers.
- Unbounded K is permitted in the exactness, sums, limits, reduction, and localizing
  clauses. Boundedness occurs only in the Dbc generator predicate.
- Both characteristic conditions are present; l=2 is permitted. No independent
  small test universe makes a hypothesis vacuous; small diagrams and coefficient
  objects use the established u+1 convention.

Searches for existing statements and definitions (2026-10-18):

- msearch LeanFinder: `extension by zero preserves integral constructibility
  localizing subcategory limits adic reduction`: eight hits concerning local
  cohomology and adic-completion extension; none states this theorem.
- msearch Loogle: `CategoryTheory.Limits.PreservesLimitsOfSize`: twelve hits,
  including the exact general preservation class and its universe documentation;
  no geometric extension-by-zero theorem.
- msearch grep: `openImmersionLowerShriek|extension by zero` in
  `Mathlib/CategoryTheory`: zero hits.
- msearch LeanSearch: `Extension by zero for a quasi compact open immersion preserves
  limits and bounded constructible integral complexes`: eight generic support,
  extension, affine-limit, and Noetherian quasi-compactness hits; none matches.
- `rg` in upstream `WeilConjectures/SixFunctors/ProEtale` for extension by zero,
  `openImmersionLowerShriek`, and integral coefficient names found adic-sheaf
  constructibility and abelian-sheaf extension APIs, without the combined module
  derived theorem. The prescribed grep for this item id in upstream had no match.
- `rg` in `lean/Sheaf` found the recorded ringed open product theorem, integral
  tensor theorem, and related `OpenImmersionLocalizing`,
  `OpenExtensionConstantModelConstructible`, and `CompletedExtensionZeroComparison`.
  Their source statements were read: the first concerns admissible Dctf generators,
  the second sheaves and their strata, and the third completed exchange under a
  cartesian square. None gives all three clauses of this integral Dbc theorem.
- Exact-name searches for `integralExtensionByZero` in Mathlib, upstream, and
  `lean/Sheaf` found no collision. Existing coefficient, reduction, constructibility,
  and localizing definitions are reused without copying them.

Validation: the initial statement elaborated in both sandbox and library mode with
only two long-line warnings. Formatting those lines initially exposed Lean's dot
continuation parsing; the class is now written with `Functor.IsTriangulated` and the
final application is wrapped at its argument. Final compilation and the prescribed
preflight/delivery results are recorded by the delivery tool. No disputed statement
or node fault was found.

## Second reading by Q35

I reopened the retained theorem module, the new alias module, and both node records.
The theorem has the same binders and seven conjuncts as the item: exactness and
triangulated descent, all Type (u+1) sums, existing limits of size (u+1,u+1), reduction
for every n, Dbc preservation, and the Loc(Dbc) implication. Each occurrence of the
coefficient ring, derived category, and reduction now goes through the canonical aliases.
The aliases reduce definitionally to the existing DerivedNakayama declarations and do
not duplicate their data. No hypothesis, edge case, or proof dependency was changed.

## New nodes

`def-sfb-integral-derived-coefficient-data` records the coefficient ring, ordinary
unbounded derived category, and derived reduction modulo the uniformizer-power quotient
used by the item. Its source is the coefficient setup in the blueprint item. Searches
found only the component declarations in `Sheaf.Paper.DerivedNakayamaResolution`, so the
module `Sheaf.Paper.IntegralDerivedCoefficientData` provides canonical aliases and no
second construction. The item cites this node in `stmt_deps`.

## Dependency modules

No dependency module repair was needed. The returned theorem dependency was not an
unusable interface; it was simply proof-only, so the new definition node supplies the
statement-level interface while the theorem remains in `proof_deps`.
