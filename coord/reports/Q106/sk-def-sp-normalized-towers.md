## Worker report

The module `Sheaf.Paper.SmoothPurityNormalizedTowers` defines the finite-level Dctf
predicate and category, the uniformly bounded constructible finite-Tor tower predicate
and category, and their normalized full subcategory. It introduces no postponed theorem,
no new DAG node, and no dependency replacement. All definition bodies contain real terms.
The item JSON changes only `lean`.

Clause-by-clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`. The coefficient field is `(E : Type u)
  [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
  The scheme is `(T : Scheme.{u})`. This uses a common ambient size for the scheme
  and field, as do the recorded intrinsic constructibility and Tor interfaces;
  the actual small site retains objects in universe `u+1` and morphisms in `u`.
  There is no invertibility assumption on l on T, no Noetherian condition, and no
  nonemptiness assumption.
- The integer ring is the recorded `Padic.coefficientExtensionIntegers l E`.
  The actual A_(n+1) is its quotient by `spEllIdeal l E ^ (n + 1)`.
  This is an ell-power quotient, not a uniformizer-power quotient. The proof-valued
  instance `spEllQuotientFinite` obtains finiteness from the existing cofinality
  theorem and a surjection from a finite uniformizer-power quotient. The latter
  quotient is only used to supply a finiteness proof, never to replace A_(n+1).
- Natural-number index n represents positive paper level n+1, so all levels n>=1
  occur, including the first. The ring sheaf at that level is precisely the
  dependency's `spCoefficientRing`, definitionally the intrinsic constant ring
  used by `Scheme.proEtaleDerivedCategory T A_(n+1)`.
- The parameter `D : SpCoefficientTowersAbelian l E T` is the fully specified
  interface of the dependency lemma, whose existence is already stated by
  `sp_coefficient_towers_abelian`. It supplies the normalized equivalence with
  strict systems, exact evaluation, localization and canonical reduction. It is
  not an arbitrary family of level functors or maps. The definitions work for
  every such interface; no new existence claim or arbitrary map choice is made.
- `spDerivedCoefficientTowers` is `DerivedCategory (spCoefficientTowers l E T)`,
  using `D.hasDerived`. The level `C_n` is
  `(spDerivedCoefficientEvaluation l E T D n).obj C`, the dependency's exact
  evaluation followed by its ordinary derived functor.
- Finite-level finitely supported cohomology is the ordered integer interval in
  `spFiniteConstructibleTor`, with `IsZero (homologyFunctor _ i |>.obj K)` outside
  it. A finite subset of integers is bounded; conversely an integer interval is
  finite. The zero complex can use [0,0].
- Every cohomology sheaf is constructible by the conjunct quantifying over all
  `i : ℤ` and applying the recorded `Scheme.IsConstructibleProEtaleModuleSheaf`.
  Finite Tor amplitude is exactly `Scheme.HasFiniteProEtaleTorAmplitude T A K`.
  `spFiniteConstructibleTorCategory` is this predicate's `FullSubcategory`.
- `spConstructibleTorTowers` first requires finite-level membership for every n.
  It then quantifies `∃ a b c d : ℤ, a ≤ b ∧ c ≤ d ∧ ∀ n`, giving separate common
  cohomology and Tor intervals. The former is homology vanishing outside [a,b];
  the latter is the recorded `HasProEtaleTorAmplitude ... c d`. The bounds are
  outside the level quantifier, so shifting the bounds with n is not permitted.
  A common stratification across levels is not required.
- `IsSpNormalizedTower` requires `IsIso ((D.reduction h).app C)` for every pair
  `(m n : ℕ)` and `(h : m ≤ n)`. The dependency defines these maps using the
  composite quotient maps and characterizes them on all complex representatives;
  its identity formula is the tensor unitor, and its composition formula is the
  canonical derived tensor associator. Thus these are the specified reduction
  arrows over R_n, with target in the R_m-derived category.
- `spNormalizedConstructibleTorTowers` conjoins constructibility/uniform bounds
  with this normalization predicate. Both `spConstructibleTorTowerCategory` and
  `spNormalizedConstructibleTorTowerCategory` are `ObjectProperty.FullSubcategory`
  of the ambient ordinary derived tower category. Their morphisms are exactly
  its morphisms; they are not families of maps between derived levels.

Dependencies read and used:

- `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spEllIdeal`, `spCoefficientTowers`,
  `sp_coefficient_ideals_cofinal`; its ring sheaves and quotient reductions are
  the ones underlying the evaluation and reduction interfaces.
- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`: `SpCoefficientTowersAbelian`,
  `spCoefficientEvaluation`, `sp_coefficient_towers_abelian`, its abelian instance,
  and the structure's equivalence, exactness, localization and reduction fields.
- `Sheaf.Paper.ProEtaleConstructibleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleProEtaleModuleSheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`:
  `Scheme.HasProEtaleTorAmplitude`, `Scheme.HasFiniteProEtaleTorAmplitude`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory`, through the dependency imports.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, the cohomology node's explicit `mathlib_match`.
  The current primary recorded `pbcQbarCohomology` specializes to a different
  Qbar category, so the still-recorded generic Mathlib match is the applicable
  interface here. No replacement or duplicate cohomology definition is needed.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and Mathlib's
  `Ideal.pow_le_pow_right`, `Ideal.Quotient.factor`,
  `Ideal.Quotient.factor_surjective`, `Finite.of_surjective`, to assemble the
  proof-valued finiteness instance from recorded results.

Edge cases checked against the formulas: empty T and the zero tower are permitted;
positive level one is index zero; m=n is included and uses the recorded unitor;
common cohomological bounds do not force common Tor bounds to be the same interval;
levels A_n[-n] are excluded by the independent-of-n bound; zero transition maps
are not accepted merely because their levels are individually Dctf; no residue
characteristic, invertibility, or nonzero-coefficient assumption has been added.
The source's positive finite-stratum convention on the empty scheme is inherited
unchanged from the dependency.

Searches (logged by the prescribed msearch wrapper in searches.jsonl):

- LeanFinder, `Normalized constructible towers in a derived category with uniform
  cohomological and Tor amplitude bounds`: eight hits, on DerivedCategory IsGE,
  IsLE, t-structures and bounded representatives; no normalized tower definition.
- Loogle, `DerivedCategory, FullSubcategory`: no hits; the service reports unknown
  identifier FullSubcategory. This negative search was supplemented by source reads.
- Mathlib grep, `normalized.*tower|constructibleFiniteTor|Dctf|TorAmplitude`: three
  hits, all normalized traces for field towers, unrelated to module towers.
- `rg` in the upstream WeilConjectures tree and side-project `lean/Sheaf` for
  normalized towers and Dctf found related definitions. In particular the upstream
  `ProEtale.IsNormalizedTower` uses a functor into a derived fixed-R category and
  additional chosen level objects; it is not a full subcategory of D(Tow).
  The existing `NormalizedDVRTower` and bounded-constructible adic towers similarly
  have different ambient categories and coefficients, as the item's split review
  already records. These cannot be rebound as this item's definition.
- Upstream grep for `sk-def-sp-normalized-towers` found no recorded declaration.
  Searches of dag/lean_names_upstream.json, upstream sources and side-project
  sources for every new declaration name found no collision.

Compilation uses only scompile.py. The initial diagnostics were missing explicit
finiteness and exact-evaluation witnesses and ambiguous larger-coefficient instance
resolution. The explicit proof-valued instances and structure projections resolve
those issues. The cohomology and evaluation constructions explicitly pass the standard
localization on the intrinsic module category, preventing inference from selecting
an unrelated generalized localization instance. Two proof/construction specializations, `spFiniteLevelSheafify` and
`spFiniteLevelLocallyBijective`, reuse the existing transport at the exact `u+1`
coefficient size; their priority prevents a universe metavariable in the broader
transport instance from remaining unresolved. No imported instance attributes are
changed. Additivity of the exact evaluation is obtained from its recorded finite-limit
preservation using Mathlib `Functor.additive_of_preserves_binary_products`. No source checkout or shared
repository file is edited. No statement fault or STATEMENT-DISPUTED claim is recorded.

## Second reading by Q106

Independent reading by the maintainer's review service (reviewer sub-agent of L), replacing
the author's self-rereading that the delivery carried under this heading (delivery-errors
H11). The worker's own note said that it was only an author rereading; its content
(derived evaluation now passes D's additivity and exactness witnesses explicitly) is
retained in the worker report above. The delivered Lean module and the item record are
unchanged.

Node statement as a list, with the Lean that renders it and the verdict:

1. Prime l, finite E/Q_l, scheme T: `(l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
   [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})`. Correct; no
   l-invertibility, Noetherian or nonemptiness hypothesis. E and T share the universe u.
   This is forced by the recorded finite-level interfaces (`proEtaleDerivedCategory`,
   `proEtaleConstantRing`, `IsConstructibleProEtaleModuleSheaf`, `HasProEtaleTorAmplitude`
   all take `A : Type t` with `Y : Scheme.{t}`), and A_n is a quotient of O_E. The site
   universes are untouched: objects in u+1, morphisms in u. No mathematical case is lost
   because every finite E/Q_l has an isomorphic copy in any universe. With t = u the
   dependency's `spCoefficientCommRings` level is definitionally `proEtaleConstantRing T A_n`,
   as the compile confirms. Accepted, and stated in the worker report.
2. A_n = O_E/l^n, R_n, q_{n,m}: `Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^
   (n + 1)`, index n meaning level n+1. This is an l-power quotient, not a uniformizer-power
   one. q_{n,m} enters only through D.reduction, which is built on the dependency's
   transitions. Correct.
3. D(Tow(T,O_E)): `spDerivedCoefficientTowers` = `DerivedCategory (spCoefficientTowers l E T)`
   with D.hasDerived. Correct. Taking D as a parameter is the recorded interface of
   det-sp-coefficient-towers-abelian. Its equivalence, transitions and reduction are pinned
   by the HEq normalizations and `reduction_rep`; it is not an arbitrary map.
4. C_n: `spDerivedCoefficientEvaluation` is `Functor.mapDerivedCategory` of the dependency's
   `spCoefficientEvaluation`, with target the standard `proEtaleDerivedCategory T A_n`.
   Correct.
5. Finite-level Dctf: `spFiniteConstructibleTor`. "Finitely many nonzero H^i" is rendered as
   ∃ a ≤ b with H^i = 0 outside [a,b], which is equivalent. "All constructible" uses the
   recorded intrinsic predicate for every i, which is equivalent because zero cohomology
   sheaves are constructible. Finite Tor amplitude is `HasFiniteProEtaleTorAmplitude`.
   H^i is Mathlib `DerivedCategory.homologyFunctor` at `HasDerivedCategory.standard`, the
   cohomology node's `mathlib_match`; the recorded `pbcQbarCohomology` concerns a different
   Qbar category. Correct.
6. Tower Dctf: `spConstructibleTorTowers` requires every level in Dctf and
   ∃ a b c d, a ≤ b ∧ c ≤ d ∧ ∀ n, with vanishing outside [a,b] and
   `HasProEtaleTorAmplitude … c d`. The bounds are independent of each other and uniform in
   n, and the quantifiers are in the node's order. Correct.
7. Normalized: `IsSpNormalizedTower` asks for `IsIso ((D.reduction h).app C)` for all
   m ≤ n, m = n included. D.reduction has the right direction
   (C_n ⊗^L_{R_n} R_m → C_m, codomain the level-m derived category) and is the canonical
   reduction of clause (3). Correct.
8. Full subcategories with the ambient morphisms:
   `spConstructibleTorTowerCategory`, `spNormalizedConstructibleTorTowerCategory` and
   `spFiniteConstructibleTorCategory` are all `ObjectProperty.FullSubcategory`. Correct.

Edge cases: level 1 is index 0. m = n is included; there the reduction is the tensor unitor
by `reduction_identity`. Empty T, the zero tower and the zero ring are not excluded. Levels
A_n[-n] fail the uniform bound. Zero transitions are rejected by normalization. No residue
characteristic or invertibility assumption is made.

Other checks:
- Searches: `rg` over the side tree and upstream for the new names found no collision.
  Upstream `ProEtale.IsNormalizedTower` in TraceFormula/Adic.lean is a different notion: a
  functor into D(X,R) for a fixed R, with chosen levels.
- Not hollow: every def has real data. The proof-valued instances (`spEllQuotientFinite`,
  `spFiniteLevelSheafify`, `spFiniteLevelLocallyBijective`) are Prop-valued glue
  specializing recorded results. No theorem is proved.
- Docstrings carry the source and `(blueprint: sk-def-sp-normalized-towers)`.
- No line exceeds 100 characters, and all three imports are used.
- The item node differs from the base only in `lean`; `lean.statement` is verbatim.
- Compile: `nt_compile.py --json` on the delivered file gave exit 0 in 2.9 s with no
  diagnostics.
