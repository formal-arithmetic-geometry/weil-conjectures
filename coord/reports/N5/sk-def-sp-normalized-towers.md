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
an unrelated generalized localization instance. Two proof/construction specializations,
`spFiniteLevelSheafify` and
`spFiniteLevelLocallyBijective`, reuse the existing transport at the exact `u+1`
coefficient size; their priority prevents a universe metavariable in the broader
transport instance from remaining unresolved. No imported instance attributes are
changed. Additivity of the exact evaluation is obtained from its recorded finite-limit
preservation using Mathlib `Functor.additive_of_preserves_binary_products`. No source checkout or
shared repository file is edited. No statement fault or STATEMENT-DISPUTED claim is recorded.

## Second reading by N5

I independently opened the authoritative node JSON, the blueprint source named there, the
complete Lean module, and the six dependency records before checking this section. The item
is a definition node, so the source has no proof clauses to account for. The following checks
compare every clause of the node statement with the declarations in the module.

- The node's fixed data (prime `ell`, finite extension `E / Q_ell` with its field and finite
  dimensionality assumptions, and scheme `T`) is rendered by `l`, `Fact l.Prime`, `E`, the
  `Field`, `Algebra (Padic l) E`, `FiniteDimensional`, and `T : Scheme.{u}`. The module has no
  invertibility, Noetherian, separatedness, or nonemptiness assumption. The shared universe is
  the one required by the recorded finite-level interfaces and leaves the pro-etale site
  universes unchanged.
- The coefficient rings are the actual ell-power quotients of
  `Padic.coefficientExtensionIntegers l E` by `spEllIdeal l E ^ (n + 1)`. The natural index `n`
  therefore ranges over every positive paper level, and the coefficient sheaf used by the
  derived evaluation is the dependency's `spCoefficientRing` at that quotient. No uniformizer
  quotient is substituted for the stated ring; `spEllQuotientFinite` supplies only its finite
  instance.
- `spDerivedCoefficientTowers` is the ordinary `DerivedCategory` of the recorded abelian
  tower category, with `D.hasDerived`. The level object `C_n` is exactly
  `(spDerivedCoefficientEvaluation l E T D n).obj C`; this is the exact level evaluation from
  the coefficient-towers dependency, followed by its ordinary derived functor.
- The finite-level category predicate `spFiniteConstructibleTor` has the three required
  clauses: an integer interval outside which every homology object is zero, constructibility
  of every homology sheaf via `IsConstructibleProEtaleModuleSheaf`, and
  `HasFiniteProEtaleTorAmplitude`. Its `FullSubcategory` abbreviation retains exactly the
  ambient derived morphisms.
- `spConstructibleTorTowers` requires that predicate at every level and then chooses
  integers `a ≤ b` and `c ≤ d` before `∀ n`. Its two displayed conjuncts are respectively
  homology vanishing outside `[a,b]` and Tor amplitude in `[c,d]`, so the bounds are uniform
  in the level and independent of one another. The corresponding full subcategory is
  `spConstructibleTorTowerCategory`.
- `IsSpNormalizedTower` quantifies every `m ≤ n`, including `m = n`, and requires
  `IsIso ((D.reduction h).app C)`. The reduction is the dependency's canonical derived
  tensor reduction, with the correct direction from level `n` to level `m`; the equal-index
  case is its tensor unitor. The final predicate conjoins this condition with the uniform
  constructible/Tor predicate, and `spNormalizedConstructibleTorTowerCategory` is its full
  subcategory. No morphism condition is added beyond the ambient derived category.

I checked edge cases directly against these binders and predicates: the zero object and an
empty scheme satisfy the bounded conditions, level one is included by index zero, equal
indices use the identity reduction, independently chosen cohomological and Tor intervals
are allowed, and shifted levels with unbounded shifts fail the uniform bound. A tower with
individually admissible levels but zero transition maps is not made normalized by the
finite-level predicate. No clause of the node is omitted, and no stronger hypothesis or
weaker conclusion is introduced.

The module's imports are exactly the coefficient-tower abelian interface, constructible
pro-etale sheaves, and pro-etale Tor amplitude modules named by the dependencies. Every
declaration has the source and `(blueprint: sk-def-sp-normalized-towers)` docstring, all
variables and universes are explicit, and the only proof-valued declarations are Prop-valued
instance glue. A fresh `scompile.py` run for this file completed without diagnostics.
