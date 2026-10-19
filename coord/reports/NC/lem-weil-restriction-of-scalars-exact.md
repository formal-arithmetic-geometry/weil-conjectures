## Worker report

The module `Sheaf.Paper.RestrictionOfScalarsExact` states
`WeilConjectures.completedIntegralRestrictScalars_exact`, with its entire proof `sorry`.
It introduces no definitions. The node is unchanged except for `lean`.

Hypothesis and clause correspondence:

- The ambient prime characteristic `p` is `D.p` for `D : FiniteFieldDatum.{d}`,
  exactly the global datum required by the recorded completed-coefficient construction.
  The coefficient prime is `(l : ℕ) [Fact l.Prime]` and `hl : l ≠ D.p`.
- The finite extension `E/ℚ_l` is `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. Its valuation ring and chosen uniformizer are the
  dependency's `Padic.coefficientExtensionIntegers` and
  `Padic.coefficientExtensionUniformizer`; no independent coefficient ring is substituted.
- The scheme is `(Y : AlgebraicGeometry.Scheme.{t})`, with no smoothness, finite type,
  nonemptiness, or relation between the universes `d`, `t`, and `u` imposed.
- The positive integer exponent is represented by `(n : ℕ)` meaning exponent `n + 1`,
  exactly as in the dependency. Every positive exponent occurs, including exponent one
  at `n = 0`; exponent zero is not included.
- The stated reduction is precisely
  `completedIntegralCoefficientProjection l E Y D hl n`, built as the inverse-limit
  projection to `integralCoefficientSheaf l E Y n`. The statement uses the canonical
  projection through `completedIntegralRestrictScalars`; it does not substitute an
  arbitrary ring map or add surjectivity as a hypothesis. Its surjectivity is not
  needed for exactness.
- `completedIntegralRestrictScalars l E Y D hl n` has source
  `SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n)` and target
  `completedIntegralModuleSheaves l E Y D hl`. Thus these are the displayed finite
  coefficient and completed integral coefficient module-sheaf categories on
  `AlgebraicGeometry.Scheme.ProEt.topology Y`, with the target explicitly built from
  `completedIntegralCoefficientSheaf`, not from the discrete constant valuation ring.
- Exactness is the conjunction `PreservesFiniteLimits (...) ∧ PreservesFiniteColimits (...)`.
  These are abelian categories and restriction is already additive by Mathlib's instance,
  so this is equivalent to preservation of short exact sequences. There is no additional
  continuity, flatness, or sectionwise-surjectivity clause.

Dependencies read and used:

- `Sheaf.Paper.CompletedIntegralCoefficients`: the full signatures and docstrings of
  `WeilConjectures.integralCoefficientSheaf`, the transition/system/completion/projection,
  `completedIntegralModuleSheaves`, and `completedIntegralRestrictScalars` were read.
  Its transported sheafification instances supply the abelian structures at
  `max u (t + 1)`, retaining the small site's object universe `t + 1` and morphism universe `t`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` and its docstring establish the
  small pro-etale topology and constant ring sheaf convention. This statement concerns
  module sheaves, so the derived category itself is not inserted in its signature.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` and its additive instance; this is the Mathlib match
  for `def-pc-sheaf-restrict-scalars`, used by the completed-coefficient functor.
- Proof imports: `Mathlib.CategoryTheory.Sites.Sheafification`, including the finite-limit
  preservation instance for `presheafToSheaf`, represents the Mathlib dependency
  `lem-weil-pbc-sheafification-exact`; `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`,
  `CategoryTheory.moduleSheaves_colimits_forgetful`, supplies the recorded proof tool.
  Their interfaces and docstrings were read. All recorded proof dependencies are imported,
  either directly or as the same statement dependencies.

Edge cases: exponent one is included; the empty scheme is permitted; zero module sheaves
and zero exact sequences are permitted; the zero finite-limit/colimit shapes are included.
No equality between the site and coefficient universes is assumed. No assertion that a
sheaf epimorphism is surjective on every object's sections is made. The complete proof
plan in the docstring follows all three node steps: unchanged underlying abelian sheaf;
faithful forgetful preservation of kernels/cokernels/images; detection of the three zero
obstructions to short exactness.

Searches (2026-10-15):

- `msearch.py ... leansearch 'Restriction of scalars on sheaves of modules preserves exact sequences'`:
  service unavailable (Internal Server Error); recorded as unavailable.
- `msearch.py ... leanfinder 'Restriction of scalars along a morphism of sheaves of rings is an exact functor'`:
  eight hits, including `SheafOfModules.restrictScalars`, its additive instance, abelian
  structure, and forgetful finite-limit preservation; no completed-coefficient exactness theorem.
- `msearch.py ... loogle 'SheafOfModules.restrictScalars'`: four hits, the definition,
  additive instance, and underlying object/map formulas; no exactness theorem.
- `msearch.py ... grep 'restrictScalars.*(exact|Exact|preserves|Preserves)|(exact|Exact|preserves|Preserves).*restrictScalars' Algebra/Category/ModuleCat`:
  twenty hits, ordinary ModuleCat exactness and presheaf limit/colimit constructions,
  not exactness for this module-sheaf reduction functor.
- `rg` in the source repository for restriction/scalar/exactness combinations found
  `CategoryTheory.Sheaf.restrictScalars` for discrete constant rings, which is a different
  coefficient category. Its full definition and adjunction signatures were read.
  Searching the item id there found no hit.
- `rg` in `lean/Sheaf` found the existing completed-coefficient functor and several
  private scalar-restriction helper proofs for topological ringed spaces (e.g.
  `AffineAlgebraUpperTruncationEdge.restriction_properties`); none states this node.
  The topological helper interface was read and does not cover this pro-etale site.
- `rg` in Mathlib's sheaf `ChangeOfRings.lean` confirmed only the restriction definition,
  additive instance, and a locally-surjective Hom equivalence.
- `rg` in `dag/lean_names_upstream.json` for scalar-restriction exactness names found
  no completed-coefficient theorem. Searching the chosen new declaration name in
  Mathlib/project source and `lean/Sheaf` found no collision.

No new nodes, dependency repairs, statement corrections, or disputes are needed.

## Second reading by NC

Independently read the complete node, blueprint order 1456, Stacks
`sites-modules.tex`, Tag 03DA (`lemma-abelian`), and the surrounding kernel/cokernel
construction. The source assumes a ringed topos, not a Noetherian, finite-type,
nonempty, or flat situation. Also read each statement dependency's node and its
recorded declaration, the completed-coefficient construction through its projection
and restriction functor, and the two proof dependency interfaces.

Object, hypothesis, and conclusion checklist:

- Prime ell: `(l : ℕ) [Fact l.Prime]`; ambient characteristic and ell different
  from it: `(D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)`. Verdict: exact, using
  the global datum stipulated by the completed-coefficient dependency, not an
  assumption that Y is finite type over that datum.
- Finite extension of Q_ell: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. Verdict: exact. The recorded coefficient API
  supplies the valuation subring and chosen uniformizer, not an arbitrary ring.
  Read `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionIdeal`, and `coefficientExtensionRing`; the quotient is
  by the nth power of the principal uniformizer ideal. The uniformizer is fixed
  by the dependency convention, and replacing it by an associate leaves the ideal.
- Arbitrary scheme Y: `(Y : AlgebraicGeometry.Scheme.{t})`. Verdict: exact;
  no base morphism, smoothness, or nonemptiness instance is introduced.
- Integer exponent at least one: `(n : ℕ)` is exponent `n + 1` throughout the
  dependency. Verdict: exact bijective indexing of positive exponents.
- Completed ring, finite quotient ring sheaf, and canonical reduction:
  `completedIntegralCoefficientSheaf l E Y D hl` is the inverse limit of
  `integralCoefficientSheafSystem l E Y`; `integralCoefficientSheaf l E Y n`
  is the sheafification of the constant quotient ring at exponent `n + 1`;
  `completedIntegralCoefficientProjection ... n` is `limit.π ... (op n)`.
  Verdict: exactly the specified objects and map. The source's two-headed arrow
  describes this fixed reduction, not an independently quantified surjective map
  or a separate conclusion. No sectionwise-surjectivity claim is inserted.
- Restriction functor and its direction: `completedIntegralRestrictScalars ... n`
  is exactly `SheafOfModules.restrictScalars` along that projection, from
  `SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n)` to
  `completedIntegralModuleSheaves l E Y D hl`. Read Mathlib's definition and
  additive instance: only the action changes. Verdict: exact; the target is
  over the completed sheaf, never the discrete constant valuation ring.
- Small pro-etale site: both categories use `Scheme.ProEt.topology Y`.
  Read `proEtaleDerivedCategory` and the dependency's size-transport instances;
  the statement uses the underlying module categories, not derived categories.
  Verdict: exact. `ringedSiteModules` is a direct abbreviation of `SheafOfModules`.
- Exactness: `PreservesFiniteLimits (...) ∧ PreservesFiniteColimits (...)`.
  Verdict: exactly categorical exactness, equivalent here to preservation of short
  exact sequences because the functor is additive and the categories are abelian.
  All preceding parameters are universally quantified before this conclusion.

Edge cases: `n = 0` gives exponent one; exponent zero is outside the node. Empty
Y, zero sheaves, zero sequences, and empty finite diagram shapes are permitted.
The characteristic restriction is precisely ell different from D.p. Universes
`d`, `t`, and `u` are all declared and independent; the coefficient/module lift
`max u (t + 1)` retains site objects in `Type (t + 1)` and morphisms in `Type t`.
No variable or universe is unbound and no additional instance is assumed.

Independent searches (2026-10-15):

- LeanFinder via msearch: `Changing the ring of a module sheaf preserves kernels
  and cokernels`; eight hits, including `SheafOfModules.toSheaf`, category and
  abelian instances; no exactness theorem for the stated completed reduction.
- Loogle via msearch: `SheafOfModules.restrictScalars`; four hits, restriction,
  additive instance and object/map formulas, not this theorem.
- LeanSearch via msearch: `A functor retaining the underlying abelian sheaf is
  exact for restriction of ring actions`; unavailable (Internal Server Error).
- Independent rg of Mathlib's ModuleCat tree, slopmaster2 `WeilConjectures`, and
  project `lean/Sheaf` for exactness/preservation and scalar restriction, plus
  the exact imported pro-etale framework. Ordinary ModuleCat preservation and
  discrete-coefficient sheaf restriction are different categories. Opened
  `WeilConjectures/Algebra/Category/ModuleCat/Sheaf/RestrictScalars.lean`:
  its `CategoryTheory.Sheaf.restrictScalars` acts between `Sheaf J (ModuleCat R)`,
  not completed ring-sheaf modules. Opened the project's
  `DerivedRHomAlgebraModule.lean`: private finite-limit/colimit helpers require
  `[SmallCategory C]` with the category and ring/module universes all equal,
  and cannot be referenced outside their file; public instances specialize to
  sheaf algebras on topological spaces. Neither supplies this statement with
  its unequal small-pro-etale site universes. Framework matches
  likewise use constant-coefficient `Sheaf.restrictScalars`. No duplicate found.

No mathematical mismatch found; no Lean or node change was needed. No new nodes,
dependency modules, or statement correction are present. The single theorem has
only `sorry`, and its source/blueprint docstring carries each of the node's three
proof steps, including sheaf cokernels and faithful detection of zero objects.
The recorded `lean.statement` was checked verbatim against the file signature.

Compilation: scompile's `run_server` compiled the delivered file cleanly in
1.6 seconds, nice 19, two threads, hard 60-second per-file limit. The installed
scompile now defaults to a local overlay; to honor this item's server-only rule,
compilation and deliver2 are invoked with `scompile.run_many = scompile.run_server`
in the invoking Python process. No tool source is changed and no local compiler runs.
