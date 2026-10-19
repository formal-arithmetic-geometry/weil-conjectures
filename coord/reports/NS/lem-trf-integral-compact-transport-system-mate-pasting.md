## Worker report

Repair of the returned immutable head c835f1932537. The original saved packet was
inspected and dry-run first (743da9196d); it passed mechanical checks but retained the
mathematical defects in the return. The retained equation has now been restated using
the landed simultaneous-system operations. No natural-language node statement changes.
The node copy was checked against current main; only its `lean` is replaced.
The seven original `stmt_deps` are unchanged.

The module is `Sheaf.Paper.IntegralCompactTransportSystemMatePasting`, with primary
statement `WeilConjectures.FrobeniusExchange.integralCompactTransportSystemMatePasting`.
The one postponed theorem has proof `sorry`. All helper definitions have actual data;
there is no `IntegralCompactTransportSystemData` structure or free exchange/compositor.

Hypothesis and clause correspondence:

- `D : FiniteFieldDatum` supplies p, a, q, the finite field k₀ and its algebraic closure k.
  The hypotheses on its fields are precisely the landed finite-field convention.
- `l : ℕ`, `[Fact l.Prime]` and `hl : l ≠ D.p` supply the coefficient prime distinct
  from the characteristic. `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]` and
  `[FiniteDimensional ℚ_[l] E]` supply the finite coefficient extension. The coefficient
  systems use the dependency's valuation ring and canonical maximal-ideal powers;
  the uniformizer is not additional system data. Index n in the sequence site denotes
  the positive exponent n+1, retaining every A_n in the statement.
- `X₀ Y₀ : Over (Spec (.of D.k₀))`, each with `LocallyOfFiniteType` and `QuasiCompact`
  structure morphism, are exactly finite-type k₀-schemes. `f₀ : X₀ ⟶ Y₀` is over k₀;
  `[IsSeparated f₀.left]`, `[LocallyOfFiniteType f₀.left]`, `[QuasiCompact f₀.left]`
  express separated finite type. These hypotheses are stated even where the system
  operations also make sense more generally; no separatedness of Y₀ is imposed.
- `c₀ : Compactification f₀.left` is supplied over k₀. Its middle structure map is
  c₀.g followed by Y₀.hom, as in `zlCompactificationMiddle`. The functor is defined
  using `geometricCompactification D f₀ c₀`, not an independent compactification over k.
- `compactTransportPower` is `End.of (galois D W₀) ^ r`. The landed `galois` is literally
  id × Spec(geometric field Frobenius), also the hom of `D.geometricFrobenius W₀` and
  `geometricGaloisFrobenius`. This is the geometric Galois Frobenius in the node,
  not the scalar-extended q-power scheme Frobenius. Powers are scheme endomorphisms,
  with no assumption that they are morphisms over k.
- The categories are `coefficientSequenceDerived l E (D.geometricFiber W₀).left`:
  ordinary unbounded derived categories of strict semilinear quotient-ring systems
  on the small pro-étale vertical sequence site. `compactTransportSystemPull` is
  exactly `integralComparisonDerivedSequencePullback` along that Frobenius power.
  The middle scheme is the Z of the geometric compactification, so all three system
  categories use the same coefficients and descended geometry.
- `compactTransportSystemCompositor` is the inverse of
  `integralComparisonSystemComposition l E (g^1) (g^m)`, followed solely by the
  equality of scheme maps g^1 ≫ g^m = g^(m+1). Thus t^W_m is canonical, with source
  G_{W,m} ⋙ G_{W,1} in Lean's composition order. It cannot be independently changed.
- `compactTransportSystemFunctor` is exactly `systemDerivedOpen l E c.i ⋙
  systemDirect l E c.g`, the specified J_j then S_p. Exact open extension and total
  right-derived direct image are the dependency's operations on whole systems.
- `compactTransportSystemExchange` is exactly `systemCompactExchange`: proper
  `systemExchange` (the actual adjunction mate of `systemSquare`), then proper image
  of `systemOpenExchange`. The latter is the inverse of the actual inverse open mate.
  `compactTransportPowerSquare` merely constructs the required geometric square by
  iterating the landed square with `IsPullback.paste_horiz`; it supplies no new axiom.
- `∀ (m : ℕ), 1 ≤ m →` includes exactly all m≥1. The left side is whiskering t^Y_m
  by F, followed by E_{m+1}. The right side is whiskering E_m by G_{Y,1}, then E_1
  by G_{X,m}, then t^X_m by F. Associators only change parentheses. Both endpoints
  are F ⋙ G_{Y,m} ⋙ G_{Y,1} and G_{X,m+1} ⋙ F, rendering the displayed equation.
- Equality of natural transformations states the equation for EVERY C and its
  naturality simultaneously. No boundedness, constructibility, normalization,
  cartesianness or finite Tor-amplitude condition is imposed on C. Nothing is
  inferred from separate level evaluations.
- Applying levelwise sections when Y₀ = Spec k₀ preserves equality and gives the
  coefficient-complex tower equation. This functorial consequence is explained in
  proof step 6. For a general Y the equation is already in the system category over
  Y; no identification with RΓ_c is made.

Dependency declarations and imports:

- `Sheaf.Paper.TraceFormulaCoefficientConventions`: read
  `WeilConjectures.TraceFormulaCoefficientConventions` and its coefficientField and
  geometricBaseChange. Its FiniteFieldDatum and Padic coefficient conventions are used;
  the finite-level constructible category is not substituted for the unbounded systems.
- `def-weil-scheme-morphism-properties` is an aggregate node with no declaration or
  separate module. Use the recorded Mathlib `LocallyOfFiniteType`, `QuasiCompact`,
  `IsSeparated`, `IsOpenImmersion` and `IsProper`, available through the imports.
- `WeilConjectures.Compactification.Refinement`: read `Compactification.Refinement`
  and `Compactification` in its public Defs import. Use that same Compactification
  for c₀, with its open/proper fields and factorization, not a new record.
- `Sheaf.SixFunctors.SchemeFrobenius`: read schemeFrobenius,
  geometricGaloisFrobenius and geometricGaloisIntegralDerivedPullback. The actual
  geometric Galois map is the publicly imported `galois`/geometricFrobenius hom.
- `Sheaf.Paper.SemilinearDerivedSections`: read `semilinearDerivedSections` and
  `SemilinearDerivedSectionsData`; the actual coefficient-system specialization is
  the landed sequence-site calculus, used by the SystemOperationExchangeRealization
  definitions. This dependency is imported, without constructing a private calculus.
- `Sheaf.Paper.IntegralFinitePullbackComposition`: read the full general
  `integralTowerGeneralPullbackComposition`; the whole-system compositor is the
  recorded `integralComparisonSystemComposition` in IntegralComparisonSequenceSystems,
  localized from its section-normalized strict diagram compositor.
- `Sheaf.Paper.FrobeniusGeometricExchange`: read `frobeniusCommonStage` and the finite,
  integral and chosen-compactification wrappers. Use its `geometricCompactification`
  and public SystemOperationExchangeRealization definitions `systemDirect`,
  `systemDerivedOpen`, `systemExchange`, `systemOpenExchange`, `systemCompactExchange`.
- Proof imports include `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates`
  (`mateEquiv_whiskerTop_whiskerBottom`) and
  `Sheaf.SixFunctors.OpenTensorNormalization` (`openTensorNormalization`). Mathlib
  `mateEquiv_vcomp`, `unit_conjugateEquiv_symm`, `Adjunction.comp` and `mateEquiv` are
  public prerequisites. The docstring contains all six node proof steps, including
  inverse-image coherence, proper pasting, inverse-open pasting, the explicit naturality
  interchange, and the final unbounded/point consequence.

Edge cases checked: m=1 is included; r=0 in the helper definitions is the identity
scheme endomorphism and identity square. For p=id or j=id the very same mate words
are used. Empty schemes and empty opens remain allowed. The zero complex and arbitrary
unbounded complexes, with noninvertible quotient transitions, remain in the ambient
system category. Proper exchanges need not be invertible. The maintainer's End-category
counterexample no longer instantiates the theorem: neither E_1 nor E_2 is a free map,
and no free functor categories or compositors can be selected.

Searches retained from initial preparation: leanfinder on compact-support Frobenius
system mates, loogle on mate/pullback composition, Mathlib grep on
`mate.*pasting|pullback.*composition|compact.*transport`, and LeanSearch on system
compact transport: ordinary pullback/mate tools, no theorem for this whole construction.
Repeated for this repair:

- `msearch.py ... leanfinder 'The mate of a pasted square of functors is the composite
  of the mates with inverse image composition isomorphisms'`: eight hits, including
  mateEquiv_square, mateEquiv_hcomp, mateEquiv_vcomp and the two conjugate/mate
  compatibility lemmas. These are generic tools, not the node's statement.
- `msearch.py ... loogle CategoryTheory.mateEquiv_vcomp`: one exact generic hit.
- `msearch.py ... grep 'mateEquiv_vcomp|mateEquiv_hcomp'`: eleven generic Mathlib hits.
- `rg` of upstream WeilConjectures and project Sheaf for the theorem and new helper
  names, and upstream for the node id: no existing statement or conflicting name.
- `rg` for systemCompactExchange and integralComparisonSystemComposition found the
  actual landed constructions, reused here. Read the full signatures and docstrings.

No new nodes, `STATEMENT-DISPUTED`, or mathematical statement correction.

## Return repair

H3/H5: removed the unconstrained structure entirely. G, F, E_r and t are now defined
by the actual landed operations on concrete coefficient systems and Frobenius powers.
H4: imported all six available statement-dependency modules and both remaining
non-Mathlib proof modules; the seventh statement dependency is the property aggregate
with no module. No import has been dropped to conceal a timeout.
H3 geometry/coefficient omission: explicit finite-field, prime, finite coefficient field,
finite-type models, separated finite-type relative map, and k₀ compactification.
H8: the theorem docstring now gives the complete six-step DAG proof.

## Current-base self-check (2026-10-18)

The saved mathematical repair was retained. With the node and module open, each
return point was checked: Frobenius powers determine G; the descended compactification
determines F; systemCompactExchange determines E; and the inverse of the recorded
system compositor determines t. The End-category counterexample cannot choose E_2.
The explicit finite-field, coefficient and separated finite-type binders match the
node. The equation includes every m >= 1 and every unbounded input, and all six
proof steps are present. The signature in lean.statement is verbatim from the file.
No non-lean field differs from the current node. No second worker was started;
the maintainer supplies the independent review.

The prescribed initial dry run found two elaboration errors. Rewriting End.one_def
and Over.pullback_obj_left fixes the zero-power square; Category.comp_id closes the
expanded compositor equality. These change neither statement nor canonical data.
The saved SemilinearSystemModels instance repair is already in current main, so its
redundant module/node are omitted. The subsequent dry run rejected the documentation-only
IntegralCompactSupportCoefficientData repair as outside this item's prerequisite
closure; that module/node are also omitted. All six original statement-dependency
modules and both non-Mathlib proof-dependency modules remain imported. No dependency
interface is copied or modified. The original seven stmt_deps remain unchanged.

The final item-only scompile.py check is clean: sandbox 8.9 s, library 7.5 s.
The final deliver2.py --no-push check passed: a11660a87b. The packet contains only
the item module, item node and this report. All delivered Lean lines are <=100 columns.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
