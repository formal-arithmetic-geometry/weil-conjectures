## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedFunctorTruncationStabilization` states
`AlgebraicGeometry.isIso_rightDerivedFunctor_lowerTruncation_step`, with proof `sorry`.
It introduces no definitions. The item node changes only in `lean`.

Source read: https://stacks.math.columbia.edu/tag/08D4, proof of (2), the successive
truncation triangle and the stabilization conclusion. The local literature checkout does
not contain `perfect.tex`, so the cited Stacks page was opened directly. The stabilization
step itself uses only additivity and the uniform vanishing hypothesis; product preservation
is needed later in that proof for the derived limit, not for this statement.

Hypotheses and clauses, individually:

- A scheme X: `(X : Scheme.{u})`, using the recorded `AlgebraicGeometry.Scheme`.
- The category Mod(O_X): `SheafOfModules.{u} (moduleRings X.toRingedSpace)`, exactly
  the carrier used by the dependency `schemeDerivedCategory`, with Mathlib's existing
  category and abelian instances. No alternative `X.Modules` category instance is chosen.
- F from Mod(O_X) to Ab: the explicit functor binder into `AddCommGrpCat.{u}`.
- Additivity: `[F.Additive]`. No left-exactness hypothesis is imposed.
- With right derived functors RF and R^p F: the existing unbounded
  `F.rightDerivedFunctor` and `F.rightDerived p`. The `HasDerivedCategory` binders
  specify the two localizations, and `Abelian.HasKInjectiveResolutions` and
  `HasInjectiveResolutions` supply the resolution infrastructure required by these
  definitions. These are the standard existence data implicit in having the right
  derived functors on module sheaves; no acyclicity or preservation assumption on F
  is introduced. The unbounded RF restricted to bounded-below truncations computes
  the same RF as the bounded-below construction used in the node's proof.
- Integer N >= 0: `(N : ℕ)`, with explicit coercion to ℤ in the bound. Natural numbers
  parametrize exactly the nonnegative integers, including zero.
- Every quasi-coherent module M: `∀ (M : SheafOfModules ...), M.IsQuasicoherent → ...`.
- Every p >= N: `∀ p : ℕ, N ≤ p → ...`; R^p has nonnegative indexing, and N >= 0.
- R^p F(M) = 0: `IsZero ((F.rightDerived p).obj M)`, categorical vanishing of that
  abelian group, not equality to an arbitrarily chosen zero representative.
- E in D_QCoh(O_X): `(E : schemeDerivedQCohCategory X)`. Its `.obj` is the underlying
  derived object and its membership includes quasi-coherence in every integer degree.
- Every integer i and n: `(i n : ℤ)`; n is not restricted to a natural-number tower.
- n >= N - i: `(hn : (N : ℤ) - i ≤ n)`.
- E_n = τ>=(-n)E, and E_(n-1) = τ>=(-(n-1))E: the source and target of
  `DerivedCategory.TStructure.t.natTransTruncGEOfLE (-n) (-n + 1) ...`, applied to
  `E.obj`. The identity `-n + 1 = -(n - 1)` gives exactly the stated target.
- Canonical transition: Mathlib's `natTransTruncGEOfLE`, whose composite with the
  truncation projection equals the next truncation projection, not an arbitrary map.
  `Int.le_add_one (le_refl (-n))` supplies only the unconditional ordering of the cutoffs.
- The induced H^i(RF(E_n)) -> H^i(RF(E_(n-1))) is an isomorphism: apply
  `F.rightDerivedFunctor.map`, then `DerivedCategory.homologyFunctor AddCommGrpCat i`,
  and assert `IsIso` of this precise composite-induced morphism.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`;
  full structure signature and docstring read in the pinned source.
- `def-weil-sheaf-of-modules-category` (Mathlib leaf):
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`, `SheafOfModules`, and its category;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`, its existing Abelian instance.
- `def-sp-left-exact-additive` (Mathlib leaf):
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`, `CategoryTheory.Functor.Additive`;
  `Mathlib.CategoryTheory.Abelian.RightDerived`, `CategoryTheory.Functor.rightDerived`.
  Its left-exact clause is not a hypothesis of this item, whose source says additive.
- `def-pc-derived-category`: `Sheaf.AlgebraicGeometry.DerivedCategory`,
  `AlgebraicGeometry.schemeDerivedQCohCategory`, built from `schemeDerivedCategory` and
  `schemeDerivedQCohProperty`; their entire declarations/docstrings were read.
- `def-sbc-standard-tstructure-derived-category` (Mathlib leaf):
  `Mathlib.Algebra.Homology.DerivedCategory.TStructure`, `DerivedCategory.TStructure.t`;
  `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE`, `TStructure.truncGE` and
  `TStructure.natTransTruncGEOfLE`, with their signatures/docstrings read.
- RF is the existing `CategoryTheory.Functor.rightDerivedFunctor` in
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`; its complete
  definition and assumptions were read. This is used directly, not redefined.
- Quasi-coherence uses the existing `SheafOfModules.IsQuasicoherent` in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`, already used by D_QCoh.

Edge cases checked before writing: N = 0 forces both endpoint indices into the assumed
vanishing range even at n = N-i; equality is allowed. Both i and n can be negative.
For zero E and for the empty scheme all terms vanish and the conclusion is consistent.
No boundedness hypothesis is placed on E: its lower truncations are bounded below.
For an object concentrated in degree -n, the endpoints are R^(i+n)F(M) and
R^(i+n+1)F(M), verifying the shift signs and inclusive cutoff. The object universe u
is arbitrary and the two localization morphism universes are explicit and independent.
No disputed statement or node correction was needed.

Searches for an existing statement (all through the prescribed tools unless noted):

- `msearch.py leanfinder`: "right derived functor lower truncation cohomology stabilizes
  under uniform vanishing bound"; eight hits concerning isGE/isLE and complex truncations,
  none the derived-functor stabilization assertion.
- `msearch.py loogle`: "CategoryTheory.Functor.rightDerived, truncGE"; no hits,
  unknown identifier truncGE in the online index.
- `msearch.py grep`: "truncGE.*rightDerived|rightDerived.*truncGE"; no Mathlib hits.
- `msearch.py leansearch`: "right derived functor cohomology stabilizes on lower
  truncations under cohomological dimension bound"; unavailable, Internal Server Error.
  No mathematical conclusion is drawn from this unavailable search.
- `rg` of the source's WeilConjectures and landed lean/Sheaf for the item id,
  "truncGE.*rightDerived|rightDerived.*truncGE": no matching statement.
- `rg` of `dag/lean_names_upstream.json`, source WeilConjectures and lean/Sheaf for
  "isIso_rightDerivedFunctor_lowerTruncation_step": no collision.
- Source-file searches found the unbounded RF definition and the canonical truncation
  transformations; the landed RightDerivedFunctorTruncationIso module concerns upper
  truncations for left exact functors, so it does not state this node.

Validation: server single-file compilation via `scompile.py`, followed by the required
`deliver2.py --no-push` dry run. Only the named theorem's proof is postponed.

## Second reading by H1

I reread the node statement against the source place (Stacks Project, Tag 08D4,
proof of (2)) and matched each item to the Lean signature.

- The scheme `X` is `(X : Scheme.{u})`; this is the Mathlib
  `AlgebraicGeometry.Scheme` required by the node.
- `Mod(O_X)` is exactly
  `SheafOfModules.{u} (moduleRings X.toRingedSpace)`, with the existing category,
  abelian, and derived-category infrastructure.  No extra geometric hypothesis is
  introduced.
- `F` is the explicit functor from that category to `AddCommGrpCat.{u}` and
  `[F.Additive]` is the sole functor property.  The Lean binders for both derived
  categories, K-injective resolutions, and injective resolutions provide the data
  used by `F.rightDerivedFunctor` and `F.rightDerived`; they do not add a
  left-exactness, product-preservation, or acyclicity assumption.
- `N : ℕ` represents the source's integer bound `N >= 0`; `hvan` quantifies over
  every quasi-coherent module, every `p : ℕ` with `N ≤ p`, and states categorical
  vanishing `IsZero ((F.rightDerived p).obj M)`.
- `E : schemeDerivedQCohCategory X` is the required QCoh derived object.  The
  integers `i n : ℤ` and `hn : (N : ℤ) - i ≤ n` have the source quantifiers and
  inequality, including equality cases.
- `natTransTruncGEOfLE (-n) (-n + 1)` applied to `E.obj` is the canonical map
  `τ≥(-n)E → τ≥(-(n-1))E`; `Int.le_add_one (le_refl (-n))` supplies only its
  cutoff ordering.  Mapping it first by `F.rightDerivedFunctor` and then by
  `DerivedCategory.homologyFunctor ... i` gives precisely the induced map
  `H^i(RF(E_n)) → H^i(RF(E_(n-1)))`, and the conclusion asserts `IsIso` of that map.

The edge cases are covered: `N = 0`, negative `i` and `n`, equality in the bound,
the zero object, and the empty scheme introduce no excluded case.  The universe of
`X` is arbitrary, while the two localization universes are explicit.  The lower
truncation tower is available for every integer `n`, so no hidden boundedness or
nonempty-index assumption occurs.

I searched Mathlib, `WeilConjectures`, landed `lean/Sheaf`, and the upstream-name
index with the truncation/right-derived terms and the proposed declaration name;
the only hits were generic truncation or derived-functor infrastructure.  The
prescribed LeanFinder/Loogle/grep searches likewise found no statement with this
content (LeanSearch was unavailable).  Thus this is a new statement node and its
recorded declaration is not an existing duplicate.

No mismatch was found, so no source, hypothesis, quantifier, or conclusion was
changed.  The module compiled with `scompile.py`; its only postponed proof is the
named theorem's `sorry`.
