## Worker report

Status: The complete statement module, including its recorded proof imports, compiles
cleanly. The theorem proof is intentionally `sorry` at stage 2. Nothing was pushed.

The module `Sheaf.Paper.ConstructibleHomComparison` reuses the landed canonical map
`AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom` and states
`AlgebraicGeometry.ProEtale.isIso_comparisonDerivedHom_of_constructible` with `sorry`.
The existing map transposes inverse derived tensor comparison followed by pulled-back evaluation.
The earlier private helper was removed after locating this newly landed definition.
The sole helper instance supplies finiteness of the canonical lifted positive-level coefficient
ring by the recorded coefficient finiteness theorem; it assumes no extra mathematical data.

Hypothesis and clause correspondence:

- The fixed finite-field datum is `(D : WeilConjectures.FiniteFieldDatum.{u})`; its `D.k`
  is the fixed algebraic closure of its finite base field.
- The coefficient conventions are `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`, a field
  `E : Type u` with `Algebra (Padic l) E` and `FiniteDimensional (Padic l) E`, and
  `(n : ℕ+)` (equivalently a natural number with `1 ≤ n`). The ring is exactly `Padic.coefficientExtensionRing l E n`.
  Its canonical `ULift` implements the established etale coefficient universe convention.
- The scheme over the algebraic closure is `(X : Scheme.{u})` with
  `[X.Over (Spec (CommRingCat.of D.k))]`.
- Finite type is the conjunction of `LocallyOfFiniteType` and `QuasiCompact` instances
  on `X ↘ Spec (CommRingCat.of D.k)`. No separatedness assumption is added.
- The two complexes are `K M : Etale.DerivedCategoryModule (ULift …) X`.
- Bounded constructibility of K is `_hK`, using the recorded
  `Etale.DerivedCategory.isBoundedConstructible` predicate.
- Finite Tor amplitude of K is `_hTor : ∃ a b : ℤ, a ≤ b ∧
  Etale.DerivedCategory.hasTorAmplitudeIn … X a b K`.
- Bounded constructibility of M is `_hM`, using the same recorded predicate. M has no
  Tor-amplitude hypothesis.
- The conclusion is `IsIso (siteComparisonEvaluationHom (ModuleCat …) X K M)`, for the specific evaluation
  transpose. Its source is inverse image of RHom(K,M), and its target is RHom of the
  two inverse images. The exact inverse-image functor is represented by its termwise
  derived functor, canonically identified with its total left derived functor by
  `Functor.leftDerivedFunctorIsoMapDerivedCategory`.
- The adjunction convention evaluates `K tensor RHom(K,M)`; tensor symmetry identifies
  this transpose with the source's `RHom(K,M) tensor K` convention.

Recorded statement-dependency interfaces read:

- `Sheaf.AlgebraicGeometry.EvaluationHomSiteComparison`:
  `AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom`. Its definition applies the
  tensor-Hom `homEquiv` to the inverse of
  `derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso` followed by pullback of
  the etale tensor-Hom counit. The new dependency id is the already landed
  `def-sf-evaluation-hom-site-comparison`; no dependency node is restated or edited.

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and the imported coefficient-ring construction.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparisonModules`, the canonical adjunction for the existing
  `ProEtale.comparisonUpperStar`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`.
- `Sheaf.Paper.FiniteCoefficientFlatModel`: the four recorded finite-coefficient flat-model
  declarations, especially its etale finite-Tor condition and coefficient lift convention.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses` and its representative comparison.
  The module uses the existing fixed-coefficient `Etale.derivedHom` and `ProEtale.derivedHom`
  closed structures on the ModuleCat-valued sheaf encoding, not a second Hom definition.
  In the fixed-module encoding these are the closed derived Hom structures used by the
  landed `siteComparisonEvaluationHom`: they are right derived homotopy internal Hom,
  constructed by the K-injective resolution adjunction in
  `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed`. The sheaf equivalence
  between fixed-module sheaves and modules over the constant ring preserves tensor and
  Hom; uniqueness of right adjoints identifies the two encodings. No second definition
  of RHom is introduced in this delivery.

The proof docstring reproduces all seven node-proof steps. The recorded proof modules are
listed in the node and docstring; their imports are deferred because the shared overlay
defect below prevents importing them together. Mathlib proof leaves are imported through
the public statement modules. The only unstated proof
node is `lem-weil-finite-duality-site-comparison`; it has neither lean nor mathlib_match.
This is a proof prerequisite, not a missing statement prerequisite: its theorem is not
needed to type the canonical map, and it is not restated in this delivery.

Edge cases checked mathematically: X need not be separated; the empty scheme and empty
finite affine cover are permitted; K or M can be zero; the Tor interval may consist of a
single integer; no finite-Tor condition is imposed on M; n=0 and l=p are excluded exactly
by the global conventions; site object and morphism universes remain distinct.

Searches:

- `msearch.py leanfinder`, query `etale proetale derived internal Hom canonical comparison
  finite Tor constructible`: eight unrelated light-condensed/condensed declarations;
  no exact theorem. The repeated query in this attempt returned eight scheme/site
  declarations, also no match.
- `msearch.py loogle`, query `"ihomComparison"`: zero hits.
- `msearch.py grep`, query `leftDerivedTensorComparison|ihomComparison`, subdirectory
  CategoryTheory: zero hits in Mathlib.
- `rg` in upstream WeilConjectures and side Sheaf sources for Hom/comparison names,
  `internalHom`, `derivedHom`, and the blueprint id: the upstream
  `ProEtale.DerivedCategory.nonempty_iso_mapDerivedCategory_derivedHom` is explicitly
  only existence of an isomorphism. It does not assert invertibility of this specific
  canonical arrow and cannot be used as an exact existing statement match.
- Side upstream `CategoryTheory.Functor.leftDerivedTensorComparison` provides the canonical
  tensor comparison with the representative counit normalization. The landed
  `EvaluationHomSiteComparison` module already combines this with evaluation; it is
  reused directly, without a new comparison-map definition.
- The current blueprint at
  `main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/` has the same statement as
  the node's older source, including the specific arrow. No statement correction made.

## Validation

On 2026-10-16, importing the proof-only chain through
`Sheaf.CategoryTheory.LocalizedModuleExactIndependent` failed in the overlay at
`Sheaf.Paper.RingedProjectionRestriction:491:5` with unknown constant
`AlgebraicGeometry.ProEtale.lowerStar`. Removing that import reached the same defect
through `CompletedTowerDirectImage`; adding the other proof imports also triggered a
duplicate declaration from the side `FiniteCoefficient.UpperLowerStar.Defs` overlay.
The public statement imports compile cleanly. This is a framework overlay fault, not a
statement elaboration fault; no live source or tool was modified.

A fresh scompile.py check of scratchpad/StatementProbe.lean passed in sandbox (3.9 seconds)
and library (4.2 seconds) positions, without warnings. Its module/declaration docstrings,
helper instance, exact theorem signature and sorry proof are byte-for-byte identical to
the complete delivery; it retains all public statement imports and the finite-type import,
omitting only private proof imports. This diagnoses the failure but does not replace the
required complete-module validation.

The node changes only lean and adds the already landed definition dependency
`def-sf-evaluation-hom-site-comparison`. Its signature is verbatim from the file; JSON
uses indent 1, Unicode and a final newline; every Lean line is at most 100 characters;
autoImplicit is false. No new node, dependency restatement, statement correction, or
new second-reading result is claimed here. A fresh complete-module `scompile.py` run passed in both
sandbox and library positions, and the required `deliver2.py --no-push` dry run passed
its compile and preflight checks.

## Earlier second reading (a previous round; superseded)

I independently opened the stage-2 node, its blueprint source, all seven recorded statement dependencies, and `lean/Sheaf/Paper/ConstructibleHomComparison.lean`.

The node introduces a finite-type scheme (X) over the fixed algebraic closure \overline{\\mathbf F}_q), the etale-to-pro-etale comparison \nu_X, a first input (K\in D^b_{ctf}(X_{\\Et},A_{E,n})), and a second input (M\in D^b_c(X_{\\Et},A_{E,n})). Its conclusion is that the canonical comparison from pulled-back derived internal Hom to derived internal Hom of the two pullbacks is an isomorphism.

* The fixed field datum is rendered by `(D : WeilConjectures.FiniteFieldDatum.{u})`; `D.k` is its fixed algebraic closure and `Spec (CommRingCat.of D.k)` is the base.
* The coefficient assumptions are rendered by `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`, `E : Type u` with `Field`, `Algebra (Padic l) E`, and `FiniteDimensional (Padic l) E`, and `(n : ℕ+)`. The coefficient ring is exactly `Padic.coefficientExtensionRing l E n`; the `ULift.{u + 1}` is the recorded etale module-universe convention. The local finite instance is real data supplied by `Padic.finite_coefficientExtensionRing` and `n.property`.
* The scheme and finite-type hypotheses are rendered by `(X : Scheme.{u}) [X.Over (Spec (CommRingCat.of D.k))]`, `[LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]`, and `[QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]`. No separatedness assumption is added, matching the source reduction by a finite affine cover.
* The two objects are rendered by `K M : Etale.DerivedCategoryModule (ULift ... ) X`.
* (K\in D^b_{ctf}) is rendered by `_hK : @Etale.DerivedCategory.isBoundedConstructible ... X K` together with `_hTor : ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn ... X a b K`. This is exactly bounded constructibility plus finite Tor amplitude; the interval is existential as in the node convention.
* (M\in D^b_c) is rendered by `_hM : @Etale.DerivedCategory.isBoundedConstructible ... X M`. There is no additional Tor-amplitude hypothesis on (M).
* The conclusion is rendered by `IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} (ULift ...)) X K M)`. The opened declaration `siteComparisonEvaluationHom` has source the comparison pullback of etale derived Hom and target pro-etale derived Hom of the two comparison pullbacks, and is defined by the tensor--Hom transpose of pulled-back evaluation through the canonical derived tensor comparison. Thus it is the specific arrow in the node, rather than an arbitrary isomorphism of endpoint objects.

No mismatch was found. In particular, the Lean does not impose separatedness, does not impose Tor amplitude on (M), does not replace the canonical map by a mere `Nonempty` isomorphism, and preserves the distinct site universes. The empty scheme and empty affine cover, zero (K) or (M), a singleton Tor interval (including (a=b)), and arbitrary positive (n) are covered. The excluded cases (n=0) and (l=p) are excluded exactly by the coefficient conventions. The finite-type hypotheses permit the empty scheme.

I searched the current Mathlib and project sources with LeanFinder/LeanSearch, Loogle, and `rg` for etale/pro-etale derived internal-Hom comparisons, `RHom`, `derivedHom`, `ihomComparison`, and the blueprint id. Hits were unrelated generic Hom or site declarations. The upstream theorem `ProEtale.DerivedCategory.nonempty_iso_mapDerivedCategory_derivedHom` only asserts existence of some isomorphism and is not an exact match for the canonical arrow, so the new statement module is required. The landed dependency `Sheaf.AlgebraicGeometry.EvaluationHomSiteComparison` was opened and reused; no duplicate notion or private replacement was introduced.

The file compiles cleanly with `python3 /home/ubuntu/weil-launcher-nt/scompile.py Q69 thm-sf-hom-comparison-constructible lean/Sheaf/Paper/ConstructibleHomComparison.lean`; only the intended `sorry` proof remains. The node copy keeps its `lean.statement` byte-for-byte equal to the theorem signature and records the already-landed `def-sf-evaluation-hom-site-comparison` dependency.


## Second reading by Q69

I reread the node `dag/nodes/sec-six-functors/thm-sf-hom-comparison-constructible.json`,
the source place in
`literature/blueprint/master/blueprint/sec-six-functors/sk-thm-sf-hom-ctf/`, every
recorded statement dependency, and
`lean/Sheaf/Paper/ConstructibleHomComparison.lean`.

The node's objects, hypotheses, and conclusion match the Lean signature item by item:

1. The global finite-field datum and its fixed algebraic closure are rendered by
   `D : WeilConjectures.FiniteFieldDatum.{u}` and the base
   `Spec (CommRingCat.of D.k)`, using `FiniteFieldDatum` from `FiniteFieldFiber`.
2. The coefficient conventions are rendered by `l : ℕ`, `[Fact l.Prime]`,
   `_hl : l ≠ D.p`, a field `E : Type u` with `Algebra (Padic l) E` and
   `FiniteDimensional (Padic l) E`, and `n : ℕ+`; the coefficient is exactly
   `Padic.coefficientExtensionRing l E n`, lifted canonically with `ULift.{u + 1}`.
3. The finite-type scheme over the algebraic closure is rendered by
   `(X : Scheme.{u}) [X.Over (Spec (CommRingCat.of D.k))]`, with exactly the two
   finite-type classes `[LocallyOfFiniteType (X ↘ ...)]` and
   `[QuasiCompact (X ↘ ...)]`. No separatedness class is added.
4. The first and second derived objects are the two arguments
   `K M : Etale.DerivedCategoryModule (ULift ... ) X`.
5. `K ∈ D^b_c` is rendered by `_hK :
   Etale.DerivedCategory.isBoundedConstructible ... X K` with the recorded finite
   coefficient instance.
6. The finite Tor condition on `K` is rendered by
   `_hTor : ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn ... X a b K`,
   preserving the existential interval and allowing `a = b`.
7. `M ∈ D^b_c` is rendered by `_hM` with the same bounded-constructibility predicate;
   no Tor-amplitude condition is imposed on `M`.
8. The conclusion is `IsIso (siteComparisonEvaluationHom (ModuleCat ...) X K M)`,
   the specific evaluation-transpose arrow supplied by the landed
   `def-sf-evaluation-hom-site-comparison` declaration. Its source and target are the
   comparison pullback of derived internal Hom and derived internal Hom of the two
   pullbacks, respectively, so it is not an arbitrary isomorphism or a mere
   `Nonempty` assertion.

The source and Lean cover the empty scheme and empty affine cover, zero `K` or `M`, a
singleton Tor interval, and all positive `n`. The excluded cases `n = 0` and `l = D.p`
are excluded by the stated coefficient conventions. Site object and morphism universes
remain distinct; no universe equality or extra finiteness/separatedness hypothesis was
introduced.

I searched with `msearch.py` using fresh LeanFinder and Loogle queries for derived
internal-Hom/site-comparison results, and with `rg` across Mathlib, the upstream
`WeilConjectures` sources, and the project `Sheaf` sources for comparison/Hom names.
The hits were generic condensed internal-Hom or tensor-comparison declarations. The
upstream `ProEtale.DerivedCategory.nonempty_iso_mapDerivedCategory_derivedHom` only
asserts existence of some isomorphism and does not match this canonical arrow. The
landed `siteComparisonEvaluationHom` declaration was opened and reused directly, so no
second definition was introduced.

No mismatch was found and no file or node correction was needed. The complete module was
compiled with `scompile.py` in both sandbox and library positions; it completed cleanly
with only the intentional theorem `sorry`.

