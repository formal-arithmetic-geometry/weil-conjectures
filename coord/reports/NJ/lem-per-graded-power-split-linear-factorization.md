## Worker report

Module `Sheaf.RingTheory.GradedPowerSplitLinearFactorization` states
`Ideal.exists_graded_power_split_linear_factorization`, with proof `sorry`.
No definitions, dependency repairs, or statement corrections were needed.

Clause-by-clause correspondence:

- The fixed Noetherian commutative ring, ideal and nonnegative integer are
  `(R₀ : Type u₀) [CommRing R₀] [IsNoetherianRing R₀] (K₀ : Ideal R₀) (c : ℕ)`.
- The uniform constants occur as `∃ e N : ℕ, 2 * e + 1 ≤ N ∧`, before all
  varying rings, ideals, isomorphisms, exponents, modules and maps.
- Every varying Noetherian commutative ring and ideal is bound by
  `∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Ideal R)`.
- The unital graded ring isomorphism is
  `E : associatedGraded K ≃+* associatedGraded K₀`, together with equality
  of the images of the degree-j homogeneous pieces for every `j : ℕ`.
  These pieces are exactly the ranges of `DirectSum.of (associatedGradedPiece K) j`.
  Equality of ranges includes preservation by the inverse, and a degree-preserving
  bijection already implies this equality; no extra graded hypothesis is imposed.
- `∀ (n : ℕ), N ≤ n →` is the threshold; `R ⧸ K ^ n` is precisely `R_n`, and
  `n - e` is `s`. Since `n ≥ N ≥ 2e+1`, natural subtraction agrees with the
  integer expression and `s ≥ 1`, `s ≤ n`.
- `M : ModuleCat.{v} (R ⧸ K ^ n)` and `[Module.Finite (R ⧸ K ^ n) M]`
  give an arbitrary finite module. Module and both ring universes are explicit
  and independent. Bundling includes every ordinary module.
- `r : ℕ` and `d : M →ₗ[R ⧸ K ^ n] (Fin r → R ⧸ K ^ n)` give the specified
  map to the rank-r free module. For a finite index set, the function module
  is the usual finite direct sum, including rank zero.
- The splitting hypothesis quantifies over `a : (K ^ c : Ideal R)` and asks
  for `h : (Fin r → R ⧸ K ^ n) →ₗ[R ⧸ K ^ n] M` with
  `h.comp d = Ideal.Quotient.mk (K ^ n) (a : R) • LinearMap.id`.
  Thus it is exactly `h_a d = ā id`, with the same fixed differential `d`.
  There is no injectivity assumption or global choice of splittings.
- The source quotient `K^n/K^(2n)` is represented by
  `(K ^ n).map (Ideal.Quotient.mk (K ^ (2 * n)))`, the image ideal in the
  quotient ring. The target is the corresponding image of `K^(n-e)` modulo
  `K^(2*(n-e))`. These are the same quotient modules by the elementary
  first isomorphism theorem, not larger ambient quotient rings.
- Both are used with their canonical multiplication action of R. The source
  is killed by `K^n` since `K^n K^n = K^(2n)`. The target is killed by `K^n`
  since `n ≥ s` gives `K^n K^s = K^(n+s) ⊆ K^(2s)`. Hence R-linear maps
  from modules over `R/K^n` to these image ideals are EXACTLY R_n-linear maps
  for the induced action. `ModuleCat.restrictScalars (Ideal.Quotient.mk (K ^ n))`
  supplies the canonical R-action on M; the function module already has its
  canonical R-action. There is no arbitrary scalar action binder.
- The equation `v d = ρ u` is given on representatives: for all `x : M` and
  `y : R`, `mk_(K^(2n)) y = (u x).val` implies
  `mk_(K^(2s)) y = (v (d x)).val`. Every value of u has a ring representative,
  and `2s ≤ 2n` makes its reduction independent of representative. Such a y
  automatically lies in `K^n`: the source value is in the image of `K^n`,
  and the difference from a representative in `K^n` lies in `K^(2n) ⊆ K^n`.
  Thus this is exactly the specified canonical ρ, with no chosen or arbitrary
  map and no additional conclusion. Surjectivity of the quotient map shows
  conversely that this equation is equivalent to the linear-map equality.
- No completeness, nonzero, properness, or characteristic assumption appears.

Dependencies read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, whose docstring
  identifies being Noetherian as a module over itself with all ideals being FG.
- `WeilConjectures.RingTheory.AssociatedGradedRing`: `Ideal.associatedGradedPiece`
  is the submodule quotient `K^j/K^(j+1)`; `Ideal.associatedGraded` is their
  direct sum with the published canonical commutative ring structure.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, finite generation
  of the top submodule, as required by `def-weil-finitely-generated-module`.
- Mathlib's `ModuleCat.restrictScalars` in
  `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings` supplies the standard
  restriction of scalars, whose docstring and implementation were read.
- The proof dependency `lem-per-graded-near-projective-hom-divisibility` has
  no Lean record or module at preparation time, so it has no import yet.
  It is used only in the natural-language proof, copied step by step into
  the theorem docstring. Its future module can be added as a plain proof import.

Sources opened: `literature/stacks-project/local-cohomology.tex`, section-uniform
(0GA6), lemma-factor-hom (0GAC), and the finite-sum composition in
lemma-bound-two-term-complex (0GAD). The statement uses the module formulation
and larger loss already recorded in the accepted node, avoiding the source's
Ext subscript issue. The proof records the D=0 threshold separately.

Edge cases checked before writing and in the second pass:

- `c=0`: the scalar 1 splitting is required; the module is a retract along d,
  so arbitrary u extends. The theorem permits e=0 and requires N≥1.
- `e=0`: s=n and ρ is the identity, including its representative equation.
- `r=0`: the free function module on `Fin 0` is the zero module. The theorem
  retains this case, rather than assuming a positive rank or an injection.
- `M=0`: all maps and required equations have their canonical zero interpretation.
- `K=⊥`: for n≥1 both quotient image ideals are zero, so the conclusion holds.
- `K=⊤`, including the zero ring: R_n and the two image ideals are zero;
  no Nontrivial instance excludes these cases.
- n=0 never satisfies n≥N because N≥2e+1. No extra restriction was added.
- Distinct ring/module universes and arbitrary characteristic are preserved.

Searches (the wrapper also recorded the queries/results in searches.jsonl):

1. LeanFinder: "Uniform linear factorization through an ideal power split
   differential with bounded adic precision loss controlled by the associated
   graded ring". Eight hits: completion lifts, transition identities, and
   adic completion approximation results; none states this finite-precision
   factorization through the fixed differential.
2. Loogle: `"LinearMap", "quotient"`. Twelve hits, principally the second
   isomorphism theorem `LinearMap.quotientInfEquivSupQuotient` and its map
   lemmas; no uniform extension result.
3. Mathlib grep through msearch: `near.?projective|powerSplit|gradedPowerSplit|factor_hom`
   in RingTheory. Zero hits.
4. LeanSearch: "A finite module with scalar splittings through a fixed finite
   free module admits uniform extension of linear maps to quotients of ideal
   powers after bounded precision loss". Eight hits: finiteness of Hom,
   splittings of surjections, local projectivity criteria, and Baer extensions;
   none has the statement of this node.
5. `rg` on `lean/WeilConjectures` and `lean/Sheaf` for
   `gradedPowerSplit|power.split|near.projective|lem-per-graded-power-split-linear-factorization`
   found only an unrelated purity-composition docstring. Searches for ideal
   power quotients and degree-preserving associated graded equivalences found
   existing quotient constructions and associated graded maps, reused here.
6. Exact declaration-name search in `dag/lean_names_upstream.json`, Mathlib,
   WeilConjectures, and Sheaf found no existing name or theorem.

Validation: scompile.py compiled both the sandbox and intended module cleanly;
no warning or error remained. Only the named theorem has a postponed proof.
No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by NJ

The dispatcher prohibits starting other agents and supplies the maintainer's
independent delivery review. This section records an honest second pass by the
same worker, not an independent agent review. I reopened the node and module
and matched every binder, inequality, splitting hypothesis, and output clause
above. The first compile found Lean interpreting `a : K ^ c` as exponentiation
of the coerced Type; annotating `(K ^ c : Ideal R)` repaired the elaboration
without changing the mathematics. The second compile was clean. In particular
I checked that R-linearity here is equivalent to the stated R_n-linearity,
that the equation uses the same d, and that all representatives, including
ones differing by K^(2n), have the required canonical reduction. No changes
to the node's statement or dependencies are necessary.
