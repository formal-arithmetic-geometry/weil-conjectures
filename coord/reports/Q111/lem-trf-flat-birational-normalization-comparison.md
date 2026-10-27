## Worker report

The module `Sheaf.RingTheory.FlatBirationalNormalizationComparison` states
`RingTheory.flat_finite_birational_normalization_comparison`, with one whole-proof
`sorry` and no new definitions. The node is unchanged except for its `lean` record.
The theorem docstring reproduces all eight steps of the accepted proof, including
its flat-injection, tensor, localization, finite-integrality and integral-closure
inputs. Source read: Stacks `varieties.tex`, Tag 0C3V,
`lemma-normalization-same-after-completion`, especially its last two paragraphs.
The arbitrary-flat-base-change version is the agent-explicit calculation that the
node records; the source itself treats henselizations and completion. I also read
the current blueprint ancestor `lem-trf-local-term-locality` and its proof under
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/`.

Hypothesis and clause correspondence:

- Reduced commutative A and R: `(A : Type u) (R : Type v) [CommRing A]
  [CommRing R] [IsReduced A] [IsReduced R]`. The universes are independent.
- The ring homomorphism f is encoded by `[Algebra A R]`, and flatness is precisely
  `hf : (algebraMap A R).Flat`. Every ring homomorphism supplies this structure
  through `RingHom.toAlgebra`; this does not assume faithfulness or injectivity.
- A contained in B contained in Q(A): `B : Subalgebra A (FractionRing A)`.
  Mathlib's `FractionRing A` is the localization at `nonZeroDivisors A`, not a
  restriction to integral domains. Its structural map is injective for every
  commutative ring. Finiteness is exactly `[Module.Finite A B]`.
- C = B tensor_A R is written `R ⊗[A] B`, using Mathlib's standard base-change
  order. `TensorProduct.comm` gives the canonical commutation. Thus the node's
  `b tensor r` is written `r ⊗ₜ[A] b`; i is `algebraMap R (R ⊗[A] B)` and sends
  r to `r tensor 1`, corresponding to `1 tensor r` in the node's order.
- Preservation of all regular elements is the existential `hregular :
  nonZeroDivisors A ≤ (nonZeroDivisors R).comap (algebraMap A R)`.
- The canonical phi is the actual Mathlib construction
  `IsLocalization.map (FractionRing R) (algebraMap A R) hregular`. The first
  conjunct gives its fraction formula for every numerator a and every regular
  denominator t. The second conjunct says every ring homomorphism psi agreeing
  on A equals that map. The formula at denominator 1 also gives the extension
  property, so existence, extension, uniqueness, and the fraction formula are
  all present without choosing an arbitrary comparison map.
- The existential `j : R ⊗[A] B →ₐ[R] FractionRing R` has exactly the pure-tensor
  formula phi(b)*r. Its R-algebra type includes preservation of multiplication,
  one, addition and the structural R map. Consequently ji is the localization
  map R to Q(R). `Function.Injective j` and the following
  `Function.Injective (algebraMap R (R ⊗[A] B))` are both explicit.
- `J : FractionRing (R ⊗[A] B) ≃+* FractionRing R` is the total-fraction
  isomorphism. The conjunct quantified over all c says its composite with the
  C localization map is j. This specifies the canonical isomorphism by the
  localization universal property, independently of any denominator family.
- Integral closedness is exactly
  `IsIntegrallyClosedIn (R ⊗[A] B) (FractionRing (R ⊗[A] B))`. Under this
  hypothesis `j.range = integralClosure R (FractionRing R)` identifies C with
  the integral closure through the injective R-algebra map j. No prime-local
  substitute for this hypothesis is used.
- The last conjunction quantifies over every finite generating family:
  `n : ℕ`, `b : Fin n → B`, `a : Fin n → A`, `t : Fin n → nonZeroDivisors A`,
  with `Submodule.span A (Set.range b) = ⊤` and the displayed equality
  `b h = IsLocalization.mk' ... (a h) (t h)`. Using Fin n covers every finite
  family after reindexing; it includes n = 0.
- The regular element s is universally quantified with `s = ∏ h : Fin n, t h`.
  Taking the product in the non-zero-divisor submonoid retains its proof of
  regularity, and its underlying element is the required product in A.
- The next two conjuncts give injectivity of multiplication by f(s) on R and C
  as the two displayed `Function.Injective` propositions.
- `d : B →ₗ[A] A` satisfies `(d x)/1 = (s/1)*x` for every x. This explicitly
  states sB contained in A and defines the linear map b to sb, without selecting
  witnesses from a bare existence theorem in a definition.
- `dR : R ⊗[A] B →ₗ[R] R` is explicitly the composite of `d.baseChange R` and
  `TensorProduct.AlgebraTensorModule.rid A R R`. Thus it is the induced map,
  rather than an unconstrained linear map. Its next conjunct is precisely
  `dR (r tensor x) = f(d x)*r`, the node's `f(sx)*r` formula.
- The following two conjunctions are exactly `i(dR(c)) = f(s)c` and
  `dR(i(r)) = f(s)r`, with multiplication on C written as its R scalar action.
- The equation for j(c) is `IsLocalization.mk' (FractionRing R) (dR c)` with
  regular denominator f(s). Fractions use `mk'`, as division is not a field
  operation for general total quotient rings.
- The image inclusion in R[1/f(s)] is rendered by existence of a preimage
  `z : Localization.Away (algebraMap A R s)` under the canonical localization
  map from the powers of f(s) to all non-zero-divisors. That map is injective
  because its source denominators are regular; no alternative localization or
  arbitrary map replaces the subring inclusion.
- Finally, for all c and all regular tC of C, `ht : dR tC ∈ nonZeroDivisors R`
  is provided, and `J (c/tC) = (dR c)/(dR tC)`. The preceding i-dR identity
  identifies these entries with f(s)c and f(s)tC in the embedded R. Thus both
  the numerator-in-R and regular-denominator-in-R assertions, as well as the
  fraction formula, are explicit.

Dependency declarations read and used:

- `def-weil-pbc-flat-ring-map`: `Mathlib.RingTheory.RingHom.Flat`,
  `RingHom.Flat`, and `Module.Flat` in `Mathlib.RingTheory.Flat.Basic`.
- `def-weil-finitely-generated-module`: `Mathlib.RingTheory.Finiteness.Defs`,
  `Module.Finite` (top submodule finitely generated).
- `def-weil-module-base-change`: `Mathlib.LinearAlgebra.TensorProduct.Tower`,
  `LinearMap.baseChange`, and its pure-tensor formula; `TensorProduct`,
  `TensorProduct.mk`, and `TensorProduct.AlgebraTensorModule.distribBaseChange`
  give the recorded notion. The theorem uses `d.baseChange R` directly.
- `def-weil-pbc-integral-closure`:
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, `integralClosure`,
  `IsIntegral`, and `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosedIn`. I read these signatures and their docstrings.
- Proof-only leaf `lem-trf-flat-tensor-preserves-injection`:
  `Mathlib.RingTheory.Flat.Basic`, `Module.Flat.lTensor_preserves_injective_linearMap`.
- Proof-only leaf `lem-weil-pbc-ring-localization-universal-property`:
  `Mathlib.RingTheory.Localization.Defs`, `IsLocalization.lift` and
  `IsLocalization.ringHom_ext`; the statement uses its canonical `map`.
- Proof-only leaf `def-weil-pbc-module-tensor-product`:
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, `TensorProduct` and `TensorProduct.mk`,
  with `TensorProduct.lift` in Basic and the recorded tensor-map declarations.
- Proof-only leaf `lem-weil-pbc-finite-algebra-is-integral`:
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, `Algebra.IsIntegral.of_finite`.
  Its module is already a public statement dependency. All recorded proof modules
  are imported; there is no missing prerequisite or import cycle.

Edge cases checked mathematically before writing: A = 0 forces B = 0 and R = 0;
R = 0 is allowed independently, and all conclusions become the unique zero-ring
maps. An empty generating family forces B = 0 and hence A = R = 0; s is still
1 and all injectivity and fraction clauses hold. B = A gives C = R. No nontrivial
or domain instance was imposed, so reduced rings with zero divisors are allowed.
For the nonfaithful flat projection k × k to k, the product of nonzero component
entries remains regular in k, although the projection itself is not injective;
the theorem assumes no injectivity of f or phi. The integral-closedness clause is
conditional and does not assert normality for arbitrary finite B. No statement
fault, correction, new node, or dependency repair was needed.

Searches (all msearch service searches made with the prescribed wrapper):

- LeanFinder: "Flat base change of a finite subalgebra of the total quotient ring
  embeds into total fractions and has the same total quotient ring" returned eight
  hits including `Algebra.IsAlgebraic.isBaseChange_of_isFractionRing`, flatness of
  localizations, and `TensorProduct.toIntegralClosure_injective_of_flat`.
  I read the two closest source declarations: the former has domain/algebraicity
  hypotheses, and the latter has ambient tensor-product integral-closure codomain.
  Neither states the present result or its common-denominator clauses.
- Loogle: `TensorProduct, IsFractionRing` returned only
  `Ideal.eq_top_of_mk_tensor_eq_one`, about inverse invertible ideals.
- Mathlib grep in RingTheory:
  `([Ff]lat.*[Bb]irational|[Bb]irational.*[Ff]lat|[Tt]ensor.*[Ff]raction[Rr]ing|[Ff]raction[Rr]ing.*[Tt]ensor)`
  returned that same Picard-group result, not a matching theorem.
- LeanSearch: "A flat finite birational algebra has the same total ring of
  fractions after base change and is the integral closure if integrally closed"
  returned integral-closure characterizations, including
  `IsIntegralClosure.of_isIntegrallyClosed`, and the tensor integral-closure
  injection above; no whole-statement match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  flat/birational combinations, and total fraction/quotient phrases found
  `flat_integral_totalFractions` in `Sheaf.RingTheory.FlatIntegralTotalFractions`
  and `RingTheory.curve_normalization_completion` in
  `Sheaf.TraceFormula.CurveNormalizationCompletion`. Both were read in full.
  The former treats arbitrary integral B, omits the finite-generator/common-
  denominator formulas, and uses prime-local normality in its last clause.
  The latter specializes to completion of a local curve. Neither duplicates this
  statement. The proposed declaration name was searched in both trees and in
  `dag/lean_names_upstream.json`, with no match.

Validation: `scompile.py` is used for each compile; the final compiler and delivery
results are recorded below after the checks finish.

## Second reading by Q111

(Written by the maintainer's independent cc reviewer, 2026-10-24. The group's own
section said that no second worker was started, as the dispatcher forbids one, and
gave only the worker's own re-check. That re-check is kept at the end.)

Node clauses → Lean (`RingTheory.flat_finite_birational_normalization_comparison`):

1. A, R are reduced commutative rings: `[CommRing A] [CommRing R] [IsReduced A] [IsReduced R]`,
   with independent universes u, v. No domain, Noetherian or nontriviality instance. ✓
2. f flat [def-weil-pbc-flat-ring-map]: `[Algebra A R]`, `hf : (algebraMap A R).Flat`. ✓
3. Q(T) = S_T⁻¹T: Mathlib `FractionRing T` is the localization at `nonZeroDivisors T`
   for any commutative ring. ✓
4. A ⊆ B ⊆ Q(A), finite as an A-module: `B : Subalgebra A (FractionRing A)`,
   `[Module.Finite A B]` [def-weil-finitely-generated-module]. ✓
5. C = B ⊗_A R, i(r) = 1⊗r: `R ⊗[A] B` (order commuted, as the
   def-weil-module-base-change record notes), with i = `algebraMap R (R ⊗[A] B)`. ✓
6. f(S_A) ⊆ S_R: `∃ hregular`. φ is the canonical `IsLocalization.map`. Its fraction
   formula holds for all a and t, and it is unique among ring maps agreeing on A. ✓
7. j: an R-algebra map C → Q(R) with j(r⊗b) = φ(b)r (this pins j), and j is injective. ✓
8. i is injective. ✓
9. For every finite generating family (Fin n, span = ⊤, b_h = a_h/t_h) and every
   s = ∏ t_h (in the submonoid, so s is regular), these hold:
   - multiplication by f(s) is injective on R and on C (the R-action on C is
     multiplication by i(f(s))) ✓
   - sB ⊆ A: d : B →ₗ A with d(x)/1 = (s/1)x. d is unique because A → Q(A) is
     injective. ✓
   - d_R = rid ∘ d.baseChange R, the induced map (not an arbitrary one), with
     d_R(r⊗x) = f(d x)r ✓
   - i(d_R c) = f(s)c and d_R(i r) = f(s)r ✓
   - j(c) = d_R(c)/f(s) ✓
   - j(C) ⊆ R[1/f(s)], as a preimage under the canonical map
     Localization.Away f(s) → Q(R) ✓
   - J(c/t) = d_R(c)/d_R(t) with d_R(t) ∈ S_R. Under the identification by i,
     d_R(c) is f(s)c and d_R(t) is f(s)t, which is the node's
     (f(s)c)/(f(s)t) with both entries in R. ✓
10. Q(C) ≅ Q(R) compatibly with C: `J : FractionRing C ≃+* FractionRing R` with
    J ∘ (C → Q(C)) = j. This determines J by localization uniqueness, so J is
    canonical. ✓
11. If C is integrally closed in Q(C) [def-weil-pbc-integral-closure], then j(C) is the
    integral closure: `IsIntegrallyClosedIn C (FractionRing C) → j.range = integralClosure R
    (FractionRing R)`. ✓

Edge cases:
- A = 0 forces B, C and R to be 0.
- R = 0 alone is allowed.
- n = 0 forces B = 0.
- B = A gives C = R.
- The flat projection k×k → k is not injective; no injectivity of f is assumed.
- Rings with zero divisors are allowed.

All of these are covered by the statement as written.

Searches and duplicates: `flat_integral_totalFractions`
(lem-per-flat-integral-total-fractions, Q29) assumes integral B. Its conclusion
uses prime-local normality, and it has no common-denominator clauses. It is a
different DAG theorem, not a duplicate definition. No definitions are introduced,
so H4 does not apply. The item node is unchanged apart from its `lean` record, which
matches the side-live node. No citer has this item as a stmt_dep.

The docstring gives the source (Stacks 0C3V), `(blueprint: ...)` and all eight proof
steps. The proof is a whole `sorry`. `lean.statement` matches the file verbatim.

Mismatches: none in the Lean statement. The only change is this section.

Worker's own re-check (kept): Compiler repairs only made the target non-zero-divisor
subtype and submonoids explicit; they did not change a mathematical hypothesis or
conclusion. Final validation: the delivery dry run passed on 2026-10-24: `OK (dry run)`;
server preflight and both the sandbox and library-path compiles passed with no
unexpected warnings.
