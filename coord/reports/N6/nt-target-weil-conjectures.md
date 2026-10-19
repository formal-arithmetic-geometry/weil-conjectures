## Worker report

This delivery binds nt-target-weil-conjectures to the exact existing declaration
`AlgebraicGeometry.Scheme.weil_conjectures` in `WeilConjectures.Statement`
(`WeilConjectures/Statement.lean`, theorem beginning at line 92 in the reference checkout).
No Lean module is written: the standing one-definition/one-statement rule requires reuse.
The local upstream theorem has a postponed proof, which is permitted in stage 2. The current
source read with `scompile.py --source WeilConjectures.Statement` has the same signature and
an assembly proof. This record asserts a statement match, not an axiom or completion audit.
There is no repair note for this item.

Source checked: `lean/Comparator/Weil/Challenge.lean`, `WeilConjectures.weil_conjectures`;
`lean/Comparator/Weil/Definitions.lean`; and the current blueprint
`literature/blueprint/main-20261015/blueprint/sec-zeta-weil/sk-thm-weil-final/`
`thm-weil-final.md` and `thm-weil-final.proof.md`. The existing theorem has exactly the
challenge type, with its namespace changed to `AlgebraicGeometry.Scheme`.

Hypotheses and quantified objects, clause by clause:

- A finite field k: `variable {k : Type u} [Field k] [Finite k]`. Its cardinality is
  `Nat.card k`; the node's q is this expression, not an extra independent parameter.
- A scheme and its specified structure morphism: `{X : Scheme.{u}}` and
  `(f : X ⟶ Spec (.of k))`. The node explicitly names f, so this uses that morphism.
- A natural dimension: `(d : ℕ)`; no positivity hypothesis is added.
- Smooth of relative dimension d: `[SmoothOfRelativeDimension d f]`.
- Proper: `[IsProper f]`.
- Geometrically integral: `[GeometricallyIntegral f]`. There is no added choice of
  algebraic closure, geometric connectedness assumption, or characteristic restriction.
- The common family of integral polynomials: `∃ P : Fin (2 * d + 1) → Polynomial ℤ`.
  All three conjuncts use this same P, d, q and structure morphism.

The node's explanation of the zeta series is the definition used by the existing theorem:
`AlgebraicGeometry.Scheme.Hom.zetaSeries f` in `Weil.Definitions` (the comparator definitions
source). `FiniteField.galoisExtension k n` is
`(Polynomial.X ^ Nat.card k ^ n - Polynomial.X : Polynomial k).SplittingField`.
`Hom.fieldPoints f K` is the subtype of `g : Spec (.of K) ⟶ X` satisfying
`g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))`.
`Hom.pointCount f n` is `Nat.card (f.fieldPoints (FiniteField.galoisExtension k n))`,
including the specified zero junk value for an infinite set. The zeta definition is
`(PowerSeries.exp ℚ).subst (PowerSeries.mk fun n ↦
if n = 0 then 0 else (f.pointCount n : ℚ) / n)`.
The recorded point-count dependency's main name is its logarithmic derivative theorem;
its `lean.others` explicitly records `Hom.pointCount` and `Hom.zetaSeries`, whose complete
signatures/docstrings were read in the shared definitions source. The current source of
`WeilConjectures.ZetaSeries` was also read through `scompile.py --source`.
No alternative point-count model is introduced.

Conclusion (1) is `IsWeilFactorization (Nat.card k) d f.zetaSeries P` in
`Weil.Definitions`. Each field agrees with the node:

- `coeff_zero_eq_one : ∀ i, (P i).coeff 0 = 1` renders every constant coefficient.
- `apply_zero : P 0 = 1 - Polynomial.X` renders P_0 = 1-t.
- `apply_last : P (Fin.last (2 * d)) =
  1 - Polynomial.C ((q : ℤ) ^ d) * Polynomial.X` renders P_{2d} = 1-q^d t.
- `factorization` multiplies Z by the product over
  `Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Even i.1)` and equates it to the
  product filtered by `Odd i.1`. Every factor is
  `((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ)`, exactly the specified
  coefficientwise inclusion followed by polynomial-to-series inclusion.

Conclusion (2) is `WeilFunctionalEquation (Nat.card k) d P` in `Weil.Definitions`:
`∀ i, ((P i.rev).map (Int.castRingHom ℂ)).roots =
(((P i).map (Int.castRingHom ℂ)).roots.map fun z ↦ ((q : ℂ) ^ d * z)⁻¹)`.
`i.rev` has value 2d-i. Polynomial roots are a multiset, so the equality preserves
multiplicity, including repeated roots; it is not just an equality of sets.

Conclusion (3) is `WeilRiemannHypothesis (Nat.card k) d P` in `Weil.Definitions`:
`∀ i : Fin (2 * d + 1), ∀ z ∈ ((P i).map (Int.castRingHom ℂ)).roots,
‖z‖ = (q : ℝ) ^ (-(i.1 : ℝ) / 2)`.
This is the real exponent -i/2, not integer division. The inverse-root sentences of the
node restate these two clauses: constant term one excludes zero roots, and inversion
changes the root norm q^{-i/2} to q^{i/2} and the reflection to alpha ↦ q^d/alpha.

Dependency declarations and source signatures/docstrings checked:

- `def-weil-point-counts-zeta`: `WeilConjectures.ZetaSeries`,
  `AlgebraicGeometry.Scheme.Hom.X_mul_derivative_zetaSeries`; the recorded other names
  `Hom.pointCount` and `Hom.zetaSeries` in the comparator/shared `Weil.Definitions`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`, extending separated, universally closed and locally of
  finite type. Universal closedness supplies quasi-compactness, matching finite type.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.SmoothOfRelativeDimension`; its charts are standard smooth of the
  specified dimension. This is the dependency's recorded class, with no extra smoothness
  assumption required.
- `def-pc-geometrically-irreducible`: the `mathlib_match` explicitly supplies
  `AlgebraicGeometry.GeometricallyIntegral` in
  `Mathlib.AlgebraicGeometry.Geometrically.Integral`, quantifying over field-valued fibres.
- `def-weil-polynomial-ring` and `def-weil-polynomial-coefficient`:
  `Polynomial` and `Polynomial.coeff`, `Mathlib.Algebra.Polynomial.Basic`.
- `def-weil-formal-power-series`: `PowerSeries`,
  `Mathlib.RingTheory.PowerSeries.Basic`, the one-variable specialization of MvPowerSeries.
- `def-weil-polynomial-as-power-series`: `Polynomial.coeToPowerSeries.ringHom`,
  `Mathlib.RingTheory.PowerSeries.Basic`; its coefficient-preserving coercion is used.
- `def-weil-coefficientwise-ring-hom-map`: `Polynomial.map` in
  `Mathlib.Algebra.Polynomial.Eval.Defs`, with `PowerSeries.map` and
  `Polynomial.polynomial_map_coe` in `Mathlib.RingTheory.PowerSeries.Basic`.
- `def-weil-polynomial-root`: `Polynomial.eval₂`,
  `Mathlib.Algebra.Polynomial.Eval.Defs`; the predicates use roots of the mapped polynomial.
- `def-weil-root-multiplicity`: `Polynomial.rootMultiplicity`,
  `Mathlib.Algebra.Polynomial.Div`; `Polynomial.roots` and `Polynomial.count_roots` in
  `Mathlib.Algebra.Polynomial.Roots` realize the corresponding multiset convention.
- `def-weil-complex-absolute-value`: `Complex.instNorm` in
  `Mathlib.Analysis.Complex.Norm`, whose norm is the square root of normSq.
- `def-weil-real-power`: `Real.rpow` in
  `Mathlib.Analysis.SpecialFunctions.Pow.Real`; for positive q this is exp(log(q)*y).

Edge cases checked: d=0 gives one index, both endpoint formulas coincide because q^0=1,
with empty odd product and the usual zeta of a geometric point. Finite fields have q>1,
so real powers and the reciprocal-root interpretation have their intended positive base.
No finite field characteristic is excluded. The empty scheme cannot meet geometric
integrality; the statement does not silently add nonemptiness. Constant factors have
empty root multisets. Multiplicities are retained, zero roots are excluded by constant
coefficient one, and the n=0 point-count junk model is ignored by the zeta definition's
zero constant coefficient. The common universe u follows the exact comparator signature
and does not change its scope. No hypothesis, definition or statement correction is needed.

Searches for an existing declaration:

- `msearch.py ... leanfinder` with "Weil conjectures existence integral polynomial
  factorization functional equation Riemann hypothesis smooth proper geometrically
  integral finite field": eight unrelated matches; no exact theorem.
- `msearch.py ... loogle` with
  "IsWeilFactorization, WeilFunctionalEquation, WeilRiemannHypothesis": zero hits,
  unknown identifier IsWeilFactorization in that search service.
- `msearch.py ... grep` with
  "weil_conjectures|IsWeilFactorization|WeilFunctionalEquation|WeilRiemannHypothesis"
  in AlgebraicGeometry: zero Mathlib hits.
- Additional LeanFinder search "AlgebraicGeometry Scheme weil_conjectures smooth proper
  geometrically integral": smoothness/integrality results, no theorem.
- Additional Loogle query "SmoothOfRelativeDimension → IsProper → GeometricallyIntegral
  → ∃ P" returned a parser error; it is not evidence for absence.
- `msearch.py ... leansearch` with "Weil conjectures smooth proper geometrically integral
  scheme finite field integral polynomials functional equation Riemann hypothesis": eight
  generic proper/integral/smooth results, no Weil conjectures theorem.
- Direct `rg -n` in upstream `WeilConjectures/` found the exact theorem in
  `WeilConjectures/Statement.lean`, and usages in IntegralFactors and HasseWeil.
  `grep -rn nt-target-weil-conjectures` there had no hits.
- Direct `rg -n` in `lean/Sheaf` for weil_conjectures and the three predicates had no hits.
- The upstream name index also records `AlgebraicGeometry.Scheme.weil_conjectures`.
- `msearch.py ... grep weil_conjectures WeilConjectures` returned zero service hits;
  the direct source search above is the successful match and is decisive.

Only the item's `lean` field changes. There are no new nodes, dependency modules,
statement corrections, or disputed statements. The existing theorem and definitions
supply the exact comparator statement; no new theorem or definition should be added.

## Earlier second reading (a previous round; superseded)

I independently reopened the node and `WeilConjectures/Statement.lean`. The recorded
declaration is `AlgebraicGeometry.Scheme.weil_conjectures`; its normalized signature is
`theorem weil_conjectures (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f]
[GeometricallyIntegral f] : ∃ P : Fin (2 * d + 1) → Polynomial ℤ,
IsWeilFactorization (Nat.card k) d f.zetaSeries P ∧ WeilFunctionalEquation (Nat.card k) d P ∧
WeilRiemannHypothesis (Nat.card k) d P`, exactly the node's target. The finite field
binders are the source variables `{k : Type u} [Field k] [Finite k]`, and the scheme and
explicit structure morphism are `{X : Scheme.{u}}` and `f : X ⟶ Spec (.of k)`. The three
typeclass hypotheses render smooth relative dimension, properness, and geometric
integrality without additions. The existential uses one common `P` indexed by
`Fin (2*d+1)` and its conjunction has the node's factorization, root functional equation,
and complex-root Riemann hypothesis clauses in order. I checked `d = 0`, repeated and
constant polynomial roots, and finite fields of every characteristic; no mismatch or
statement correction was found. No file or node field other than `lean` was changed.

## Second reading by N6

I read the sandbox node and its `lean` record against the full comparator source
`lean/Comparator/Weil/Challenge.lean`, its imported `Definitions.lean`, the local
`WeilConjectures/Statement.lean`, and the current declaration returned by
`scompile.py --source WeilConjectures.Statement`. I also read the current blueprint
`main-20261015/.../sk-thm-weil-final/thm-weil-final.md` and its proof. The node's
source is the comparator challenge, not a Stacks tag; all surrounding assumptions
are the two `variable` lines immediately above that challenge theorem. No repair
note exists. This is an independent second reading of an existing-statement binding.

My object/hypothesis/conclusion checklist, with a verdict for every item:

1. Finite field k and q=#k: `{k : Type u} [Field k] [Finite k]` and `Nat.card k`.
   Exact; q is determined, and no additional characteristic or chosen Fintype occurs.
2. Scheme X and the named structure morphism f: `{X : Scheme.{u}}`
   `(f : X ⟶ Spec (.of k))`. Exact; the result concerns this morphism throughout.
3. Natural dimension d: `(d : ℕ)`. Exact, including zero.
4. Smooth of relative dimension d: `[SmoothOfRelativeDimension d f]`. Exact;
   the dependency records this very Mathlib class. Its affine standard-smooth
   relative-dimension charts include smoothness; no second Smooth assumption occurs.
5. Properness: `[IsProper f]`. Exact; I opened Morphisms/Proper.lean: the class
   extends separated, universally closed and locally of finite type. The dependency's
   recorded universally-closed-to-quasi-compact instance makes this finite type.
6. Geometric integrality: `[GeometricallyIntegral f]`. Exact; I opened
   Geometrically/Integral.lean, where this is `geometrically IsIntegral f`, and the
   dependency's mathlib_match explicitly includes it (not just irreducibility).
7. Zeta and point-count objects: `f.zetaSeries`, `f.pointCount n`, `f.fieldPoints K`,
   and `FiniteField.galoisExtension k n`. Exact real definitions in the shared
   comparator Definitions.lean: the splitting field of `X^(Nat.card k^n)-X`;
   points are morphisms with `g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))`;
   their count is `Nat.card`; the exponential substitutes the coefficient sequence
   `if n = 0 then 0 else (f.pointCount n : ℚ) / n`. I opened the dependency's `lean`
   record including `others`, which records these exact pointCount/zetaSeries names.
   The dependency's closure-subfield presentation is the same point-count notion
   through the splitting-field identification already explicit in node proof step 1;
   it is not replaced here by an arbitrary model or map.
8. One simultaneous family of integral polynomials: `∃ P : Fin (2 * d + 1) → Polynomial ℤ`.
   Exact; all three conjuncts refer to this P, with no hidden choice of different factors.
9. Every constant coefficient equals one: `IsWeilFactorization.coeff_zero_eq_one`,
   namely `∀ i, (P i).coeff 0 = 1`. Exact.
10. First endpoint: `IsWeilFactorization.apply_zero : P 0 = 1 - Polynomial.X`. Exact.
11. Last endpoint: `apply_last : P (Fin.last (2 * d)) =
    1 - Polynomial.C ((q : ℤ) ^ d) * Polynomial.X`. Exact, including q^0.
12. Factorization: `IsWeilFactorization.factorization` is Z times the finite product
    on `Even i.1`, equal to the product on `Odd i.1`. Each P is mapped by
    `Int.castRingHom ℚ` then coerced to `PowerSeries ℚ`. Exact direction, parity,
    coefficient map, and ambient ring; no rational-function equality is substituted.
13. Functional equation for each degree with multiplicity: `WeilFunctionalEquation`
    is `∀ i, ((P i.rev).map (Int.castRingHom ℂ)).roots =
    (((P i).map (Int.castRingHom ℂ)).roots.map fun z ↦ ((q : ℂ) ^ d * z)⁻¹)`.
    Exact: on `Fin (2*d+1)`, rev is 2d-i; roots is a multiset and map preserves
    repetitions. This is the ordinary-root transform in the node.
14. Riemann hypothesis for every complex root: `WeilRiemannHypothesis` quantifies
    `∀ i : Fin (2*d+1), ∀ z ∈ ((P i).map (Int.castRingHom ℂ)).roots` and concludes
    `‖z‖ = (q : ℝ) ^ (-(i.1 : ℝ) / 2)`. Exact, with real division and real power.
15. Quantifier order and reciprocal-root restatement: the existential P precedes
    the conjunction of (9)--(14). Constant term one excludes zero roots; inversion
    turns the norm into q^(i/2), and transforms z↦1/(q^d*z) into alpha↦q^d/alpha.
    Integral coefficients and constant term one give algebraic-integer inverse roots.
    Thus the final equivalent sentence adds no unrendered condition.

Dependency reading: I opened all thirteen stmt_deps and their lean/mathlib_match
records. Besides the three geometric classes and point-count definitions above, I
opened Mathlib's Polynomial/Basic (Polynomial and coeff), Polynomial/Eval/Defs
(eval₂ and map), Polynomial/Div (rootMultiplicity), Polynomial/Roots (roots and
count_roots), PowerSeries/Basic (PowerSeries, the coefficient-preserving polynomial
coercion, and polynomial_map_coe), Analysis/Complex/Norm (instNorm), and
Analysis/SpecialFunctions/Pow/Real (rpow). These are exactly the notions used by the
three comparator predicates. No dependency module or new definition node is needed.

Edge cases: d=0 gives Fin 1, both endpoint identities are 1-X, the odd product is
empty and equals one, and rev fixes the only index. For general d the entire index
set cannot be empty; either parity subset and any constant polynomial root multiset
use the standard empty-product/empty-multiset conventions. Zero polynomial factors
are excluded by coefficient-zero-equals-one. Zero roots are likewise excluded, so
reciprocation is meaningful. Geometric integrality excludes an empty scheme without
an extra nonemptiness hypothesis. The n=0 splitting-field junk is not used in the
exponent, whose constant coefficient is explicitly zero. Every finite field
characteristic is allowed and q>1 follows from Field and Finite. Universe u is
explicitly declared; k, X and their affine spectrum are in the exact comparator
universe, and there are no free universe variables or extra size instances.

Independent searches, using different language from the first worker:

- `msearch.py N6 nt-target-weil-conjectures leanfinder` with
  "zeta function finite field smooth projective variety roots weight factorization":
  eight unrelated Chevalley--Warning, polynomial cardinality and Jacobi-sum results.
- `msearch.py ... loogle` with `"zetaSeries"`: zero results.
- `msearch.py ... leansearch` with "Exist integer polynomials giving zeta function
  factors with complex roots of prescribed norm over finite fields": eight unrelated
  cyclotomic, Mahler-measure, Diophantine and Dedekind-zeta results.
- Direct `rg` for `weil_conjectures|isWeilFactorization|exists_isWeilFactorization|`
  `WeilFunctionalEquation|WeilRiemannHypothesis` in Mathlib/AlgebraicGeometry,
  upstream WeilConjectures and this project's lean/Sheaf: the exact theorem is
  upstream Statement.lean; IntegralFactors and HasseWeil use it; the trace-datum
  statements have different input objects. No second project declaration is present.
  I also checked the upstream name index, which records this exact full name.

The current source lookup for `Weil.Definitions` is outside the wrapper's accepted
module-prefix grammar, so I used the actual shared comparator definitions file,
which is present in both named read-only source trees and has been read above.
This does not affect the successful current-source check for WeilConjectures.Statement.

Verdict: no mathematical mismatch and no statement correction. The recorded signature
is verbatim equal to the local theorem header (excluding `:=`), and matches the current
server source as well. I changed only this report by appending the independent reading;
the correct existing binding is retained. As `existing: true`, no Lean module is
created, compiled, duplicated or modified. There are no new docstrings or postponed
proofs to audit under H5/H6/H8. The required delivery preflight validates this existing
binding; no new module requires the single-file compile wrapper.
