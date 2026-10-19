## Worker report

Recorded `existing: true` for `AlgebraicGeometry.Scheme.zetaSeries_rational`,
module `WeilConjectures.Statement`, branch `slopmaster2`. No new Lean module,
notion, theorem, proof, dependency node or statement correction is necessary.
Only the item's `lean` field changes. There is no repair note for this item.

The source is the current blueprint
`main-20261015/blueprint/sec-zeta-weil/sk-thm-rationality/_section.md`,
whose statement matches the DAG statement verbatim. I read the full node,
including all eight repaired proof steps, and all seven statement dependencies.
The existing theorem's docstring explicitly identifies it as Dwork's theorem
for arbitrary finite-type schemes, without smoothness or properness.
I read the declaration in the read-only upstream `WeilConjectures/Statement.lean`
and confirmed its current published signature using
`scompile.py --source WeilConjectures.Statement`. The latter has the same
signature, with body `f.exists_int_mul_zetaSeries_eq`; no upstream file is changed.

Hypothesis and clause correspondence:

- The finite field F_q is `{k : Type u} [Field k] [Finite k]`. Its cardinality
  is `Nat.card k`, as in the dependency's zeta definition; there is no independent
  numeric q requiring an additional cardinality hypothesis. Every finite field,
  in every characteristic, is allowed.
- A scheme X_0 over that field is `{X : Scheme.{u}}` and
  `(f : X ⟶ Spec (.of k))`. This is exactly the dependency's structure-morphism
  interface; there is no further geometric hypothesis. The universe `u` is
  explicit and arbitrary. A common universe for schemes and fields follows
  the existing `Scheme` and zeta-series interface, and does not impose a
  cardinality restriction on schemes over a finite field.
- Finite type is `[LocallyOfFiniteType f] [QuasiCompact f]`, precisely the
  two conditions in `def-weil-finite-type-morphism`. In particular, there is
  no separatedness, reducedness, smoothness, properness or connectedness binder.
- The requested A,B in Z[T] are `∃ P Q : Polynomial ℤ`, with P=A and Q=B.
- B(0)=1 is `Q.coeff 0 = 1`. Polynomial evaluation at zero is its zeroth
  coefficient. No unrequested coprimality, degree or numerator normalization
  is included in the theorem's conclusion.
- The equality in Q[[T]] is
  `f.zetaSeries * (Q.map (Int.castRingHom ℚ) : PowerSeries ℚ) =
    (P.map (Int.castRingHom ℚ) : PowerSeries ℚ)`.
  Polynomial coefficient mapping is the canonical inclusion Z[T] -> Q[T];
  coercion is the dependency's polynomial-to-series ring homomorphism.
  Multiplication in Q[[T]] is commutative, so the order Z*B instead of B*Z
  changes no assertion.
- The final words "in particular Z in Q(T) intersect (1+T Z[[T]])" are a
  consequence of this exact normalized integral presentation and the zeta
  definition, rather than a missing independent hypothesis or conclusion.
  Indeed Q(0)=1 makes Q nonzero, giving the rational function P/Q regular
  at zero, whose series is Z. It also makes Q a unit in Z[[T]]. Its inverse
  has integral coefficients: if Q=sum b_i T^i and Q^-1=sum c_n T^n, then
  c_0=1 and c_n=-sum_{i=1}^n b_i*c_{n-i}. Hence P*Q^-1 is an integral series.
  Mapping this series to Q[[T]] yields Z by uniqueness after multiplication
  by the unit Q. Finally `Scheme.Hom.constantCoeff_zetaSeries` gives Z(0)=1.
  Equivalently write the integral series as 1+T times its shifted coefficient
  sequence. Thus all of the stated "in particular" clause follows without
  adding any axiom, geometric restriction, or independent rationality assumption.

Dependency declarations read and reused by this existing theorem:

- `sk-def-zeta`: `WeilConjectures.ZetaSeries` exports
  `AlgebraicGeometry.Scheme.Hom.zetaSeries`, with its real exponential
  construction in `Comparator/Weil/Definitions.lean` (module `Weil.Definitions`).
  I read `FiniteField.galoisExtension`, `Hom.fieldPoints`, `Hom.pointCount`,
  `Hom.zetaSeries`, and their docstrings there, and `Hom.constantCoeff_zetaSeries`,
  `Hom.X_mul_derivative_zetaSeries`, `Hom.residueFieldAlgebraMap`, `Hom.degreeOver`
  in `WeilConjectures/ZetaSeries.lean`. This is the recorded splitting-field and
  Nat.card model, not a second definition of point counts or the zeta function.
- `def-weil-finite-type-morphism`: Mathlib module
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, declaration
  `AlgebraicGeometry.LocallyOfFiniteType`, and module
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, declaration
  `AlgebraicGeometry.QuasiCompact`. Their complete class signatures and
  docstrings were read; finite type means both properties of f.
- `def-weil-polynomial-ring`: `Mathlib.Algebra.Polynomial.Basic`, `Polynomial`,
  the finitely supported coefficient construction.
- `def-weil-polynomial-coefficient`: the same module, `Polynomial.coeff`,
  with type `R[X] → ℕ → R` and the documented coefficient interpretation.
- `def-weil-formal-power-series`: `Mathlib.RingTheory.PowerSeries.Basic`,
  `PowerSeries`, the one-variable specialization of `MvPowerSeries`.
- `def-weil-polynomial-as-power-series`: the same module,
  `Polynomial.coeToPowerSeries.ringHom`; its actual data is polynomial coercion,
  preserving the coefficients, including coefficient zero.
- `def-weil-coefficientwise-ring-hom-map`:
  `Mathlib.Algebra.Polynomial.Eval.Defs`, `Polynomial.map` and
  `Polynomial.mapRingHom`; `Mathlib.RingTheory.PowerSeries.Basic`,
  `PowerSeries.map` and `Polynomial.polynomial_map_coe`. I read their
  signatures/docstrings and compatibility statement. The theorem uses
  `Int.castRingHom ℚ`, exactly the inclusion specified in this node.

I additionally read `WeilConjectures.ZetaIntegrality`: the existing
`Hom.exists_int_zetaSeries` and `Hom.constantCoeff_of_map_eq_zetaSeries`
state the integral-lift consequence separately. They are not needed as new
statements, and no duplicate is introduced. The existing-match delivery writes
no module, so it adds no imports or proof-dependency import cycles.

Edge cases checked against the statement and its quantifiers:

- Empty scheme: all positive point counts are zero, Z=1, P=Q=1 works.
- Spec F_q: Z=1/(1-T), P=1 and Q=1-T.
- Affine line: Z=1/(1-qT), P=1 and Q=1-qT; properness is unnecessary.
- The line with doubled origin is allowed (finite type, not separated);
  point counts q^n+1 give Z=1/((1-qT)(1-T)).
- Nilpotent thickenings retain the same field-valued points, so reducedness
  is not needed. Disconnected schemes are likewise not excluded.
- Characteristic 2 and all other characteristics are allowed by the finite-field
  binders. No prime ell or auxiliary coefficient field occurs in the statement.
- Q cannot be zero since Q.coeff 0=1; the constant term of Z is one by the
  recorded zeta definition, so no exceptional zero-series case is silently used.

Searches for an existing statement (2026-10-17):

- `msearch.py ... leanfinder "The zeta series of a scheme of finite type over a
  finite field is rational with integer numerator and denominator and denominator
  constant coefficient one"`: eight Mathlib hits, including
  `Polynomial.cardPowDegreeIsAdmissible`, function-field valuations,
  `Polynomial.existsUnique_hilbertPoly`, and `NumberField.dedekindZeta`;
  none states scheme-zeta rationality.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme, PowerSeries"`: zero hits.
- `msearch.py ... grep "zetaSeries_rational|rational.*zeta|zeta.*rational"`:
  zero Mathlib hits.
- `msearch.py ... leansearch "The Hasse Weil zeta function of a finite type scheme
  over a finite field is rational with integer numerator and denominator"`:
  eight hits on number-field/arithmetic zeta functions and rational-function
  numerator/denominator APIs; none is the theorem in question.
- `rg -n 'zetaSeries_rational|zetaSeries.*[Rr]ational|[Rr]ational.*zetaSeries|sk-thm-rationality'`
  in upstream `WeilConjectures` and shared `lean/Sheaf`: found the exact existing
  theorem at `WeilConjectures/Statement.lean:80`; also found
  `Hom.zetaSeries_rational_of_traceDatum`, which has additional cohomological
  input and is not used as a substitute. No Sheaf duplicate was found.
- `rg -n 'zetaSeries_rational' dag/lean_names_upstream.json`: found the exact
  upstream name. Searching the upstream source for the blueprint id itself
  had no hits; the name search resolved the declaration.

No `STATEMENT-DISPUTED` fault: the existing theorem matches the current blueprint
and the DAG. The recorded signature is verbatim from its keyword to `:=`, including
its original line breaks; its ambient binders are documented above.

## Second reading by Q44

I independently opened `dag/nodes/sec-zeta-weil/sk-thm-rationality.json`, the source
place `literature/blueprint/main-20261015/blueprint/sec-zeta-weil/sk-thm-rationality/_section.md`,
and `WeilConjectures/Statement.lean` (also checked with
`scompile.py --source WeilConjectures.Statement`). The node's statement has these
objects and clauses: a finite field `k` (the notation `F_q`), a scheme `X₀`, and its
structure morphism `f : X₀ ⟶ Spec k`; finite type means locally of finite type and
quasi-compact; there exist `A,B : ℤ[T]`; `B(0)=1`; and
`B(T) Z(X₀,T)=A(T)` in `ℚ[[T]]`, followed by membership in
`ℚ(T) ∩ (1+Tℤ[[T]])`. The final membership is the stated consequence of the
normalized integral presentation and the zeta-series constant term.

The existing Lean declaration renders the same list item by item. Its implicit
`{k : Type u} [Field k] [Finite k]` is the finite-field object, and its implicit
`{X : Scheme.{u}}` with explicit `(f : X ⟶ Spec (.of k))` is `X₀` over `F_q`.
The two typeclass hypotheses `[LocallyOfFiniteType f] [QuasiCompact f]` are exactly
finite type, with no separatedness, smoothness, properness, reducedness,
connectedness, or characteristic hypothesis. The existential
`∃ P Q : Polynomial ℤ` is the pair `A,B`; `Q.coeff 0 = 1` is `B(0)=1`; and the
conclusion
`f.zetaSeries * (Q.map (Int.castRingHom ℚ) : PowerSeries ℚ) =
(P.map (Int.castRingHom ℚ) : PowerSeries ℚ)` is precisely the displayed equality
in `ℚ[[T]]`, using the canonical coefficient map and polynomial-to-series coercion.
Since multiplication is commutative, the Lean order `Z * B` agrees with the
source order `B * Z`. No extra conclusion is introduced and no source clause is
weakened. The declaration's source docstring identifies Dwork's theorem and
explicitly says it holds without smoothness or properness.

I checked the dependency declarations used by this existing theorem: the recorded
zeta-series definition is `AlgebraicGeometry.Scheme.Hom.zetaSeries` from
`WeilConjectures.ZetaSeries` (with its finite-field point-count model), finite type
uses Mathlib's `LocallyOfFiniteType` and `QuasiCompact`, and the polynomial,
coefficient, `PowerSeries`, polynomial-to-series, and coefficientwise ring-map
notions are the recorded Mathlib declarations. None is a private replacement or a
second definition. The upstream module contains the exact theorem declaration, so
there is no statement module to compile or repair.

Edge cases are covered by the binders and definitions: the empty scheme gives
`Z=1` and admits `P=Q=1`; `Spec k` and affine space give the usual normalized
examples; nonseparated finite-type schemes and nilpotent thickenings remain
allowed; every finite characteristic, including characteristic two, is allowed;
`Q.coeff 0=1` excludes the zero denominator; and the common universe `u` is the
same universe used by `k`, `X`, and the structure morphism, with no artificial
restriction. No index set, `n`, prime, or auxiliary coefficient field occurs.

I repeated the existing-declaration searches: grep in the upstream project and
shared Lean found `AlgebraicGeometry.Scheme.zetaSeries_rational` only in
`WeilConjectures.Statement` (plus unrelated references); LeanSearch, LeanFinder,
and Loogle returned no finite-type-scheme zeta-rationality theorem in Mathlib;
`scompile.py --source WeilConjectures.Statement` confirmed the declaration and
signature. The node's `lean` record was changed from null to this exact existing
record. No mismatch was found, so no Lean module, dependency repair, statement
correction, or citer audit is required.
