## Worker report

Existing declaration attachment; no new Lean module is needed. The declarations are
`LinearMap.inv_charpolyRev_eq_exp` and `LinearMap.logOf_charpolyRev` in
`WeilConjectures.ZetaLinearAlgebra.DetTrace` (slopmaster2), at lines 208 and 285.
I read both complete declarations, their docstrings, and their shared variable context.
The node already had a partial attachment naming these declarations; this delivery changes
only `lean`, completing the required existing-declaration record. There is no repair note
for this item. No statement, dependency, proof, or other node field changes.

Source checked: Milne, *Lectures on Etale Cohomology*, Lemma 27.5, printed pages 155–156
(PDF pages 155–156), and its upper-triangular-matrix proof. I also read the current blueprint
`main-20261015`, `sec-zeta-weil/sk-thm-tracetodeterminant/prop-trace-determinant.md` and
its proof. Milne states the logarithm of the reciprocal determinant as the trace sum;
the blueprint writes the equivalent negative logarithm of the determinant. The explicit
characteristic-zero hypothesis in the node makes division by every positive integer valid.

Hypotheses and objects, clause by clause:

- The field is `{K : Type*} [Field K]`; characteristic zero is `[CharZero K]` on each theorem.
  The rational algebra structure used by `PowerSeries.exp K` is inferred canonically.
- The vector space is `{V : Type*} [AddCommGroup V] [Module K V]` with
  `[FiniteDimensional K V]`. The upstream type universes for K and V are independent;
  neither a dimension lower bound nor a positive-dimensional hypothesis is present.
- The arbitrary K-linear endomorphism is `(F : Module.End K V)`, the node's u.
  No invertibility, diagonalizability, or semisimplicity assumption appears.
- The reverse characteristic polynomial is `F.charpolyRev : Polynomial K`, viewed as
  `(F.charpolyRev : K⟦X⟧)` by the standard polynomial-to-power-series coercion.
  `LinearMap.charpolyRev_toMatrix` identifies it with the recorded dependency's
  `Matrix.charpolyRev` for any basis; the latter is exactly `det (1 - X • M.map C)`.
  Thus the existing basis-free interface uses the dependency's same construction.
- The indeterminate T is the formal variable X of `PowerSeries K`, written `K⟦X⟧`.
  No value of T, topology, or analytic convergence hypothesis is introduced.
- `LinearMap.trace K V (F ^ n)` is the trace of the nth iterate; multiplication in
  `Module.End K V` is composition.
- The series is `PowerSeries.mk fun n ↦ if n = 0 then 0 else
  LinearMap.trace K V (F ^ n) / n`. Its nth coefficient is the requested trace divided
  by the cast of n for n positive. Its zeroth coefficient is explicitly 0.
- The formal exponential is `(PowerSeries.exp K).subst` at that series, exactly the
  substitution encoding of `def-weil-power-series-exponential`. Zero constant coefficient
  makes the substitution legitimate by `PowerSeries.HasSubst.of_constantCoeff_zero'`.
- The inverse clause is precisely `LinearMap.inv_charpolyRev_eq_exp`, with the two sides
  interchanged relative to the prose: P inverse equals the displayed exponential.
- The unit and product clauses are equivalent formulations rather than extra hypotheses.
  `LinearMap.coeff_zero_charpolyRev F` and `Polynomial.constantCoeff_coe` give constant
  coefficient 1, so `PowerSeries.isUnit_iff_constantCoeff` makes P a unit.
  `PowerSeries.mul_inv_cancel` then gives P times the displayed exponential equal to 1.
  These are the same standard facts the existing exponential proof uses, not new results
  being asserted or proved in this delivery.
- The logarithmic clause is represented by `LinearMap.logOf_charpolyRev`:
  `PowerSeries.logOf (F.charpolyRev : K⟦X⟧) = -LinearMap.traceSeries F`.
  Its `traceSeries` definition at line 262 is exactly the same coefficient formula as
  the exponential theorem. Negating this equality gives the blueprint's `-log P = S`;
  formal `log(P inverse) = -log P` for constant-term-one series gives Milne's `log(1/P)=S`.
  This is an equivalent logarithmic form, with no changed sign or missing trace term.

Dependency declarations read and used:

| Node | Declaration and module |
| --- | --- |
| `def-weil-field` | `Field`, `Mathlib.Algebra.Field.Defs` |
| `def-weil-finite-dimensional-subspace` | `FiniteDimensional`, `Mathlib.LinearAlgebra.FiniteDimensional.Defs` (abbreviation for `Module.Finite`) |
| `def-weil-reverse-characteristic-polynomial` | `Matrix.charpolyRev`, `Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff`; its basis-free version `LinearMap.charpolyRev` and bridge `LinearMap.charpolyRev_toMatrix` are in `WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix` |
| `def-weil-formal-power-series` | `PowerSeries`, `Mathlib.RingTheory.PowerSeries.Basic` |
| `def-weil-polynomial-as-power-series` | `Polynomial.coeToPowerSeries.ringHom`, `Mathlib.RingTheory.PowerSeries.Basic` |
| `def-weil-endomorphism-trace` | `LinearMap.trace`, `Mathlib.LinearAlgebra.Trace` |
| `def-weil-power-series-exponential` | `PowerSeries.exp`, `Mathlib.RingTheory.PowerSeries.Exp`, composed using `PowerSeries.subst`, `Mathlib.RingTheory.PowerSeries.Substitution` |

I opened the full definition signatures and docstrings listed above. These dependencies
are Mathlib leaves and correctly have `mathlib_match` rather than `lean` records. The
logarithm is the existing `PowerSeries.logOf` of `Mathlib.RingTheory.PowerSeries.Log`;
its definition substitutes f - 1 into the universal series for log(1 + X).
No private copies, helper definitions, dependency repairs, or new nodes are required.

Edge cases checked mathematically against the signatures:

- Dimension zero: the empty determinant is 1, all traces are zero, the exponential is 1,
  and the logarithm is 0. No `Nontrivial V` or nonempty basis is assumed.
- F = 0 on any finite-dimensional V: all positive-power traces vanish and P = 1.
- A singular endomorphism is allowed: the polynomial's constant coefficient is still 1,
  even when its degree is less than dim V. Inverting the power series never requires F
  itself to be a unit.
- A scalar in dimension one gives P = 1 - aX and S = sum of a^n X^n/n, confirming the signs.
  Nilpotent nonzero endomorphisms are also covered, with no semisimplicity assumption.
- n = 0 is excluded from the trace sum by the explicit conditional. The formula never
  attempts to include trace(identity)/0 as a contributing term. Positive denominators
  are nonzero by characteristic zero; positive-characteristic fields are rightly excluded.

Searches performed with the prescribed msearch.py wrapper (group NG, this item):

1. LeanSearch query: "The inverse of the reverse characteristic polynomial of a linear map
   is the formal exponential of the generating series of traces of its powers".
   Eight hits include `LinearMap.charpoly`, `Matrix.charpolyRev`, `Matrix.reverse_charpoly`,
   and `Matrix.charpoly_inv`; no formal trace-exponential identity in Mathlib.
2. LeanFinder query: "inverse reverse characteristic polynomial exponential traces of powers".
   Eight hits include `Matrix.charpolyRev`, `Matrix.charpoly_inv`, `Matrix.reverse_charpoly`,
   and `Matrix.coeff_charpolyRev_eq_neg_trace`; no exact Mathlib match.
3. Loogle query: "LinearMap.inv_charpolyRev_eq_exp, LinearMap.logOf_charpolyRev".
   Zero hits; Mathlib search reports the upstream name as unknown.
4. Mathlib grep query: `charpolyRev|trace_pow`, subdirectory `LinearAlgebra`.
   Eight hits, including `Matrix.charpolyRev`, `Matrix.reverse_charpoly`, and finite-field
   trace-power lemmas; no exact exponential/logarithmic identity.
5. Direct rg query: `inv_charpolyRev_eq_exp|logOf_charpolyRev|lem-weil-exp-trace-determinant`
   in upstream `WeilConjectures/` and shared `lean/Sheaf/`. It finds the two exact upstream
   theorems in DetTrace.lean, their module documentation, and an upstream consumer docstring;
   it finds no duplicate declaration under `lean/Sheaf/`.
6. Direct rg of `dag/lean_names_upstream.json` for the two theorem names locates both
   existing declarations. The node's `lean_audit.slopmaster2` also records both as closed.
7. Direct source inspection of `charpolyRev` in upstream `Mathlib/LinearAlgebra/` finds
   the basis-free definition, its matrix comparison, and constant-coefficient-one lemma.

No node fault or STATEMENT-DISPUTED issue was found. The delivery uses the existing
attachment route of brief-stage2 section 1; it adds no theorem proof or Lean module.
The dry run performs real compiler `#check @` probes for both existing declarations.


## Second reading by NG

I independently opened the delivered node, both complete upstream theorems and their
shared variable context in `WeilConjectures/ZetaLinearAlgebra/DetTrace.lean`, and all
seven statement-dependency nodes. This is an existing-declaration delivery, with no
Lean module, new definition node, dependency module, or statement correction.
The recorded `lean.statement` was compared mechanically with the upstream signature,
from `theorem` to before `:=`, and is verbatim equal. All non-`lean` node fields agree
with the read-only base.

Source reading: Milne, *Lectures on Etale Cohomology*, Lemma 27.5 and its proof,
pp. 155–156 (read directly from the local PDF). It introduces an endomorphism of a
finite-dimensional vector space, defines P as det(1 - t u), and identifies
log(1/P) with the positive-degree trace sum. Its proof extends the field to
triangularize the endomorphism, computes the traces of its powers from diagonal
entries, and sums log(1/(1 - c t)) over those entries. This does not assume
semisimplicity or invertibility. Division by every positive integer requires the
node's characteristic-zero hypothesis. I also read the current blueprint's
`main-20261015/blueprint/sec-zeta-weil/sk-thm-tracetodeterminant/prop-trace-determinant.md`
and its proof: they explicitly assume a characteristic-zero field and give
-log(P) = the same trace sum. This item is the single-endomorphism input, not the
whole graded-family or geometric application. The source is Milne rather than a
Stacks tag; no Stacks-wide hypotheses are applicable.

My object/hypothesis/conclusion checklist, made from the node:

| Node item | Lean rendering and verdict |
| --- | --- |
| Arbitrary field K | `{K : Type*} [Field K]` in the shared context. Exact; no algebraic closure or splitting hypothesis. |
| Characteristic zero, hence rational coefficients | `[CharZero K]` on each theorem. The rational algebra structure is canonical for such a field. Exact. |
| Finite-dimensional K-vector space V | Independent `{V : Type*}` with `[AddCommGroup V] [Module K V] [FiniteDimensional K V]`. Exact; `FiniteDimensional` abbreviates `Module.Finite`, and field modules have the needed free structure. |
| Arbitrary K-linear endomorphism u | Explicit `(F : Module.End K V)`. Exact; no unit or diagonalizability condition. |
| Indeterminate T and formal ring K[[T]] | `K⟦X⟧`, the standard power-series type. X renames T; there is no numerical parameter or convergence requirement. Exact. |
| P = det(1 - T u) as a polynomial | `F.charpolyRev`. I read its definition as `F.charpoly.reverse`, and `LinearMap.charpolyRev_toMatrix`, which identifies it with `(LinearMap.toMatrix b b F).charpolyRev` for every finite basis. The recorded dependency's `Matrix.charpolyRev` is literally `det (1 - X • M.map C)`. Exact basis-independent object, not a private replacement. |
| P regarded as a power series | `(F.charpolyRev : K⟦X⟧)`, the dependency's polynomial coercion, defined coefficientwise by `Polynomial.toPowerSeries`. Exact. |
| Trace of the nth iterate | `LinearMap.trace K V (F ^ n)`. I read `trace`, `traceAux`, and `trace_eq_matrix_trace`; on a finite-dimensional space this is the sum of diagonal matrix entries. Powers in `Module.End` are iterated composition. Exact. |
| S = sum over n >= 1 of trace(u^n) T^n/n | `PowerSeries.mk fun n ↦ if n = 0 then 0 else LinearMap.trace K V (F ^ n) / n`. The natural denominator is cast into K. The conditional gives constant coefficient zero and exactly the requested coefficients for positive n. Exact. |
| Formal exponential of S | `(PowerSeries.exp K).subst S`. I read `exp` (coefficients 1/n!) and `subst`; this is precisely the recorded exponential dependency's encoding, legitimate because S has constant coefficient zero. Exact. |
| P times exp(S) = 1 | `LinearMap.inv_charpolyRev_eq_exp` states P inverse = exp(S). `LinearMap.coeff_zero_charpolyRev`, `Polynomial.constantCoeff_coe`, and `PowerSeries.mul_inv_cancel` give P times P inverse = 1, since P has constant coefficient 1. Thus the recorded equality is the same identity, with the explicitly explained standard unit normalization. Pass. |
| Equivalently P is a unit and exp(S) = P inverse | `PowerSeries.isUnit_iff_constantCoeff` makes P a unit from its constant coefficient 1. Symmetry of the attached exponential equality gives exactly the second clause. This is not an extra assumption about F. Pass. |
| Logarithmic form log(1/P) = S | The second recorded theorem `LinearMap.logOf_charpolyRev` states `PowerSeries.logOf P = -traceSeries F`. I opened `traceSeries`: it is definitionally the displayed S. I opened `PowerSeries.logOf`: substitution of P - 1 into log(1 + X). For a constant-term-one unit, log(P inverse) = -log(P), so this is Milne's form and the blueprint's -log(P) form with the correct sign. Pass. |

The last equivalence does not depend on choosing a branch of an analytic logarithm:
all series are formal. It can also be checked from the already available
`PowerSeries.mul_derivative_logOf` applied to P and P inverse, the inverse derivative
identity, and equality of formal series with equal derivative and zero constant
coefficient in characteristic zero. This explains why the attachment covers the
logarithmic clause even though it spells it with log(P).

I read the dependency interfaces themselves: `Field` in
`Mathlib.Algebra.Field.Defs`, `FiniteDimensional` in
`Mathlib.LinearAlgebra.FiniteDimensional.Defs`, `Matrix.charpolyRev` in
`Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff`, `PowerSeries` and the polynomial
coercion in `Mathlib.RingTheory.PowerSeries.Basic`, `LinearMap.trace` in
`Mathlib.LinearAlgebra.Trace`, and `PowerSeries.exp` and `PowerSeries.subst` in
`Mathlib.RingTheory.PowerSeries.Exp` and `.Substitution`. The basis-free reverse
characteristic polynomial and its matrix bridge are in the upstream
`WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix`. Every required instance
is furnished by the node's field/vector-space/finite-dimensional hypotheses.
There is no dependency interface to repair and no missing independent notion.

Edge cases checked against the actual signatures:

- V = 0 is allowed: its finite basis is empty, P = 1, S = 0, exp(S) = 1,
  and the logarithm is 0. No `[Nontrivial V]` or positive dimension is present.
- F = 0 is allowed in every dimension. The positive iterates have zero trace,
  P = 1, and all three formulations hold. At n = 0 the explicit conditional
  suppresses the trace of the identity, including on a nonzero V.
- Singular and nonzero nilpotent maps are included. P is a power-series unit
  because P(0) = 1, independently of whether F is invertible or the degree of P
  equals the dimension.
- On a one-dimensional space, F = multiplication by a gives P = 1 - aT and
  S with positive coefficients a^n/n; this confirms the logarithmic sign.
- All characteristic-zero fields are allowed; positive characteristic is
  excluded exactly as the node requires. No topology or analytic exponential
  is assumed.
- Each `Type*` introduces its own universe, so K and V have independent
  universes. There is no index type beyond natural coefficient indices; the
  empty-basis case covers the relevant empty finite index set. Schemes and
  their empty case do not occur in this lemma.

Independent searches (different queries from the first reader), using msearch.py
for this group and item:

1. LeanFinder: `formal logarithm reciprocal determinant equals generating function
   of power traces` returned eight related determinant/discriminant results,
   including `Matrix.det_one_add_X_smul`, but no exact Mathlib statement.
2. Loogle: `PowerSeries.logOf, Inv.inv` returned zero results.
3. LeanSearch: `logarithm determinant linear endomorphism trace generating function`
   returned eight determinant results, but no exact trace-series identity.
4. Direct rg in upstream `WeilConjectures/ZetaLinearAlgebra`, upstream
   `WeilConjectures/Mathlib`, Mathlib's `RingTheory/PowerSeries`, and the project's
   `lean/Sheaf`, using `det.*exp|exp.*det|log.*charpoly|charpoly.*log|trace.*generat|generat.*trace`,
   found the two attached DetTrace statements and related consumers, with no
   duplicate Sheaf statement. Direct rg in Mathlib's `LinearAlgebra` for
   `trace.*exp|exp.*trace|log.*determinant|determinant.*log` found none.
5. Direct rg in `dag/lean_names_upstream.json` independently confirmed both exact
   upstream declaration names.

No H3 mismatch was found; no source-based statement correction, new node, dependency
module, or Lean edit is needed. I retained the worker's correct existing attachment.
H5/H6/H8/H9 were checked on that basis: this delivery creates no definition data,
postponed theorem, proof, import, or file-local notation. The existing proved
upstream declarations and their docstrings are read-only and are reused under
section 1's existing-declaration route; they are not restated merely to retag their
docstrings. The node has no proof steps to transplant (`proof: []`).

Second-reading changes: appended this independent source/interface/edge-case/search
review only; the Lean record and all mathematical statements are unchanged.

Verification: `deliver2.py NG lem-weil-exp-trace-determinant --no-push`
printed `OK (dry run)` and confirmed that preflight and compilation pass.
The wrapper checked the existing-declaration probes; there are no delivered
Lean files or sibling modules requiring separate compilation.
