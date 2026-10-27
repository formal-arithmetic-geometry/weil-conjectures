## Worker report

The new module `Sheaf.RingTheory.QuadraticHomogeneousSubstitution` states
`QuadraticSeries.homogeneous_substitution`, with its whole proof `sorry`.
There are no new definitions, extra nodes, dependency repairs, or statement corrections.
The node's statement and all its other fields are unchanged; only `lean` is set.

The source was read in `literature/stacks-project/curves.tex`, Tag 0C4A,
`lemma-2-branches-delta-1`: the proof of (1) implies (2), Cases I and II, and the
final scalar-constant description. The node extracts the homogeneous calculation and
explicitly extends it to degenerate quadratics; its six-step proof was checked in full
and reproduced in the theorem docstring. This does not assert normalization without
the discriminant hypothesis.

Hypotheses and clauses, in signature order:

- The field is `(F : Type u) [Field F]`, with explicit universe `u`.
  The coefficients are `(a b c : F)` and the only mathematical hypothesis is
  `(ha : a ≠ 0)`. Neither separability nor a characteristic or discriminant restriction
  appears.
- The binders `r`, `hr` name exactly `aZ²+bZ+c`; `q`, `hq` name exactly
  `aX²+bXY+cY²`, with `X = MvPowerSeries.X 0` and `Y = MvPowerSeries.X 1`.
  These equality binders implement the node's "put" definitions without `let` in a
  statement, and are not restrictions: for every `a,b,c` the displayed expressions
  supply `r,q` and reflexivity supplies `hr,hq`. No arbitrary equation is substituted.
  The parent module already has abbreviations `QuadraticSeries.polynomial`, `equation`,
  `CurveRing`, and `CoefficientAlgebra`; importing it would import the downstream
  integral-closure theorem. We introduce no competing abbreviations or constructions.
- `β=b/a`, `γ=c/a` are written as `b / a`, `c / a` throughout. The monic polynomial
  is written as `Polynomial.X ^ 2 + Polynomial.C (b/a) * Polynomial.X +
  Polynomial.C (c/a)`. The first conjunct equates its principal ideal with
  `Ideal.span {r}`. Thus the two quotient descriptions have the same defining ideal.
- `L` is `AdjoinRoot r`, Mathlib's definitionally exact polynomial quotient, and
  `z` is `AdjoinRoot.root r`, the class of `Polynomial.X`. `B` is
  `PowerSeries (AdjoinRoot r)`, with parameter `PowerSeries.X`.
- `Function.Injective (algebraMap F (AdjoinRoot r))` is precisely scalar injectivity.
  The existential `e : Module.Basis (Fin 2) F (AdjoinRoot r)` with `e 0 = 1` and
  `e 1 = AdjoinRoot.root r` asserts the ordered basis `1,z`, including spanning and
  linear independence. The next conjunct is exactly `z² = -βz-γ`, with scalars mapped
  into `L`.
- The existential `φ : MvPowerSeries (Fin 2) F →ₐ[F] PowerSeries (AdjoinRoot r)`
  asserts an algebra homomorphism, with its value specified on every series and
  every coefficient. The finite sum for degree `n` ranges over `0 ≤ i ≤ n` and
  uses exponent `Finsupp.single 0 i + Finsupp.single 1 (n-i)`; multiplication by `z^i`
  evaluates exactly `H_n(z,1)`. There is no unspecified choice of substitution.
- The next two equations give `φ(X)=zt` and `φ(Y)=t`.
  `RingHom.ker φ.toRingHom = Ideal.span {q}` states the kernel equality as an ideal.
- The image clause says for every `h`, `(∃ H, φ H = h)` iff
  `∃ d : F, ∃ g : B, h = C(algebraMap d) + X*g`. This is exactly the set `F+tB`,
  keeping the scalar map explicit rather than introducing another subalgebra definition.
- The existential `j` has domain `MvPowerSeries (Fin 2) F ⧸ Ideal.span {q}`.
  Its equation on every quotient representative identifies it with the map induced
  by the same `φ`; `Function.Injective j` gives injectivity; the equivalence of its
  image with the image of `φ` gives image `A` by the preceding clause.
- Every scalar-coefficient series enters through `PowerSeries.map (algebraMap F L)`;
  the corresponding existential preimage is exactly `F[[t]] ⊆ A`. Likewise the
  existential preimage of `PowerSeries.X * g` for every `g` is `tB ⊆ A`.
- The final clause quantifies over arbitrary `α δ : ℕ → F`. Its input is the real
  coefficient function: on exponent `(0,j)` the coefficient is `α j`, on `(1,j)`
  it is `δ (j+1)`, and on other exponents it is zero. Thus it is precisely
  `α₀ + Σ(n≥1) α_n Y^n + Σ(n≥1) δ_n X Y^(n-1)`.
  The output `PowerSeries.mk` has constant coefficient `algebraMap (α 0)` and positive
  coefficient `algebraMap (α n) + algebraMap (δ n)*z`, exactly the node's `h`.
  `δ 0` is deliberately unused, as in the node. No infinite sums or convergence
  hypotheses are imposed on formal series.

Dependency declarations read and used:

- `def-weil-polynomial-ring`: `Polynomial`, from
  `Mathlib.Algebra.Polynomial.Basic`, including its finitely supported coefficients.
  It is publicly available through the `AdjoinRoot` import.
- `def-weil-pbc-multivariate-power-series`: `MvPowerSeries`, `MvPowerSeries.C`,
  `MvPowerSeries.X`, `MvPowerSeries.coeff`, from `Mathlib.RingTheory.MvPowerSeries.Basic`.
  The recorded one-variable convention is `PowerSeries`, with `coeff`, `C`, `X`,
  `mk`, and `map` from `Mathlib.RingTheory.PowerSeries.Basic`.
- `def-weil-pbc-algebra-hom-quotient` is Mathlib status, without a `lean` record.
  Its match supplies `AlgHom` (`Mathlib.Algebra.Algebra.Hom`) and the quotient algebra
  and quotient map (`Mathlib.RingTheory.Ideal.Quotient.Operations`). `AdjoinRoot`,
  `AdjoinRoot.root`, and the inherited algebra structure are read in
  `Mathlib.RingTheory.AdjoinRoot`; they implement the same quotient, not a new ring.
- `def-weil-pbc-free-module`: `Module.Free`, from
  `Mathlib.LinearAlgebra.FreeModule.Basic`; its basis notion is `Module.Basis`,
  read in `Mathlib.LinearAlgebra.Basis.Defs`. The statement needs the specific basis,
  so uses `Module.Basis` rather than only asserting freeness.
- Proof dependency `lem-weil-pbc-monic-quotient-free` is Mathlib status. Its recorded
  `AdjoinRoot.powerBasis'` signature and docstring were read in
  `Mathlib.RingTheory.AdjoinRoot`: a monic polynomial gives the power basis indexed
  by its natural degree. This module is already public for the quotient in the signature.

Edge cases checked mathematically: degree zero of `H` gives its scalar constant and
the finite range is `{0}`; degree one gives `uY+vX`; the explicit lift treats its
constant separately and never uses a negative exponent. The degenerate case
`a=1,b=c=0` has `z²=0` with basis `1,z`, and its kernel is `(X²)` and image `F+tB`.
Repeated-root quadratics, split quadratics, irreducible quadratics, `c=0`, and
characteristic two all use the same finite division and basis argument; no inverse
of `2` or discriminant occurs. The hypothesis `a≠0` is retained, so the quadratic
degree cannot collapse. The zero series, scalar series and `t*g` have the required
preimages. All coefficients may live in an arbitrary universe `u`.

Searches made with the prescribed `msearch.py NE` interface:

- LeanFinder: "Homogeneous substitution X=z*t and Y=t from bivariate formal power
  series to power series over a quadratic quotient has kernel the quadratic relation
  and image F+tB". Eight hits: general `HasSubst`, coefficient substitution ideals,
  Weierstrass quotient equivalences, and `MvPowerSeries.expand`; no exact statement.
- Loogle: `"MvPowerSeries", "subst"`. Twelve hits: `HasSubst`, `subst`, `subst_X`,
  and substitution admissibility lemmas; none proves this kernel and image.
- Grep: `quadratic|homogeneousComponent_mul|ker.*subst|range.*subst` in
  `RingTheory/MvPowerSeries`. Eight hits: homogeneous-component products and
  substitution truncation formulas; no exact theorem.
- LeanSearch: "The homogeneous substitution x=z*t and y=t for a quadratic quotient
  of bivariate formal power series has the homogeneous quadratic kernel and
  scalar-constant image". Eight hits: `subst`, `substAlgHom`, rescaling and
  composition compatibility; none states the node's conclusion.
- Local `rg` in `lean/WeilConjectures` and `lean/Sheaf` for quadratic, homogeneous
  substitution, and the node id: the parent `QuadraticSeries.integral_closure` is
  a theorem with a nonzero-discriminant hypothesis and normalization conclusions,
  so is neither a general statement match nor an acyclic dependency of this item.
  The other hits (smooth quadratic relations, power-series quadratic ideals) concern
  different statements. `dag/lean_names_upstream.json` has no collision with
  `QuadraticSeries.homogeneous_substitution`.

The prescribed server `scompile.py` compiled this module cleanly, both in sandbox
mode and at its intended library module name (about 1.4 seconds per check).
Every binder is explicit, every line is at most 100 characters, and the only theorem
has a whole-proof `sorry`. There are no disputed statements or identified node faults.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
