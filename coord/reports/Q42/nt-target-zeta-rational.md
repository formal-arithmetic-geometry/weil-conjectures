## Worker report

The node is already stated exactly by `AlgebraicGeometry.Scheme.zetaSeries_rational`
in `WeilConjectures.Statement` (the current slopmaster2 source). I therefore add no
Lean module or theorem. The comparator declaration
`WeilConjectures.zetaSeries_rational` in `Comparator.Weil.Challenge` has the same
elaborated type under a different namespace; the recorded source declaration is the
canonical existing statement and avoids a duplicate.

The existing declaration's signature is:

```lean
theorem zetaSeries_rational [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ P Q : Polynomial ℤ, Q.coeff 0 = 1 ∧
      f.zetaSeries * (Q.map (Int.castRingHom ℚ) : PowerSeries ℚ) =
        (P.map (Int.castRingHom ℚ) : PowerSeries ℚ)
```

Clause-by-clause, `[Field k] [Finite k]` and the scheme `X` with structure morphism
`f : X ⟶ Spec (.of k)` are the surrounding explicit variables in the module. The
hypotheses `[LocallyOfFiniteType f]` and `[QuasiCompact f]` are exactly the node's
locally-finite-type and quasi-compact assumptions; no smoothness, properness, or
separatedness hypothesis is present. The witnesses `P Q : Polynomial ℤ` render the
integer polynomials. `Q.coeff 0 = 1` is the constant-coefficient clause. The equation
is in `PowerSeries ℚ`: `Polynomial.map (Int.castRingHom ℚ)` supplies the coefficientwise
integer-to-rational map, and the coercions to `PowerSeries ℚ` supply the polynomial to
formal-power-series inclusion. This is precisely `Z(X,t) * Q = P` in the node.
The zeta series is the recorded `f.zetaSeries` from `sk-def-zeta`, including the
splitting-field point-count model, the zero convention for infinite point sets, and
the formal exponential starting at `n = 1`.

Dependency declarations read:

- `sk-def-zeta`: `FiniteField.galoisExtension`,
  `AlgebraicGeometry.Scheme.Hom.fieldPoints`, `pointCount`, and `zetaSeries` in
  `WeilConjectures.ZetaSeries` (the module's recorded interface also includes the
  residue-field and degree declarations).
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, supplying
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.
- `def-weil-scheme-morphism-properties`: the convention node collecting the named
  scheme and morphism properties; it introduces no separate declaration.
- `def-weil-polynomial-ring`: `Mathlib.Algebra.Polynomial.Basic`, `Polynomial`.
- `def-weil-polynomial-coefficient`: `Mathlib.Algebra.Polynomial.Basic`, `Polynomial.coeff`.
- `def-weil-formal-power-series`: `Mathlib.RingTheory.PowerSeries.Basic`, `PowerSeries`.
- `def-weil-coefficientwise-ring-hom-map`: `Mathlib.Algebra.Polynomial.Eval.Defs`,
  `Polynomial.map`, and `Mathlib.RingTheory.PowerSeries.Basic`,
  `PowerSeries.map`, specialized to `Int.castRingHom ℚ`.
- `def-weil-polynomial-as-power-series`: `Mathlib.RingTheory.PowerSeries.Basic`,
  `Polynomial.coeToPowerSeries.ringHom` and the coercion of a polynomial to a
  power series.

Edge cases checked against the source definitions are the empty scheme (all point
counts zero), `Spec k` (the unique point), `Spec k[e]/(e^2)` (nonreduced schemes are
allowed), and an affine line with doubled origin (no separatedness assumption). The
finite field and scheme universes are shared as in the source declaration, and no
positive-degree or nonempty-scheme assumption is introduced.

Searches for an existing declaration (2026-10-17):

- `msearch.py ... leanfinder "Dwork rationality theorem for the zeta series of any finite type scheme over a finite field"`: `Polynomial.cardPowDegreeIsAdmissible`, `mahler`, Hilbert polynomials and function fields; no scheme theorem.
- `msearch.py ... loogle "Scheme.Hom.zetaSeries, PowerSeries.map, Polynomial"`: 0 hits for the combined query.
- `msearch.py ... grep "zetaSeries_rational" /home/ubuntu/weil-src-slopmaster2/WeilConjectures`: found `AlgebraicGeometry.Scheme.zetaSeries_rational` in `Statement.lean` and its uses in the rationality modules.
- `rg -n "zetaSeries_rational|zetaSeries"` in the source and project located the same source declaration and the comparator wrapper; reading both signatures confirmed exact agreement.
- `msearch.py ... grep "zetaSeries_rational|zetaSeries"` at the Mathlib root: 0 hits.
- `grep -rn "nt-target-zeta-rational"` in upstream `WeilConjectures`: 0 hits.
- The upstream name index records `AlgebraicGeometry.Scheme.zetaSeries_rational`.
- The project `lean/Sheaf` search found no competing declaration.

The source was also read through `scompile.py --source WeilConjectures.Statement`, and an
explicit `#check @AlgebraicGeometry.Scheme.zetaSeries_rational` compiled successfully
through `scompile.py`. No statement correction, new node, dependency module, or
`STATEMENT-DISPUTED` issue is present.


Independent second reading is pending the dispatcher's second reader.

## Second reading by Q42

I independently read `dag/nodes/sec-zeta-weil/nt-target-zeta-rational.json`, the source
place `lean/Comparator/Weil/Challenge.lean` (`WeilConjectures.zetaSeries_rational`),
and the recorded existing declaration `AlgebraicGeometry.Scheme.zetaSeries_rational`
in `WeilConjectures.Statement`.

The node's objects and clauses match as follows.

1. The finite field is rendered by the source variables `{k : Type u} [Field k]
   [Finite k]`; the shared universe `u` is retained. Verdict: exact, with no extra
   characteristic, cardinality, or nonemptiness assumption.
2. The scheme and structure morphism are rendered by `{X : Scheme.{u}}` and
   `f : X ⟶ Spec (.of k)`. Verdict: exact same object and universe; the target does
   not introduce a separate scheme or base field.
3. The locally-finite-type and quasi-compact hypotheses are rendered by the typeclass
   binders `[LocallyOfFiniteType f] [QuasiCompact f]`. Verdict: exact hypotheses,
   with no smoothness, properness, separatedness, or finite-presentation assumption.
4. The zeta series is rendered by `f.zetaSeries : PowerSeries ℚ`. The recorded
   `sk-def-zeta` declarations define its point counts through
   `FiniteField.galoisExtension`, `f.fieldPoints`, and `Nat.card`, with zero for an
   infinite point set, and define the formal exponential with the `n = 0` term zero.
   Verdict: exact node convention, including the sum beginning at `n ≥ 1`.
5. The witnesses are rendered by `∃ P Q : Polynomial ℤ`. Verdict: exact integer
   polynomial witnesses; no degree or nonzero condition is added.
6. The normalization clause is rendered by `Q.coeff 0 = 1`. Verdict: exact constant
   coefficient clause.
7. The equality is rendered in `PowerSeries ℚ` as
   `f.zetaSeries * (Q.map (Int.castRingHom ℚ) : PowerSeries ℚ) =
   (P.map (Int.castRingHom ℚ) : PowerSeries ℚ)`. Verdict: exact coefficientwise
   integer-to-rational map and polynomial-to-power-series coercion, with the same
   multiplication order as the node.
8. The node's final exclusion of smoothness, properness, and separatedness is
   reflected by their absence from the theorem signature. Verdict: exact.

Edge cases checked: an empty scheme is allowed and has zero point counts; `Spec k`
has the expected single base-rational point; nonreduced schemes such as
`Spec k[ε]/(ε²)` and nonseparated schemes are not excluded; `n = 0` contributes no
term to the zeta exponent (the definition gives its coefficient zero); infinite
point sets use the stipulated junk value `0`; and no characteristic or positive
cardinality assumption beyond `[Field k] [Finite k]` is present. No index type or
finite-product edge case occurs in this statement.

Existing-definition searches were rechecked with `msearch.py` LeanFinder and Loogle
queries for scheme zeta rationality, `rg` over `WeilConjectures/` and `lean/Sheaf`,
and `rg` over Mathlib for `zetaSeries_rational`, `zetaSeries`, and the polynomial /
power-series maps. The only exact source declaration is
`AlgebraicGeometry.Scheme.zetaSeries_rational` in `WeilConjectures.Statement`; the
comparator declaration has the same elaborated signature under
`WeilConjectures`. The dependency declarations were read: `sk-def-zeta` supplies
`galoisExtension`, `fieldPoints`, `pointCount`, and `zetaSeries`; the finite-type
properties are Mathlib's `LocallyOfFiniteType` and `QuasiCompact`; and the polynomial,
coefficient, map, and power-series notions are the recorded Mathlib matches.
No project declaration duplicates the theorem.

No mismatch was found, so no Lean module, statement correction, new node, dependency
repair, or node-field change was needed. The existing node copy already records the
verbatim theorem signature, module `WeilConjectures.Statement`, declaration
`AlgebraicGeometry.Scheme.zetaSeries_rational`, `branch: slopmaster2`, and
`existing: true`. Validation with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py --source WeilConjectures.Statement`
completed successfully.
