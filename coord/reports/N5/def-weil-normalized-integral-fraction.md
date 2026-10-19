## Worker report

Existing declaration: `PowerSeries.IsNormalizedIntegralFraction` in the published upstream
module `WeilConjectures.ZetaLinearAlgebra.ReciprocalRoots` (branch `slopmaster2`).
No module is delivered. The item changes only in `lean`; no definition, theorem, statement
correction, dependency repair, or new DAG node is needed.

Read the source definition in
`literature/blueprint/master/blueprint/sec-zeta-weil/sk-def-roots/def-weil-normalized-integral-fraction.md`,
its node and all six statement dependencies. There is no repair note for this item,
and its node has no `blueprint_update`.

The local read-only checkout lacks the newer module. The first dry run identified the
existing name in the server's upstream sorry map. Read its module name from the exact
matching definition record, then retrieved and read the full current source with:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py --source WeilConjectures.ZetaLinearAlgebra.ReciprocalRoots`

The declaration's complete definition is:

```lean
def IsNormalizedIntegralFraction (Z : ℚ⟦X⟧) (A B : ℤ[X]) : Prop :=
  A.coeff 0 = 1 ∧ B.coeff 0 = 1 ∧
    IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)) ∧
    Z * (B.map (Int.castRingHom ℚ) : ℚ⟦X⟧) = (A.map (Int.castRingHom ℚ) : ℚ⟦X⟧)
```

Its docstring explicitly identifies this blueprint node. The same module supplies the
proved theorem `PowerSeries.isNormalizedIntegralFraction_map_iff`, whose full signature is:

```lean
theorem isNormalizedIntegralFraction_map_iff (f : ℤ⟦X⟧) (A B : ℤ[X]) :
    IsNormalizedIntegralFraction (map (Int.castRingHom ℚ) f) A B ↔
      A.coeff 0 = 1 ∧ B.coeff 0 = 1 ∧
        IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)) ∧
        f * (B : ℤ⟦X⟧) = (A : ℤ⟦X⟧)
```

Clause-by-clause correspondence:

- The fixed indeterminate is the formal variable of `Polynomial` and `PowerSeries`.
- The node's integral series is `f : PowerSeries ℤ`; its image regarded in `ℚ[[T]]`
  is `PowerSeries.map (Int.castRingHom ℚ) f`, which is the first argument to the existing
  predicate. This is precisely the node's coefficientwise inclusion convention.
- The pair of integral polynomials is `(A B : Polynomial ℤ)`, supplied as curried arguments.
- `A(0) = 1` is `A.coeff 0 = 1`.
- `B(0) = 1` is `B.coeff 0 = 1`.
- Reducedness over `ℚ[T]` is
  `IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ))`.
- The fraction identity is the final rational power-series equality in the definition.
  The proved `isNormalizedIntegralFraction_map_iff` identifies it exactly with the
  integral power-series equality `f * B = A`; commutativity makes this the node's `Bf = A`.
  Hence the existing predicate is the node's notion, not a merely similar rational identity.
- The ambient conditions of constant coefficient one and rationality over `ℚ` need no
  additional proof arguments to this predicate. Its defining clauses already force them:
  taking constant coefficients of the integral equality gives `constantCoeff f = 1`, and
  coefficientwise mapping gives rationality witnesses `A.map (Int.castRingHom ℚ)` and
  `B.map (Int.castRingHom ℚ)`, with denominator constant coefficient `1 ≠ 0`.
  Applying the existing definition to the integral image loses no integrality condition.
- The unit/inverse interpretation follows from `B.coeff 0 = 1`; it adds no conjunct.
  The predicate makes no existence or uniqueness assertion. The separate upstream
  `existsUnique_isNormalizedIntegralFraction` theorem is not substituted for this definition.

Dependency declarations and docstrings read:

- `def-weil-polynomial-ring`: `Polynomial`, `Mathlib.Algebra.Polynomial.Basic`.
- `def-weil-formal-power-series`: `PowerSeries`, `Mathlib.RingTheory.PowerSeries.Basic`.
- `def-weil-coefficientwise-ring-hom-map`: `Polynomial.map`,
  `Mathlib.Algebra.Polynomial.Eval.Defs`, and `PowerSeries.map`,
  `Mathlib.RingTheory.PowerSeries.Basic`.
- `def-weil-rational-power-series`: `HahnSeries.ofPowerSeries`,
  `Mathlib.RingTheory.HahnSeries.PowerSeries`, and its recorded existential specialization
  `∃ P Q, Q.coeff 0 ≠ 0 ∧ Q * f = P`. This is the rationality condition just explained;
  no private copy of a rationality notion is introduced.
- `def-weil-coprime-polynomials`: `IsCoprime`, `Mathlib.RingTheory.Coprime.Basic`.
- `def-weil-polynomial-as-power-series`: `Polynomial.coeToPowerSeries.ringHom`,
  `Mathlib.RingTheory.PowerSeries.Basic`, used by the displayed coercions.

Edge cases checked: `f = 1`, `A = B = 1` is permitted; zero numerator or denominator
fails normalization; `f = 0` fails the constant-coefficient consequence; `A = B = 1 + T`
fails reducedness; denominator `1` permits polynomial series; denominator `1 - T`
permits the geometric series; common scaling by `-1` fails normalization; nonmonic
polynomials such as denominator `1 - 2T` remain permitted. No analytic convergence,
monicity, positive degree, field extension, or universe restriction is added.

Searches performed using the prescribed `msearch.py`:

- LeanFinder: "A normalized reduced integral presentation of a rational power series
  consists of coprime integer polynomials A and B with constant coefficients one and
  B times the series equal to A". Eight results concerned power-series normalization
  and Weierstrass preparation; no matching predicate.
- Loogle: "IsCoprime, Polynomial.map, PowerSeries". Zero results.
- Grep: `normalized.*fraction|Normalized.*Fraction|IsCoprime.*constantCoeff|num.*coeff 0 = 1`.
  Zero Mathlib results.
- LeanSearch: "normalized reduced integer polynomial fraction representing a rational
  power series". Eight results included `RatFunc.numDenom`, `RatFunc.num`, `RatFunc.denom`
  and `RatFunc.isCoprime_num_denom`. Read `numDenom`'s definition and docstring: monic
  denominator over a field is a different normalization from the node's integral pair.
- Direct `rg` of upstream `WeilConjectures`, project `lean/Sheaf` and
  `dag/lean_names_upstream.json` for normalized/integral/fraction variants initially found
  existence theorems but no predicate. Read local `ZetaLinearAlgebra/Fatou.lean` in full
  and `TraceDatum.exists_reduced_int_normalized_fraction` with its docstring.
  The exact node-id search and exact declaration-name search in these local trees
  returned no match because the checkout predates `ReciprocalRoots.lean`.
- The prescribed dry run found the name in the newer server source index. Read-only
  inspection of that exact record identified `WeilConjectures.ZetaLinearAlgebra.ReciprocalRoots`;
  `scompile.py --source` then supplied the exact predicate and its integral comparison.
  The proposed duplicate module was removed and this delivery binds the existing notion.

Validation: the delivery wrapper compiles an actual `#check` probe importing the
published module for this `existing: true` record. No authored Lean module is delivered.
No statement dispute or node fault remains.

## Second reading by N5

Independent maintainer second reading of immutable delivery
373675ddbb73e8c728cb00a94a45b5e55a0efcda, performed after delivery. This section
replaces the placeholder saying that no second reading occurred; it does not attribute
this reading to the original worker.

Read the item and all six statement dependency JSON records in the immutable snapshot,
the source blueprint definition (order 2862) in the read-only N5 clone, and the complete
published `WeilConjectures.ZetaLinearAlgebra.ReciprocalRoots` source obtained using
`scompile.py --source`. The older local upstream checkout lacks that module.

Clause checks, all correct:

- The indeterminate is the common formal variable of `Polynomial` and `PowerSeries`.
  For the node's integral series `f : PowerSeries ℤ`, use the existing predicate on
  `PowerSeries.map (Int.castRingHom ℚ) f`. This is the explicitly recorded inclusion.
- The pair is exactly `A B : Polynomial ℤ`; curried arguments represent the ordered pair.
- The first two conjuncts are exactly `A.coeff 0 = 1` and `B.coeff 0 = 1`.
- Reducedness is `IsCoprime` of the two coefficientwise images in `Polynomial ℚ`.
  Its definition is the required Bezout identity, so reducedness is over ℚ, not ℤ.
- The last conjunct is the fraction identity in rational formal power series.
  `PowerSeries.isNormalizedIntegralFraction_map_iff` identifies this with
  `f * (B : PowerSeries ℤ) = (A : PowerSeries ℤ)`. Commutativity gives the node's `Bf=A`.
  The comparison uses coefficient-map injectivity and polynomial-map compatibility,
  not an arbitrary comparison map or an additional hypothesis.
- Constant coefficient one and rationality need no extra predicate arguments:
  taking constant coefficients forces `f(0)=1`, and the mapped polynomials witness
  rationality with denominator constant coefficient one. On the stated ambient series,
  this predicate has precisely the requested meaning. Invertibility of `B` follows from
  the constant-coefficient unit criterion. No existence or uniqueness is asserted here.

Read exact dependency declarations and docstrings in pinned Mathlib:
`Polynomial` (Algebra/Polynomial/Basic.lean:74), `PowerSeries`
(RingTheory/PowerSeries/Basic.lean:60), `Polynomial.map`
(Algebra/Polynomial/Eval/Defs.lean:494), `PowerSeries.map` (Basic.lean:450),
`IsCoprime` (RingTheory/Coprime/Basic.lean:45), and
`Polynomial.coeToPowerSeries.ringHom` (PowerSeries/Basic.lean:836).
For the rational-series dependency, read `HahnSeries.ofPowerSeries` and injectivity
(HahnSeries/PowerSeries.lean:90,97); its recorded existential specialization is precisely
what the mapped numerator and denominator supply. No dependency interface repair is needed.

Edge checks: `f=A=B=1` is admitted; zero numerator and denominator violate normalization;
`f=0` cannot satisfy the identity; polynomial series with denominator one are admitted;
nonmonic denominators such as `1-2X` are admitted; `A=B=1+X` violates reducedness;
simultaneous multiplication by minus one violates normalization. The construction is
formal, not analytic. There are no scheme, index-set, characteristic, or universe binders
to restrict: the coefficient rings are exactly ℤ and ℚ and all arguments are bound.

Independent searches used reduced/integer/normalized fraction and integral-presentation
variants in upstream `WeilConjectures`, project `lean/Sheaf`, and Mathlib's RatFunc files.
Read `RatFunc.numDenom` (FieldTheory/RatFunc/Basic.lean:860): its monic field denominator
is a different normalization. The exact published predicate already supplies this notion;
`existing: true` correctly avoids duplication. The worker also records LeanSearch,
LeanFinder, Loogle, and grep searches.

The recorded `lean.statement` is verbatim the published definition signature, excluding
`:=`. No Lean module, new node, dependency repair, or statement correction is delivered.
The upstream module and definition docstrings explicitly identify the blueprint notion;
they use upstream blueprint wording rather than the new-module literal marker format.
Reusing that published module adds no local proofs or hollow definitions. The theorem
used for comparison is already proved upstream, not a stage-2 local proof.

Reproduced compilation through `scompile.py N5 def-weil-normalized-integral-fraction
/dev/stdin`, supplying only an import, `autoImplicit false`, `#check` commands for the
predicate, its integral comparison and its application, and `#print` of the predicate.
The wrapper's sandbox and library checks both exited cleanly, with no errors or warnings
(1.4 s and 1.6 s respectively, temporary overlay artifacts). The installed wrapper now
runs the overlay checks on the server; no direct ssh command, global build, live Lean
write, or project-clone edit was performed. This reproduces the worker's reported import
probe; there are no delivered Lean files requiring separate compilation.

Finding: H11, the original second-reading section was a placeholder, contrary to the
required real reading. This complete replacement report supplies the independent reading.
The worker report and mathematical binding are preserved. No substantive fault remains.
