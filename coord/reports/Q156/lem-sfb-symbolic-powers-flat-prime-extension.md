## Worker report

The module `Sheaf.RingTheory.SymbolicPowersFlatPrimeExtension` states
`Ideal.map_symbolic_power_of_flat`, with its sole proof `by sorry`.
It uses the node's inline definition of symbolic power directly as
`Ideal.comap (algebraMap T (Localization.AtPrime P))
  (Ideal.map (algebraMap T (Localization.AtPrime P)) (P ^ n))`.
Thus no new definition, helper, dependency repair, or statement correction is needed.
The source read was `literature/stacks-project/algebra.tex`,
`definition-symbolic-power` (Tag 0313), lines 15549 onward, and
`lemma-symbolic-power-flat-extension` (Tag 0BC0), lines 15578–15615.
The node retains its explicitly permitted Noetherian restriction of Tag 0BC0.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Commutative rings R and S | `{R : Type u} {S : Type v} [CommRing R] [CommRing S]` |
| Both rings Noetherian | `[IsNoetherianRing R] [IsNoetherianRing S]` |
| Ring homomorphism R → S | `(f : R →+* S)` |
| Flat homomorphism | `(hf : f.Flat)`, the recorded `RingHom.Flat` |
| Prime ideal p of R | `(p : Ideal R) [p.IsPrime]` |
| Extended ideal q = pS is prime | `[(Ideal.map f p).IsPrime]`; q is substituted by its definition |
| Every integer n ≥ 0 | `(n : ℕ)` |
| T localized at the complement of P | `Localization.AtPrime P` |
| Localization map x ↦ x/1 | `algebraMap T (Localization.AtPrime P)` |
| Ordinary power extended to T_P | `Ideal.map (algebraMap T (Localization.AtPrime P)) (P ^ n)` |
| Symbolic power: x/1 belongs to that ideal | `Ideal.comap` of the preceding ideal under the same localization map |
| P^0 = T | Mathlib's ideal power with natural exponent, including `n = 0` |
| p^(n) extended to S | `Ideal.map f` of the symbolic-power expression for p |
| Equality with q^(n) | The right side is precisely that expression with `T = S`, `P = Ideal.map f p` |

`Ideal.map` is ideal extension (the span of the image), not merely the set image.
`Ideal.comap` is the inverse image. These definitions were read in
`Mathlib/RingTheory/Ideal/Maps.lean`, lines 41–54. The comap expression therefore
literally has the set of elements specified in the node. It also equals the
kernel formulation of Tag 0313 by the definition of the quotient map.
The separate universe variables u and v impose no equality of ring sizes.
No algebra, domain, injectivity, faithful flatness, or lies-over hypothesis is added.
All variables are explicit; `autoImplicit` is disabled in the file.

Statement dependency declarations read and used:

- `def-weil-pbc-flat-ring-map`: `RingHom.Flat`,
  `Mathlib.RingTheory.RingHom.Flat`; its data is `Module.Flat R S` for `f.toAlgebra`.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`; the ideals are the submodules of R over itself.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`,
  `Mathlib.RingTheory.Localization.AtPrime.Basic`; it is `Localization P.primeCompl`.

Every recorded statement-dependency module is publicly imported. The declarations
of all proof dependencies were also read, including their full signatures and
surrounding docstrings; their modules are imported for the stage-3 proof plan:

- `lem-weil-pbc-flat-tensor-exact`: `Module.Flat.lTensor_exact` and
  `Module.Flat.rTensor_exact`, `Mathlib.RingTheory.Flat.Basic`.
- `lem-weil-pbc-tensor-over-quotient-ring`: `TensorProduct.quotTensorEquivQuotSMul`,
  `Mathlib.LinearAlgebra.TensorProduct.Quotient`, and
  `TensorProduct.AlgebraTensorModule.cancelBaseChange`,
  `Mathlib.LinearAlgebra.TensorProduct.Tower`.
- `lem-weil-pbc-localization-tensor-over-base`: `IsLocalizedModule.rTensor` and
  `IsLocalizedModule.map_lTensor`, `Mathlib.RingTheory.Localization.BaseChange`.
- `lem-weil-pbc-module-tensor-cancel-base-change`:
  `TensorProduct.AlgebraTensorModule.cancelBaseChange`,
  `Mathlib.LinearAlgebra.TensorProduct.Tower` (shared import).
- `def-weil-pbc-localization-at-prime`: same public localization import as above.
- `lem-weil-pbc-vector-space-free`: `Module.Free.of_divisionRing`,
  `Mathlib.LinearAlgebra.Basis.VectorSpace`.

Edge cases checked mathematically before writing:

- `n = 0`: ordinary powers are the unit ideal; extension and contraction here
  preserve the unit ideal, and both sides are S.
- `n = 1`: contracting pR_p gives p; likewise for q, so this is pS = q.
- Identity homomorphism: the same contraction expression occurs on both sides.
- Polynomial extension k[t] → k[t,x], p = (t): powers and symbolic powers are
  the corresponding (t^n), and the statement gives their usual extensions.
- Zero prime of a domain, when its extension is prime: localization at (0) is
  injective; positive symbolic powers are zero, and the displayed equality agrees.
- Zero rings have no prime ideals, so they satisfy no missing prime case;
  no separate `Nontrivial` hypothesis is required.
- Non-domain rings and noninjective flat maps are allowed. For example, the flat
  projection k × k → k with p = 0 × k has q = 0; positive symbolic powers of p
  are p and extend to zero, as required.
- The flat map k[t] → k[s], t ↦ s², does not have prime extension of (t):
  q = (s²) is not prime. This verifies the extended-prime assumption has content.

Searches for an existing declaration (all via the prescribed `msearch.py`, Q156,
item `lem-sfb-symbolic-powers-flat-prime-extension`, 2026-10-24):

- leanfinder: `Symbolic powers of prime ideals commute with flat extensions when
  the extended ideal is prime`: eight hits, including `Algebra.HasGoingDown.of_flat`,
  `instFlatAtPrime`, and `Ideal.exists_isPrime_liesOver_of_faithfullyFlat`;
  none states the symbolic-power equality.
- leansearch: `Symbolic powers commute with flat ring extensions if a prime ideal
  extends to a prime ideal`: eight hits about localized flatness, faithful-flat
  contraction, and base change; none gives the equality here.
- loogle: `Ideal.map, Ideal.comap, Localization.AtPrime`: two fibre-localization
  equivalences, `Ideal.Fiber.algEquivAux₂` and
  `Ideal.Fiber.localizationAlgEquivQuotient`; neither is the statement.
- grep, RingTheory: `symbolic[Pp]ow|symbolic_power|symbolic power`: only two
  docstring lines in `Mathlib/RingTheory/Polynomial/Eisenstein/Criterion.lean`.
- `rg` with the same pattern over both `lean/WeilConjectures` and `lean/Sheaf`:
  only proof commentary in `LocalGenericUnitFactorization.lean`; no declaration.
- Exact item-id search over `lean/WeilConjectures`: no match.
- Name-clash search for `map_symbolicPower_of_flat` and
  `map_comap_pow_localizationAtPrime_of_flat` in Mathlib, both project libraries,
  and `dag/lean_names_upstream.json`: no match; the delivered declaration name
  is separately checked by delivery preflight.
- DAG search for symbolic powers: nodes about completion, Krull quotients, and
  the present item; no standalone symbolic-power definition is needed because
  the item already defines it inline and the Lean renders that inline expression.

No STATEMENT-DISPUTED issue was found. The source proof's final word
“invertibly” is understood as “injectively”, as explicitly recorded in the node's
proof_origin. The theorem's docstring includes all seven proof steps and names
every dependency used by them, including the denominator-clearing step.
The example CompactObject module was read; it is currently withdrawn and contains
no declarations. The delivered file follows the current required module header,
public/private import convention, expose section, source docstrings, and line width.

Validation: `scompile.py Q156 lem-sfb-symbolic-powers-flat-prime-extension` on the
single delivered module succeeded both for the sandbox and its actual library
module name, with no errors or warnings (7.2 s and 1.2 s respectively).

## Second reading by Q156

I reopened the node and the delivered module for a separate second pass. This is
an in-worker rereading: the dispatcher's explicit instruction prohibits starting
another agent; the maintainer's independent review remains separate.
The second pass checked both CommRing and both IsNoetherianRing binders, arbitrary
f and its flatness, p prime, the exact extended ideal prime, and all n including 0.
The ideal maps and comaps are ordered correctly: first extend p^n to R_p, contract
to R, and extend to S; on the right extend q^n to S_q and contract to S.
Substituting q = Ideal.map f p eliminates a redundant name and requires no added
condition. Checking the implementation of Ideal.comap shows membership is exactly
x/1 ∈ P^n T_P. The statement includes no ordinary-power/symbolic-power substitution.
No mismatch was found and no mathematical change was necessary. Only `lean` is
changed in the copied node; its statement, dependencies, and proof are preserved.
