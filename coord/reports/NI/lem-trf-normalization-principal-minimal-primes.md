## Worker report

Repaired return H1 for immutable delivery fb4f905639b0. That delivery was a stage-1 split;
this packet supplies the missing stage-2 theorem, its item `lean` record, the worker report,
and per-file compiler evidence. The retained sandbox contained only dispatcher markers,
so there was no earlier Lean implementation to preserve. The node copy starts from the
current shared DAG (including its six-step proof); only `lean` changes. Delivery is rebased
by the prescribed delivery wrapper against current `origin/newtargets-dag`.

Module: `Sheaf.RingTheory.NormalizationPrincipalRadical`.
Declaration: `Ideal.integralClosure_principal_radical_eq_finite_iInf_primes`.
It is a theorem with the sole proof `sorry`; it introduces no definitions or helper axioms.
The module and declaration docstrings identify the node and carry its six-step proof.

Hypothesis and clause comparison:

| Node text | Lean rendering |
| --- | --- |
| Commutative ring R | `(R : Type u) [CommRing R]` |
| Noetherian | `[IsNoetherianRing R]` |
| Domain, including 1 ≠ 0 and no zero divisors | `[IsDomain R]` |
| K = Frac(R) | `(K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]` |
| Field extension F/K | `(F : Type w) [Field F] [Algebra K F]` |
| Finite dimension over K | `[FiniteDimensional K F]` |
| R inside F through R → K → F | `[Algebra R F] [IsScalarTower R K F]` |
| D is the integral closure of R in F | the existing subtype `integralClosure R F` |
| Every nonzero b in D | `(b : integralClosure R F) (_hb : b ≠ 0)` |
| Finitely many ideals Q₁,…,Qₜ | `∃ (t : ℕ) (Q : Fin t → Ideal (integralClosure R F))` |
| Each ideal is prime | `∀ i : Fin t, (Q i).IsPrime` |
| Principal ideal bD | `Ideal.span ({b} : Set (integralClosure R F))` |
| Its radical | the existing `.radical` operation |
| Equality with the intersection | `.radical = ⨅ i : Fin t, Q i` |
| Empty intersection is D | `Fin 0` is empty; the empty infimum is `⊤` |
| No Noetherian or finite-module hypothesis on D | neither is a binder |

The scalar tower expresses compatibility with the specified field extension; it does not
restrict the mathematics. Any extension F/K has the R-algebra structure induced by composition.
`K` is any model of the fraction field, with independent explicit universes `u v w` for all
three rings. No test-object quantifier imposes a universe restriction. `autoImplicit` is false.

Dependencies read and reused directly:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`, the abbreviation for `IsNoetherian R R` and its
  documentation that every ideal is finitely generated.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`; with the two field
  structures, its `algebraMap` is precisely the extension map.
- `def-weil-pbc-integral-closure`: `integralClosure`,
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, whose actual carrier is
  `{x | IsIntegral R x}`. Read `IsIntegral` and `RingHom.IsIntegralElem` in
  `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs`: a monic polynomial vanishing at x.

Additional standard Mathlib interfaces read: `IsFractionRing` is localization at the
nonzero divisors (`Mathlib.RingTheory.Localization.FractionRing`);
`FiniteDimensional` is `Module.Finite` over a division ring
(`Mathlib.LinearAlgebra.FiniteDimensional.Defs`); and `Ideal.radical` in
`Mathlib.RingTheory.Ideal.Operations` has carrier `∃ n : ℕ, x^n ∈ I`.
Although Mathlib allows n = 0 here, this agrees with the node's positive-exponent definition:
n = 0 forces 1 ∈ I, hence I = ⊤, and exponent 1 then works for every x.
The finite intersection uses the existing complete lattice of ideals, not a private notion.

The stated Mathlib proof dependencies are available through the imports:
`Algebra.finite_adjoin_of_finite_of_isIntegral` and `Algebra.IsIntegral.of_finite`
through `IntegralClosure.Algebra.Basic`, `Algebra.FiniteType.isNoetherianRing` through
`Mathlib.RingTheory.FiniteType`, and `RingHom.IsIntegral.trans` through
`Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic`.
The last two modules are ordinary proof-only imports. The two structural children
`lem-trf-normalization-integral-closure-krull` and
`lem-trf-krull-principal-primary-decomposition` currently have neither a Lean record nor a
Mathlib match; they are proof dependencies only, so no import can yet be added for them.
The present statement does not require their definitions.

Edge cases checked before drafting:

- A unit b gives bD = ⊤; choose t = 0, so primehood is vacuous and the intersection is ⊤.
- If R is a field and K = R, any finite F/K is integral over R, and D is F; all allowed
  b are units, handled by the same empty family.
- A nonunit does not permit an empty intersection: the left side remains a proper radical.
- b = 0 is excluded exactly as in the node. No separability, dimension-one, or normality
  hypothesis on R is imposed. Arbitrary characteristic and inseparable finite extensions
  remain included. No Noetherianity of D is inferred or assumed.
- Neither height one nor minimality of the Qᵢ is asserted: the node's title does not add
  these to its actual statement.

Searches performed with the prescribed search wrapper, plus direct source inspection:

- LeanFinder: “In the integral closure of a Noetherian domain in a finite extension of
  its fraction field every nonzero principal ideal has radical a finite intersection
  of prime ideals”. Eight hits, including `IsDedekindDomain`, `primesOver_finite`, and
  `Ideal.finite_factors`; all impose extra Dedekind or finiteness hypotheses.
- Loogle: `integralClosure, Ideal.radical`. Two conductor lemmas in
  `Mathlib.RingTheory.ZariskisMainTheorem`, neither the requested statement.
- grep: `Mori.Nagata|KrullDomain|radical.*principal`, subdirectory `RingTheory`.
  One documentation hit in `Radical/Basic.lean`, no theorem match.
- LeanSearch: “finite intersection prime ideals radical nonzero principal ideal integral
  closure Noetherian domain finite field extension”. Eight hits; `Ideal.radical_eq_sInf`
  and `Ideal.sInf_minimalPrimes` give unrestricted intersections, not finite ones.
  `integralClosure.isIntegrallyClosedOfFiniteExtension` proves normality, not the result.
- Direct `rg` over upstream `WeilConjectures` and project `lean/Sheaf` for
  `lem-trf-normalization-principal-minimal-primes|normalization.*principal|radical.*integralClosure|integralClosure.*radical`:
  only unrelated normalization/affine-open declarations; no exact result. The required
  exact node-id search in upstream has no occurrence. An exact search for the chosen
  declaration name in upstream, Mathlib, `dag/lean_names_upstream.json`, and side-project
  sources has no occurrence.
- Inspected `Ideal/MinimalPrime/Noetherian.lean`: its finiteness result assumes the ideal's
  ambient ring is Noetherian. Applying it to D would add a forbidden hypothesis.
- Inspected `DedekindDomain/IntegralClosure.lean`: its Noetherianity theorem requires an
  integrally closed base and a separable extension, neither assumed here.

Read the author-hosted book, especially PDF pp. 96–98 and 102–105 (printed pp. 83–85,
89–92): [Swanson–Huneke](https://www.math.purdue.edu/~iswanso/book/SwansonHuneke.pdf).
The finite integral model reduction and the Krull principal decomposition support the
unchanged six-step proof. The node's top-level source mentions Proposition 4.8.5; its proof
steps and proof-origin also correctly identify the proof of Proposition 4.8.2. The module
cites the latter directly; no source metadata is silently edited.

No statement correction, new node, dependency replacement, or disputed statement is needed.

## Second reading by NI

Author's second pass only; no independent worker was started, as the dispatcher brief
forbids sub-agents. The maintainer performs the independent review.

Reopened the current node and the complete module and checked each row above. All three
ring universes and all structures are explicitly bound. `IsFractionRing` and the scalar
tower fix the intended composite inclusion, and D is the actual Mathlib integral closure.
The conclusion has exactly a finite prime family, with no extraneous nonempty,
height-one, or minimality condition. The positive-exponent and empty-family conventions
match the node. The only changes from returned H1 are the missing stage-2 artifacts;
the node statement and six proof steps are retained. No mismatch was found in this pass.

## Validation

`scompile.py NI lem-trf-normalization-principal-minimal-primes
lean/Sheaf/RingTheory/NormalizationPrincipalRadical.lean` exited 0. The wrapper compiled
the sandbox statement and then the library module; the library module took 7.3 s.
No errors or unexpected warnings were printed. The complete output is retained in the
sandbox at `scratchpad/compile.log`. No direct Lean/Lake or global build was run.

The prescribed `deliver2.py NI lem-trf-normalization-principal-minimal-primes --no-push`
dry run passed preflight and compilation (initial reviewable commit `10ad2832a7`).
A final dry run follows the docstring refinement adding the exact proof-dependency ids.
The theorem signature is unchanged by that refinement. Compiler and dry-run output are
retained under `scratchpad/` in the sandbox.
