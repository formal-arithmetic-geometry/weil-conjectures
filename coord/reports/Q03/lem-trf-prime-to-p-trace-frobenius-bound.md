## Worker report

The module `Sheaf.FieldTheory.PrimeToPTraceFrobeniusBound` defines
`Algebra.finiteDegreeNormalizedTrace` by the real construction
`(Module.finrank F E : F)⁻¹ • Algebra.trace F E`, with type `E →ₗ[F] F`.
It states `Algebra.finiteDegreeNormalizedTrace_primeTo_residueChar` with one
`sorry`. There are no other postponed proofs or hollow data. The helper is the
very map T introduced in this node, not a separate mathematical prerequisite.
Both declarations are recorded in `lean.declarations`.

The node's statement and dependency lists are unchanged. Only its `lean` field
is set. No correction, disputed statement, new node, or dependency repair is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Fields F and E, with arbitrary independent universes: `(F : Type u) (E : Type v)`
  and `[NontriviallyNormedField F] [NontriviallyNormedField E]`. These classes
  include `Field`, multiplicative real norms, definiteness, norm one of one, and
  nontriviality. The compatible inclusion is `[Algebra F E]` together with
  `hcompat : ∀ c : F, ‖algebraMap F E c‖ = ‖c‖`. A field algebra map is injective.
- Both absolute values are nonarchimedean: `[IsUltrametricDist F]` and
  `[IsUltrametricDist E]`. Their norm formulation is exactly the maximum triangle
  inequality, via `IsUltrametricDist.norm_add_le_max`.
- Both fields are complete for these norms: `[CompleteSpace F] [CompleteSpace E]`.
- The unit ball F° is `(NormedField.valuation (K := F)).integer`. The valuation is
  `nnnorm`; `Valuation.mem_integer_iff` therefore makes membership exactly
  `‖x‖ ≤ 1`. Its canonical valuation-ring instance is
  `ValuationRing.instValuationRingInteger`, which uses the dependency's
  `ValuationRing` notion, not a private definition.
- The residue field is
  `IsLocalRing.ResidueField (NormedField.valuation (K := F)).integer`.
  `IsLocalRing.ResidueField` is the quotient by `IsLocalRing.maximalIdeal`.
  `IsLocalRing.mem_maximalIdeal` identifies membership with being a nonunit, and
  `Valuation.Integer.not_isUnit_iff_valuation_lt_one` identifies this with
  `‖x‖ < 1`. Thus this is exactly the quotient in the node.
- Its positive characteristic is `(p : ℕ) (hp : 0 < p)` with
  `[CharP (IsLocalRing.ResidueField (NormedField.valuation (K := F)).integer) p]`.
  Primality follows from being the positive characteristic of a field; it is
  not an added hypothesis. The case p = 0 is excluded exactly as in the node.
- Finite extension of degree n: `[FiniteDimensional F E]`, with n written
  `Module.finrank F E`. There is no separately supplied degree or extra bound.
- Normal and separable: `[IsGalois F E]`. Reading `IsGalois` shows its two fields
  are `Algebra.IsSeparable F E` and `Normal F E`; reading those definitions gives
  separability and splitting of each element's minimal polynomial, respectively.
  In the finite setting this is the node's stated normality criterion.
- Prime-to-p degree: `hn : ¬ p ∣ Module.finrank F E`. No characteristic-zero,
  unramifiedness, or preassumed invertibility of the degree is introduced.
  Its image in F is nonzero as a consequence of this residue-characteristic
  condition; the helper uses field inversion directly.
- Field trace: `Algebra.trace F E`, whose definition is the composition of
  `LinearMap.trace F E` with multiplication as a linear endomorphism. Its source
  definition was read, not inferred from its name.
- The specified formula for T: the helper's body is degree inverse times that
  exact trace; scalar multiplication on the linear map evaluates to multiplication
  by the inverse in F. Its bundled type `E →ₗ[F] F` asserts F-linearity.
- Identity on F: the first conjunct is
  `∀ c : F, finiteDegreeNormalizedTrace F E (algebraMap F E c) = c`.
- Both estimates for every x: the second conjunct is `∀ x : E, ... ∧ ...`,
  with `‖finiteDegreeNormalizedTrace F E x‖ ≤ ‖x‖` and
  `‖finiteDegreeNormalizedTrace F E (x ^ p) -
  (finiteDegreeNormalizedTrace F E x) ^ p‖ ≤ ‖(p : F)‖ * ‖x‖ ^ p`.
- The integer p on the right is explicitly cast into F, not into the residue
  field or the reals. If `CharP F p`, this factor is zero, so the same estimate
  expresses exactly the final equal-characteristic clause of the node.

Dependency declarations and imports read:

- `def-weil-field`: Mathlib's `Field`,
  `Mathlib.Algebra.Field.Defs`, line 180. The field structures are inherited
  through the normed field classes, whose full signatures were read in
  `Mathlib.Analysis.Normed.Field.Basic`, lines 154–169.
- `def-trf-valuation-ring`: `ValuationRing` and `ValuationRing.TFAE`,
  `Mathlib.RingTheory.Valuation.ValuationRing`, lines 62–64 and 407–416.
  The canonical integer-ring instance at lines 480–481 uses this same notion.
- The unit ball uses `NormedField.valuation`,
  `Mathlib.Topology.Algebra.Valued.NormedValued`, and `Valuation.integer`,
  `Mathlib.RingTheory.Valuation.Integers`, lines 31–40.
- The residue quotient uses `IsLocalRing.ResidueField`,
  `Mathlib.RingTheory.LocalRing.ResidueField.Defs`, lines 28–32.
- The field trace is `Algebra.trace`, `Mathlib.RingTheory.Trace.Defs`, lines 67–70.
- Galois structure uses `IsGalois`, `Mathlib.FieldTheory.Galois.Basic`, lines 54–59;
  the full normal and separable signatures were also read in
  `Mathlib.FieldTheory.Normal.Defs` and `Mathlib.FieldTheory.Separable`.
- Stated proof dependencies are imported privately: the unique-absolute-value
  dependency through `spectralNorm_unique_field_norm_ext` in
  `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`, lines 770–773; the Galois-trace
  dependency through `trace_eq_sum_automorphisms` in
  `Mathlib.RingTheory.Trace.Basic`, lines 263–272; finite ultrametric sums through
  `IsNonarchimedean.apply_sum_le_sup` and `apply_sum_eq_of_lt` in
  `Mathlib.Algebra.Order.Ring.IsNonarchimedean`, lines 134–137 and 227–230.
  Their ambient binders and full signatures were read.
- `lem-trf-nonarchimedean-prime-power-root-estimates` has neither a Lean record nor
  a Mathlib match yet. It is a proof dependency only; no import or copy is made.
  The theorem's docstring names it explicitly at step 5 for later proof work.

Sources and proof plan: read the current blueprint ancestor
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`
and the node's complete six-step proof. Also opened the contextual primary source,
[Temkin, Stable modification of relative curves, §6.2](https://arxiv.org/html/0707.3953v3#S6.SS2),
in particular Proposition 6.2.4 and Lemma 6.2.10(i). The trace assertion is the
agent-supplied supplement as the node says, not a theorem attributed to Temkin.
The module/declaration docstrings say this and reproduce all six proof steps,
including the scalar normalization, uniqueness of extended norms, conjugate-sum
bound, pth-power estimates for conjugates and the n copies of one, and the final
algebraic identity and ultrametric bound.

Edge cases checked before writing:

- x = 0 gives zero on both sides of both estimates, with no nonzero-x binder.
- The identity extension has degree one and T = identity; both errors vanish.
- Equal characteristic p remains allowed: the residue characteristic assumption
  does not impose characteristic zero, and `‖(p : F)‖ = 0` forces exact Frobenius
  commutation. The extension degree is still nonzero in F because p does not divide it.
- Mixed characteristic keeps `‖(p : F)‖` as the actual small norm, not zero or one.
- Degree zero is impossible for a finite field extension; p-divisible degrees
  are excluded by the exact stated premise, not by an additional hypothesis.
- A trivial valuation is excluded by the node's nontriviality premise. Both norms
  may be nondiscrete. No chosen uniformizer or rank/discreteness condition is used.
- The fields inhabit independent universes; no equality of universes is imposed.

Searches made (all before introducing the helper):

1. `msearch.py ... leanfinder` with query
   `Normalized trace in a prime-to-residue-characteristic finite Galois extension of complete nonarchimedean fields is norm nonincreasing and commutes with pth powers up to norm p times norm x to p`.
   Eight hits, including `Algebra.normalizedTrace_map`, spectral norm results,
   and integral norms; none states the two trace estimates.
2. `msearch.py ... loogle 'Algebra.trace'`: twelve hits. `Algebra.trace` is the
   exact field-trace construction; `Algebra.trace_algebraMap` supplies the scalar
   identity for later proof. Neither gives the valued Frobenius bound.
3. `msearch.py ... grep 'normalizedTrace|trace.*norm|trace.*pow' RingTheory/Trace`:
   five hits in Trace.Basic, all power-basis trace calculations, not this assertion.
4. `rg` in Mathlib and in `lean/WeilConjectures`, `lean/Sheaf`, and
   `dag/lean_names_upstream.json` for normalized trace, trace norm/power estimates,
   the item id, and both proposed declaration names. No existing exact statement
   or degree-normalized helper covering positive characteristic was found.
   Project hits concern sheaf traces, finite-dimensional Frobenius modules, and
   proper-curve trace normalization, which are different notions.
5. Read `Mathlib.FieldTheory.NormalizedTrace`: the public `Algebra.normalizedTrace`
   assumes `[CharZero F]`; its auxiliary definition is private and normalizes the
   trace on a simple adjoin. It is not the finite-degree interface needed here.
   The delivery therefore reuses `Algebra.trace` with one scalar multiplication
   rather than excluding equal characteristic p.
6. Focused `rg` searches for `NormedField.valuation`, integer rings, residue fields,
   and valuation-ring instances found the canonical Mathlib constructions used
   above; no duplicate valuation ring or residue-field definition was introduced.

Validation: `scompile.py` compiled the delivered module in sandbox and library
modes cleanly (1.5 seconds each on the first pass). `autoImplicit` is disabled in
the final file, and universes and all binders are explicit. The required dry run
and delivery perform the final compile and server preflight.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
