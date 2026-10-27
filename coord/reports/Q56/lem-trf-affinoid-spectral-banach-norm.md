## Worker report

Item: `lem-trf-affinoid-spectral-banach-norm`, group Q56, stage 2.
The new module `Sheaf.RingTheory.AffinoidSpectralBanachNorm` states
`RestrictedSeries.affinoid_spectral_banach_norm`, with its sole proof `sorry`.
No definition is introduced, and the node changes only in `lean`.

The source was checked at Conrad, *Several approaches to non-archimedean geometry*,
Theorem 1.2.6(1),(5) and the following paragraph, PDF pp. 6--7:
https://math.stanford.edu/~conrad/papers/aws.pdf . The theorem states Banach-norm
equivalence and the reduced affinoid supremum norm; the next paragraph states
power multiplicativity and notes that full multiplicativity can fail. The node's
proof supplies the sharper lower constant one for Tate quotient norms. BGR
Theorem 6.2.4/1 is the node's primary citation; its archival PDF is absent, as
already recorded in the node. The latest blueprint's
`sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md` was read:
this is a historical supporting analytic input, not that unit's own statement.

Hypothesis-by-hypothesis rendering:

- The field is `K : Type u` with `NontriviallyNormedField K`. This includes the
  field laws and a nontrivial real-valued multiplicative absolute value.
- Nonarchimedeanness is `IsUltrametricDist K`; completeness is `CompleteSpace K`;
  algebraic closedness is `IsAlgClosed K`. No characteristic is fixed.
- `C : Type v` has `CommRing C`, `Algebra K C`, `Nontrivial C`, and `IsReduced C`:
  it is the specified nonzero reduced commutative unital K-algebra. Universes
  `u` and `v` are independent and explicit.
- `TopologicalSpace C` is its given affinoid Banach topology. The hypothesis
  `haff` says there are `r : ℕ` and a surjective ring map `q` from Mathlib's
  `MvPowerSeries.IsRestricted.subring` at polyradius one, with
  `q.comp (constants K r) = algebraMap K C`. Thus `q` is exactly a unital
  scalar-compatible Tate-algebra quotient map.
- The final clause of `haff` identifies the open sets of C with those whose
  inverse images are open in Gauss-norm balls: at every `s` mapping into U,
  some positive epsilon-ball around s maps into U. This is precisely the
  affinoid quotient topology; it does not use the coefficientwise product
  topology. No extra chosen norm, continuity assumption on characters, or
  Banach-algebra structure on the restricted-series subring is hypothesized.
  The existence of the Banach norm inducing this topology is a conclusion.

Clause-by-clause rendering of the conclusion:

- `∃ ρ : AlgebraNorm K C` supplies a genuine K-algebra norm. Its `RingNorm`
  fields give zero preservation, invariance under negation, nonnegativity,
  and `ρ c = 0 ↔ c = 0`; `mul_le'` is `ρ (c*d) ≤ ρ c * ρ d`.
  The inherited `Seminorm.smul'` is `ρ (a • c) = ‖a‖ * ρ c`, where the
  algebra action is multiplication by `algebraMap K C a`.
- The first conjunct fixes its value at every c to
  `sSup {x : ℝ | ∃ χ : C →ₐ[K] K, Continuous χ ∧ x = ‖χ c‖}`.
  `AlgHom` includes unitality and scalar compatibility, and continuity is
  explicitly for the given topology on C and the absolute-value topology on K.
  This pins the existential norm to the actual character supremum rather than
  asserting only existence of some equivalent norm.
- `ρ 1 = 1` is explicit. `IsNonarchimedean ρ` means
  `∀ c d, ρ (c+d) ≤ max (ρ c) (ρ d)` over the real numbers.
- `IsPowMul ρ` means `∀ c {m : ℕ}, 1 ≤ m → ρ (c^m) = (ρ c)^m`.
- `@CompleteSpace C ρ.toRingNorm.toNormedRing.toUniformSpace` is completeness
  for the metric of this very norm, with distance `ρ (c-d)`.
- Equality of `ρ.toRingNorm.toNormedRing.toUniformSpace.toTopologicalSpace`
  with the given `TopologicalSpace C` asserts that this complete norm induces
  the affinoid Banach topology.
- Finally, `∀ r q` ranges over every Tate presentation, not just the one in
  `haff`. Surjectivity and scalar compatibility are its only hypotheses.
  The real `sInf` of Gauss norms of lifts of c is the quotient norm, exactly
  as in the recorded dependency `IsAffinoidQuotient`. The conclusion supplies
  `M : ℝ` with `1 ≤ M`, uniform over `∀ c`, and both inequalities
  `ρ c ≤ quotientNorm c` and `quotientNorm c ≤ M * ρ c`. This includes every
  Tate quotient norm even when two presentations give different norms.

Dependency declarations read and used:

- `def-weil-field` has mathlib match `Field`, read in
  `Mathlib.Algebra.Field.Defs`; inherited by `NontriviallyNormedField`.
- `def-trf-restricted-series-presentation` records
  `Sheaf.RingTheory.RestrictedSeriesPresentation`. Its full module and
  docstrings were read, including `RestrictedSeries.constants` and
  `RestrictedSeries.IsAffinoidQuotient`. The statement uses the existing
  constants map, restricted-series subring and Gauss norm directly. The
  predicate `IsAffinoidQuotient` requires a particular quotient norm as the
  ambient norm on C, so using it as the hypothesis would unnecessarily choose
  that norm. Instead `haff` expresses just the topology, exactly as the existing
  `RestrictedSeries.grauert_remmert_powerbounded` interface does. No competing
  affinoid predicate or restricted-series construction is defined.
- `AlgebraNorm`, `RingNorm.toNormedRing`, `IsNonarchimedean`, `IsPowMul`,
  `MvPowerSeries.IsRestricted.subring`, and `MvPowerSeries.gaussNorm` were
  read in Mathlib, including their inherited signatures and norm fields.
- The proof-only imports are `Mathlib.Analysis.Normed.Algebra.Spectrum`
  (`AlgHom.norm_apply_le_self`, recorded mathlib match for
  `lem-per-banach-character-norm-bound`) and
  `WeilConjectures.RingTheory.TraceFormEtaleField`
  (`Algebra.traceForm_nondegenerate_iff_etale`). Their full signatures and
  docstrings were read. The six other proof dependencies currently have no
  recorded Lean module, so there is no module to import for them. They do not
  supply any additional object needed to type this statement. Their uses are
  all included in the seven-step natural-language proof in the docstring.

Edge cases checked before writing:

- `r = 0` is permitted both in `haff` and in the universal comparison: the
  multi-index type is `Fin 0 →₀ ℕ`, so the Tate algebra is K. For C = K the
  scalar character gives the original absolute value and M = 1.
- C = 0 is excluded exactly by `Nontrivial C`, as in the node. A nonzero
  quotient cannot have the zero quotient norm, and has a maximal ideal.
  Algebraic closedness makes its residue field K; the corresponding character
  is continuous. The character indexing family is therefore nonempty.
- Products such as K × K and the nodal reduced algebra K⟨X,Y⟩/(XY) are allowed:
  `IsReduced` does not impose `IsDomain`, and `AlgebraNorm` imposes only
  submultiplicativity. In K × K the two orthogonal idempotents show why a
  multiplicative norm must not be requested.
- Nonreduced quotients are excluded exactly as required: characters kill
  nilpotents, so without `IsReduced` separation would fail.
- c = 0, a = 0, c = 1, and m = 1 give the stated norm laws. m = 0 is not
  required by `IsPowMul`. Both characteristic zero and positive characteristic
  are allowed. Real-valued nontrivial absolute values need not be discrete.
- Every lift set in the quotient norm is nonempty by surjectivity and bounded
  below by zero; the coefficient suprema are finite for restricted series.
  Character values are bounded by each quotient norm by the proof's first
  step, so the real supremum is the intended finite one.

Searches for an existing statement (all prescribed search wrappers used group
Q56 and this item's id):

- `msearch.py leanfinder`: "The supremum over continuous scalar valued
  characters on a reduced affinoid algebra is a complete power multiplicative
  norm equivalent to every Tate quotient norm". Eight hits, headed by
  `spectralNorm_unique`, `spectralMulAlgNorm`, and `spectralAlgNorm`.
  Their signatures concern algebraic FIELD extensions; they do not handle
  arbitrary reduced affinoid algebras or quotient-norm comparison.
- `msearch.py loogle`: `spectralAlgNorm, IsPowMul`. Two hits,
  `spectralAlgNorm_isPowMul` and `spectralNorm_unique`, both with `[Field L]`
  and `[Algebra.IsAlgebraic K L]`. Neither matches the node.
- `msearch.py leansearch`: "reduced affinoid spectral supremum norm complete
  equivalent quotient norm". Eight hits including `spectralNorm.completeSpace`
  and `Ideal.Quotient.normedCommRing`. They provide field-extension or normed
  quotient infrastructure, not this spectral Banach theorem.
- `msearch.py grep`: `affinoid|spectralAlgNorm|AlgebraNorm`, subdirectory
  `Analysis/Normed/Unbundled`. Twenty hits, including `AlgebraNorm.lean` and
  `SpectralNorm.lean`; reuse the bundled norm, but no affinoid theorem exists.
- Direct `rg` searches of both `lean/WeilConjectures` and `lean/Sheaf` for
  `affinoid`, `Affinoid`, `spectralBanach`, `RestrictedSeries`, and the proposed
  declaration name, plus the exact node id in `lean/WeilConjectures` and
  `dag/lean_names_upstream.json`: found the presentation definitions and
  affinoid polynomial comparison / Grauert--Remmert consumers, and many
  unrelated algebraic-field spectral-norm consumers, but no duplicate theorem.
  There is no repair note for this item in `coord/repair-notes`.

No statement fault or `STATEMENT-DISPUTED` issue was found. No new node,
dependency repair, target change, or node-statement correction is required.

## Second reading by Q56

A separate second pass re-read the original node and the complete new module.
This is Q56's own verification; no second agent was started, as the dispatcher
explicitly forbids it. The maintainer's independent delivery review remains
the independent reading.

The pass checked each binder against the original hypotheses, the precise
definition of the Tate subring and Gauss norm, and both directions of the
quotient-topology open-set condition. In particular the topology on C is not
silently set to the formal-series product topology. It checked the `AlgebraNorm`
inheritance for separation, negation, submultiplicativity and scalar equality;
normalization is a separate conjunct because `AlgebraNorm` alone does not
normalize at 1. It read `IsPowMul` to confirm the exact range `1 ≤ m` and checked
that the complete uniformity and topology equality are both built from the
same existential norm. The final `∀ r q` really quantifies every scalar-compatible
surjection, with one M for all c, rather than only the initially chosen
presentation. Character continuity uses the original topology. No mismatch
was found and no mathematical change was made during this pass.
