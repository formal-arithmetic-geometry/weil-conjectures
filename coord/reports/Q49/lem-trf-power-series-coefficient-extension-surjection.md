## Worker report

Q49 states `MvPowerSeries.exists_coefficient_extension_surjection` in
`Sheaf.RingTheory.PowerSeriesCoefficientExtensionSurjection`. This is a single theorem
with the single proof `by sorry`; it defines no new notion. The item node changes only
in `lean`. No statement correction, new node, dependency repair, or disputed statement
is needed.

Source read: `literature/stacks-project/varieties.tex`, Tag 0C54,
`lemma-base-change-complete-local-ring`, especially lines 4122–4182: compatible coefficient
fields, generators of the extended maximal ideal, the surjection on power series, vanishing
of transported relations, and the quotient square. The node abstracts this part of the
proof to compatible complete local rings; the theorem retains exactly that abstraction.
It does not assert the later injectivity conclusion, which requires flatness.

Hypotheses, each matched to the Lean signature:

- Fields `F,K` and the embedding: the two independently universe-polymorphic types with
  `[Field F] [Field K]` and `(ι : F →+* K)`. A unital homomorphism from a field to a field
  is automatically injective, so no injectivity assumption is added or omitted.
- Nonzero commutative Noetherian local rings `R,C`: `[CommRing R] [CommRing C]`,
  `[IsNoetherianRing R] [IsNoetherianRing C]`, and `[IsLocalRing R] [IsLocalRing C]`.
  Mathlib's `IsLocalRing` extends `Nontrivial`; thus these include the nonzero condition.
- Complete and separated maximal-ideal-adic topologies: the two
  `[IsAdicComplete (IsLocalRing.maximalIdeal ...) ...]` binders, which include Hausdorffness.
- The two residue identifications: `(ρR : R ⧸ maximalIdeal R ≃+* F)` and the analogous
  `ρC`. The coefficient sections are encoded by `[Algebra F R] [Algebra K C]`, with
  `σ = algebraMap F R` and `τ = algebraMap K C`. The equations `hσ` and `hτ` state that
  composing each section with the quotient and the given residue identification is the
  identity. Specifying an algebra structure is equivalent to specifying the ring section;
  no scalar action or section is chosen arbitrarily.
- The continuous local ring homomorphism: `(h : R →+* C)`, `hlocal` for containment of
  maximal ideals, and `hcont` for each target ideal power containing the image of some
  source ideal power. For an additive ring map this is exactly adic continuity at zero,
  hence continuity everywhere. The ideal-extension equality is `hm` using `Ideal.map h`.
  The compatibility `hσ = τι` is `hcompat`, an equality of composed ring homomorphisms.
- The nonnegative integers are `n s : ℕ`; their indexing types are `Fin n` and `Fin s`.
- The chosen continuous surjective `F`-algebra presentation is
  `φ : MvPowerSeries (Fin n) F →ₐ[F] R`, with `hφ` and `hφcont`. The algebra-homomorphism
  type fixes the constants to the specified section.
- Its kernel `I=(f₁,...,fₛ)` is rendered directly by
  `hker : RingHom.ker φ.toRingHom = Ideal.span (Set.range f)`; `hrel` is precisely
  containment of this generated ideal in the variables ideal. There is no independent
  unspecified ideal or missing relation condition.

Objects and conclusion clauses:

- The coefficientwise `j` is the existing `MvPowerSeries.map ι`. Its definition applies
  `ι` to every coefficient, including when the field universes differ.
- `∃ J, J = Ideal.span (Set.range (fun a ↦ map ι (f a))) ∧ ...` fixes the ideal `I_K`
  to its exact stated construction. This existential with its defining equality merely
  names that ideal without file-local notation, a new definition, or an arbitrary choice.
  Everywhere `T` is the actual quotient `MvPowerSeries (Fin n) K ⧸ J`, and `π` is the
  actual quotient ring map `Ideal.Quotient.mk J`.
- `∃ Ψ : MvPowerSeries (Fin n) K →ₐ[K] C` is the asserted algebra map; the following
  `Function.Surjective Ψ`, ideal-power condition, and variable-image equations give its
  surjectivity, continuity, and prescribed values. The next equality of composed ring
  homomorphisms is exactly `Ψj=hφ` on all series.
- `J ≤ RingHom.ker Ψ.toRingHom` is annihilation of the entire transported relation ideal.
- `∃ θ : T →ₐ[K] C`, `Function.Surjective θ`, and the equality for every power series
  `g` give the surjective quotient algebra map and `θπ=Ψ`.
- `IsNoetherianRing T` and the existential `IsLocalRing T` give Noetherianity and locality
  of the same quotient ring. Binding the latter instance permits reference to its actual
  maximal ideal. Its equality with the span of `Ideal.Quotient.mk J (X i)` is the exact
  stated generating-ideal formula.
- `ρT : T ⧸ maximalIdeal T ≃+* K` asserts the residue field. Its normalization on each
  constant class fixes the identification to the canonical coefficient identification,
  so the final compatibility cannot be made true by choosing a different field isomorphism.
- `∃ α : R →+* T` has explicit maximal-ideal containment (locality), followed by the
  ring-map equation `α.comp φ.toRingHom = (Ideal.Quotient.mk J).comp (map ι)`.
  The universal equality for any other `α'` satisfying this factorization is the requested
  uniqueness. `θ.toRingHom.comp α = h` is the remaining commuting square.
- `Ideal.map α (maximalIdeal R) = maximalIdeal T` says `m_R T = m_T`.
- The final equation for every `x : T`,
  `ρC (Ideal.Quotient.mk _ (θ x)) = ρT (Ideal.Quotient.mk _ x)`, states the identity
  on `K` after reducing `θ`. Together with `hm` and the preceding ideal-extension equality,
  these quotients are exactly the node's `C/m_R C` and `T/m_R T`. No separate arbitrary
  residue map replaces the map induced by `θ`.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs`, with `isNoetherianRing_iff_ideal_fg` explaining the
  ideal-theoretic formulation.
- `def-weil-pbc-adically-complete-ring`: `IsAdicComplete` in
  `Mathlib.RingTheory.AdicCompletion.Basic`, extending `IsHausdorff` and `IsPrecomplete`.
- `def-weil-pbc-multivariate-power-series`: `MvPowerSeries` and its `C`, `X`, and `map`
  in `Mathlib.RingTheory.MvPowerSeries.Basic`. All three statement modules are public imports.
- Available proof dependencies are imported without `public`: the unit/local-ring
  criterion in `Mathlib.RingTheory.MvPowerSeries.Inverse`, the Noetherian instance in
  `Mathlib.RingTheory.MvPowerSeries.Equiv`,
  `power_series_mem_combined_ideal_pow_iff` in
  `WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients`, and
  `MvPowerSeries.exists_unique_adic_evaluation` in
  `WeilConjectures.RingTheory.PowerSeriesAdicEvaluation`. Their full signatures and
  docstrings were read. `lem-trf-coefficient-field-generator-presentation` currently has
  no recorded Lean statement, so it supplies no import; it is only a proof dependency,
  and the current theorem does not need its declaration to state any object or hypothesis.
  The six-step theorem docstring retains its use in the eventual proof.

Edge cases checked before and after writing:

- `n=0`: the variables ideal is zero, the surjective presentation makes `R` its
  coefficient field, and `hm` makes `C` a field. The extended quotient is `K` and the
  statement specializes to the prescribed section and field embedding. No nonempty index
  assumption is present.
- `s=0`: the empty relation span and its transported ideal are zero; the theorem gives
  the unquotiented power-series extension and allows a noninjective map to `C`.
- Zero rings are excluded exactly by the specified local nonzero rings; the quotient's
  nonzeroness is part of its concluded `IsLocalRing` instance.
- `N=0` in adic continuity is valid because an ideal's zeroth power is the whole ring.
- Identity embeddings and arbitrary characteristic are included; no separability or
  flatness assumption has been added. Universes `uF,uK,uR,uC` are independent and explicit.

Existing-declaration searches (2026-10-24):

- `msearch.py ... leanfinder "Surjective power series coefficient extension presentation
  for compatible complete Noetherian local rings"`: 8 hits, including
  `AdicCompletion.surjective_evalₐ`, `PowerSeries.map_surjective`, and quotient-surjectivity
  facts. None includes this chosen-presentation comparison and local quotient square.
- `msearch.py ... loogle "MvPowerSeries.map, Function.Surjective"`: 0 hits.
- `msearch.py ... grep "coefficient.*extension|surjective|map" RingTheory/MvPowerSeries`:
  25 hits, including coefficientwise maps and substitutions, no complete statement match.
- `msearch.py ... leansearch "coefficient extension power series quotient surjects onto a
  complete local ring with compatible coefficient fields"`: 8 hits, including residue
  surjectivity, one-variable map surjectivity, and Weierstrass results; no match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for coefficient-extension and
  power-series-coefficient-extension names, followed by the focused expression
  `power.series.*coefficient.*extension|coefficient.*extension.*surject|power-series-coefficient-extension-surjection`
  in the RingTheory/Paper directories: unrelated p-adic coefficient-extension declarations,
  no matching statement. The exact new declaration name was searched in Mathlib,
  `WeilConjectures`, and `Sheaf`, with no hit. The prescribed `grep -rn` of the item id
  in `WeilConjectures` also had no hit.

Validation: `scompile.py Q49 lem-trf-power-series-coefficient-extension-surjection` compiled
both the sandbox and actual module names cleanly. An initial redundant explicit
`Nontrivial` binder triggered the overlapping-instance linter; those binders were removed
because `IsLocalRing` already contains them. The final run has no errors or warnings
(4.6 seconds sandbox, 1.6 seconds actual module). No global build or direct repository edit
was performed.

## Second reading by Q49

I reopened the node and reread the full signature against it after compilation. This is
an author second pass, not an independent agent review: the dispatcher expressly forbids
starting other agents, and the maintainer performs the independent delivery review.

The field, ring, completeness, residue-identification, section, and local/continuous-map
hypotheses match the node as listed above. In particular the local-ring instances include
nonzeroness, and the algebra-map equations retain both given residue splittings. The
presentation retains both surjectivity and continuity, all finite relations, and the
containment of the full relation ideal in the variable ideal.

I checked the conclusion beginning with the forced equality defining `J`, then the actual
quotient type: it never substitutes an arbitrary ring or an arbitrary map for the quotient
construction. Both surjections, continuity of `Ψ`, both prescribed-value conditions,
annihilation of `J`, Noetherianity, locality, the complete maximal-ideal formula, the residue
field identification, locality and uniqueness of `α`, both square equalities, and the
extended maximal-ideal equality are present. The normalization of `ρT` on constants and
the last equation on every quotient element retain the identity residue reduction with
the original `ρC`. The equality of extended ideals justifies using the maximal-ideal
quotients in that last clause. Empty variable and relation tuples remain allowed.

No mathematical mismatch was found and no node statement was changed. The only compile
repair removed the redundant explicit nontriviality instances, with no mathematical
hypothesis removed. The proof is entirely postponed, as required by stage 2.
