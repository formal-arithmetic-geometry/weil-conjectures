## Worker report

`Sheaf.TraceFormula.ValuationFiniteHeightComposition` states
`valuation_finite_height_composition`, with its only proof `sorry`. The saved packet
was retained and repaired after the required first dry run. Its concrete diagnostics
were a truncated `lean.statement` (at an internal `:=`) and a blueprint tag containing
backticks. The self-check additionally found forbidden statement-local `let` bindings,
a tautological ideal equality, and an incomplete proof docstring. These are repaired.
The mathematical DAG statement and every field outside `lean` are unchanged.

Hypothesis and clause correspondence:

- `V : Type u`, `[CommRing V] [IsDomain V] [ValuationRing V]` is the valuation ring.
- `K : Type v`, `[Field K] [Algebra V K] [IsFractionRing V K]` is its fraction field.
- `A : Type w`, `[CommRing A] [Algebra V A] [Module.IsTorsionFree V A]` is exactly
  the commutative torsion-free algebra, without a domain or nontriviality assumption.
- `p : Ideal V`, `[p.IsPrime]`, `hp0 : p ≠ ⊥` is the nonzero prime.
- The generic algebra is literally `A ⊗[V] K`. `S : Subalgebra A (A ⊗[V] K)` with
  `[IsLocalization (p.primeCompl.map (algebraMap V A)) S]` represents `A_T` as
  its canonical subalgebra in the generic algebra. This is a representation of the
  localization named by the node, not an extra mathematical condition: torsion-freeness
  embeds `A` into its generic algebra, and the image of its localization there is
  uniquely characterized by this `IsLocalization` property. No arbitrary map is used.
  Both arbitrary localizations and the concrete `Localization` model transport to it
  by the canonical localization equivalence. The subalgebra inclusion is the embedding.
- `hclosed : IsIntegrallyClosedIn S (A ⊗[V] K)` is precisely the assumed relative
  integral closedness, using the canonical subtype algebra structure.
- `B` is literally `integralClosure A (A ⊗[V] K)` throughout, not a different
  integral closure chosen inside the localization. The existential proof `hB : B ≤ S`
  states the first conclusion `B ⊆ A_T` and enables `Subalgebra.inclusion hB`.
- Write `pA = Ideal.map (algebraMap V A) p`. The ideal of `B` is
  `Ideal.map (algebraMap A B) pA`, and that of `S` is
  `Ideal.map (algebraMap A S) pA`. By composition of ideal extension these are exactly
  `pB` and `pA_T`. The first two conjuncts equate their **set images** in `A ⊗[V] K`
  under the canonical embeddings: image of `pA` equals image of `pB`, which equals
  image of `pA_T`. Thus these are equal as subsets of `A_T`, and the subset `pA`
  is an ideal there, since the last subset is an ideal of `A_T`. This preserves the
  substantive assertion of the node; merely extending all three ideals to `A_T`
  would be tautological and would lose that assertion.
- The next two conjuncts supply ring homomorphisms `f : A/pA →+* B/pB` and
  `g : B/pB →+* S/pS`, each with `Function.Injective` and its formula on every
  quotient generator. Those formulas uniquely characterize the induced maps. The
  second uses `Subalgebra.inclusion hB`, the canonical inclusion already concluded.
- The last conjunct quantifies over **every** `z : S/pS` and states
  `IsIntegral (A/pA) z ↔ ∃ x : B, Ideal.Quotient.mk _ (Subalgebra.inclusion hB x) = z`.
  Its right side is the image of `B/pB`, by surjectivity of its quotient map. Along
  with the preceding injectivity this says exactly that `B/pB` is the relative
  integral closure in `S/pS`. The quotient algebra is Mathlib's canonical one for
  `pS = Ideal.map (algebraMap A S) pA`.

Dependencies read and used:

- `def-trf-valuation-ring`: Mathlib `ValuationRing`, defined and documented in
  `Mathlib.RingTheory.Valuation.ValuationRing`; its divisibility characterization
  agrees with the fraction-field characterization recorded by that Mathlib node.
- `def-weil-pbc-integral-closure`: the recorded Mathlib `integralClosure` and
  `IsIntegral` in `Mathlib.RingTheory.IntegralClosure.Algebra.Basic` and
  `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs`, and `IsIntegrallyClosedIn`
  in `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`. Their full definitions
  and docstrings were read. Both proof dependencies are these same Mathlib leaves;
  no additional project proof modules are recorded or needed.
- Standard constructions reused without a copy: `IsLocalization` from
  `Mathlib.RingTheory.Localization.Defs` and `Subalgebra.inclusion` from
  `Mathlib.Algebra.Algebra.Subalgebra.Basic` (both signatures/docstrings read).

Edge cases: `A = 0` is admitted, including the localization at a submonoid containing
zero and the zero generic algebra and quotients. No `Nontrivial A` is present. The
prime may have arbitrary height; no finite-type, reducedness or separably closed
hypothesis appears. `p` maximal and `A = V` are admitted; `p = 0` is excluded exactly
as required. `u`, `v`, `w` are independent explicitly bound universes. A localization
subalgebra lives in the generic algebra's universe; no independent test-object universe
or restriction on the three rings is introduced. Monic-equation lifting in the
proof plan handles the zero quotient by using a positive-degree monic equation.

Saved searches retained: `msearch.py NB lem-trf-valuation-finite-height-composition
leanfinder "integral closure modulo a prime of a valuation ring localization residue
comparison"` found no whole-statement hit; `msearch.py ... loogle "integralClosure
quotient"` found no hit; `msearch.py ... grep
"integralClosure.*[Qq]uotient|[Qq]uotient.*integralClosure"` found only the basic
integral-closure material. The DAG's own Mathlib searches additionally record
LeanSearch and exact results. Saved `rg` searches over `WeilConjectures` and
`lean/Sheaf` for `valuation-finite-height`, `primeCompl`, and `integralClosure`
found no existing whole statement. Current-session `rg` over those same two source
roots for `valuation_finite_height_composition|valuation-finite-height-composition|
Residue comparison for relative integral closure` likewise found no hit. No new
notion or dependency module was needed.

Validation: `scompile.py NB lem-trf-valuation-finite-height-composition <module>`
compiled both wrapper sandbox and library module cleanly (3.8 s each). The node's
`lean.statement` is extracted through the theorem's final `:= by`, so contains the
complete signature. No `STATEMENT-DISPUTED` marker or node fault.

## Self-check after recovery

Read the saved node, module, dependency records and their actual Mathlib definitions.
The first two ideal equalities now assert equality of set images, rather than extension
of ideals to the localization. All statement-local lets and the auxiliary denominator
proof have been removed by using the uniquely specified localization subalgebra.
The real ambient integral closure is used throughout; its containment is a conclusion.
The quotient generator formulas retain the identity of both canonical maps, and the
last biconditional retains both inclusions of the integral-closure assertion. The
module and declaration docstrings now give the exact blueprint tag and all six steps
of the DAG proof. No independent reader is claimed: the dispatcher brief assigns the
independent reading to the maintainer and prohibits spawning agents.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
