## Worker report

The module `Sheaf.RingTheory.ParameterIdealFormalNormalization` states
`MvPowerSeries.parameter_ideal_formal_normalization`, with its entire proof `sorry`.
The single theorem is the conjunction of the coefficient-field case and the
complete-DVR case of the node. No definitions, helper nodes, dependency repairs,
statement corrections, or proofs were added. Only the item's `lean` record changes.

Assignment check: Q86's reviewed delivery was the stage-1 split, not a stage-2
statement. The current node has `reviewed.group = Q86`, but no `lean` or
`reviewed_lean`. Its Q86 report explicitly says that no Lean was written. The
retained N5 sandbox contained dispatcher markers only, with no interrupted delivery
or compiler process to resume. Thus writing its missing Lean statement respects the
existing split and review. The earlier worker's stale-assignment diagnosis confused
the two stages.

Hypotheses, matched individually:

- `B : Type v`, `[CommRing B]`, `[IsLocalRing B]`, and `[IsNoetherianRing B]`
  express the Noetherian local ring. Its named maximal ideal is `maximalIdeal B`.
  `[IsAdicComplete (maximalIdeal B) B]` expresses completeness, including separatedness.
- `e : ℕ` expresses exactly `e ≥ 0`; no positivity hypothesis occurs.
- The first conjunct quantifies over `Λ : Type u` with `[Field Λ]` and `[IsReduced B]`.
  The supplied coefficient inclusion is `α : Λ →+* B` with `_hα : Function.Injective α`.
  `_hres : Function.Bijective ((residue B).comp α)` is exactly the isomorphism
  from the coefficient field to the residue field of B. In particular the coefficient
  field is supplied, not chosen by the conclusion.
- In that conjunct, `_hdim` says for every `q : PrimeSpectrum B` whose ideal belongs
  to `minimalPrimes B` that `ringKrullDim (B ⧸ q.asIdeal) = (e : WithBot ℕ∞)`.
  This is componentwise equidimensionality, including every minimal component.
- Both conjuncts take the supplied family `b : Fin e → B`, with `_hb` asserting
  membership in `maximalIdeal B` for each entry. `_hparam` in case (a) is
  `(Ideal.span (Set.range b)).radical = maximalIdeal B`.
- The second conjunct quantifies over `[CommRing Λ] [IsDomain Λ]
  [IsDiscreteValuationRing Λ]`, and separately `[IsDomain B]`.
  `[IsAdicComplete (maximalIdeal Λ) Λ]` retains an arbitrary complete DVR, without
  an unramified, Cohen-ring, or residue-characteristic restriction.
- Its supplied uniformizer is `π : Λ` with `_hπ : maximalIdeal Λ = Ideal.span {π}`.
  The coefficient inclusion `α` is injective and has `[IsLocalHom α]`.
  `_hres : Function.Bijective (ResidueField.map α)` asserts exactly its induced
  residue-field isomorphism. `_hdim` is `ringKrullDim B = ((e + 1 : ℕ) : WithBot ℕ∞)`.
- In case (b), `_hparam` is
  `(Ideal.span (insert (α π) (Set.range b))).radical = maximalIdeal B`.
  Thus the uniformizer is transported along the actual supplied inclusion.

Conclusions, matched individually:

- In each case `R` is literally `MvPowerSeries (Fin e) Λ`. The existential
  `Algebra R B` records its evaluation ring homomorphism as `algebraMap R B`.
  Its scalar multiplication is the one subsequently used for finiteness,
  torsion-freeness and the tensor product. The two value equations require
  `algebraMap R B (C c) = α c` for every coefficient and
  `algebraMap R B (X i) = b i` for every variable. This is the canonical evaluation,
  uniquely determined by `MvPowerSeries.exists_ringHom_of_isAdicComplete` for these
  data; it is not an arbitrary ring map or an assumed algebra structure.
- `∀ N : ℕ, ∃ M : ℕ, ∀ F ∈ maximalIdeal R ^ M,
  algebraMap R B F ∈ maximalIdeal B ^ N` spells out continuity for the source and
  target maximal-ideal adic topologies, also in the DVR case with its coefficient
  uniformizer included in the source maximal ideal.
- `Function.Injective (algebraMap R B)` is injectivity of that very map.
  The existential `IsLocalHom (algebraMap R B)` is its locality.
  `Function.Bijective (ResidueField.map (algebraMap R B))` is its residue-field
  isomorphism. No independent, unrelated residue-field equivalence is substituted.
- `Module.Finite R B` and `Module.IsTorsionFree R B` state the two module conclusions
  for the same evaluation action. The imported domain instance for power series
  over the coefficient domain makes the latter the usual torsion-free assertion.
- Only case (a) has the generic-product conclusion. Its indices are exactly
  `{q : PrimeSpectrum B // q.asIdeal ∈ minimalPrimes B}`, without an enumeration,
  an omitted component, or an auxiliary finiteness assumption.
  `FractionRing R` is K, and `FractionRing (B ⧸ q.val.asIdeal)` is L_q; the
  quotient is a domain since q is prime.
- `f q : FractionRing R →+* FractionRing (B ⧸ q.val.asIdeal)` is required on every
  `r : R` to send its fraction-ring image to the image of its evaluated quotient
  class. Thus it is the field-extension map induced by the evaluation, not a
  freely chosen field embedding. Maps between these fields are injective.
- `(f q).Finite` for each minimal q means `Module.Finite K L_q` for precisely
  this field map's algebra structure, hence the required finite field extension.
- `E : B ⊗[R] FractionRing R ≃+* (∀ q, FractionRing (B ⧸ q.val.asIdeal))`
  is the claimed ring isomorphism with the product. Its equation on every pure
  tensor is `E (x ⊗ₜ[R] k) q = image(x mod q) * f q k`. Pure tensors generate the
  tensor product additively, so this equation fixes the canonical comparison
  itself. Both the actual quotient maps and the induced fraction-field maps
  appear explicitly. The order of the tensor factors agrees with the node.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete` (Hausdorff and
  precomplete, equivalent to the node's completion-map formulation).
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim` in `WithBot ℕ∞`.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`;
  the uniformizer equation is the one in `irreducible_iff_uniformizer`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`, reexported by its `Inverse` module:
  `MvPowerSeries`, `C`, and `X`.
- `Mathlib.RingTheory.Finiteness.Defs`, reexported by the finite-ring-map module:
  `Module.Finite`, not finiteness of the underlying set.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`, reexported by
  `Mathlib.RingTheory.TensorProduct.Basic`: `TensorProduct` and its algebra tensor
  ring structure. The node's `LinearMap.baseChange` is the companion map API;
  no linear map needing base change occurs in this particular statement.

The seven statement dependencies retain their recorded notions or Mathlib matches;
none requires a repair. The module also imports every recorded proof dependency:
the power-series Noetherian/domain/local/quotient/completeness/universal-property
modules, the quotient-dimension and maximal-ideal bound modules, Artinian finiteness,
finite-over-complete, integral dimension, minimal-prime zero-divisors, total fractions,
and finite fraction-field degree. Those proof imports remain non-public. The docstring
gives all eight steps of the current Q86 split, including the supplied-ideal power
containment and the general complete-DVR argument, for stage 3.

Edge cases checked: e=0 gives `Fin 0` and the empty range in both cases. In (a)
this is the zero ideal; reduced local dimension zero gives a field. In (b) the
parameter ideal is generated just by `α π`, with B of dimension one. The existing
power-series definition covers zero variables. Local rings are nontrivial, so the
zero ring is not inadvertently included. Reducible equidimensional rings are retained:
for `k[[x,y]]/(xy)` with parameter x+y, both minimal components occur in the product.
Arbitrary ramified and equal-characteristic complete DVRs are permitted. The coefficient
and target universes u and v are independent, with no imposed equality. No finite
index type or cardinality assumption was added for minimal primes. The statements
are consistent with positive characteristic, where arbitrary supplied parameters
need not give a separable extension; no separability or generic-étaleness conclusion
was added.

Searches made with the prescribed wrapper:

- LeanFinder: `complete Noetherian local ring supplied parameter ideal power series
  finite torsion free injective generic minimal prime product`. Eight hits included
  `PowerSeries.exists_isWeierstrassFactorization`, adic Hausdorffness results,
  `IsAdicComplete.henselianRing`, and DVR equivalences; no result states this node.
- Loogle: `MvPowerSeries.eval₂Hom, IsLocalHom, FractionRing`. Zero hits.
- Mathlib grep, `RingTheory`: `parameter.*[Nn]ormalization|[Nn]ormalization.*parameter|
  finite.*eval|eval.*finite`. Seventeen hits concerned Chevalley, finite adic completion
  evaluations, ordinary polynomial evaluation and localization infrastructure;
  none gives the parameter-ideal normalization theorem.
- Direct `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for the node id,
  parameter normalization and formal normalization found only contextual references
  in `CohenGabberFinitePresentations` and an unrelated dualizing module. Those
  reference the informal theorem in proof docstrings, without a declaration of it.
- Read `PowerSeriesUniversalPropertyComplete` and `PowerSeriesAdicEvaluation`:
  they give evaluation existence and uniqueness, but no finite/torsion-free
  normalization or generic-product conclusion. Read the recorded total-fraction
  theorem too: its inputs and conclusion differ from this supplied-parameter map.
- Checked the new declaration name in Mathlib, upstream, project modules and the
  upstream name index: no collision. All searches were read-only; none claimed
  infrastructure as an exact match.

Source: read Stacks `algebra.tex`, the full proof of Tag 032D Cases I and II.
The node's accepted componentwise reduced and arbitrary-DVR extensions are retained,
as are its ILO source citations and its current reviewed proof. No statement fault
or `STATEMENT-DISPUTED` finding was discovered.

Validation: `scompile.py N5 lem-per-parameter-ideal-formal-normalization` compiled the
file separately under the sandbox and actual module names, in 2.2 and 2.5 seconds,
with no error or warning. The theorem signature is copied verbatim into `lean.statement`;
all source lines are at most 100 characters. Delivery preflight is run with the
prescribed `deliver2.py --no-push`, then the delivery command, on this complete packet.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
