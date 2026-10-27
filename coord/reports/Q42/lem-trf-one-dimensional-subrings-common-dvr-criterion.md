## Worker report

The module `Sheaf.RingTheory.OneDimensionalSubringsCommonDvr` states
`Subring.not_surjective_tensorProduct_iff_exists_common_dvr`, with the sole proof
`sorry`. No definition or auxiliary theorem is introduced. The node changes only
in `lean`; its accepted stage-1 split is preserved.

Source read: `literature/stacks-project/varieties.tex`, lines 7303–7354,
Situation 09MY and Lemma 09N0. Situation 09MY supplies the common fraction field;
09N0 gives precisely this equivalence. The node specifies the tensor over the
integers; its image is the same product subring as the tensor over A ∩ B.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| K is a field | `{K : Type u} [Field K]` |
| A and B are unital subrings of K | `(A B : Subring K)` |
| Each has fraction field K | `[IsFractionRing A K] [IsFractionRing B K]`, with Mathlib's canonical subring inclusion algebra structures |
| A is Noetherian | `[IsNoetherianRing A]` |
| A has Krull dimension exactly one | `(hdim : ringKrullDim A = 1)` |
| μ is the homomorphism A ⊗[ℤ] B → K sending a ⊗ b to ab | `Algebra.TensorProduct.lift A.subtype.toIntAlgHom B.subtype.toIntAlgHom (fun _ _ => Commute.all _ _)`; `Algebra.TensorProduct.lift_tmul` evaluates it to `(a : K) * (b : K)` |
| μ is not surjective iff | `¬ Function.Surjective (...) ↔` |
| There exists a DVR O ⊆ K | `∃ O : Subring K, IsDiscreteValuationRing O ∧ ...` |
| O has fraction field K | `IsFractionRing O K` |
| O contains A and B | `A ≤ O ∧ B ≤ O` |

The universal commutativity proof is a property of the field multiplication,
not an additional hypothesis. Domains of all subrings are inferred from K.
`IsDiscreteValuationRing` excludes fields by its nonzero maximal-ideal field.
The arbitrary universe `u` includes all field sizes and all characteristics.

Statement dependencies, read at their recorded declarations:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs` (publicly available
  through the statement imports).
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` and
  `isNoetherianRing_iff`, `Mathlib.RingTheory.Noetherian.Defs`.
- `def-weil-pbc-krull-dimension-ring`: `ringKrullDim`,
  `Mathlib.RingTheory.KrullDimension.Basic`.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs`; its universal construction is
  used via `Algebra.TensorProduct.lift` in
  `Mathlib.RingTheory.TensorProduct.Maps`. Also read the recorded signatures
  of `TensorProduct.mk`, `TensorProduct.lift`, `TensorProduct.ext'`, and
  `LinearMap.rTensor`. No replacement tensor is defined.
- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`.

The fraction-field condition uses `IsFractionRing` from
`Mathlib.RingTheory.Localization.FractionRing`; the map uses the existing
`RingHom.toIntAlgHom` and `Subring.subtype`, not a newly chosen map.

All distinct proof-only dependency modules are plain imports:
`Mathlib.RingTheory.Ideal.Maximal` (`Ideal.exists_le_maximal`),
`Mathlib.RingTheory.Localization.AtPrime.Basic` (`Localization.AtPrime`),
`Mathlib.RingTheory.Valuation.LocalSubring`
(`LocalSubring.exists_le_valuationSubring`),
`WeilConjectures.RingTheory.KrullAkizukiNoetherian`
(`krullAkizukiNoetherian`), and
`Mathlib.RingTheory.DiscreteValuationRing.TFAE`
(`IsDiscreteValuationRing.TFAE`). The module docstring contains the full
five-step node proof, including nonfieldness of the dominating valuation ring
and the identity-extension use of Krull–Akizuki.

Edge cases checked before writing:

- B = K: every x is μ(1 ⊗ x), so nonsurjectivity is false; a DVR containing
  all of K would equal K, contradicting nonfieldness. Both sides are false.
- A = B: the multiplication image is A, a proper subring since a field has
  dimension zero. A nonzero maximal localization is dominated by a valuation
  ring; Krull–Akizuki makes that nonfield valuation ring a DVR.
- A = ℤ, K = ℚ, B = ℤ[1/2]: μ has proper image ℤ[1/2], and ℤ localized at
  an odd prime is a common DVR. Inverting 2 need not make μ surjective.
- A = k[t], B = k[t⁻¹], K = k(t): the image k[t,t⁻¹] is proper, and
  k[t] localized at (t − 1) contains both. This works in every characteristic.
- A = K, zero rings, and dimension-zero rings are excluded by the stated
  field/subring and dimension-one assumptions, not by extra assumptions.

Searches performed with the prescribed `msearch.py Q42 <item>` wrapper:

- LeanFinder: “Two subrings A and B of a field K, each with fraction field K,
  with A Noetherian of dimension one: their tensor multiplication map over
  integers is not surjective if and only if they lie in a common discrete
  valuation subring of K”. Eight hits on tensor stalks, residue-field tensors,
  and localization surjectivity; no common-DVR criterion.
- Loogle: `IsDiscreteValuationRing, TensorProduct`. Zero hits.
- Mathlib grep, RingTheory:
  `(tensorProduct|tensor.product).*(valuation|surject)|(valuation).*(tensor|overring)`.
  Twenty-five hits on tensor maps, stalks, differentials and related
  surjectivity results; no matching equivalence.
- LeanSearch: “Two subrings of a common fraction field, one Noetherian of
  Krull dimension one, have tensor multiplication map not surjective exactly
  when some discrete valuation subring contains both”. Eight hits on individual
  valuation rings and DVR characterizations, none stating the criterion.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for common DVR/valuation,
  one-dimensional subrings, and the item id found no existing statement.
  A declaration-name search there and in `dag/lean_names_upstream.json` found
  no collision with the selected theorem name.

No statement fault or dispute was found. The old worker's stale-assignment
ending concerned a stage-1 delivery; the current stage-2 brief explicitly
permits stating the reviewed split, and the item had no Lean record.

Validation: the prescribed `scompile.py` compiled the module in both sandbox
and library contexts cleanly (1.3 s and 1.4 s respectively).

## Second reading by Q42

Reopened the node and finished module for a separate clause-by-clause audit.
The field, the two inclusions, both fraction-field hypotheses, Noetherianity
of A alone, and exact dimension one all appear in the binders. The left side
uses the canonical integer-algebra tensor lift, whose pure tensor formula
is multiplication of the two inclusions. The right side quantifies over
subrings of the same K and retains all four requirements: DVR, fraction
field K, containment of A, and containment of B. No arbitrary map, extra
finiteness condition on B, or properness hypothesis is present. No mismatch
was found and no correction was needed. This is an in-session rereading;
no other agent was started, as the dispatcher brief expressly forbids it.
The maintainer's independent delivery review remains separate.
