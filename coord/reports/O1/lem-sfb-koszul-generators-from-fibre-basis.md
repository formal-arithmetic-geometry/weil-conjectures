## Worker report

The delivery states `Ideal.exists_notMem_isKoszulRegular_of_fibre_basis` in
`Sheaf.RingTheory.KoszulGeneratorsFromFibreBasis`. Its only theorem proof is `sorry`.
The node is unchanged outside `lean`; no new nodes or dependency modules are needed.

Hypothesis and conclusion correspondence:

- The arbitrary commutative ring is `(A : Type u) [CommRing A]`, with the universe
  `u` explicitly declared and `autoImplicit false`.
- The prime ideal is `(p : Ideal A) [p.IsPrime]`. The ideal contained in it is
  `(I : Ideal A) (hIp : I ≤ p)`.
- Finite Koszul-regular generation is `hI : ∃ (m : ℕ) (g : Fin m → A),
  Ideal.span (Set.range g) = I ∧ RingTheory.Sequence.IsKoszulRegular g`.
  This asserts exactly the existence in the node and does not require a chosen
  tuple or impose a length in advance.
- The nonnegative length is `(r : ℕ)` and the elements of the ideal are
  `(f : Fin r → I)`. The subtype includes precisely their membership in `I`;
  coercions `(f i : A)` recover the ring elements.
- The localization at `p` is Mathlib's `Localization.AtPrime p`, used in the
  definition of `p.ResidueField`. The fibre is represented by the ordinary
  module tensor product `p.ResidueField ⊗[A] I`. This is canonically
  `I_p / pI_p`, not the image of `I` in the residue field (which would be zero).
  To see this, localization is flat, so localizing `I ↪ A` identifies
  `A_p ⊗[A] I` with `I.map (algebraMap A A_p) = I_p`. Tensor associativity
  and the identity action identify `κ(p) ⊗[A] I` with
  `κ(p) ⊗[A_p] I_p`. Finally tensoring a module with `A_p / pA_p` is the
  quotient by its maximal-ideal multiple. Mathlib supplies
  `TensorProduct.quotTensorEquivQuotSMul` and its generator formula
  `quotTensorEquivQuotSMul_mk_one_tmul` in
  `Mathlib.LinearAlgebra.TensorProduct.Quotient` for this last identification.
  Under these canonical identifications `1 ⊗ f i` is exactly the localized
  generator's class. Thus no extra map, structure, or hypothesis is supplied.
- The fibre-basis hypothesis `hf` asserts existence of
  `b : Module.Basis (Fin r) p.ResidueField (p.ResidueField ⊗[A] I)` with
  `∀ i, b i = (1 : p.ResidueField) ⊗ₜ[A] f i`. This includes both linear
  independence and spanning of the specified images.
- The required neighbourhood is `∃ s : A, s ∉ p ∧ ...`.
  `Localization.Away s` and its `algebraMap` are exactly `A[1/s]`.
- Generation is the equality between `Ideal.span` of the images of the `f i`
  and `I.map (algebraMap A (Localization.Away s))`.
- The last conjunct is `RingTheory.Sequence.IsKoszulRegular` on the very same
  image tuple and at the very same `s`. There are no additional conclusions.
- No local, Noetherian, domain, characteristic, or positive-length assumption
  is present.

Statement dependencies read and used:

- `def-weil-pbc-koszul-regular-sequence`:
  `WeilConjectures.RingTheory.KoszulRegularSequence`,
  `RingTheory.Sequence.IsKoszulRegular`, the homology-vanishing definition.
- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`,
  and `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, `Ideal.ResidueField`.
  The latter abbreviates the residue field of the former.
- `def-weil-ring-localization-away`:
  `Localization.Away` from `Mathlib.GroupTheory.MonoidLocalization.Away`, with
  its ring/algebra structure imported through
  `Mathlib.RingTheory.Localization.Away.Basic`.

The stated proof dependencies are imported as ordinary proof-only imports:
`Mathlib.RingTheory.Flat.Localization` (`IsLocalization.flat`),
`WeilConjectures.RingTheory.KoszulRegularFlatBaseChange`
(`RingTheory.Sequence.isKoszulRegular_of_flat`), and
`WeilConjectures.RingTheory.KoszulConormalBasis`
(`ExteriorAlgebra.exists_koszul_conormal_basis`).
The localization-away definition is already publicly imported.
`lem-sfb-koszul-equal-length-generators` has no recorded Lean declaration in
this checkout, so its proof import is omitted; it is not a statement
prerequisite. The docstring retains its role in the complete six-step proof.

Source read: `literature/stacks-project/divisors.tex`,
`lemma-generate-regular-ideal` (Tag 067N), assertion (3), and the whole proof.
The affine matrix/determinant specialization in the node agrees with that
source. The module docstring contains the fibre identification and the
statement docstring contains all six steps of the DAG proof.

Edge cases checked before writing:

- `r = 0` is allowed by `Fin r`. Its basis hypothesis forces the residue fibre
  to vanish; the original Koszul-regular tuple has the same length, so `I = 0`
  and one can take `s = 1`. The conclusion uses the actual empty tuple.
- If `I = 0`, only a zero-length tuple can be a residue-field basis. Conversely
  the empty tuple gives the expected conclusion.
- `I = A` is excluded exactly by `I ≤ p` and primality, rather than by an
  additional assumption.
- A zero ring has no prime, so no separate nontriviality hypothesis is needed.
- No finite-generation or finite-presentation assumption on other modules,
  and no Noetherian assumption, has entered the signature.

Searches (all on 2026-10-24; exact wrapper results are in `searches.jsonl`):

- `msearch.py ... leanfinder`: “An ideal generated by a finite Koszul regular
  sequence admits Koszul regular generators lifting a residue fibre basis
  after inverting an element outside the prime”: 8 hits, on weakly regular
  sequences, smooth presentations, or localization of module bases; none
  states this Koszul-regular ideal theorem.
- `msearch.py ... loogle`: `"IsKoszulRegular", "Basis"`: 0 hits.
- `msearch.py ... grep`: `Koszul|koszul`, subdirectory `RingTheory`: the sole
  hit is the TODO for Koszul regularity in `Regular/RegularSequence.lean`.
- `msearch.py ... leansearch`: “Koszul regular ideal generators lifting a
  basis of the residue fibre”: 8 hits. In particular
  `IsLocalRing.span_eq_top_of_tmul_eq_basis` uses the same tensor form of a
  residue basis but asserts only local spanning, not this theorem.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: searched the item identifier and patterns
  `Koszul.*generat`, `koszul.*generat`, `fibreBasis`, `fiberBasis`,
  and combinations of `basis`, `fibre`/`fiber`, and `koszul`.
  Found conormal-basis, base-change, and faithfully-flat descent material,
  but no declaration of this statement or of the chosen new name.
- Read Mathlib `TensorProduct/Quotient.lean` and the residue-field and
  localization declarations to check the tensor representation explicitly.

No statement fault or `STATEMENT-DISPUTED` issue was found.

## Second reading by O1

This is a self-check of the final node and module, not a claim of independent
review. The dispatcher instructs this worker not to start other agents;
independent delivery review belongs to the maintainer.

On rereading, `hIp` is the containment, `hI` is the original finite
Koszul-regular generation, and `hf` fixes every specified generator class in
an actual basis of the fibre module. In particular using the subtype `I`
inside the tensor avoids replacing the fibre by the zero image of `I` in
`κ(p)`. Both conclusion conjuncts share the existential `s`, with
`I.map` giving the extended ideal and the same generator tuple supplying
both generation and Koszul regularity. Length zero remains allowed.
The six proof steps and recorded dependency signatures were checked again;
no mathematical change to the node was required.

Validation: `scompile.py O1 lem-sfb-koszul-generators-from-fibre-basis
<module path>` passed both the sandbox and library module compilations.
`deliver2.py O1 lem-sfb-koszul-generators-from-fibre-basis --no-push`
reported `OK (dry run)` after preflight and per-file compilation.
