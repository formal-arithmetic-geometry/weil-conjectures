## Files written

- `dag/nodes/sec-trace-formula/lem-trf-local-fibres-integral-projective.json` — item, split into three source-faithful steps.
- `dag/nodes/sec-trace-formula/lem-trf-local-noetherian-approximation.json` — statement node, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-local-noetherian-fibres-projective.json` — statement node, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-local-projective-tensor-base-change.json` — Mathlib leaf, `Module.Projective.tensorProduct`.
- `citations.json` — verbatim node-statement quotes for every step citation.

## Attachments

None. I searched `WeilConjectures/` in `/home/ubuntu/weil-src-slopmaster2` and `/home/ubuntu/weil-newtargets-master` for the item id and its key phrases; no finished declaration states this item exactly.

## WANTED

None. The proof source is present in `literature/stacks-project/flat.tex`, and the scalar-extension input is in the pinned Mathlib source.

## Not duplicates

- `lem-trf-local-noetherian-approximation` vs `def-nagata-noetherian-inverse-system`: the existing node defines an inverse system of schemes; this node states the relative affine ring approximation preserving flatness and geometrically integral fibres from Tag 05FT.
- `lem-trf-local-noetherian-fibres-projective` vs `lem-trf-local-fibres-integral-projective`: the new node has a Noetherian base and finite-type map and is the Noetherian input; the item removes Noetherianity and finite-type in favour of finite presentation and uses the approximation step.
- `lem-trf-local-projective-tensor-base-change` vs `lem-weil-pbc-localization-projective`: the new Mathlib leaf is arbitrary scalar extension by tensor product; the existing node is only localization.
- `lem-trf-local-noetherian-approximation` vs `lem-trf-local-fibres-integral-projective`: the existing item is the full non-Noetherian conclusion; this child is only the cocartesian approximation construction and does not conclude projectivity.
- `lem-trf-local-noetherian-approximation` vs `lem-trf-affine-geometrically-integral-projective`: the existing node states projectivity for the original finitely presented map; this child states the intermediate Noetherian model and its preservation of flatness and geometric integrality.
- `lem-trf-local-noetherian-fibres-projective` vs `lem-trf-affine-geometrically-integral-projective`: the existing node is the non-Noetherian finitely presented theorem; this child is the Noetherian finite-type lemma used as the intermediate step in Tag 05FT's proof.

## What I checked before writing

I read the item, its `sk-i-curve-zero` unit, the `sec-trace-formula` chapter, and the full Tag 05FT material in `literature/stacks-project/flat.tex`. The source has exactly the three logical paragraphs used here: construct a cocartesian Noetherian approximation preserving flatness and geometrically integral fibres; apply the Noetherian Tag 05FT lemma; then use projectivity under tensor base change. I also read Mathlib's `Mathlib/Algebra/Module/Projective.lean` at line 242, where `Module.Projective.tensorProduct` is declared.

## Review by Q36

The item statement agrees with Tag 05FT's non-Noetherian lemma hypothesis by hypothesis: `R → S` is finitely presented and flat, every fibre ring over every residue field is geometrically integral, and the conclusion is projectivity of `S` as an `R`-module. The existing definition dependencies in the item cover flat maps, projective modules, finite presentation, residue fields, affine spectra, and geometric integrality. No Lean declaration in either read-only source tree states this item without `sorry`.

Step 1 cites `lem-trf-local-noetherian-approximation`; its statement explicitly supplies the cocartesian square, finite-type-over-ℤ base, finite-type flat model, geometrically integral model fibres, and the identification `S ≅ S₀ ⊗_{R₀} R`. I checked that the item hypotheses are exactly the hypotheses written in that node. Step 2 cites that approximation statement for the model hypotheses and `lem-trf-local-noetherian-fibres-projective`; the latter explicitly requires a Noetherian base, finite-type flat map, and geometrically integral fibres and concludes projectivity. The sentence that a finite-type ℤ-algebra is Noetherian is the standard Hilbert-basis fact used by the cited Tag 05FT proof. Step 3 cites the approximation identification, the projectivity conclusion for `S₀`, and the Mathlib leaf. `lem-trf-local-projective-tensor-base-change` states exactly that scalar extension of a projective `R₀`-module is projective over `R`; it is the one-line specialization of `Module.Projective.tensorProduct` with the first tensor factor the free rank-one `R`-module.

I checked the new statements on small cases: for `R₀ = ℤ`, `S₀ = ℤ[x]`, and `R = ℚ`, the base-change node gives `ℚ[x]` projective over `ℚ`; for the identity map `R → R`, the item reduces to the free rank-one module; and for a field base with a geometrically integral finite-type algebra, the Noetherian node agrees with the expected projectivity. The empty-spectrum case is harmless because the source approximation and projectivity conclusions are module statements. The Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch for the item and each new node; the recorded verdicts are in their `mathlib_searches` fields and the command logs.

No statement was corrected, no SGA source was used, and no off-unit tool citation was needed. The only change from the imported item is replacing its empty proof with the three source steps and adding the three strictly smaller dependencies.

## What could not be finished

Nothing. No Lean files were written and no compiler or build tool was run, as required for stage 1.
