# Q21 stage-1 report: lem-trf-stein-smooth-generic-curve

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-stein-smooth-generic-curve.json`: repaired item split with five proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-finite-projective-bundle.json`: one new unsplit statement-only node; Mathlib searches found no match.
- `citations.json`: verbatim statement quotes for every cited node in every item step.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, blueprint tag, Stein-factorization names and geometric keywords. No sorry-free declaration states the item exactly.

## WANTED

None.

## Not duplicates

- `lem-trf-finite-projective-bundle` vs `lem-trf-stein-smooth-generic-curve`: the item is the full Stein-factorization theorem with a projectivity conclusion among many clauses; the new node isolates the general finite-morphism projective-bundle lemma used to prove that clause.
- `lem-trf-finite-projective-bundle` vs `lem-wf-curve-normal-smooth-compactification`: that existing node is a curve compactification theorem whose source happens to cite Tag 0B3I; it does not state finite morphisms are projective, whereas the new node does.
- `lem-trf-finite-projective-bundle` vs `def-pc-projective-morphism`: the existing node defines the narrower H-projective convention, while the new node proves projective-bundle projectivity for every finite morphism.
- `lem-trf-finite-projective-bundle` vs `def-trf-projective-bundle-morphism`: the existing node defines projective-bundle projectivity; the new node asserts the finite-morphism implication.
- `lem-trf-finite-projective-bundle` vs `lem-fin-finite-over-projective`: that node treats a finite cover of a globally projective morphism; this node treats an arbitrary finite morphism.
- `lem-trf-finite-projective-bundle` vs `lem-trf-projective-bundle-to-h-projective`: that node gives the implication from projective-bundle projectivity to H-projectivity under an ample-base hypothesis; this node gives finite implies projective-bundle.

## What was wrong or incomplete in the imported material

The returned delivery identified five faults. I repaired all of them. Step 1 now cites `lem-pc-coherent-hi` for quasi-coherence/coherence of `f_*O_C` before applying the relative spectrum. Step 4 cites `lem-sc-fraction-field-sections-base-change` for the equality of generic-section rings and identifies the generic residue field accordingly. Step 5 no longer claims `C_{eta_0}=C_eta\\times_K L`; it uses the actual Stein fibre and explains its fibre-product identification, then proves smoothness via the finite separable etale field map, the graph section and `lem-weil-pbc-etale-section-clopen-immersion`, with smoothness of the ambient base change from `lem-pc-proper-base-change`. The child node source now cites Stacks Lemma 0B3I and Definition 01W8 clause (1), rather than the wrong clause (2).

## What I could not finish

No unfinished proof remains at stage 1; the new child is intentionally statement-only and enters the queue for a later split.

## Review by Q21

I reread the repaired item and child, the `sk-i-curve-zero` unit, the `sec-trace-formula` chapter record, the ILO Exposé IX §1.3 passage, and the current `main-20261015` blueprint ancestry. I opened every cited node and checked each quote in `citations.json` against the node statement. Step 1 now checks that properness over the Noetherian base and coherence of `O_C` permit the coherent proper-pushforward theorem, so the relative-spectrum hypothesis is actually met. Step 2 checks the affine proper/coherent finiteness hypotheses and the finite-type, Noetherian, excellent, integral conclusions before invoking the finite-projective child. Step 3 applies the affine Stein theorem on affine opens and uses its stated properness and geometric connectedness; dominance supplies the nonempty generic fibre.

For Step 4 I checked proper base change, integrality of the generic curve, the proper-variety global-sections hypothesis, geometric reducedness from smoothness, and the separability hypothesis. The fraction-field sections node is now the explicit source for the section-ring identification, rather than an unstated relative-spectrum inference. For Step 5 I checked the distinction between the Stein fibre and the full scalar extension: the fibre is `C ×_{S_0} Spec L`, canonically identified through `S_0 ×_S Spec K = Spec L`; the larger scalar extension is used only as a smooth ambient scheme. The finite separable extension node gives an etale separated projection, the existing clopen-section node applies to its graph, and smoothness restricts to the clopen component. The affine Stein statement supplies geometric connectedness, while regularity after arbitrary field extension and the connected-regular-integral node give geometric integrality; dimension preservation supplies dimension one. I checked the child against Stacks 0B3I and 01W8(1), and reran all required Mathlib searches recorded in `searches.jsonl`.
