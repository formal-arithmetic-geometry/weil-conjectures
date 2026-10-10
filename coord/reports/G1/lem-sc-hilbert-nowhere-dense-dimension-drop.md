1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-hilbert-nowhere-dense-dimension-drop.json` — item, statement split into three proof steps; Mathlib searches found no exact theorem.
- `dag/nodes/sec-abelian-varieties/lem-sc-locnoeth-components-locally-finite.json` — one new unsplit prerequisite; Mathlib searches found no local-finiteness theorem (only global Noetherian finite-component results).
- `citations.json` — verbatim statement excerpts for every cited node in every item step.

2. Attachments: none.

3. WANTED: none; the proof is written from Stacks Tag 02P2 and Tag 0052.

4. The item had no Lean declaration and no complete proof. I kept its statement unchanged. The only new prerequisite is the local-finiteness statement for irreducible components of a locally Noetherian scheme; it is distinct from the existing globally Noetherian finite-components leaves and is needed for the nowhere-dense contradiction.

## Not duplicates

lem-sc-locnoeth-components-locally-finite vs lem-weil-pbc-noetherian-open-subscheme-noetherian: the existing node says an open subscheme of a quasi-compact Noetherian scheme is Noetherian; it does not state local finiteness of irreducible components.
lem-sc-locnoeth-components-locally-finite vs lem-sc-noetherian-finite-irreducible-components: the existing node proves finiteness of components for a globally Noetherian topological space, while the new node concerns local finiteness for a merely locally Noetherian scheme, which need not be quasi-compact.

## Review by G1

I read the item and its consumer `lem-sc-hilbert-difference`, the existing one-dimensional specialization `lem-pc-nowhere-dense-dim-zero`, and the dimension argument in `lem-sc-hilbert-embedded-points`. The item proof follows the Tag 02P2 argument: empty Z is handled by the dimension convention; each irreducible component of Z lies in an ambient component using `lem-sc-irreducible-components-cover`; local finiteness gives an open part of the ambient component disjoint from the others, so nowhere density forces strict containment; adjoining the ambient component to every chain gives the strict dimension bound; taking the supremum finishes. I checked the exact statements of the cited component-cover and Krull-dimension nodes and added the local-finiteness node because no existing node stated that fact. I tested the edge cases Z empty, d = 0, and a principal closed point in Spec k[t]. Mathlib searches were run for both the item and the new node with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such.

5. Nothing remains unfinished.

## Second reading by G1

- Item statement: checked against the finite-dimensional nowhere-dense component argument used with Topology Tag 0052 (`topology-lemma-Noetherian`) and Tag 004W (`topology-lemma-irreducible`); hypotheses and the empty, field/zero-dimensional, and `Spec k[t]` cases are consistent.
- New node `lem-sc-locnoeth-components-locally-finite`: checked against Topology Tag 0052 on affine Noetherian neighbourhoods; it is self-contained, cites its definitions, has statement-only form, and its recorded Mathlib searches are genuine no-match/unavailable results.
- Step 1: checked that `lem-sc-irreducible-components-cover` supplies component containment and the dimension definition supplies the empty case.
- Step 2: checked that local finiteness plus `lem-sc-irreducible-components-cover` yields an open neighbourhood of the generic point of `W` contained in `W` after deleting the other components; nowhere density then forces `C` to be a proper subset, and the chain extension gives the dimension bound.
- Step 3: checked the supremum calculation and the `d=0` edge case directly from the Krull-dimension definition.

Changes made:

- Corrected the erroneous source citation from Divisors Tag 02P2 (an unrelated regular-section lemma) to Topology Tag 0052 with its label, and recorded Tag 004W for the component-cover input.
- Added `lem-sc-irreducible-components-cover` to step 2, `proof_deps`, and `citations.json` because the open-neighbourhood argument needs the fact that components cover `X`.
- Corrected the local-finiteness node title and source wording to state local finiteness for components of `X`, as used by the proof.
