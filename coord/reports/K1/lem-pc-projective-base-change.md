Files written:

- `dag/nodes/sec-picard-framework/lem-pc-projective-base-change.json` — split item; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-quasi-compact-base-change.json` — new unsplit statement; no Mathlib match.

Attachments:

- None.

WANTED: `literature/stacks-project/morphisms.tex`, Lemmas 01WF and 01K5, because the repository contains only the citation index and not the fetched Stacks source.

What was checked or corrected:

- The item statement was checked against the H-projective convention in Stacks Definition 01W8 and the imported node: projectivity means a closed immersion into relative projective space followed by the structural projection, together with quasi-compactness. The unused statement dependency on `def-weil-scheme-over-base` was removed.
- The first proof step uses exactly the definition of projective morphism, the fibre-product/base-change definitions, and the existing statement `lem-pc-closed-imm-base-change`. It explicitly transports the relative projective space to `\\mathbf P^n_{S'}` and identifies the resulting composite with the projection `f'`; this is the content of Stacks Lemma 01WF.
- The second proof step uses the new node `lem-pc-quasi-compact-base-change`, whose statement is the quasi-compactness preservation assertion of Stacks Lemma 01K5, and then applies the quasi-compact clause in Definition 01W8. All hypotheses are present: `f` is quasi-compact because it is projective, and `g` is arbitrary.
- Before creating the new node, I searched the whole DAG and blueprint for 01K5 and for quasi-compactness under base change; no existing node or blueprint node stated it. I also searched Mathlib by LeanSearch, Loogle, and source grep; no matching declaration was found. The existing closed-immersion base-change node was cited rather than duplicated.
- Small cases checked conceptually: identity base change gives `f'=f`; base change of `\\mathbf P^n_S\\to S` gives `\\mathbf P^n_{S'}\\to S'`; and a closed immersion remains closed after base change. No statement error was found.

## Review by K1

I read the imported item and the Stacks citations attached to Tags 01WF, 01K5, and 01W8. The item statement introduces `X`, `S`, `S'`, both morphisms, the fibre product, and its projection, and agrees with the source clause by clause. In step 1, the cited projective-morphism definition supplies the closed immersion into `\\mathbf P^n_S`; the cited closed-immersion base-change statement supplies the base-changed closed immersion; the base-change and fibre-product definitions supply the canonical identification and projection. In step 2, the new node says exactly that quasi-compactness survives arbitrary base change, and the projective definition supplies the original quasi-compactness hypothesis. Neither step hides an additional theorem under an elementary label.

For the new node I checked that its statement is self-contained, cites every introduced notion, has no proof sketch because it is intentionally unsplit, records Stacks Tag 01K5 as its source, and records all three required Mathlib searches with no match. I tested identity base change and projective-space base change as edge cases. I also checked the blueprint ancestor reference and the item split report. The only correction made during review was removing the item’s unused `def-weil-scheme-over-base` dependency; no mathematical correction was needed.
