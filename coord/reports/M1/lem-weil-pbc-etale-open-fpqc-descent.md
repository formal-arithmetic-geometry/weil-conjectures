# Stage-1 worker report

1. Files written:
   - `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-open-fpqc-descent.json` — statement, two proof steps; no Mathlib match.
   - `dag/nodes/sec-proper-base-change/lem-weil-pbc-open-subscheme-fpqc-descent.json` — statement-only Tag 03N0 dependency; no Mathlib match.
   - `citations.json` — verbatim citations for both proof steps.
2. Attachments: none.
3. WANTED: none.
4. The imported item had no proof and its only dependency was the fpqc-cover definition. I added the scheme, fibre-product, and etale statement dependencies and supplied the missing base-change and compatible-open descent arguments. The latter is a separate statement-only node because Tag 03N0 is not in Mathlib.
5. Nothing remains unfinished.

## Review by M1

I read the item source in `literature/stacks-project/descent.tex`, Tag 03N0, and the Tag 09XN application in `literature/stacks-project/etale-cohomology.tex`. I also read the existing node `lem-galois-fpqc-covering-base-change`, whose statement explicitly says that the first projections of the fibre products form an fpqc covering; this is the exact input used in step 1. For the new node I checked the Tag 03N0 statement and verified that it says precisely that compatible opens on every cover member descend uniquely to an open on the base, including the pairwise pullback equality used in step 2. The fibre-product definition is cited for the iterated-product identifications in step 2. I tested the identity-cover case and a singleton cover: both reduce to the given open and its unique descent. I ran all required Mathlib searches for the item and new node; LeanSearch was unavailable and is recorded as such, while LeanFinder, Loogle, and source grep found no exact family-level open descent theorem.
