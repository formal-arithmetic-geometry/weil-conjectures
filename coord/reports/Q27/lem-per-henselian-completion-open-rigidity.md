Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-henselian-completion-open-rigidity.json`: existing item split into four proof steps, with five proof dependencies.
- `lem-per-admissible-modification-cohomology-presentation`: new unsplit statement node; Mathlib searches found no match.
- `lem-per-admissible-modification-valuative-stalks`: new unsplit statement node; Mathlib searches found no match.
- `lem-per-dense-henselian-field-etale-comparison`: new unsplit statement node; Mathlib searches found no match.
- `citations.json`: verbatim statement quotes for every proof-step citation.

Attachments: none.

WANTED: none. The ILO paper and the cited Stacks source files are present locally.

The item keeps the imported statement and hypotheses. I expanded the completion-comparison sketch into the admissible-blowup limit spectral sequence, its valued-field stalk reduction, dense henselian valued-field comparison, and the page-to-abelian-filtration argument. The helper nodes are strictly smaller inputs and do not restate the item's completion-invariance conclusion. I normalized the TeX escaping and changed the helper-node coefficient dependency to the existing sectionwise etale-sheaf definition, which is the definition their statements use. The source's displayed cohomology comparison is first written after reduction to strictly henselian local rings; the item is the general Noetherian henselian-pair form, and Step 1 verifies the completion pair and identifies its open complement before applying that reduction.

## Not duplicates

No new node carries a Stacks tag or duplicates an existing tagged node. The existing Riemann--Zariski nodes concern valuation spaces and filtered local rings, whereas the new presentation node concerns the etale-topos spectral sequence for admissible blowups; they are not interchangeable inputs.

## Review by Q27

I read the item against ILO XX §4.4, printed pages 373--374, including the CTC statement, the admissible-blowup spectral sequence, the limit-topos comparison, the reduction to henselian I-valuative local rings, the dense valued-field step, and the completion note. I also read the Stacks statements for the two algebraic inputs used in Step 1: Tag 05GG (completion modulo a finitely generated ideal) and Tag 0ALJ (an adically complete pair is henselian). The source files and line labels are recorded in the item and the cited existing nodes.

Step 1 uses exactly the statements of `lem-weil-pbc-adic-completion-mod-ideal` and `lem-weil-pbc-complete-pair-henselian`: finite generation follows from Noetherianity, the completion has quotient (C/I), the completed pair is henselian, and the inverse image of (V(I)) is (V(I\widehat C)). Step 2 uses the statement of `lem-per-admissible-modification-cohomology-presentation`, which supplies the common limit topos, coefficient colimits, spectral sequences, and the canonical abutment pullback. Step 3 uses the statement of `lem-per-admissible-modification-valuative-stalks` for the conservative valued-field stalk family and the statement of `lem-per-dense-henselian-field-etale-comparison` for the stalkwise isomorphisms; the conservativity and functoriality then give the (E_2)-page isomorphism. Step 4 is the elementary spectral-sequence page induction and finite-filtration five-lemma argument, with the nilpotent-ideal edge case checked directly.

I checked every statement dependency exists, every proof dependency is included in `proof_deps`, every new node is statement-only and unsplit, all Mathlib searches are logged in `searches.jsonl`, and every citation quote is copied verbatim into `citations.json`. The server-side `review_split` check passed, and the server-side `check_dag` check reported no introduced finding.
