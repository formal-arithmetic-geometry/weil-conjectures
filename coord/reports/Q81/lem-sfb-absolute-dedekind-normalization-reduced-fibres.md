# Stage-1 report: lem-sfb-absolute-dedekind-normalization-reduced-fibres

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-absolute-dedekind-normalization-reduced-fibres.json` — existing statement retained, split into 10 proof steps, 31 existing dependencies, no new nodes, Mathlib searches recorded as no exact match.
- `citations.json` — 35 verbatim statement quotations, one for every cited node in every step.
- `report.md` — this report.

Attachments: none. No sorry-free declaration in `lean/WeilConjectures/` carries the item’s full statement, and no declaration has the blueprint tag.

WANTED: archival local copy of `literature/anantharaman-groupes-dimension-un.pdf`; the primary Numdam scan was read online, especially Appendix II, Theorem 1, pp. 73–74.
WANTED: archival local copy of `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`; the primary PDF was read online, especially Proposition 3.5.2 and Theorem 3.5.5, pp. 20–24.
WANTED: Bourbaki, *Algèbre commutative*, VI §8, for the valuation-extension background used to identify localizations of the absolute integral closure.

The imported statement is the affine form of Anantharaman Appendix II, Theorem 1: the base is a Noetherian normal one-dimensional domain, its fraction field is extended to an algebraic closure, and the normalization of the flat finitely presented algebra has the asserted finite, flat, finitely presented, normal and geometrically reduced properties. I did not weaken the statement or add Noetherianity, semilocality, excellence, or module-finiteness of the absolute integral closure.

## Not duplicates

- `lem-sfb-absolute-dedekind-normalization-reduced-fibres` vs `lem-sfb-semitrait-potential-reduced-normalization`: the latter is the finite-field-stage, finite-family corollary (Anantharaman Corollary 2); this item is the single affine normalization over the full algebraic closure and is the input used before finite-stage descent.
- `lem-sfb-absolute-dedekind-normalization-reduced-fibres` vs `lem-trf-valuation-reduced-fibre-normalization`: the latter assumes the base is already a separably closed valuation ring and states the valuation-local normalization theorem; this item constructs the absolute integral closure from all finite Dedekind stages and then globalizes the valuation-local result.
- `lem-sfb-absolute-dedekind-normalization-reduced-fibres` vs `lem-sfb-complete-trait-normalized-reduced-fibres`: the latter is a complete-trait scheme theorem with finite field extension and nonaffine/global normalization data; this item is the affine algebra theorem over an arbitrary Noetherian Dedekind domain and an infinite algebraic closure.
- `lem-sfb-absolute-dedekind-normalization-reduced-fibres` vs `lem-sbc-integral-closure-finite-normal-product`: the latter only proves normality of localizations of an integral closure in a finite product of normal domains; it does not prove Raynaud finiteness, flatness, finite presentation, or geometric reducedness.

## Review by Q81

I read the item node, its chapter record, the `sk-thm-sf-ctf-stability` unit record, and the latest direct-images proof. The primary source is Anantharaman, Appendix II, Theorem 1 (printed p. 73, with the detailed proof on pp. 74–77 of the Numdam scan). I also read Temkin, Proposition 3.5.2 (η-normality) and Theorem 3.5.5 (valuation normalization and the finite-height/limit argument), and the exact Stacks source places recorded in the existing dependency nodes.

Step 1 checks the injection (A_B\to A_K\otimes_K\Omega), the tensor identification after inverting (B\setminus\{0\}), and finite presentation and flatness of (A_B/B). Its cited integral-closure, flatness, finite-presentation, and tensor nodes state those facts. Step 2 checks that every localization (B_\mathfrak p) is the directed union of the DVR localizations of finite Dedekind stages, hence a valuation ring with fraction field Ω; the cited finite-extension, Dedekind-localization, and DVR nodes provide exactly those hypotheses. Step 3 uses localization of integral closure and the valuation normalization theorem; the generic algebra is geometrically reduced because the item assumes geometric normality, and this is where the zero algebra and arbitrary field extensions are allowed.

Step 4 descends the finitely presented normalization algebra and its map from the filtered principal-localization system. Step 5 descends finiteness, flatness, and reduced geometric fibres using the existing filtered-colimit and limit-descent statements; I checked that the maps are finite presentation maps and that all transition morphisms are affine. Step 6 verifies the hypotheses of Temkin’s η-normality theorem: the base principal open is normal integral affine, and the descended algebra is flat, finitely presented, and has reduced geometric fibres. Step 7 applies η-normality to (H[c]) for each integral element (c\in C_f); the open where (c=h/s) is schematically dense because all rings embed in the generic algebra. This identifies the descended finite model with the actual integral closure on a principal neighbourhood, rather than asserting only stalkwise finiteness.

Step 8 globalizes over finitely many principal opens: finite descends fpqc-locally, flatness is checked on the localization cover, and local finite presentation gives a finite presentation of the global B-algebra. Step 9 checks normality independently using finite components of the Noetherian generic algebra, finite products of integrally closed domains, and the existing integral-closure finite-product normality node. Step 10 checks the canonical generic-fibre isomorphism by localization and translates reduced geometric fibres into the stated field-valued reduced fibres using the affine geometric-fibre comparison. I checked the edge cases (A=0), empty fibres, and (D=0), and verified that no step assumes (B) Noetherian or (B/R) finite.

The four Mathlib searches required for this item were rerun through `msearch.py`; they found only relative normalization, geometric-reducedness predicates, and finite-extension Dedekind closure results, so the item remains a non-Mathlib theorem. The earlier recorded searches in `searches.jsonl` were retained and read. The server-side `srvcheck.py ... check_dag` passed, and every citation quote was checked as a verbatim substring of the cited node statement.

What was corrected: the imported proof had no steps. I replaced it with the full local-to-global proof above, explicitly inserting the valuation-localization construction, filtered descent, η-normality recognition, fpqc globalization, normality, and generic-fibre/reduced-fibre checks. No existing node was modified and no new node was needed.

What remains unfinished: the archival copies listed under WANTED are not present locally; the online primary scans were sufficient for this stage-1 split.
