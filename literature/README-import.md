# Literature import, 2026-10-08

- `CITATIONS.tsv`: one row per (node, document, place as cited). Columns: `node_id` (`-` when the citation sits in a LaTeX unit that maps to no node), `source` (file, and `#label` for LaTeX), `document_key`, `document`, `place_as_cited`, `stacks_tag`, `extraction_pattern`. Rows from `master/blueprint/**/*.md` are exact per node; rows from LaTeX are attributed to the nearest preceding `\label`, which is approximate.
- `stacks-tags-cited.tsv`: the 652 Stacks tags cited, each with label, TeX file, kind and citing nodes. All resolve in `stacks-project/tags/tags` at the commit in `LIST.md`.
- `stacks-project/` is a nested git clone and is listed in `.gitignore`; re-create it from the commit in `LIST.md`.
- Produced by regex extraction, not by reading every node; a hand check of 40 nodes found 1 missed tag in about 50 citations (a `Tags 0130/0131` list, since handled).

## Unidentified references

Document not identifiable:

- Numbered references with no document named, in 15 nodes of `sec-poincare-duality` (`cor-pod-constant-coefficients`, `cor-pod-reciprocal-eigenvalues`, `cor-pod-untwisted-similitude`, `def-pod-derived-poincare-pairing`, `def-pod-dual-tate-datum`, `prop-pod-degree-of-the-pairing`, `prop-pod-dual-tate-data-compatibility`, `thm-pod-adic-reconstruction-and-scalar-extension`, `thm-pod-degreewise-perfectness-over-a-field`, `thm-pod-derived-poincare-duality`, `thm-pod-equivariance-of-the-twisted-pairing`, `thm-pod-qbar-coefficient-pairing`, `thm-pod-trace-isomorphism`, `thm-weil-poincare-duality`): "Proposition 1.48", "Definition 1.49", "Definition 1.50", "Proposition 1.58", "Definition 2.148", "Lemma 2.156", "Definition 7.2", "Definition 7.7", "Definition 9.5"–"Theorem 9.35". The numbering matches no file in `blueprint/`; it is probably the authors' `weil_conjectures_complete_notes.pdf` (Wanted). Rows: `document_key = UNIDENTIFIED-NUMBERED`.
- `sk-prop-cohsm`: "Zavyalov 5.7.7", no title.
- `slopmaster2/.../08_weights_v2.tex#found:rank-one-purity`: "the rank-one Katz–Lang theorem", no title or place.
- `lem-sc-tsen`: "Tsen, 1933", no title.

Document identified, place missing or doubtful:

- `lem-sc-isogeny-facts`, `sec-abelian-varieties`, `sk-prop-jacobian`, `thm-sc-jacobian-representability`: "Mumford and Milne, *Abelian Varieties*" with no place. `lem-sc-rigidity` and `thm-sc-jacobian-representability` cite "Milne, Abelian Varieties, Ch. I" and "Ch. 12": the obtained notes have chapters I–IV only, so "Ch. 12" may mean §12 or Milne's chapter in Cornell–Silverman.
- `thm-pur-with-support-exactness`: "Milne, Lectures on Etale Cohomology, Section 9, Theorem 9.3"; in the obtained v2.21, 9.3 is a Remark.
- `lem-pc-fpqc-descent`: "EGA 0_IV, (2.5.7)"; 0_IV begins at §14, so the volume is doubtful.
- `lem-sc-connected-finite-order`: Milnor–Moore is cited as "Ann. of Math. 68 (1958)"; the paper is Ann. of Math. 81 (1965).
- `def-wf-iota-real`: "Deligne, Weil II, (1.2.13)"; not found by text search in the scanned PDF (1.2.12 is), unchecked by eye.
- `lem-sc-brauer-zero-all-curves`: "Grothendieck, Le groupe de Brauer III" with no place.
- No place at all: SGA 5 (`sec-trace-formula`, `sk-def-sf-weil-complexes`, `sk-thm-sf-kunneth-verdier`), SGA 4½ (`sk-prop-sf-biduality-general` in part, `thm-weil-pbc-amplification-proper`), SGA 4 (`lemma-constructible-torsor-trivialises`), BBD (`prop-weil-heart-abelian`), Spaltenstein (`lem-weil-derived-limit-existence`), Olivier (`thm-weil-pbc-weak-etale-strict-local`), Balmer–Schlichting (`lem-weil-karoubi-envelope-triangulated`), Greenberg (`lem-sc-tsen`), Tate (`sk-thm-picard-duality`).
- Stacks project cited without a tag: 62 rows in 45 nodes (`extraction_pattern` = `stacks:notag` or `stacks:number-only`), e.g. "Stacks Project, Algebra: the Nullstellensatz", "Lemma 44.6.1". Chapter.section.item numbers drift between Stacks versions; they were not resolved to tags.

`import-tools/` holds the three scripts that produced `CITATIONS.tsv`, `stacks-tags-cited.tsv` and the tables of `LIST.md` (`extract_citations.py <out.tsv>`, then `stacks_tag_index.py`, then `make_list.py`).
