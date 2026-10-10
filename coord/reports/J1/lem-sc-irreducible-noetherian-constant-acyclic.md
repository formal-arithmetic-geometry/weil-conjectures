Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-irreducible-noetherian-constant-acyclic.json` — statement, 2 proof steps, no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-irreducible-constant-sections.json` — statement-only dependency, no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-topological-flasque-acyclic.json` — statement-only dependency, no Mathlib match.
- `citations.json` — verbatim citations for every step dependency.

Attachments: none. There is no matching declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`.

WANTED: `literature/stacks-project/cohomology.tex`, Lemma 02UW and Lemma 09SY, for the exact source text; the repository contains only the imported citation metadata.

No statement error was found. The imported item had no proof and its three Mathlib searches were stale, so I reran LeanSearch, LeanFinder, Loogle, and Mathlib grep for the item and both new nodes. LeanSearch was unavailable; the other searches found no matching theorem. The existing `lem-sc-zariski-flasque-acyclic` node has Zariski-site cohomology in its statement, so it was not used as a direct citation for the topological cohomology conclusion; the new topological specialization records that distinction. No existing DAG or blueprint node states either new dependency.

## Not duplicates

lem-sc-irreducible-constant-sections vs lem-weil-pbc-locally-constant-maps-sheaf: the existing node proves that locally constant maps form a sheaf; the new node computes sections of the constant abelian sheaf on every nonempty open of an irreducible space and identifies restrictions with the identity.
lem-sc-irreducible-constant-sections vs lem-weil-pbc-closed-pushforward-constant-stalks: the existing node computes stalks of a closed pushforward of locally constant set-valued maps; the new node computes sections and restriction maps of an abelian constant sheaf on irreducible opens.
lem-sc-irreducible-constant-sections vs lem-weil-pbc-constant-sheaf-open-maps-sections: the existing node gives a Hom universal property for the sheaf of locally constant set-valued maps; the new node specializes the section values and restrictions to an irreducible space and abelian coefficients.
lem-sc-irreducible-constant-sections vs lem-weil-pbc-locally-constant-germ-evaluation: the existing node identifies germs at one point with the coefficient set; the new node identifies sections over all nonempty opens of an irreducible space and their restriction maps.

## Review by J1

I read the imported item and the neighboring Proposition 02UZ split, especially its d=0 irreducible step. I also read `def-sc-topological-abelian-cohomology`, `def-sc-zariski-flasque`, and `lem-sc-zariski-flasque-acyclic`; the first defines the same right-derived global-sections cohomology used by the item, while the latter two establish the restriction-surjectivity notion and the analogous Zariski acyclicity. The new constant-section statement is the locally constant-map description of the sheafification of the constant presheaf (Stacks 006W), specialized to an irreducible space: every nonempty open is irreducible and hence connected, so a locally constant map is constant. In item step 1 I checked this hypothesis and handled the empty open separately using the sheaf axiom; the cited section node says exactly the section and restriction facts used, and the flasque definition says exactly the resulting surjectivity condition. In step 2 I checked that the new topological flasque node has the same cohomology convention as the item and quotes the required positive-degree vanishing. I tested the edge cases of an empty space (the item excludes it), a one-point irreducible space, and a nontrivial irreducible space with A=0. I corrected the imported Mathlib-search records by replacing them with the searches actually run and changed the item status to `split`.

What could not be finished: no local copy of the cited Stacks source is present, so the report records it as WANTED; the natural-language split is complete and all dependencies are statement-only as required.

## Second reading by J1

- Item statement: checked against Stacks Cohomology Lemma 02UW (cohomology-lemma-constant-sheaf), including irreducibility, Noetherian minimal-closed-subset hypothesis, the opens-site constant sheaf, and q > 0; verdict: correct.
- Item step 1: checked the cited section calculation, flasque definition, and the elementary fact that nonempty opens of an irreducible space are irreducible; the empty-open case is supplied by the sheaf axiom; verdict: dependencies say exactly what is used.
- Item step 2: checked against Stacks Cohomology Lemma 09SY (lemma-flasque-acyclic); the flasque hypothesis and derived-global-sections convention match; verdict: correct.
- New node `lem-sc-irreducible-constant-sections`: checked against Sheaves Definition 006W (definition-constant-sheaf), the preceding locally-constant-map description, and the existing locally-constant-map sheaf node; tested on a one-point space, a nontrivial irreducible space, and A = 0; verdict: correct and not a duplicate.
- New node `lem-sc-topological-flasque-acyclic`: checked against Cohomology Lemma 09SY and the topological cohomology definition; tested on the empty space and a one-point space; verdict: correct and not a duplicate.
- New-node form: both statements are self-contained and now explicitly introduce the opens site; definitions, TeX, source tags, and three Mathlib search kinds were checked. No sorry-free Lean declaration matches either node.
- Blueprint and DAG checks: searched the full blueprint and DAG for matching statements; no same-as blueprint node was found and no cycle was introduced.

Changes made: added `def-weil-pbc-sites-and-cohomology` to the item and both new statements and their statement dependencies, because the original wording left the site implicit; added this independent second-reading record. The existing worker review and source-WANTED note remain unchanged.
