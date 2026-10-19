## Worker report

Files written: item `lem-weil-pbc-proetale-qcqs-finite-family-geometry.json`; new nodes `lem-weil-pbc-proetale-qcqs-site-limits` (unsplit, no Mathlib match), `lem-weil-pbc-proetale-subcanonical` (unsplit, no Mathlib match), and `lem-weil-pbc-proetale-finite-coproduct-evaluation` (unsplit, no Mathlib match); `citations.json`.

Attachments: none. WANTED: none.

The imported item had no proof steps. I split it into the qcqs finite-cover site/limits statement, the subcanonicality statement, and the finite disjoint-union/evaluation statement. I searched the DAG and blueprint for the Stacks tags and key words; no duplicate node stated these facts. The Lean source tree contains no declaration tagged with this item, so it is not attached.

## Review by NF

I read the item source references in Stacks `proetale.tex`: Tag 09A1's qcqs-subsite paragraph and Tag 098M's fibre-product lemma, Tag 098Z's subcanonical lemma, and Tag 0F4P's finite-disjoint-union argument, together with Hypercoverings Tag 0DB1. The first proof step cites the qcqs-site node, whose statement explicitly supplies the site, scheme fibre products and finite limits, slice agreement, and stability of finite coverings under adjoining arrows; the affine qcqs clause is taken from the existing scheme-conventions node and its statement was checked verbatim. The second step cites the subcanonical node, which states exactly that every representable is a sheaf. The third cites the finite-coproduct node, which states existence, affineness, representable comparison, evaluation products, and the empty-family case. The final assembly step only combines those cited statements and is marked elementary.

I tested edge cases conceptually: a singleton family gives the identity comparison, and the empty family gives the empty scheme with singleton sheaf evaluation. Mathlib searches were run for the item and each new node with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such, while the other searches returned only unrelated étale or scheme-coproduct declarations. No source or statement correction was needed.

## Not duplicates

lem-weil-pbc-proetale-finite-coproduct-evaluation vs lem-weil-pbc-site-hypercover-disjoint-union: the existing node states a hypercover disjoint-union construction and epimorphism property, while this node states scheme coproduct existence plus the sheaf representable isomorphism and evaluation product for every finite family, including the empty family.
lem-weil-pbc-proetale-finite-coproduct-evaluation vs lem-weil-pbc-proetale-qc-affine-contractible-cover: the existing node constructs a weakly contractible affine cover of a qcqs object, while this node gives the general finite coproduct and sheaf evaluation comparison for arbitrary finite qcqs objects.
lem-weil-pbc-proetale-qcqs-site-limits vs lem-weil-pbc-proetale-affine-acyclic-hypercover: the existing node applies the qcqs subsite facts to construct a particular affine acyclic hypercover; this node states the underlying site, finite-limit, slice, and covering-stability geometry for all qcqs objects.

## Second reading by NF

- Item statement: checked every clause against Stacks Tags 09A1 (qcqs finite-cover site and finite coproduct hypercover construction), 098M (fibre products and equalizers), 098Z (subcanonicality), 0F4P (finite disjoint-union evaluation), and Hypercoverings 0DB1; the scheme, site, universe, qcqs, affine, slice, covering, representable, and sheaf notions are cited and the empty and singleton families behave as stated.
- Step 1: checked that the cited qcqs-site-limits statement supplies the site, scheme fibre products, inclusion, slice limits, adjoining-arrow stability, and affine-qcqs fact; verdict correct and non-elementary.
- Step 2: checked the cited subcanonical statement against Tag 098Z; verdict exact and non-elementary.
- Step 3: checked the cited finite-coproduct statement against Tags 0F4P and 0DB1, including affine summands, representable comparison, arbitrary sheaf evaluation, and the empty family; verdict exact and non-elementary.
- Step 4: checked that it only assembles the three cited statements and preserves naturality and edge cases; verdict elementary.
- New node `lem-weil-pbc-proetale-qcqs-site-limits`: checked B1--B7, source tags 09A1 and 098M, duplicate search, and finite-limit/slice hypotheses; verdict retained.
- New node `lem-weil-pbc-proetale-subcanonical`: checked B1--B7 and Tag 098Z; made X and the object range explicit; verdict retained after repair.
- New node `lem-weil-pbc-proetale-finite-coproduct-evaluation`: checked B1--B7 and Tags 0F4P and 0DB1; made the finite index set, qcqs hypotheses, representable notation, and empty case explicit; verdict retained after repair.

Changes: corrected the imported item's erroneous `created.item` value; repaired the two self-contained statements above and synchronized their citation quotes. No statement dispute was found. Small tests: a singleton family yields the identity comparison, and the empty family yields the empty scheme and singleton sheaf value.
