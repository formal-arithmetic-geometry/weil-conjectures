## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-nodal-normalization-picard-sequence.json`: item split, statement unchanged, seven proof steps; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-pinching-invertible-patching.json`: new statement-only lemma; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-affine-group-torsor-representability.json`: new statement-only lemma; no Mathlib match.
- `citations.json`: verbatim statement quotations for every step citation.

## Attachments

None. Searches of `lean/WeilConjectures/` by the exact blueprint tag and by nodal/Picard/gluing terminology found no declaration giving this item. Existing ordinary normalization and Picard declarations do not state its all-test-schemes exact sequence and torsor geometry. The two new general lemmas also have no matching project declaration.

## WANTED

None. The primary Stacks sources required for this split are available locally.

## Corrections and scope

The imported statement is retained in full; there is no statement dispute. The source's Tag 0C1M is an exact sequence on field-valued Picard groups. Merely iterating that displayed sequence would not prove the item's fppf-sheaf assertion. The proof now constructs the conductor square, uses invertible-sheaf patching after every base change, and treats local representatives and local equality in the Picard sheaf explicitly. The quotient torus is constructed by Laurent monomials from a rooted spanning tree; it is not inferred just from its geometric points.

The latest blueprint's direct-image proof (3) now cites the open-coefficient/direct-image results and no longer spells out the deep alteration input in this item's inherited ancestry. I read the latest version and retain the assigned local normalization/Picard route and inherited metadata. No chapter/unit route was replaced, and this auxiliary is not the unit's key statement, so no unit realization fields were changed.

## Review by Q02

I read `curves.tex` Example 0C1J (example-glue-points) and Lemma 0C1M (lemma-glue-points), including the units-sequence proof; `pic.tex` Lemma 0BA0 (lemma-picard-pieces), including its decomposition as fppf sheaves; and the current blueprint unit and direct-image proof. I also read every cited DAG statement, rather than relying on the titles or on arguments inside their proofs.

For the new patching node I read `more-algebra.tex` Situation module-over-fibre-product, Lemma 07RU (module-over-fibre-product), Lemma 0D2I (flat-module-over-fibre-product), and Lemma 0D2J (finitely-presented-module-over-fibre-product). The input is a ring fibre product with one surjective arrow, not arbitrary descent across a finite surjection. The stated equivalence restricts finite-projective patching to rank one; the affine spectra cover all points by the same fibre-product description, so ranks are detected. The inverse is the matching-pairs module. Its canonical restriction comparisons give base-change and tensor compatibility. These are arguments to be proved when that new node is split, not a proof hidden in its statement. Empty pinching centre reduces to the identity equivalence. I checked a split node and a nontrivial gluing unit over a ring with nilpotents: no step asks that the parameter ring be reduced or that a unit lift globally across an arbitrary quotient.

For the new torsor node I read `groupoids.tex` Remark 049C (fun-with-torsors), specifically the affirmative representability answer for affine groups and its affine-descent reference, and its distinction from the definition/characterization in Lemma 049B. I read the affine-effectivity statement in `descent.tex` and the smoothness-descent statement 02VL, and `morphisms.tex` 056G (smooth-open). The node is for fppf-locally trivial sheaf torsors under smooth affine finitely presented groups; it does not assert representability of torsors under arbitrary group schemes. Local translations give the descent cocycle, affine descent constructs the representative, and smoothness and surjectivity descend from the local model. The trivial group gives the identity over S. Nonreduced bases are permitted. Smoothness of the total space over k is assembled separately with the existing smooth-composition node; it was removed from this auxiliary to avoid duplicating that generic theorem.

Step 1 uses the statement of `lem-sfb-nodal-completed-normalization-model` for finiteness, component geometry, branch residues and the completed normalization. It does not assume normalization commutes with arbitrary base change. The completed model explicitly has pairs with equal constant terms. `lem-weil-pbc-local-completion-faithfully-flat` applies since the cited geometry node gives Noetherian local rings. `lem-weil-pbc-flat-tensor-exact` and `lem-sc-faithfully-flat-tensor-zero` detect the kernel/cokernel defects after completion. The same check on the quotient of the branch ideals verifies that the inverse image of the reduced node is the two reduced branch points. All of these statements are quoted in citations.json.

Step 2 uses flat-tensor exactness and the new patching equivalence, which states both the objects and compatible morphisms it needs. Every test scheme is flat over the field, so even nonreduced base changes preserve the conductor square. Eliminating the node line bundle from a patching triple gives a branch-fibre isomorphism; the reverse operation is stated explicitly. This is the argument for the item's gluing map, not a new node restating that map.

Step 3 originally risked silently using smooth implies geometrically reduced. I corrected it: the existing smooth-connected-curve local-ring statement gives integrality, and `lem-pc-h0-proper-variety` gives a finite constant field, equal to Omega because Omega is algebraically closed. `lem-pc-flat-base-change-cohom` applies to the proper (hence qcqs) structure map, the quasi-coherent structure sheaf, and the flat map from any affine test scheme to the field. Its degree-zero conclusion gives all component scalar automorphisms over arbitrary T. The sign of delta is checked by writing the compatibility equation for a change of frames. Graph connectedness is proved by the closed-component partition argument, not assumed without explanation.

Step 4 uses exactly the definition of `sk-def-picard-pic`: sections are locally represented by line bundles, and equality is locally witnessed by equality of their classes. Finiteness of the node and component sets permits simultaneous refinements. Branch-fibre bundles and base bundles are Zariski locally trivial. This proves epimorphy and both kernels as sheaf assertions. It does not infer relative exactness from Omega-points.

Step 5 gives the spanning-tree algorithm and both orientation formulas. The only cited non-elementary geometric input is `lem-trf-split-lattice-torus-projection`, which proves smoothness and a section for the group algebra of a finitely based free lattice. The rest is an explicit elementary Laurent-monomial computation, so the step is marked elementary with that citation. Tree normalization is unique modulo scalar component frames; loops never lie in the tree. I tested E empty, a two-component one-edge tree, an irreducible one-node curve, and a graph with parallel edges. The residual ranks are respectively zero, zero, one and the usual number of non-tree edges, in every characteristic and over nonreduced T. No Smith-normal-form or saturation theorem is concealed.

Step 6 uses `sk-thm-picard-main` for smooth proper geometrically connected degree-zero representatives. Proper-base-change and proper-composition give properness of the product. Smooth relative-dimension permanence gives smoothness, and the geometrically-connected-product-components lemma gives connectedness. Each is used under its stated hypotheses, so the definition of abelian variety applies to B. The product group law is coordinatewise. All these generic off-unit tools are declared in split_report.tool_uses.

Step 7 proves the torsor identity directly by taking differences in the established kernel; local lifts of the Picard epimorphism give local trivializations. The new torsor representability node then applies to the split torus Q and scheme B. It gives the smooth surjective open projection; `lem-trf-smooth-composition` gives smoothness over Omega, and the algebraic-space definition includes schemes. Yoneda represents the group operations. This node is not a second copy of the item: it knows nothing about nodal curves, normalization, Picard groups, graph incidence, Jacobians, or the exact sequence.

I checked delivery-errors B--E: new nodes have self-contained statements and no proof/proof-dependency content; notions have definition citations or explicit meanings; Stacks tags were matched to tags/tags and the actual source labels; duplicate and blueprint searches precede creation; no cited proof is used in place of its statement; every non-elementary inference is covered by a cited statement; no cycle or unsupported hypothesis is intentionally introduced. Each proof step is under 2000 characters. No statement was weakened, no Lean was written, and no compiler or build was run. The proof origin is marked agent because the relative upgrade and graph/sheaf assembly extend the source's field-point argument.

Mathlib searches were run only through msearch.py and the actual results are recorded. I read the returned projective lifting and Picard-group scalar-extension definitions, and the Zariski local representability source. None is the patching equivalence or fppf torsor theorem. In particular Zariski open-cover representability is not used as if it were arbitrary fppf descent. The item searches return ordinary normalization and Weierstrass Jacobian coordinates, not the generalized Jacobian. No returned candidate is an exact match or a one-line specialization.

## Not duplicates

lem-sfb-smooth-affine-group-torsor-representability vs lem-trf-smooth-fpqc-base-descent: the existing statement only descends smoothness of an already represented scheme morphism along a single fpqc map; the new statement constructs the scheme representing a sheaf torsor and also gives affineness, surjectivity and universal openness.
lem-sfb-smooth-affine-group-torsor-representability vs thm-pd-fpqc-local-properties: the existing statement concerns a scheme after finite field extension; it neither constructs a representative of a sheaf torsor nor treats arbitrary base schemes.
lem-sfb-smooth-affine-group-torsor-representability vs lem-pd-relative-smooth-dimension-codescent: the existing statement descends a ring-map smooth-coordinate condition; it does not construct a torsor scheme or its action.
lem-sfb-smooth-affine-group-torsor-representability vs lem-pur-coordinate-chart-finite-dimension-witness: the existing statement chooses points and computes local dimensions in a supplied etale affine-space chart, using openness only inside its proof; it contains no torsor representability theorem.

The pinching node has no existing node with source tags 0D2J or 07RU. Existing Ferrand/pinching nodes construct schemes and their ring fibre products; they do not classify invertible sheaves or their morphisms on those squares. The action-groupoid torsor-comparison node concerns equivalence of two stacks with scheme torsors already in one side's definition; it does not state the present all-base-schemes smooth affine representability theorem.

## Unfinished work

No unfinished part of this item's stage-1 split. The two new lemmas are intentionally statement-only items for later stage-1 splitting. Delivery validation is recorded below after the required server dry run.

## Validation

The required server dry run completed with `OK (not pushed)` at c9a13f1241d; the full delivery preflight passed, including the DAG and split checks, search log, duplicate distinctions, and verbatim citations. A final punctuation correction in Step 7 is being checked again before direct delivery. No Lean compilation was performed.
