# Stage-1 split: lem-sc-p1-boundary-connecting-naturality

Files written: dag/nodes/sec-picard-framework/lem-sc-p1-boundary-connecting-naturality.json (item, split); citations.json; report.md. No new nodes or Mathlib leaves.

Attachments: none. The slopmaster2 H.δ and H.δ_apply declarations give the boundary by extension-class composition, but neither states the item's pullback naturality. There is no exact declaration to attach.

WANTED: literature/stacks-project/cohomology.tex, Section Tag 01DZ and Lemma Tag 0B3A, for lem-sc-p1-boundary-connecting-naturality.
WANTED: literature/stacks-project/derived.tex, Lemma Tag 05TE, for lem-sc-p1-boundary-connecting-naturality.
The literature checkout is absent on this machine. I read the corresponding Stacks tag pages online.

The inherited source.place says that Stacks 0B3A states pullback naturality. It does not: 0B3A identifies the class of an extension ending in O_X with the boundary of 1. The proof here uses the derived-functor delta-functor theorem at 05TE and the module-sheaf cohomology definition at 01DZ. I left the source field unchanged because it is maintainer-owned and report the correction here. The original item's TeX had doubled backslashes after JSON decoding; the statement's mathematical content is unchanged, and its JSON escaping is corrected.

The pullback square was written out directly, so no new node restates a clause of the item. The whole DAG and blueprint were searched by the tag and by boundary/connecting/naturality terms; the existing generic node lem-weil-pbc-right-derived-universal-delta-functor supplies the one non-elementary theorem used. Mathlib searches were rerun through msearch.py with two phrasings. The hits on δ_naturality concern homology of short exact complexes or triangles; identifying the derived sheaf boundary with those constructions is additional work, so the item is not a Mathlib leaf.

## Review by M1

I read Stacks 01DZ (the module-sheaf paragraph), 05TE (the canonical delta-functor structure), and 0B3A (boundary of 1). They support the unchanged mathematical claim for schemes and sheaves of O_X-modules. I also read the unit record sk-thm-picard-duality and the blueprint place recorded in the item: this lemma serves the naturality calculation in the P1 duality Step 2.

Step 1 constructs the pullback as pairs and checks both squares, kernel, and local surjectivity. This is elementary from the definition of a pullback of a short exact sequence; no cited theorem is hidden in it. The small cases u = id and u = 0 give respectively the original sequence and the split pullback, consistent with the construction.

Step 2 uses def-sc-sheaf-cohomology-functor for all the hypotheses of the generic result: the module category is abelian with enough injectives, global sections is additive and left exact, and H^i is its right derived functor. The quoted statement of lem-weil-pbc-right-derived-universal-delta-functor explicitly gives the naturality equation for a morphism of short exact sequences. In Step 1 that morphism has left map id_A and right map u, so its degree-zero equation is exactly the desired one after evaluating at t. The identification Ext^1(O_X,A) = H^1(X,A) has the same A on both sides, so no naturality of that identification is assumed. The zero sheaf A = 0 and u = 0 both give zero boundaries, as the formula requires.

I checked the existing cited statements rather than relying on their proofs: def-sc-sheaf-cohomology-functor states the required derived-functor setup, and the generic delta-functor node states the naturality identity itself. I corrected the TeX escaping and the inherited citation error in the proof sources and reported the maintainer-owned source field above. Nothing remains unfinished in this one-level split.

## Source error

The inherited `source.place` attributes pullback naturality to Cohomology Tag 0B3A. That tag identifies the extension class of an extension ending in $\mathcal O_X$ with the connecting image of $1$; it does not state pullback naturality. The naturality used in Step 2 is the canonical delta-functor naturality in Derived Categories Tag 05TE, with module-sheaf cohomology supplied by Cohomology Section Tag 01DZ. The maintainer-owned `source` field is unchanged; this report records the correction for the maintainer.

## Second reading by M1

- Item statement: checked the scheme, short exact sequence, $\mathcal O_X$-module morphism, pullback sequence, Ext/H^1 identification, and pointwise equation against Cohomology Section 01DZ and the unit blueprint; verdict: hypotheses and conclusion are coherent, including $u=\mathrm{id}$, $u=0$, $\mathcal A=0$, and zero-scheme cases.
- Step 1: checked the pair construction, both commutative squares, kernel, and local surjectivity against the pullback short exact sequence definition in Cohomology Section 01DZ; verdict: elementary and complete.
- Step 2: checked the derived-functor hypotheses against `def-sc-sheaf-cohomology-functor` and the displayed naturality equation against `lem-weil-pbc-right-derived-universal-delta-functor`; verdict: $(\mathrm{id}_{\mathcal A},v,u)$ specializes the generic equation exactly, with $H^0(u)(t)=u\circ t$.
- New nodes: none; B1-B7, duplicate checks, and per-node small-case checks are vacuous.
- Existing-node search: searched the DAG for the item, tags 01DZ/0B3A/05TE, and boundary/connecting/naturality terms; the generic delta-functor node is the only required non-elementary dependency.
- Mathlib search: reran LeanFinder with a derived-functor connecting-map query (generic Snake Lemma naturality hits only) and Loogle with a derived-functor connecting-morphism query (no hit); the item is not a Mathlib leaf.
- Changes made: corrected `created.item` to this delivered item and recorded the 0B3A source-label error above; no mathematical statement or proof step was otherwise changed.
