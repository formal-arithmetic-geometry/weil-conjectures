## Worker report

### Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-gerbe-qc-diagonal-descent.json`: statement, split; six proof steps using existing nodes. Mathlib verdict: no match.
- `citations.json`: 21 entries, each containing a verbatim statement of the cited node.
- `report.md`: this report.

### Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint id, gerbe/Gerbe and the quasi-compact-diagonal notion found no project declaration stating this result. The additional search in `lean/Sheaf/` found only unrelated residual-gerbe docstrings, not the item.

### WANTED

None. All mathematical sources used here are available locally.

### Findings and changes

The live item was unsplit, and no repair note or prior sandbox node/report existed. The statement is correct as written. Its base is the arbitrary original scheme S: the assumption is the relative diagonal over S, not the absolute diagonal over Spec Z. No hypotheses were added and no conclusion was dropped. The existing blueprint provenance has from.node=null; `blueprint_refs.py ancestor` confirms that no ancestor can be resolved through the imported creation chain. I retained that provenance and the existing via list. I read the latest blueprint `sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), and kept the supporting alteration/moduli route named in the inherited provenance.

I used Stacks Tag 0DQL, `lemma-gerbe-diagonal-quasi-compact`, stacks-morphisms.tex lines 6437-6464. Its first map is surjective, its composite is quasi-compact, and the cartesian square descends quasi-compactness along an fppf morphism. The delivered argument performs exactly this construction after choosing a smooth atlas V of the source gerbe: R=V×_U V maps onto W=V×_Q V, R→V×_S V is a diagonal base change, and W→V×_S V is the pullback of the space diagonal. This uses the existing space fppf-locality theorem rather than introducing a general stack-descent node or a duplicate of 0DQL. The algebraic-space target permits this atlas realization of the source's diagram.

I read the item's inherited Mathlib search results and retained them. Q55 ran six further logged searches, including a second semantic phrasing. The results concern schemes (not algebraic-stack gerbes); in particular I read Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean lines 45-54 and 103-104 and checked the Scheme variables and types. The grep query for gerbe/AlgebraicStack/ArtinStack had no hits. No result is an attachment or a one-line Mathlib specialization of the item.

### Unfinished work

None in this one-level stage-1 split. Existing dependencies remain their own items.

## New nodes

None; zero new nodes and zero new Mathlib leaves. Before deciding this I searched the whole DAG by gerbe, quasi-compactness/surjectivity, Stacks 0DQL, 050X, 0DQK, 0CPS and 06QI, and opened the relevant statements. Whole-blueprint searches `gerbe`, `gerbe diagonal`, `quasi-compact diagonal` and `050X` returned zero matches. The new lemma candidates (gerbe geometry, quasi-compact surjective images, and fppf locality) already have sufficient nodes. The local-isomorphism lifting is elementary and remains a proof step.

## Not duplicates

No new node pairs to compare. In particular no new clause restates the item. Existing `lem-sfb-gerbe-smooth-universal-homeomorphism` supplies only gerbe geometry/topology, and `lem-sfb-space-quasicompact-fppf-local` supplies general space locality; neither is being duplicated.

## Review by Q55

I read the statement and full proof of Stacks 0DQL in stacks-morphisms.tex, including its diagram and the dependencies 050X (`lemma-surjection-from-quasi-compact`) and 0DQK (`lemma-descent-quasi-compact`). I also read 06QI (`lemma-gerbe-fppf`), 0CPS (`proposition-when-gerbe-over`), the relative isomorphism discussion before that proposition, and 0DN8 (`lemma-gerbe-smooth`). For the space-locality application I read spaces-descent.tex Tag 041L (`lemma-descending-property-quasi-compact`), whose fpqc-local property applies to the fppf singleton cover through the existing node's explicit formulation. I checked stacks-properties.tex 04YC (`lemma-quasi-compact-stack`) and 04XI (`lemma-characterize-surjective`) to distinguish point surjectivity from a nonexistent global section. No new nodes need a separate source audit.

Step 1: I opened `def-sfb-algebraic-moduli-stack`, which gives the atlas and representable diagonal. I opened `lem-sfb-gerbe-smooth-universal-homeomorphism` and used its explicit atlas clause: the composite V→Q is surjective flat locally finitely presented. I did not use smoothness of a gerbe section, which is false for general non-smooth stabilizers. `def-pc-fibre-product` gives the scheme B; `lem-trf-space-fibre-products-etale-covers` gives D and W; `lem-sfb-stack-diagonal-space-source-representability` gives R. Each statement explicitly covers the objects at hand, with no finite-type or field-base restriction.

Step 2: I checked `lem-sfb-representable-stack-quasicompact-tests`: its implication from stack tests to scheme tests applies to the assumed quasi-compact representable relative diagonal. The base B is a scheme, so the conclusion gives R→B as a quasi-compact space morphism. The identification is written on objects and isomorphisms using the triples in `def-sfb-stable-pointed-moduli-groupoids`; it is not an uncited transport theorem. Applying p to the isomorphism gives equality because Q has only identity arrows. I checked the algebraic-stack definition for representability of that diagonal.

Step 3: This is the one elementary step. I read the item itself for its fibrewise gerbe condition, and `def-pc-fppf-site` for joint surjectivity of its covers. The two objects come with the same Q-section, so local isomorphism applies in exactly that fibre; picking a point of a nonempty covering member and then its residue field gives the required field extension. `lem-sfb-stack-point-topology` identifies points modulo common field extension and agrees with space topology. The extra T-section is retained, so this proves surjectivity after every affine B-test, not only surjectivity of R→W before base change.

Step 4: `lem-sfb-space-quasicompact-affine-tests` really states both the affine-test equivalence and base-change preservation; it gives quasi-compact R_T and finally the quasi-compact map W→B. `lem-a1-space-etale-open-image` explicitly states the equivalence between quasi-compact point topology and a quasi-compact etale scheme atlas; this bridges the two predicates instead of silently identifying them. `lem-a1-space-point-open-calculus` explicitly states continuity for every space map. `lem-weil-pbc-continuous-image-quasi-compact` explicitly gives compactness of the image; step 3 identifies that image with all of W_T. Thus no lemma about open surjections or hidden compactness of V is being assumed.

Step 5: I checked the full statement of `lem-sfb-stack-chartwise-smooth-etale-calculus`: it gives arbitrary base change and composition for flatness/local finite presentation and separately for surjectivity, for maps representable by spaces. Here every object is a space; the representability statement is available from `lem-sfb-stack-diagonal-space-source-representability` as used in this step. The two product arrows and their respective projections are spelled out, so the claimed product map has precisely the cited properties. I corrected the four tag numbers in this source pointer against stacks-project/tags/tags: they are 06PX, 06PY, 06Q3 and 06Q4. I also retained the fibre-product existence node in this step.

Step 6: `lem-sfb-space-quasicompact-fppf-local` is about arbitrary maps of spaces and any small jointly surjective flat locally finitely presented family; it does not require the covering map to be quasi-compact. Apply it to the singleton B→D: step 5 gives its exact hypotheses. I checked its base-change statement as well for the every-scheme-test clause. The cartesian identification here is an equality calculation in sheaves, with inverse deleting/reinserting q, using the discrete-groupoid definition. `def-sfb-stack-qcqs-morphism` explicitly defines quasi-separatedness for space maps by quasi-compactness of the relative diagonal. No assertion of absolute quasi-separatedness of Q is needed when S is not quasi-separated.

The generic off-unit tools are the fibre-product existence nodes and the space/topological statements in step 4. They are declared in split_report.tool_uses with their reason; I did not set maintainer-owned tool_uses. In particular the sec-trace-formula fibre-product lemma is general algebraic-space foundations, not the trace formula or its proof.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the open nodes and sources: no new-node shape issues; every proof fact is either explicitly cited or the written gerbe-field lifting; the result is assembled rather than moved into a new node; no arbitrary intersection of affine opens is used; no Noetherian, finite-type, separation or quasi-compact atlas hypothesis appears. All six steps are below 2000 characters. Citation entries copy the actual statements verbatim; their use does not rely on a dependency's proof. I checked the small cases Q empty (then the surjective atlas source is empty), the identity gerbe (R=W), a neutral gerbe BG with non-smooth flat finitely presented stabilizer (only fppf isomorphism lifting is used), and a non-quasi-compact base or atlas (all compactness arguments test individual affine T). The point-lifting proof also covers empty R_T/W_T. No statement dispute or source error was found.
