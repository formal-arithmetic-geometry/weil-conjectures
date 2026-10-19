# Q73 stage-1 delivery: lem-trf-quasi-affine-relative-spec-embedding

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-quasi-affine-relative-spec-embedding.json`: existing statement, now split in six steps; not a Mathlib leaf. The statement and its statement dependencies are unchanged.
- `citations.json`: one entry for every step/node citation, using the cited statement verbatim.
- `report.md`: this report. `searches.jsonl` is the real search-command log; `write_split.py` is a sandbox-only authoring script.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter record changed: the item is a supporting descendant, not the unit's key statement.

## Attachments

None. Searched the project under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, its blueprint docstring tag, and the quasi-affine/relative-spectrum concepts. Read `WeilConjectures/Mathlib/AlgebraicGeometry/QuasiAffine.lean`. Its `IsQuasiAffineHom` is the relative definition, and its Zariski-main factorization has extra local-quasi-finiteness and finite-type hypotheses. The absolute Mathlib canonical embedding does not state the relative equivalence. None is an exact project attachment for this item.

## WANTED

None. All mathematical sources needed for the split are present.

## Problems found and corrections

The imported node had a correct statement and no proof. I preserved the equivalence, including quasi-compactness of the open immersion, arbitrary schemes as bases, and the meaning of quasi-affineness. No Noetherian, finite-type, finite-presentation, or separated-base hypothesis was added.

Stacks `morphisms.tex`, Tag 01SM, `lemma-characterize-quasi-affine`, proves (1) -> (2) -> (4) -> (3) and (3) -> (1). I expanded that route. In particular, I did not infer quasi-compactness of an open immersion merely from its being open, and I did not infer global quasi-compactness of X from relative quasi-affineness over a possibly non-quasi-compact S.

At first the absence of a standalone canonical-relative-affinization node looked like it required a new lemma. Reading `lem-weil-pbc-affine-algebra-local-maps` showed that its source is arbitrary: only its target is affine over S. Applying its statement to the inverse relative-Spec algebra isomorphism and then gluing gives the canonical map, including its section formula, in a short argument. Consequently no new canonical-map node was created. The general relative-Spec anti-equivalence on affine S-schemes alone would not justify applying its inverse to the arbitrary source X; the proof uses the stronger local-maps statement explicitly instead.

The word `O_X` in the quasi-coherent-algebra sentence of the Tag 01SM proof is a typographical slip: the base is S and the algebra is an O_S-algebra. The item's O_S formulation is correct and unchanged.

## Searches and duplicate audit

Read `coord/delivery-errors.md` B-E completely and the chapter and unit records. The inherited blueprint ancestry places this tool below `lem-trf-local-term-locality`, through the quasi-affine descent/base-change branch. The item has no changed `blueprint_update`. `blueprint_refs.py ancestor` confirmed that ancestor. Whole-blueprint searches included `quasi-affine`, `relative spectrum`, `canonical morphism`, `canonical morphism relative spectrum`, `01LY`, and `affinization`. The quasi-affine blueprint hits define the notion or give finite-type/Zariski-main consequences, not this equivalence. DAG tag/concept searches found the existing absolute canonical embedding, relative-Spec interface, affine algebra local maps, gluing, qcqs permanence, and qcqs pushforward statements, which are reused.

The original item's Mathlib searches remain intact. Additional item searches were run with msearch.py using leanfinder, loogle, grep and leansearch, with two semantic phrasings. All these item searches ran successfully; the results and exact queries are recorded. Read Mathlib `AlgebraicGeometry/QuasiAffine.lean`, including its class, compactness, separatedness, canonical open immersion and affine-morphism permanence. Those are absolute statements; neither the relative equivalence nor a one-line generalization was returned. Extra searches about the provisional canonical-map helper remain truthfully in searches.jsonl; no such helper node was created. Read the returned Gamma-Spec canonical map, its affine pullback theorem and affine scheme-theoretic-image factorization: these do not give the arbitrary-base characterization.

## Not duplicates

No new nodes. The existing `lem-trf-quasi-affine-canonical-affine-embedding` supplies the absolute embedding and qcqs properties. The existing `lem-weil-pbc-affine-algebra-local-maps` plus `lem-weil-pbc-scheme-morphism-gluing` supplies the local-to-global canonical map; these facts are cited rather than duplicated.

## Review by Q73

I read the item against Stacks `morphisms.tex` Tag 01SM (`lemma-characterize-quasi-affine`, including the whole proof), `constructions.tex` Tags 01LT (`lemma-spec-affine`), 01LX (`lemma-spec-properties`) and 01LY (`lemma-canonical-morphism`), `properties.tex` Tag 01P9 (`lemma-quasi-affine`, including its proof), and the diagonal argument of `schemes.tex` Tag 01KO (`lemma-characterize-quasi-separated`). There are no new-node sources to review. I opened and read the statement of every node used by every proof step; citations.json reproduces those statements verbatim.

Step 1 uses the absolute canonical-embedding node precisely for quasi-compactness and quasi-separatedness of each quasi-affine X_U, not for a relative embedding. The finite-type definition node defines the quasi-compact morphism condition actually used. The qcqs-permanence statement explicitly says that a morphism with quasi-separated source is quasi-separated; it therefore applies to X_U -> U without a hypothesis on S. I apply the quasi-compact-local-on-target node to the diagonal, not directly to an unstated quasi-separated-locality theorem. The open cover of the diagonal target and its inverse-image/restriction identifications are written explicitly, and the quasi-separated definition identifies each restricted diagonal and the resulting global conclusion. This avoids using an absolute affine-intersection criterion as though it stated relative quasi-separatedness.

Step 2 uses the quasi-coherent definition for the structure sheaf on affine charts, then the pushforward theorem with both qc and qs supplied by step 1. The relative-Spec node's clause (2) gives both the affine morphism and an algebra isomorphism whose section maps are exactly the affine charts. It states the chart formula needed in step 3, not merely existence of some affine scheme.

Step 3 takes from the local-maps node its maps, compatibility on arbitrary overlaps, structural-morphism equation, and section formula. I checked the direction: its alpha is a^{-1}: pi_*O_Y -> f_*O_X. The gluing node's statement gives existence and equality on the source cover, including equality pi c = f. The local factorization through the open Y_U is obtained by restricting the actual continuous map and its sheaf map, not by asserting a factorization through an arbitrary subscheme based on pointwise image. Under the affine chart h_U, the induced ring map is a_U^{-1}a_U = id, so the morphism-into-affine-scheme node's bijection identifies it with the absolute canonical map. No affineness of X or of U intersect V is assumed, and no theorem about the proof of a cited node is used.

Step 4 uses the absolute canonical-embedding node for open immersion of the identity-on-sections map just identified. Composition with an open inclusion is justified directly by the open-immersion definition: open embeddings and sheaf isomorphisms compose. Global injectivity is checked within one common affine base chart for any two points with the same image. Thus the local-source open-immersion node's injectivity hypothesis and every pointwise neighbourhood hypothesis hold. This step does not use the false assertion that every map locally an open immersion on its source is globally an open immersion.

Step 5 treats quasi-compactness of c separately. Each Y_U is affine by relative Spec and hence quasi-separated by the affine-qcqs node, while X_U is quasi-compact by step 1. These are exactly the source and target hypotheses of qcqs permanence (1). The quasi-compact-local-on-target node then applies to the cover (Y_U)_U. This proves relative quasi-compactness without assuming S or Y quasi-compact.

Step 6 is elementary from the cited relative-Spec affine chart and the definitions of open immersion, quasi-compact morphism, and quasi-affine morphism: Y_U is an affine open in Y, so quasi-compactness of i directly gives quasi-compactness of i^{-1}(Y_U). The restricted map identifies it with an open subscheme of that affine scheme. No uncited base-change theorem is hidden here. The definition of quasi-affine morphism is used with exactly the explicit absolute meaning in the item.

All off-unit statements are generic geometry tools, and the three substantial relative-Spec/pushforward tools are declared in split_report.tool_uses; no trace-formula unit step is replaced. The remaining cited results are definitions or existing Mathlib leaves. Every proof dependency is the union of the step citations. Each non-elementary step is under 2000 characters; none hides an independent comparison lemma: the only chart comparison is the displayed identity of ring maps and the cited Gamma-Spec bijection.

I checked the empty source and empty base, an affine identity morphism, a quasi-compact proper open of an affine scheme (for example the punctured affine plane), and a non-quasi-compact base covered by affines. The argument handles all of them. An arbitrary non-quasi-compact open is deliberately excluded by the quasi-compact-open condition; dropping that condition would invalidate the conclusion, so it remains explicit. No statement dispute or missing hypothesis was found, no SGA source is used, and no Lean file or compiler/build tool was used.

## Unfinished work

None in the requested one-level split. Existing cited nodes retain their own statuses and proof obligations. Delivery is subject to the server dry run and subsequent independent maintainer review.
