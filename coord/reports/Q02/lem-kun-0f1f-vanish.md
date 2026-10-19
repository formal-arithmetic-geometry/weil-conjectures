# Stage-1 report: lem-kun-0f1f-vanish

## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-0f1f-vanish.json`: statement; split into seven proof steps; no Mathlib match after two semantic phrasings, Loogle, and source searches.
- `citations.json`: one entry per step/node citation, quoting the cited statement verbatim.
- No new nodes and no Mathlib leaves. `prepare.py` is sandbox-only preparation material; `searches.jsonl` is the search command's evidence.

## Attachments

None. Searches of the read-only slopmaster2 project under `WeilConjectures/` for the exact blueprint id, 0F1F, and the notions of closed-point support and separably closed cohomology found no declaration proving this item. Master remains reference material, not a finished-proof attachment.

## Wanted literature

None. The shared checkout omits untracked literature files, but the obtained literature is available read-only in `/home/ubuntu/work-bp/sheaf/literature/`. I read the master blueprint's `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-0f1f-vanish.md`, the imported chapter and unit records, and the Stacks source there. No alternate slopmaster2 blueprint file for this node was found. Node source paths retain their canonical project-relative `literature/` names.

## Corrections to the imported proof

The statement agrees with Stacks 0F1F (first assertion) and is unchanged. This is an arbitrary abelian sheaf result, with no torsion, constructibility, reducedness or separatedness assumption on X.

The original one-paragraph proof concealed the finite-clopen cohomology formula. I found and reused `lem-weil-pbc-finite-coproduct-cohomology-assembly`; the related finite-geometric-point theorem assumes an algebraically closed common base field and does not apply to possibly imperfect separably closed K with differing residue extensions. The geometry of the reduced finite support is now written out in Step 3.

The imported alternative citation `lem-kun-leray-finite` concerns higher direct images through a finite *outer* morphism, not the global-cohomology comparison needed here. I removed that unused alternative and retained `lem-kun-leray-bdd` with finite-direct-image exactness. Likewise I used the existing absolute theorem `lem-weil-pbc-cohomology-filtered-colimit` (03Q5), which is exactly the final cohomology-colimit formula, rather than hiding its deduction from the relative scheme-limit theorem `sbc-lem-higher-direct-image-limit` (09Z1). Both implement the same imported finite-support and filtered-colimit route.

I added the missing statement dependencies defining finite type over K, abelian etale sheaves, and etale cohomology. The chapter and unit records are unchanged; this lemma is not the unit's key statement.

## Not duplicates

No new nodes. I searched the whole DAG by closed-point support, finite disjoint unions, cohomology/colimit, and tags 0F1F, 0F0N, 03QU, 09Z1, and searched the whole imported blueprint with `tools/blueprint_refs.py` for `closed points`, `disjoint union`, `filtered colimits`, `cohomology commutes`, `finite coproduct`, and `support is contained in the set of closed points`. The sibling global-generation node 0f1f-gen and the derived detection node 0f1g have different conclusions; neither is the vanishing item. No additional blueprint node stating this vanishing assertion was found, so `blueprint.same_as` is empty. The ancestor command returned this item's own blueprint id.

## Unfinished work

None for this one-level split. Existing cited unsplit nodes retain their own queue work. No Lean file was written, no compiler/Lake/build tool was run, and no push was made.

## Review by Q02

I read Stacks `etale-cohomology.tex`, Tag 0F1F, label `lemma-supported-in-closed-points`, statement and full proof (lines 20333–20376 in the obtained copy). It proves both acyclicity and global generation; this item requests precisely acyclicity. I checked the approximation passage against Tag 0F0N (`lemma-support-in-subset`, lines 13091ff), including its Noetherian coefficient-ring form for Z-modules, and read the stronger existing approximation statement instead of borrowing details from its proof. There are no newly created nodes needing their own source review.

Step 1 uses the full statement of `lem-weil-pbc-finite-type-over-noetherian` to deduce Noetherianity from finite type over the Noetherian field, and `lem-weil-pbc-locally-noetherian-quasi-separated` for quasi-separatedness. I read their sources: Morphisms 01T6 (`lemma-finite-type-noetherian`, lines 2765ff) and Properties 01OY (`lemma-locally-Noetherian-quasi-separated`, lines 481ff). The former explicitly includes quasi-compactness in its definition of Noetherian. Thus Step 7 has both qcqs hypotheses, without assuming X separated.

Step 2 uses exactly the approximation node's clauses: filtered colimit of finitely generated subsheaves, finite support, reduced closed support, and pushforward description. I additionally checked `lem-kun-04ca` and Stacks 04CA (`proposition-closed-immersion-pushforward`, lines 6702ff): it states the essential image on *all* abelian sheaves, fully faithfulness, and inverse image as a left inverse. No constructibility assumption is needed. I explained nonemptiness/directedness and set size of the indexing collection, instead of silently taking a possibly large colimit.

Step 3 uses only the statements of the reduced-scheme, closed-immersion, and residue-field definitions. It proves the decomposition: finite closed singletons are clopen; an affine neighbourhood in a singleton scheme is the singleton itself; a reduced ring with a single prime has that prime equal to its zero nilradical and hence is a field; the closed-point quotient identifies this field with the residue field in X. I checked this is a short elementary geometry/ring calculation, rather than creating a node that merely hides it. The support is explicitly given the reduced structure; no reducedness of X is used.

Step 4 uses clause (b) of `lem-kun-closed-point-field`, exactly with X finite type over the original separably closed K. It gives separably closed residue fields, not their equality to K. The full statement of `lem-kun-03qu-sep-closed` gives all positive-degree cohomology vanishings for arbitrary abelian sheaves on each such field spectrum; I read Stacks 03QU (`lemma-compare-cohomology-point`, lines 9100ff). The full finite-coproduct assembly statement gives the product formula for arbitrary finite clopen scheme components and arbitrary abelian sheaves, so I do not infer this theorem from the point-vanishing statement alone. Its recorded source is the componentwise passage in 0A5B (`lemma-constant-smooth-statements`, lines 15377ff), also read. This is a generic tool already present in the DAG, not a replacement route for the unit.

Step 5 uses the affine quotient clause of `def-weil-closed-immersion` and the finite-module definition of `def-weil-finite-integral-morphism`. It explicitly proves finiteness: R/J is generated over R by 1. The facts are elementary from those definitions, so no new finite-closed-immersion node was manufactured.

Step 6 uses the exactness and derived-vanishing clauses actually in `lemma-weil-pbc-finite-direct-image-exact`; I checked Stacks 03QP (`proposition-finite-higher-direct-image-zero`, lines 8245ff), which is for arbitrary abelian etale sheaves. `lem-kun-leray-bdd` states the derived-global-sections composition comparison used here. The sheaves are degree-zero complexes, so its bounded-below hypothesis holds. The cited cohomology definition identifies the degree-q groups of that comparison. The previous alternative finite-outer-map lemma was removed because its statement did not supply this inference.

Step 7 uses the exact statement of `lem-weil-pbc-cohomology-filtered-colimit`: arbitrary filtered abelian etale sheaves on a qcqs scheme, with no torsion hypothesis. I read Stacks 03Q5 (`lemma-colimit`, lines 7427ff), including the directed-set formulation, and checked that our index set from Step 2 satisfies it. The filtered colimit of zero groups is zero by its universal property. All off-unit generic theorem uses are explained in `split_report.tool_uses`; no maintainer-owned `tool_uses` field was set.

I checked delivery-errors B–E point by point: self-contained unchanged statement; definition dependencies; real literature labels; no unrun searches recorded (LeanSearch failed with HTTP 500 and is marked unavailable; the unsuccessful `Sheaf.H` pattern retains its actual unknown-identifier response); all cited statements opened and quoted verbatim in `citations.json`; no use of a cited proof's internal construction; no new-node duplication or clause relabelling; all non-elementary steps cite theorem nodes. I separately traversed statement/proof dependency paths from each proposed citation and found no path back to this item.

Small cases checked: X empty or F=0; empty support at an approximation stage; one-point support with a nonzero arbitrary abelian stalk (q=0 is deliberately excluded); several disconnected support points; nonreduced X; a nonseparated finite-type X; and positive-characteristic imperfect separably closed K, where residue fields may be nontrivial purely inseparable extensions. In each case the proof retains exactly the hypotheses of the cited statements. No statement dispute was found.

## Dry run

`python3 /home/ubuntu/weil-launcher-nt/deliver.py Q02 lem-kun-0f1f-vanish --no-push` printed `OK (not pushed)` and `preflight passed` at temporary commit `ace7c209d9`. During the final source check I corrected the affine-closed-immersion source label to `morphisms-lemma-closed-immersion` (01QO) and read its affine quotient clause; the final dry run is repeated with the corrected sandbox and this report. Nothing is delivered by the worker.

## Second reading by Q02

I independently opened the item's JSON, all its statement and proof dependency statements, the master blueprint node and its chapter/unit records, and the Stacks source in `/home/ubuntu/work-bp/sheaf/literature/stacks-project/`. The statement matches Tag 0F1F, `lemma-supported-in-closed-points`, first assertion: separably closed field, arbitrary finite-type scheme, arbitrary abelian etale sheaf supported on closed points, and precisely positive-degree vanishing. In particular there is no torsion or separatedness assumption, and no vanishing claim in degree zero. No statement dispute was found.

- Step 1: checked the two cited statements and Stacks 01T6 (`morphisms-lemma-finite-type-noetherian`) and 01OY (`properties-lemma-locally-Noetherian-quasi-separated`); PASS: finite type over the Noetherian field gives Noetherian X, including quasi-compactness, and local Noetherianity supplies quasi-separatedness without separatedness.
- Step 2: checked the complete statements of `lem-kun-cp-approximation` and `lem-kun-04ca`, and Stacks 0F0N (`lemma-support-in-subset`, Noetherian-ring coefficient clause with Z) and 04CA (`proposition-closed-immersion-pushforward`, abelian-sheaf clause); PASS: the existing approximation statement explicitly supplies finitely generated subsheaves, finite support, reduced support scheme and pushforward description. Directedness uses the union of finite generator lists, and the fixed site universe makes the collection a set.
- Step 3: checked `def-pc-reduced-scheme`, `def-weil-closed-immersion`, `def-weil-residue-field`, and 01QO (`morphisms-lemma-closed-immersion`, clauses 2 and 4); PASS after clarification: finite closed singletons are clopen, a singleton scheme is affine, and a reduced ring with one prime has zero maximal ideal because the nilradical is the intersection of its primes. The surjective local map from the ambient local ring to this field has kernel the ambient maximal ideal, explicitly giving the residue field. These are elementary topology and ring calculations; the decomposition includes empty support.
- Step 4: checked clause (b) of `lem-kun-closed-point-field`, the full statement of `lem-kun-03qu-sep-closed`, the full finite-clopen product formula `lem-weil-pbc-finite-coproduct-cohomology-assembly`, and Stacks 03QU (`lemma-compare-cohomology-point`) with its field/Galois-group context and the componentwise passage in 0A5B (`lemma-constant-smooth-statements`); PASS: each residue field is separably closed, with no identification with K required, and the cited assembly statement applies to arbitrary finite scheme components and arbitrary abelian sheaves, including the empty product.
- Step 5: checked the affine quotient clause of `def-weil-closed-immersion` and affine finite-module clause of `def-weil-finite-integral-morphism`, against 01QO (`morphisms-lemma-closed-immersion`) and 01WH (`morphisms-definition-integral`); PASS: R/J is generated as an R-module by 1, proving finiteness in two lines from the definitions.
- Step 6: checked `lemma-weil-pbc-finite-direct-image-exact`, `lem-kun-leray-bdd`, and `def-weil-pbc-etale-cohomology`, and Stacks 03QP (`proposition-finite-higher-direct-image-zero`) with the Leray comparison used in 0F1F; PASS: Step 5 supplies finiteness and the degree-zero sheaf complexes are bounded below, so the cited derived comparison gives exactly the cohomology equality needed, without torsion hypotheses.
- Step 7: checked the full statement of `lem-weil-pbc-cohomology-filtered-colimit` and Stacks 03Q5 (`lemma-colimit`); PASS: Step 1 supplies qcqs and Step 2 supplies the directed set of abelian sheaves, so positive-degree cohomology is the filtered colimit of the zero groups from Step 6.
- New nodes: NONE; B1–B7, duplicate-node deletion and per-new-node Mathlib-leaf searches are vacuous. The finite-support geometry and finite-morphism calculation remain explicit elementary steps, rather than new nodes restating parts of the item.

Small cases checked independently: the empty scheme, the zero sheaf, empty support, a singleton support with an arbitrary nonzero abelian stalk, multiple clopen support points, nonreduced X, nonseparated X, and a nontrivial purely inseparable closed-point residue extension of an imperfect separably closed field. They satisfy each invocation above. For a field spectrum with a nonzero constant sheaf, H^0 need not vanish, which confirms the q>0 boundary. H^1 and all higher positive degrees follow from the same cited point theorem.

I compared every citation quote with the current cited node's entire statement: all are verbatim. A traversal from every statement and proof dependency found no path back to this item. No citation takes a construction from the proof of a node. Existing off-unit statements serve exactly the generic tools explained in the original report; no maintainer-owned tool-use field was changed.

Independent searches were run through `msearch.py` and appended to `searches.jsonl`: LeanFinder query `Higher derived functors of global sections vanish for an abelian sheaf concentrated on closed points over a separably closed field` returned generic sheaf cohomology and injective/projective-object vanishing results; grep query `IsAcyclic.*(Sheaf|etale)|Subsingleton.*(sheaf|cohomology)|support.*closedPoint` returned six lines, including `Sheaf.subsingleton_H_of_isZero` at Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean:161 and empty-scheme ell-adic cohomology at Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean:83. I read those source statements: they require a zero sheaf or empty scheme, and do not prove this item. The generic derived-functor hits require injectivity/projectivity not supplied by the item's hypotheses. Thus neither search yields a Mathlib leaf. The previous worker's search records were preserved.

A fresh slopmaster2 keyword search found `Etale.subsingleton_H_of_isZero_upperStar` in WeilConjectures/AlgebraicGeometry/Sites/FiniteSupport.lean:69; I read its full statement and proof. Its support complement is assumed finite, whereas this item permits an infinite set of closed points. It therefore does not finish this item or replace its filtered-colimit argument. The accompanying separably-closed-point theorem belongs to the point-cohomology dependency, not to this item. The exact-id/tag search in master found no additional declaration for the item; master remains reference material.

Changes made in this second reading:

1. Replaced the compressed affine-chart residue-field identification in Step 3 with the surjective local-ring map and explicit maximal-ideal kernel. The conclusion and citations are unchanged.
2. Appended the two independent searches with their actual results and the reasons they are not matches; no existing search was rewritten.
3. Added this independent step-by-step audit and retained the entire `## Review by Q02` section. No new node, Mathlib leaf, Lean source, or build was introduced.

### Second-reader dry run

The required final dry run, `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q02 lem-kun-0f1f-vanish --no-push`, printed `OK (not pushed) deliver/Q02/lem-kun-0f1f-vanish at 7da761d5e7: preflight passed`. The tool accepts exactly group and item plus the optional flag, so the command follows its documented syntax without a trailing dot. No validation repair was required. The delivery command will rerun preflight on the final report and repaired node.
