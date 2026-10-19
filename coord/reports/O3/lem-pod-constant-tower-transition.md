# lem-pod-constant-tower-transition — N3 stage-1 delivery

## Files written

- dag/nodes/sec-poincare-duality/lem-pod-constant-tower-transition.json: existing statement split into five proof steps; its statement and stmt_deps are unchanged. No new nodes and no new Mathlib leaves.
- citations.json: fourteen step/node entries with verbatim statement witnesses (the full statement is retained so no hypotheses are lost).
- report.md: this report. searches.jsonl is the search command's original log; finish_split.py is a sandbox-only preparation script, not a project tool.

## Attachments

None. Searches of WeilConjectures in the read-only slopmaster2 checkout for the blueprint id, constant/tower transition terminology, restrictionOfScalars, and degree-zero derived augmentation did not find a project declaration stating this entire changing-coefficient equality. The unrelated constant tower in DerivedCategory/Complete/Principal.lean concerns completion; it is not an attachment. The upstream master is reference material only.

## Wanted sources

None. All sources used are available in the shared literature.

## Corrections and observations

The imported statement is correct, and remains exactly as imported. Its old empty proof did not establish the comparison's action on degree-zero sections. The first local draft appealed to naturality without writing the square, and chose an unspecified replacement of a complex where a nonnegative resolution was needed. I replaced that draft with three ordinary nonnegative resolutions and explicit equations. I also replaced initially paraphrased citation witnesses by exact statement text; the delivered citations are all verbatim. The obsolete root-level JSON was only an intermediate checkpoint, not the delivery node; the authoritative sandbox node is under dag/nodes/.

No statement dispute, source error, new definition, change of unit metadata, or replacement of a unit route is involved. The blueprint's current main-20261015 prop-cohomological-finiteness proof Step 7 is the ancestor's connected-constant-cohomology paragraph. The current split of lem-pod-connected-constant-h0 Step 6 asks for precisely this coefficient-transition comparison. I read the chapter record, sk-lem-finite unit record and current blueprint text: this auxiliary functor calculation supplies that step without replacing the unit's finiteness route. The item is not the unit's key statement, so no realized fields are changed.

## Searches and duplicate checks

No new node was created. I read and retained the five inherited Mathlib searches, inspected Mathlib/CategoryTheory/Abelian/RightDerived.lean:260-293, and used the required msearch command for LeanFinder, Loogle, grep and LeanSearch (actual results are in searches.jsonl). The second semantic phrasing and quoted toRightDerivedZero query again find fixed-functor augmentations, their naturality and generic derived comparisons. They do not give the specified pro-etale changing-coefficient comparison with its specified normalization in one line. The generic augmentation is already the existing Mathlib leaf lem-weil-pbc-left-exact-injective-resolution-degree-zero; I reuse it. The search with unqualified rightDerivedZeroIsoSelf reported an unknown identifier; the quoted query and LeanFinder results provide the meaningful search evidence, rather than treating the unknown identifier as an absence proof.

Whole-DAG and blueprint searches found no other node stating the item. In particular lem-sf-normalized-derived-comparison-common-resolution is a general resolution-level comparison, not this H^0 assertion: I cite it as a tool. I also read and reuse lem-sf-kinjective-derived-map-computation and lem-weil-pbc-kinjective-hom-derived. The blueprint_refs search for the full comparison terminology returned no equivalent blueprint node, and ancestor reports prop-cohomological-finiteness. The item's existing blueprint.from place and same_as are retained, and split_report identifies the current proof passage.

## Review by N3

I read Stacks derived.tex at lemma-left-exact-higher-derived (05TD, line 5565), including the proof that left exactness identifies the degree-zero kernel with the underived functor. I read lemma-injective-resolutions-exist (013K, line 6280), lemma-K-injective (070I, line 9632), lemma-bounded-below-injectives-K-injective (070J, line 9688), and lemma-K-injective-defined (070Y, line 9747). I read injectives.tex theorem-injective-embedding-grothendieck (079H), and the existing ringed-site resolution theorem's statement for the Grothendieck and unbounded resolution hypotheses (079P). For the direct-image identification I read sites-modules.tex definition-pushforward (03D6, line 1146). The proof_origin is agent: the final changing-coefficient calculation is written here, rather than misrepresented as a verbatim Stacks theorem. No SGA source is used.

Step 1 cites the pro-etale site's fixed small skeleton, the Grothendieck/K-injective existence statement, the enough-injectives Mathlib leaf, the nonnegative ordinary-resolution statement, the bounded-below K-injectivity leaf, and the finite-coefficient comparison statement's exact restriction clause. I opened each statement: the smallness and commutative ring-sheaf hypotheses hold for A_X and B_X; this is the pro-etale category, not an incorrectly substituted etale module category. Enough injectives supplies the hypotheses for all three ordinary resolutions, including the resolution of rG. The chosen complexes L,J,I all have zero terms below zero. Exact restriction sends the quasi-isomorphism a to a quasi-isomorphism.

Step 2 cites precisely the bijection from homotopy classes into a K-injective target to derived morphisms. Its statement permits source rJ even when rJ is not K-injective. It gives v and h and the homotopies of their composites with augmentations. I checked the homotopy formula: with source concentrated in degree zero and target I^{-1}=0, the degree-zero difference is zero. Thus the two augmentation equations are strict. Two-out-of-three for v is checked by taking cohomology and cancelling H(r(a)); no nonnegative injective replacement of rJ is silently assumed.

Step 3 cites additive left exactness of direct image, the augmentation-as-cycles isomorphism, the sectionwise direct-image definition, and exact coefficient restriction. Their statements give exactly these facts. The augmentation for rG uses b; the augmentation for G uses a. Restriction does not change underlying sections, and the constant-ring maps agree after the coefficient map, so f_*^A r=s_Y f_*^B on objects and morphisms. Exactness preserves kernels and images and therefore cohomology, giving alpha'_G=s_Y alpha_G on the underlying A-module sheaf.

Step 4 uses the statement of lem-sf-kinjective-derived-map-computation for the map represented by h, and the statement (not the proof) of lem-sf-normalized-derived-comparison-common-resolution for the successive resolutions a and v. I checked all its hypotheses: arbitrary-complex K-injective existence is Step 1; r and s_Y are exact; the two functors are additive; their underived composites agree by Step 3; the supplied c is a natural isomorphism with exactly the inverse-on-resolutions normalization in lem-weil-proetale-direct-image-restriction-of-scalars. Its w=v r(a) equals b by Step 2. Therefore it gives c as Q(f_*v)^{-1} on precisely the same resolutions, not merely some isomorphism with these endpoints. These are generic tools; their declared uses in split_report do not change the unit's route.

Step 5 is elementary from the previous steps. I wrote both equalities V alpha'_G=alpha_r and H alpha_F=alpha_r f_*u and proved them by composing with the monic inclusion of cycles, reducing to the strict augmentation equations of Step 2. Nonnegative complexes have no boundaries in degree zero. The inverse from Step 4 permits cancellation and gives exactly the displayed morphism of the item. There is no unquoted naturality theorem hidden in this step.

I tested f=id, phi=id, u=0, F=0, G=0, and X empty. All equations reduce respectively to the familiar underlying module map, the ordinary fixed-coefficient augmentation, zero maps or the unique map of zero sheaves. Nonflat A to B is allowed: the argument uses exact restriction, never scalar extension preserving injectives or rJ being K-injective. The map on every test case is the actual section map, including zero, rather than an arbitrary automorphism. Every non-elementary assertion is covered by the stated node citations; all five steps have fewer than 2000 characters. B1/B2/B3/B4/B5/B7/B9/B10, C1--C8, D1--D5 and E1--E7 were checked against these statements and sources; B6/B8 and new-node duplicate pairs are inapplicable because no new node or leaf is introduced. The proof-dependency list is exactly the union of step uses, and statement dependencies are unchanged.

## Unfinished work

No mathematical part is left unsplit. The required server dry run and direct delivery are the final validation gates; the maintainer independently reviews the delivery.
