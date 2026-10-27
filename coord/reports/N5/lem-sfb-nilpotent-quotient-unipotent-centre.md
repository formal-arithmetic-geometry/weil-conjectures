# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-nilpotent-quotient-unipotent-centre.json: split item, unchanged statement, five proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-normal-multiplicative-layers-central.json: statement-only lemma, unsplit; Mathlib searches found no match.
- citations.json: verbatim statement excerpts for every use in each numbered proof step.
- searches.jsonl: actual search records produced by msearch.py; preserved without alteration.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag, nilpotent, unipotent and multiplicative type. The only unipotent hits were unrelated matrix constructions in StrictWeilComplexNotFaithful and DerivedOpenDifferenceDiagram. No project declaration states this group-scheme result. The abstract group and Lie algebra hits returned by the Mathlib searches do not give the affine group-scheme theorem.

## WANTED

None. The needed Milne source and its erratum are present locally. No SGA source is used.

## Corrections and source reading

The item statement is unchanged and agrees with Milne Lemma 16.45, printed p.340. Its extra conclusions follow from Proposition 5.59(b), p.114, and the central-series definition and commutator criterion, Definition 6.34 and Remark 6.35, p.133. I read Theorem 16.13(a), p.328, for the commutative multiplicative part, Lemma 16.43 and its proof, p.340, Corollaries 12.37--12.41, p.244, and Corollary 12.22, p.239. The Chapter 12 erratum requires the kernel in Corollary 12.41 to be CENTRAL. This is satisfied for Lemma 16.43: a normal multiplicative-type subgroup of the connected ambient group is central by Corollary 12.38. No smoothness is required in those source statements. The available action-rigidity node is restricted to a smooth acting group over an algebraically closed field, so I did not apply it to the present arbitrary-field nonsmooth item.

The current blueprint is literature/blueprint/latest (COMMITS.txt: main-20261024 ef6f9619fdbffa59e88528fb56483d76c70258c8). I read the unit and its latest direct-images proof, especially (3), alongside the chapter/unit DAG records. This is a supporting algebraic-group input in the inherited chain beneath that place, rather than a replacement of a unit step. The ancestor command returns null for this long inherited chain; I retained the item's supplied null ancestor and via list and extended it in the new node. The blueprint searches for nilpotent, multiplicative, unipotent centre, multiplicative extension, normal multiplicative, and multiplicative layers found no blueprint statement of the item or new lemma.

## Not duplicates

lem-sfb-normal-multiplicative-layers-central vs lem-sfb-central-extension-of-tori: the old node assumes the middle group smooth and connected and the two end groups tori, and concludes it is a torus; it does not assert that an arbitrary nonsmooth normal subgroup of a separate connected ambient group is central.
lem-sfb-normal-multiplicative-layers-central vs lem-sfb-multiplicative-extension-action-rigidity: that node concerns actions by a SMOOTH connected group over an ALGEBRAICALLY CLOSED field and assumes a central kernel; the new lemma concerns normal layers in an arbitrary connected affine group over any field, with no smoothness.
lem-sfb-normal-multiplicative-layers-central vs lem-sfb-commutative-multiplicative-type-extension: that node assumes the middle group commutative over an algebraically closed field; it does not produce commutativity or centrality in an ambient group.
lem-sfb-normal-multiplicative-layers-central vs lem-sfb-multiplicative-isogeny-composition: that node concerns finite kernels of isogenies between smooth connected groups over an algebraically closed field. Here neither normal layer need be finite, smooth or connected, and the ambient field is arbitrary.
lem-sfb-normal-multiplicative-layers-central vs lem-sfb-nilpotent-quotient-unipotent-centre: the new lemma is the general normal-filtration rigidity input 16.43; it contains no nilpotence hypothesis, maximal central multiplicative subgroup, or conclusion about a quotient centre. The item's argument still constructs the inverse image and proves its collapse by maximality.

The DAG-wide searches included Lemma 16.43, Corollary 12.22, normal multiplicative subgroups, central multiplicative extensions and central series; I opened the statements of the above candidates. The existing centre, quotient geometry, homomorphism-image and commutative multiplicative-part nodes are reused. In particular lem-sc-image-subgroup assumes a PROPER source and cannot supply the present affine images; lem-sfb-affine-homomorphism-flat-image has the needed arbitrary affine hypotheses. No new elementary node or clause-restatement was introduced.

## What could not be finished

Nothing required by the stage-1 split remains. The one supporting lemma is deliberately statement-only, as required for a new unsplit node. No Lean file was written and no compiler or build tool was run.

## Review by N5

I checked the source and statements with the node files open. The item is exactly Milne 16.45 with the two stated quotient consequences; the new lemma is 16.43, with its quotient explicitly represented and centrality on all algebra extensions spelled out. The source's use of corrected 12.41 is legitimate because 12.38 first makes the normal multiplicative kernel central. The statement-only node has no proof or hidden sketch in its statement, introduces k,G,N,E,Q and the quotient, and defines multiplicative type, normality through the subgroup node, and the scheme-theoretic centre. Its definitions are named in stmt_deps. Searches were run by msearch.py with LeanFinder, LeanSearch, Loogle and grep and a second semantic phrasing; I read the returned types: ordinary groups, Lie algebras and additive/multiplicative tags are not group-scheme rigidity. The log-derived records describe these actual hits, with no claimed Mathlib leaf.

Step 1 uses affine-normal-quotient geometry for faithful flatness and surjectivity, and the connected-space definition for the clopen pullback argument. The geometry statement actually supplies the kernel and faithfully flat quotient, so no assumption about a connected kernel is used. The argument with disjoint clopen sets is elementary, and the identity guarantees nonemptiness.

Step 2 uses affine-homomorphism-flat-image to supply CLOSED subgroup images with faithfully flat maps, not merely images of geometric points. Normal-quotient geometry supplies q. Faithfully-flat-base-change supplies each algebra extension lifting h and y; these are successive covers, so I descend through them successively and do not need an uncited theorem about their composition. Faithfully-flat-universally-injective with module A detects vanishing of each value of the defining subgroup ideal. The closed-immersion node explicitly identifies affine closed subschemes with quotient rings, and the subgroup definition identifies normality on all algebras. Thus conjugation, nesting and the commutator inclusion descend to each algebra; the endpoints are H and 1. This is the source central-series argument expanded rather than an extra nilpotent-quotient node. The step is 1079 characters, below the long-step threshold, and contains no independent hidden lemma: the ideal vanishing test is the direct consequence of the cited injectivity and quotient-ring descriptions.

Step 3 uses centre-base-change for the closed COMMUTATIVE centre (no smoothness of the centre), commutative-multiplicative-part for S and the unipotence of C/S over the given arbitrary k, and normal-quotient geometry for P=q^{-1}(S), its normality and P/D=S. The latter statement explicitly contains the inverse-image exact-sequence clause; this is the quote in citations.json. S is normal in H because it is central: every algebra-valued element commutes, so conjugation preserves it, as follows directly from the centre definition.

Step 4 uses the NEW lemma with ambient group G, N=D and E=P. G is connected by hypothesis, both subgroups are normal (D is central, P by step 3), and the two layers are multiplicative by the hypothesis and step 3. Its statement gives exactly centrality AND multiplicative type for P. Maximality is applied inside Z(G), the place where the item assumes it; P=D and S=1 then follow, rather than being inserted as an assumption. Step 5 uses the commutative-part conclusion C/S unipotent and identifies the quotient by 1 with the same represented sheaf, so the required unitriangular immersion is preserved. This last identification is elementary.

I tested the item on 1, G_m, G_a, mu_p, alpha_p, and mu_p times alpha_p in characteristic p: the quotient centre is respectively 1, 1, G_a, 1, alpha_p and alpha_p. These cases check that smoothness of D or the centre and connectedness of the centre are not inadvertently assumed. Imperfect fields are allowed: no decomposition into a unipotent subgroup times a torus was used. For the new lemma I checked G=mu_{p^2}, N=mu_p, E=G (a nonsmooth central multiplicative extension); G=G_m, N=mu_n, E=G (a disconnected kernel when n is prime to p); N=1 and E=1; and failure of the ambient-connected hypothesis for G=G_m semidirect the constant order-two group acting by inversion. These validate the edge cases and show why the connected ambient group, rather than smoothness of any layer, is the essential hypothesis. None of the proof steps exceeds 2000 characters. The two off-unit algebra lemmas are declared as generic tool uses; they do not use trace-formula, duality, or SGA arguments. The final stage-1 server dry run and push are recorded by the delivery tool.
