## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-split-torus-torsor-frame-geometry.json: statement, now split into eight proof steps; no Mathlib match.
- citations.json: verbatim supporting statements for all 24 step/node citations.
- No new nodes and no Mathlib leaves. All supporting facts already have DAG nodes.

## Attachments

None. Searches in lean/WeilConjectures for the exact blueprint tag, split-torus torsors, torus/torsor combinations and frame-bundle spellings found no declaration proving this item. The torsor hits concern finite constant or etale sheaf torsors; they do not give the scheme-theoretic split-torus/frame geometry. No sorry declaration was treated as a proof.

## WANTED

None. All sources used are present in literature/stacks-project/.

## Findings and changes

The statement is unchanged. The live item had no proof and no sandbox item existed. I retained the imported source, provenance, inherited search records and creation record. I added actual logged Mathlib searches, including a second semantic phrasing and a broader grep. The returned topological vector-bundle constructions, abstract additive torsors, ring Picard groups, faithfully-flat module lemmas and prestack full faithfulness do not establish the combined scheme statement. There is no new node whose searches might be confused with inherited searches by the creating group Q52.

The proof constructs the coordinate lines by effective descent, with inverse transition units chosen so that the right action gives scalar multiplication on frames. It constructs the representing frame scheme as an explicit open of the quotient projective bundle; it does not posit an unproved classification of split-torus torsors. It descends an explicit inverse to the frame map, proves the tower by its functor of points, and checks all three finiteness/smoothness/separation properties. This is an actual argument, not one new node for each clause of the item.

The current blueprint read was literature/blueprint/latest (main-20261024, ef6f9619fdbffa59e88528fb56483d76c70258c8), including the six-functors-basics chapter, sk-thm-sf-ctf-stability unit and its direct-image proof. The inherited DAG unit is filed under the six-functors stability unit with its historical long auxiliary ancestry; this is retained, including its null blueprint ancestor, as tools/blueprint_refs.py ancestor reports. This auxiliary geometry does not change any chapter or unit statement. Whole-blueprint searches for torsor, frame, frame bundle, coordinate character and projective bundle found no node stating the entire assertion in another form. The existing etale line-bundle/torsor correspondence does not directly handle the given fppf scheme torsor; effective fpqc module descent does.

## Not duplicates

No new nodes were created. The projective quotient theorem, fpqc module descent and fpqc scheme-morphism descent are cited under their existing ids. Small coordinate and diagonal calculations stay as steps.

## Review by NW

I read the original item's entire statement and its cited source passages: descent.tex proposition-fpqc-descent-quasi-coherent (023T), lemma-finite-locally-free-descends (05B2), and lemma-refine-coverings-fully-faithful (02W0); groupoids.tex lemma-characterize-trivial-pseudo-torsors (0499), definition-principal-homogeneous-space (049A) and the preceding pseudo-torsor definition; constructions.tex definition-projective-bundle (01OB), its ensuing quotient-functor discussion and lemma-projective-space-bundle (01OE). I also read schemes.tex lemma-separated-permanence (01KU) and morphisms.tex lemma-smooth-characterize (01V6) and lemma-composition-smooth (01VA). These explain the source's intended combined assertion; no one tag was represented as stating it all. There are no new-node sources to audit.

For step 1 I opened def-pc-fppf-site and lem-trf-fppf-covering-is-fpqc: the first indeed permits flat locally finitely presented jointly surjective families, and the second explicitly supplies fpqc coverage, including its finite-affine test. Thus the descent hypotheses hold without assuming that S is quasi-compact. The difference morphism and its cocycle follow from the given scheme isomorphism and the group action; they are not checked only on geometric points.

For step 2 I opened lem-pc-fpqc-descent and def-sc-invertible-module. The former states effectivity for quasi-coherent modules, full faithfulness and preservation/reflection of local rank, not just sheaf descent; its rank-one clause is precisely what is needed. I verified the sign: the descent map is multiplication by g_i^{-1}, whereas the canonical frames satisfy e_i(z)=g_i(y,z)e_i(y). Using g_i instead would reverse the requested action, so the sign is made explicit. The argument uses neither smoothness nor finite type of S at this point.

For step 3 I opened lem-trf-projective-bundle-quotient-geometry in full. It really gives quotient-compatible isomorphisms, naturality under arbitrary scheme pullback, restriction to base opens, the free projective model and separatedness. These statements are stronger than full faithfulness of a projective embedding and supply exactly the quotient functor used. In local rank-one bases the two summand maps are units precisely on principal opens. Normalizing the first to 1 makes the second an invertible functional on A-dual, whose evaluation vector is a frame of A. This checks that A-dual, rather than A, is the second summand in the item's quotient convention. I checked independence of a change of basis and the inverse normalization, so no representability or transition comparison is hidden in a new node. The local coordinates are T_1/T_0 and its inverse. The entire step is 1368 characters: it is one direct quotient calculation, not a long unexposed classification theorem.

For step 4 I opened lem-galois-fpqc-morphisms-descend and read its precise statement of compatible morphisms and canonical descent data. It is a full-faithfulness statement for arbitrary schemes over S, not merely the finite-etale version. The local inverse (t,y) maps to (yt,y); inverses preserve the displayed compatibility equation, and faithfulness proves the inverse identities after descent. This supplies actual inverse descent instead of using an uncited 'isomorphism is local' assertion. The same equation gives equivariance on all scheme tests. For r=0 the map is q itself and the inverse-descent argument still applies; I did not infer a section of q from mere surjectivity.

For step 5 I opened the fibre-product and tensor-pullback definitions. Maps to Y_j over Y_{j-1} are exactly one more frame. Pullback of the dual agrees with the dual of the pullback by the displayed local coefficient identity; changing a basis multiplies it by a unit on both sides. This is an elementary application of the preceding construction, not a new lemma restating the projective-open clause. The order of the projections is the order in the statement, so the composite really is the original structure map.

For step 6 I checked def-weil-finite-type-morphism and the standard homogeneous-localization charts in def-nagata-relative-projective-space. Quasi-compactness supplies a finite simultaneous trivializing affine cover once the extra finite-type hypothesis on S is assumed. No intersection of affine opens is asserted affine. Both the Laurent-coordinate charts and the two projective charts have explicitly finite lists of k-algebra generators, including inverses as new generators with u_i w_i=1. A finite affine covering by these charts proves finite type directly. This avoids claiming that an arbitrary open immersion is finite type, which would be false over unrestricted bases.

For step 7 I opened all four cited smoothness statements. The affine-space node gives every n over every scheme, not just over a field; the restriction node permits open restrictions on source and target; lem-trf-smooth-composition composes arbitrary smooth morphisms; and the source-locality node permits the covering actually used. Every chart is an open in affine space over one smooth U_a, so their hypotheses are satisfied. This proves absolute smoothness without a constant relative-dimension hypothesis on S.

For step 8 I opened both closed-immersion nodes and the separatedness clause of the quotient theorem. Restricting a separated morphism to an open gives a base change of its diagonal, and the separated-composite factorization has second arrow the base change of the base diagonal. The cited nodes explicitly state arbitrary base change and composition of closed immersions. These are the only non-elementary inputs to that diagonal calculation; I do not cite a definition for a permanence theorem.

I tested S empty, r=0, r=1, a trivial torsor over an arbitrary affine ring, and a nontrivial line over a scheme. For the nontrivial line the chart construction changes by the dual transition factor and still gives the same evaluation quotient, checking the dual convention. Empty schemes cause no finite-cover or descent failure; the zero-coordinate torus case proves an isomorphism with S, not a choice of a noncanonical point. Arbitrary characteristic, nonreduced test schemes and a non-quasi-separated S are permitted in the first five steps. Smooth separated finite type is invoked only in the last three. No statement dispute, added hypothesis or weakened conclusion was found.

I checked B--E against the node files: no new statement-only nodes to violate B1/B2, all uses have matching verbatim statement quotations (C4), no uncited non-elementary descent or smoothness fact (C1), no copied clause nodes (D1/D2), and no informal transport hiding compatibility (E5). Every step is below 2000 characters. Off-unit generic tools are declared with their purpose in split_report.tool_uses; they are scheme/module/projective geometry tools, not trace-formula or Poincare-duality input. No SGA source is used. No Lean was written and no compiler/build command was run.

## Unfinished work

No mathematical part of this one-level split remains. The cited existing nodes remain their own items as appropriate; this delivery does not claim to prove their Lean declarations.
