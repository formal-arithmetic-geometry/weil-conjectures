# Worker report — Q56 (returned-delivery repair, 2026-10-19)

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-cartier-gysin-kummer-boundary.json`: repaired six-step split; restored the minus sign and retained the explicit normalization Cl_i(1)[2]=eta_{i,n}. Step 5 now uses the definition-level Yoneda pin for O(D), with h=f^{-1}; step 6 takes its closed adjoint.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-finite-coefficient-yoneda-blowup-class.json`: retained statement-only, unsplit, no Mathlib match. This is the already reviewed ILO modified-blowup construction; the earlier false clause identifying it with an independently named absolute-purity map remains removed.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-supported-yoneda-localization.json`: retained unchanged, statement-only, unsplit, no Mathlib match. Its positive signed Yoneda comparison is correct.
- `citations.json`: 19 verbatim statement quotes, exactly one for each step/node pair. In particular step 5 now quotes the actual predicate `def-asd-ordinary-supported-kummer-boundary`, as well as the theorem supplying c_D.

All earlier proof material, sources and searches are retained in the sandbox. `returned-report.md`, `returned-item-statement.txt`, and `previous-positive-sign-report.md` record the previous versions. `searches.jsonl` is unchanged. The retained Mathlib searches were read, not invented or repeated as fresh calls. No live project, source checkout or launcher file was written.

## Attachments

None. The exact blueprint-tag and Cartier/Gysin/Kummer searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no finished declaration stating the item. I repeated the exact tag and Gysin/Kummer concept searches and found no match. The source declarations for SupportedKummerBoundary and ordinary_supported_kummer were read as normalization evidence in the shared Lean reference; no compiler was run and upstream sorry declarations are not treated as finished proofs.

## WANTED

None. The ILO PDF and Stacks sources used below are present.

## What was wrong and what changed

The returned six-step delivery wrongly changed the item to +partial(kappa(f)). That version followed the preceding return's mistaken reading of the proof of `lem-asd-ordinary-supported-kummer`. This repair follows the new return's correction: the theorem's meaning is pinned by its statement dependency `def-asd-ordinary-supported-kummer-boundary`, which explicitly requires the Yoneda product of the frame extension for O(D) with its section sent to zero and the Kummer extension. It is not pinned by the termwise relative coefficient construction in the theorem's proof.

For I with frame f, section 1_U=f^{-1}f gives the pushout e_f and c1^Yon(I,1_U)=+partial(kappa(f)). For L=I^vee with dual frame e=f^{-1}, section s_D=fe gives F(e)=a(f^{-1}) when F(s_D)=0, hence the pushout e_{f^{-1}}. Its Yoneda product is partial(kappa(f^{-1}))=-partial(kappa(f)). Thus C^ILO=-c1^Yon(I,1_U)=c1^Yon(O(D),s_D)=c_D. The original negative assertion is restored. The explicit normalization Cl_i(1)[2]=eta_{i,n} is retained and read through the codimension-one clause of `lem-per-regular-immersion-class-calculus`.

The positive-sign version is false for X=Spec(F_2[t]), D=V(t), m=3. The supported group H^2_D(X,mu_3) is Z/3 and the valuation-one Kummer boundary is a generator, so its positive and negative differ. This is a counterexample to the returned positive assertion, not a defect in the original negative assertion. No original source hypothesis was removed or target statement altered.

For HUMAN.md / maintainer action: `lem-asd-ordinary-supported-kummer` proof steps 3–4 contradict its statement and Lean normalization by a sign. The statement dependency `def-asd-ordinary-supported-kummer-boundary` and Lean `SupportedKummerBoundary` require the Yoneda splice, while the proof uses the opposite relative coefficient construction. Fix the proof, for example by using -delta_{T,V}(alpha_D), and leave the statement unchanged. This delivery does not edit that other node. The previous report's proposed change to `lem-per-trait-gysin-residue` is withdrawn: its step 6 correctly needs -partial(kappa(pi)), exactly what this repaired item gives.

Every requested repair point is addressed:

1. E2 / statement correction: restored -partial(kappa(f)); retained the explicit eta normalization. No new convention is inferred from the existence of a canonical purity isomorphism.
2. C3: replaced step 5's proof-level relative-boundary inference with the definition-level Yoneda product. The dual frame gives e_{f^{-1}} explicitly, and the signed Yoneda node is applied at h=f^{-1}. Step 6 gives the required negative value by the statement-level adjunction pin.
3. HUMAN.md action: the ASD proof sign discrepancy and the exact proposed repair are reported above, without changing its statement or another worker's file.
4. Batch-5: the accepted paths remain generic tools. The scalar/stalk tensor path below ASD uses Stacks 008B; the signed-Yoneda/localization path uses generic triangulated infrastructure (014S), not the trace-formula or Poincare-duality proofs. The retained blowup node agrees with ILO 2.2.1.1–2.3.1 after removal of its old false cross-interface clause; the signed-Yoneda node is unchanged.

## Unfinished work

The item's stage-1 split is complete; its two new supporting statements remain unsplit, as required for a one-level split. The separately reported ASD proof correction belongs to the maintainer. No Lean, Lake, build or compiler work was performed.

## Review by Q56

I read the complete new return, compared the sandbox and current shared item, and continued the retained work. The shared item is still unsplit and has the negative conclusion; the explicit eta normalization is the retained clarification. The two Q56 auxiliaries are absent from current shared DAG. I read the chapter and unit records and the nearest ancestor's provenance: the item serves the finite-torsion regular local model in the duality sentence of `lem-per-artin-gabber-affine-curve`, through the trait residue node. The chapter and unit route are unchanged.

For the item and geometric auxiliary I read ILO Expose XVI printed pp.225–234 (PDF pages 231–240), including Definition 1.1 and its sign footnote, section 2.1/Definition 2.1.1, Definition 2.2.1.1, Remark 2.2.1.2, Corollary 2.2.1.4, Proposition 2.2.2.1, Corollary 2.2.2.3, Definitions 2.2.2.5/7, and Definition 2.3.1. The source distinguishes the ideal I from its dual O(D). The modified-blowup fibre product has degree q component I^q times over I^q/I^{q+1} the symmetric power of E; in the regular conormal case this is the ordinary blowup. The whole alternating Chern polynomial has a leading minus, so in rank one it is -1. The auxiliary keeps arbitrary invertible N, rank r>=1 and finite-type ideal; regularity is needed only for the final ordinary-blowup specialization. The false separate absolute-purity identification is absent. No SGA source is used; bibliographical mentions within ILO do not supply proof inputs.

For the signed-Yoneda auxiliary I read Stacks derived.tex definition-yoneda-extension (06XP), lemma-yoneda-extension (06XU) with its roof construction, the extension-composition paragraph, and sites-cohomology.tex lemma-torsors-h1 (03AJ). It explicitly refines these with the signed support identification; it does not pretend that 06XU alone states the comparison. I checked the order k[1] composed with e_h, arbitrary abelian etale coefficients, and kernel normalization z maps to (z p,0). As checked in the retained proof notes and independently in the return, a lifted ordinary connecting cocycle b with lift t gives (dt,0); subtracting D(t,0) leaves (0,-b), exactly the positive localization boundary. This is why its sign stays positive while h changes from f to f^{-1} for O(D).

I opened the statement of every node the six proof steps cite. I also read the full statement of `def-asd-ordinary-supported-kummer-boundary`, the `SupportedKummerBoundary` definition in `lean/Sheaf/AlgebraicGeometry/OrdinarySupportedKummerBoundary.lean`, and the existence and uniqueness clauses of `ordinary_supported_kummer` in `OrdinarySupportedCartierKummer.lean`. These require the extension with frame fibre and section sent to zero, and its Yoneda product, after the specified integral-generator/scalar realization. For A=Z/m the roots scalar map is the identity. I did not take an identification from that theorem's proof.

1. Step 1 uses the Cartier and regular-sequence definitions. Multiplication by the nonzerodivisor f gives the global ideal frame; cancellation gives I/I^2=O_D. The final quotient condition for a regular sequence is checked at points of D, after empty D is disposed of. These give the codimension-one regular-immersion hypothesis used in steps 2 and 6.
2. Step 2 uses the actual modified-blowup polynomial and regular-case identifications of the geometric auxiliary and the statement that an invertible-ideal blowup is an isomorphism. Here m>=2 is invertible, I is finite type, and E=I/I^2 has rank one. Substitution of -1 gives C^ILO=-c1^Yon(I,1_U); no external Gysin identification is assumed.
3. Step 3 uses the frame-torsor statement and the exact integer open-closed sequence with its adjunction maps. The equation 1_U=f^{-1}e forces F(e)=a(f), proving the pushout relation. The local quotient lift followed by kernel comparison proves the middle-sheaf isomorphism. This is an elementary calculation, not a hidden new lemma.
4. Step 4 uses the signed-Yoneda statement at h=f, exact Kummer sequence for invertible m, and canonical torsor/H^1 identification. Local lifts are m-th roots and their ratios are mu_m. It gives +partial(kappa(f)) for I; it asserts nothing different about O(D).
5. Step 5 uses the actual definition-level pin, the theorem supplying c_D, the divisor dual, frame torsor, open-closed sequence, exact Kummer sequence and signed-Yoneda statement. The displayed equations s_D=fe and F(s_D)=0 force F(e)=a(f^{-1}), giving e_{f^{-1}} by the same explicit elementary pushout calculation. Inversion of roots identifies the torsor for f^{-1} with the inverse torsor; the cited H^1 group law makes its class -kappa(f). The result is the required -partial(kappa(f)). G_m appears as an abelian sheaf and is not treated as a Z/m-module.
6. Step 6 uses the codimension-one clause saying eta is the closed transpose of c_D and the supported-Hom identification. X and D are Noetherian, ell is invertible, and the regularity/codimension hypotheses were checked in step 1. Transposing the computed c_D yields exactly the stipulated Cl=eta and negative boundary. Combining the computed equalities also checks agreement with C^ILO. There is no reliance on an auxiliary proof or on a bare purity-existence statement to choose the sign.

Small cases: empty D, unit f and the empty scheme give zero supported class; m=2 makes both signs equal and therefore cannot detect the old fault, while m=3 on Spec(F_2[t]) does. No division by two is used, so all prime powers are included. Replacing f by u f adds the boundary of the Kummer class of a globally extending unit u, which is zero by localization exactness. For the generic Yoneda node, h=0, an extending h or a split coefficient sequence gives zero. In the geometric node rank one gives -1, rank two gives -xi+c1(E), and empty support gives zero; rank zero is expressly excluded.

Against delivery-errors B–E: new nodes are self-contained and statement-only, sources give actual labels, TeX is single escaped, and searches are actual retained command records. Each auxiliary has a smaller general role rather than repeating a clause of this item. The arithmetic and prime-power hypotheses are retained. The cited statements now supply every non-elementary input, with exact citation quotes checked against the files. Step 5 explicitly cites the definition that fixes its meaning, eliminating C3/C4. All six steps are below 2000 characters, so no long-step comparison is hidden. I read the retained whole-DAG/blueprint duplicate-search conclusions and the logged Mathlib results: the Ext composition hits are generic composition infrastructure without this signed support comparison, and the geometric hits are etale presentations/immersions or cotangent facts. There is no exact match or one-line specialization. No fresh search is claimed for an unchanged auxiliary.

## Not duplicates

lem-per-finite-coefficient-yoneda-blowup-class vs lem-per-absolute-gysin-purity: the latter states the isomorphism and functoriality for regular affine morphisms, not the finite-ideal modified-blowup/Chern-polynomial construction that is needed to evaluate the sign.

lem-per-finite-coefficient-yoneda-blowup-class vs lem-per-prime-power-closed-immersion-gysin: the latter states regular base change and pinnings, not the construction or its polynomial.

lem-per-finite-coefficient-yoneda-blowup-class vs lem-per-immersion-class-calculus: the latter is F_ell-only and describes Cartier products/flat base change, not the arbitrary-rank generalized modified-blowup construction.

lem-per-supported-yoneda-localization vs lem-pur-divisor-class: the latter is a finite-field/pro-etale O(D) divisor statement; the new lemma treats any short exact sequence of abelian etale sheaves and identifies its Yoneda splice in the signed model, with no divisor/purity assumptions.

lem-per-supported-yoneda-localization vs lem-pur-divisor-torsor-boundary-signs: the latter compares termwise coefficient connecting maps of signed cones; it does not assert the comparison of that connecting map with the Yoneda splice and its shift. Its formula for partial is reused unchanged.

lem-per-supported-yoneda-localization vs lem-coef-yoneda-zero-splice: the existing node only says splicing preserves the zero extension class, not which signed supported cocycle a nonzero splice represents; the new node supplies the specified abelian-etale closed-open splice comparison.

lem-per-supported-yoneda-localization vs lem-coef-ext-contravariant-six-term: the existing node gives the general Ext exact sequence and composition boundary, not its identification with the signed support cone; the new node supplies the specified abelian-etale closed-open splice comparison.

lem-per-supported-yoneda-localization vs lem-coef-yoneda-derived-ext-comparison: the existing node identifies Yoneda and derived Ext groups, without the closed-open sequence or its signed support normalization; the new node supplies the specified abelian-etale closed-open splice comparison.

lem-per-supported-yoneda-localization vs lem-coef-yoneda-pullback-splice: the existing node compares equivalent Yoneda extensions under a pullback of their prefixes, with no signed localization computation; the new node supplies the specified abelian-etale closed-open splice comparison.

lem-per-supported-yoneda-localization vs lem-sc-p1-boundary-extension-composition: the existing node identifies an ordinary degree-zero O_X-module connecting map, not an abelian-etale supported degree-two splice; the new node supplies the specified abelian-etale closed-open splice comparison.

lem-per-supported-yoneda-localization vs lem-sc-p1-ext-yoneda-associativity: the existing node states associativity and O_X-module pushout functoriality, not the signed support-cone comparison; the new node supplies the specified abelian-etale closed-open splice comparison.

lem-per-supported-yoneda-localization vs lem-sc-p1-pullback-extension-class: the existing node gives pullback functoriality of O_X-module extensions only, with no support or localization sign; the new node supplies the specified abelian-etale closed-open splice comparison.

lem-per-supported-yoneda-localization vs def-sc-ext-sheaf: the existing node defines Ext for O_X-modules; it is not a theorem about signed localization of abelian etale sheaves; the new node supplies the specified abelian-etale closed-open splice comparison.

lem-per-supported-yoneda-localization vs lem-sc-p1-ext-yoneda-splicing-associative: the existing node asserts ringed-space module splice associativity, not a signed localization formula; the new node supplies the specified abelian-etale closed-open splice comparison.

lem-per-supported-yoneda-localization vs lem-sc-ext-yoneda-composition-derived: the existing node gives shifted derived composition of arbitrary Ext classes; identifying that composition in the closed-support cone is precisely the extra comparison in the new node; the new node supplies the specified abelian-etale closed-open splice comparison.

lem-per-supported-yoneda-localization vs lem-sc-p1-ext-pushout-postcompose: the existing node gives the O_X-module class of a pushout, without identifying its later splice in a supported cone; the new node supplies the specified abelian-etale closed-open splice comparison.

lem-per-supported-yoneda-localization vs lem-sc-p1-ext-yoneda-functoriality: the existing node gives O_X-module Ext functoriality and ordinary cohomology naturality, not the closed-open signed formula; the new node supplies the specified abelian-etale closed-open splice comparison.

lem-per-supported-yoneda-localization vs lem-sc-abelian-ext-covariant-exact: the existing node gives the general covariant Ext long exact sequence, not its comparison with the localization boundary; the new node supplies the specified abelian-etale closed-open splice comparison.

lem-per-supported-yoneda-localization vs lem-weil-pbc-ext-one-extension-classification: the existing node classifies one-extensions and exact functor images; it gives no supported degree-two signed computation; the new node supplies the specified abelian-etale closed-open splice comparison.

lem-per-supported-yoneda-localization vs lem-sc-etale-zariski-natural-acyclic-leray: the existing node compares ordinary cohomology under an acyclic site pushforward, not supported Yoneda/localization classes; the new node supplies the specified abelian-etale closed-open splice comparison.

lem-per-supported-yoneda-localization vs lem-sc-presheaf-free-ext-local-killing-witness: the existing node effaces a positive Ext class by a locally surjective presheaf cover; it does not compare a class with signed localization; the new node supplies the specified abelian-etale closed-open splice comparison.

lem-per-supported-yoneda-localization vs lem-sc-presheaf-free-ext-local-killing: the existing node effaces Ext by a cover, not a signed support-cone identity; the new node supplies the specified abelian-etale closed-open splice comparison.

lem-per-supported-yoneda-localization vs lem-sc-ext-epi-effacement: the existing node effaces Ext by an epimorphism in an abelian category, not a comparison of a specified nonzero class; the new node supplies the specified abelian-etale closed-open splice comparison.

lem-per-supported-yoneda-localization vs new-etale-cohomology-natural-derived-evaluation: the existing node compares ordinary Ext cohomology to right-derived evaluation, without support or its connecting sign; the new node supplies the specified abelian-etale closed-open splice comparison.

lem-per-finite-coefficient-yoneda-blowup-class vs lem-per-regular-immersion-class-calculus: the existing prime-power node pins eta using c_D and states its operations; it does not give the arbitrary finite-ideal modified-blowup construction, injective pullback or Chern polynomial. The rank-one calculation in this item proves their agreement, rather than assuming it in the new node.

lem-per-finite-coefficient-yoneda-blowup-class vs lem-per-generalized-blowup-class: the existing Q49 node assumes Lambda=F_ell and defines the supported first Chern operator by the relative coefficient boundary. This node works for every invertible N (in particular all ell^n) and defines the operator by the explicitly prescribed Yoneda splice, which differs by a degree-two sign. Neither changing coefficients from F_ell to Z/ell^n nor identifying those signed operators is a one-line specialization. The new id resolves a concurrent name collision between mathematically different statements, rather than modifying Q49's node.

lem-per-finite-coefficient-yoneda-blowup-class vs lem-per-cartier-blowup-polynomials: that existing statement proves the nested-Cartier polynomial identity for F_ell using Q49's relative-boundary convention, not the finite-coefficient Yoneda modified-blowup existence/injectivity construction.

## Validation

The first dry run during this repair exited successfully at aba27f504e. That run preceded the final direct definition citation and report correction, so a new full dry run is required before the push. Local checks of the JSON evidence verified all 19 citation quotes as verbatim statement substrings and exact step/node coverage. Required project gates are run only by deliver.py on the server. Final dry-run and delivery results follow when available.
