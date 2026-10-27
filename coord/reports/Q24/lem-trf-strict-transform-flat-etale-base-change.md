# Q24 repair: lem-trf-strict-transform-flat-etale-base-change

## Files written

- dag/nodes/sec-trace-formula/lem-trf-strict-transform-flat-etale-base-change.json: repaired split, statement unchanged, four assembly steps totaling 1814 characters.
- dag/nodes/sec-trace-formula/lem-trf-blowup-base-change-preserved-open-diagram.json: new statement-only node, status unsplit; no exact Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-finite-center-open-closure-kernel-data.json: new statement-only node, status unsplit; no exact Mathlib match.
- citations.json: one entry per parent-step citation, with verbatim text from the cited statement.

## Attachments

None. I searched the project WeilConjectures source for the item tag, strict-transform and flat-base-change notions, and read the relevant comparison and strict-transform APIs. The recorded declaration AlgebraicGeometry.Scheme.IdealSheafData.strictTransform_flat_baseChange, in lean/Sheaf/AlgebraicGeometry/StrictTransformFlatBaseChange.lean:65, has proof `sorry` at line 82. Its complete statement is not an attachment. The existing project lemmas for blowup comparison, the strict-transform factor, and image kernels supply tools for future workers; no project declaration found states either complete new node. No Lean file was written and no compiler, Lake or build tool was run.

## WANTED

None. All sources needed for this repair are present locally.

## What was wrong and how it was repaired

The sole return point requires spreading the 4228-character proof into at least two independent statement-only arguments, while keeping the parent statement and every old argument. The sandbox initially contained only dispatcher .brief files, with no node, report or search log. I therefore retained the complete current repository node as baseline.json and worked from that returned proof. No previous proof, report or recorded search in the sandbox was discarded. The inherited parent Mathlib records and every maintainer field are preserved.

The two work items separate geometric comparison from scheme-theoretic closure kernels. The diagram node has no closure or strict-transform base-change conclusion. The kernel-data node has no blowup or flat-base-change hypothesis or conclusion: it starts with an arbitrary morphism and a finite-type ideal, proves the required quasi-compactness, and gives a test for a proposed closed subscheme to equal the closure. Neither restates the parent or one of its conclusion clauses. These are extracted argument packages of comparable scale, rather than moving the entire proof into one child or isolating single elementary assertions. The parent's flat-density argument remains an application of an existing theorem and is not duplicated as a new node.

There is no statement dispute. The generic-point hypothesis is retained verbatim; it is not needed in this scheme-theoretic argument. No target, definition, unit route or chapter route changes. Both new nodes belong to the parent's chapter sec-trace-formula and unit sk-i-curve-zero. Their blueprint ancestor is lem-trf-local-term-locality, through the recorded chain ending in lem-trf-permissible-boundary-preservation. The precise use is that parent's coordinate-chart step 3, which identifies strict transforms after an etale neighborhood. I retained the existing item's blueprint reference and inserted this item at the front of the new nodes' via lists.

## Extraction map and retained arguments

This map accounts for every part of the old proof, including scheme structures and the maps into the ambient blowup.

1. Old step 1 goes to the diagram node. The comparison has target W times_X P before exchanging factors, so the new statement explicitly uses the exchange to obtain c:Q to P_W. The complement of the extended ideal is exactly the inverse image of U, not an arbitrary chosen open. The structure-map isomorphisms over the complement are compatible with c.
2. Old step 2 goes to the kernel-data node. Its general f:Y to X can be instantiated by T to X, and again by any of S, T_W, or S_W to X. It supplies the finite-center quasi-compactness without any global compactness assumption. The closure restricts to the entire preserved open scheme-theoretically, and the factor into the closure is quasi-compact and quasi-separated.
3. Old step 3 goes to the kernel-data node. The quotient O_Y/J injects into j_*O_Omega; the corresponding map on the closed image's structure sheaf is injective. This is schematic density and keeps all nonreduced structure.
4. Old step 4 is the parent's new step 3 using lem-weil-pbc-flat-morphism-base-change and lemma-nagata-dense-flat-pullback. The repeated finite-principal-open argument after pullback is now an instance of the kernel-data node. Its recognition clause includes the zero-kernel consequence for a quasi-compact dense open, so this argument has not been omitted.
5. Old step 5 is divided by content. Fibre-product associativity, common-open identification, and the ambient closed projections are in the diagram node. The factorization of the restriction map through the proposed closed subscheme, the consequent equality of its ideal with the restriction kernel, and the inverse-image-ideal calculation in a further closed ambient scheme are in the kernel-data node. Parent step 4 applies that criterion to S_W inside T_W inside P_W, then the strict-transform definition identifies the result. The final etale-flat implication and retained generic-point hypothesis remain explicit in the parent.

## Proof material for the statement-only children

The following records the arguments assigned to future workers. The node JSON files contain no proof steps, no proof_deps and no sketch in their statements.

For lem-trf-blowup-base-change-preserved-open-diagram: use def-nagata-blowup-flat-base-change-map and thm-nagata-blowup-flat-base-change, then exchange the two product factors to form c. Locally if I=(a_1,...,a_r), both W minus V(I O_W) and v inverse U are the union of the D(v^# a_i); thus their scheme structures as opens agree. By thm-nagata-global-blowup-complement, P over U and Q over U_W are identified with U and U_W via their structure maps. Since c is over W, its restriction under these identifications is the identity of U_W. Associativity of fibre products gives the induced theta from Z_W times_W Q to (Z times_X P) times_X W. Its composites to Z_W and P_W are the defining product maps, so the square with p, c, and the projection to Q commutes. Restricting this equality over U_W gives the common preserved open Z_W times_W U_W and its two specified projections. Finally each projection p or p-hat is a pullback of the supplied closed immersion i: on affine opens the coordinate map is the quotient by the extended ideal defining Z, so it is a closed immersion with the prescribed map, not just the same support. This is the old geometric argument, now a separate diagram construction and verification.

For lem-trf-finite-center-open-closure-kernel-data: cover Y by affine neighborhoods mapping into affine neighborhoods of X on which I has finitely many generators. The preserved open on such an affine of Y is the finite union of the principal opens of the images of these generators. It is quasi-compact there, so j is quasi-compact as a morphism; no finite cover of Y itself is needed. Stacks 01R8 makes J the actual quasi-coherent restriction kernel and describes the closed image by O_Y/J. On Omega that kernel is zero, so the fibre product of the closed image with Omega is all of Omega as a scheme. This gives the open factor h. On S the same finite-generators calculation makes h quasi-compact, and the diagonal of an open immersion is an isomorphism, giving quasi-separatedness. The map from O_Y/J into j_*O_Omega is injective by the quotient-by-kernel construction. Every open of S is the intersection with an open of Y; evaluating there proves injectivity of O_S into h_*O_Omega. Thus its image kernel is zero, giving schematic density even when Y or S is nonreduced. For the recognition clause, R contains exactly the same open Omega and maps to X, so the same local generator argument makes h_R quasi-compact. Since SIm(h_R)=R, the quasi-compact image-factor injection of lemma-nagata-scheme-image-ideal-qc gives O_R into (h_R)_*O_Omega injective. The map O_Y to j_*O_Omega factors through s_*O_R. The second map is injective, so its kernel is precisely the defining ideal of R. Hence that ideal is J and R=S. For a further closed embedding k:Y into P, taking the kernel after the quotient O_P to k_*O_Y takes this J to its inverse-image ideal, which is exactly the kernel of restriction to Omega in P. This supplies the closed-ambient equality, including nilpotents, used in old step 5. No flatness is required for this recognition lemma; flatness enters only to prove its density hypothesis in the parent.

## Searches

The complete actual answers are in search-result-0.txt through search-result-12.txt, and the command-generated searches.jsonl records every query and digest. For each new node I ran LeanFinder, Loogle, grep, and LeanSearch through the required msearch.py command. I tried a second semantic phrasing for both statements. All services answered successfully; none is mislabeled unavailable. Each new node records the exact tool and query text from that log, with its actual hits and the reason they do not match.

The diagram searches find comapIso/projection identities and flatness or closed-immersion stability, not a theorem about the canonical blowup comparison and its preserved-open diagram. The Mathlib grep for blowup|blowUp|BlowUp|strictTransform in AlgebraicGeometry has zero hits. The kernel-data searches find IsImmersion.instIsOpenImmersionToImageOfQuasiCompact, Scheme.instQuasiCompactToImage and Hom.support_ker, plus PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg. I read the image-factor implementation in IdealSheaf/Subscheme.lean, the kernel identities in IdealSheaf/Basic.lean, Immersion.lean and Prime/Topology.lean:1136. The factor theorems assume j is quasi-compact, and the last theorem is for one affine spectrum. None states the general finite-center quasi-compactness together with the closure data and the closed-ambient recognition criterion, nor is the entire child a one-line specialization of any single hit. The locally Noetherian open-immersion result has an absent hypothesis and was not used.

Blueprint searches used tools/blueprint_refs.py for strict transform, scheme-theoretic closure, preserved open, scheme-image, blowup base change, finite-type, kernel, 01PH and 02OS. DAG searches covered those notions and source tags 0805, 02OS, 080D, 01R8 and 081I. The closest existing nodes are compared below; I reuse the original flat-density node rather than creating its specialization.

## Review by Q24

I read the parent statement and all five old steps, the chapter and unit records, the current-blueprint update of def-nagata-strict-transform, the parent's use in permissible-boundary-preservation, the recorded ancestor and its current blueprint update, and the relevant project Lean declarations. For the parent I read Stacks morphisms.tex Tag 081I, lemma-flat-base-change-scheme-theoretic-image, including its affine-kernel proof, and Tag 01R8, lemma-quasi-compact-scheme-theoretic-image. For the diagram child I read divisors.tex Tag 0805 and its Rees/relative-Proj proof, and Tag 02OS assertion (1), which identifies the complement by the structure map. For the kernel-data child I read Tag 01R8 and properties.tex Tag 01PH, especially the proof of (4) implies (1), which is local on arbitrary schemes and does not impose qcqs on the present X or Y. I also read the divisors.tex Tag 080D definition and preceding paragraph so that the closure used here is the supported-section kernel, with scheme structure, not only topological closure. No SGA source is used.

I checked citations against statements, not proofs. New parent step 1 uses exactly the diagram child's specified comparison, common open, closed projections and commuting square. It is instantiated with the same finite-type ideal, closed i and flat v as in the parent. Step 2 uses the kernel-data child's quasi-compact open factor, its zero restriction kernel and schematic density. The current def-nagata-strict-transform statement is interpreted using its blueprint_update: scheme-theoretic image of the preserved open for the specified maps and specified U. Step 3 uses the statement of lem-weil-pbc-flat-morphism-base-change for S_W to S, since that map is a pullback of v. The statement of lemma-nagata-dense-flat-pullback gives SIm(h_W)=S_W; its older, stronger qcqs hypothesis already holds because the child explicitly supplies the quasi-separated open factor. Thus I do not rely on the more general clause in that node's blueprint_update alone. Step 4 uses the child recognition criterion with f:T_W to X and R=S_W. The closed immersion and intersection-with-open hypotheses follow from the specified closed inclusion and the base change of S intersect Omega=Omega. The ambient projection is the closed immersion asserted in the diagram child; its kernel clause therefore applies. Finally the strict-transform definition gives the claimed transform in that ambient blowup. The definition of an etale morphism includes flatness as used in the last sentence. Every cited statement is copied verbatim into citations.json for its step.

The extracted statements introduce all schemes and maps. The finite-type ideal notion, fibre products, open/closed immersions, kernel ideal and scheme image all have statement dependencies that actually define those notions. Quasi-separatedness in the kernel-data child is explicitly defined by its diagonal, so no unintroduced finiteness assumption enters. I checked empty Y, Z or W: all opens and images are empty where appropriate and the kernel is the unit ideal. For I=0, U is empty and the closure is the empty closed subscheme; for I=O_X the preserved open is everything and J=0. If Z lies in the center, Omega is empty and its strict transform is empty. For a nonreduced example Y=Spec(k[t,e]/(e^2)) and I=(t), localization at t is injective and the closure retains e; for Y=Spec(k[t,e]/(e^2,t e)), its restriction kernel on D(t) is (e), so the closure correctly removes the t-supported nilpotent. On Y equal to an infinite disjoint union of affine lines, j is still a quasi-compact morphism although Y need not be quasi-compact: the check is on each affine target neighborhood. These cases verify the precise hypotheses and prevent replacing the scheme kernel with support closure. The flatness hypothesis remains necessary for the parent's density transfer; it is not asserted by the new kernel criterion.

Against delivery-errors B: both children are statement-only, fully bound, have once-escaped TeX, source labels and tags, exact logged search records, and the prescribed blueprint ancestor/via. Against C: all non-elementary parent uses have nodes, every such statement was opened, citations are literal, and no child depends on the parent. Against D: the children are distinct arguments, neither a base-change equality of strict transforms; the parent still specifies how to apply them. Against E: the proof uses no Noetherian, finite-presentation, compact-base or reducedness hypothesis, and keeps the comparison's direction and ambient inclusions explicit. The only repair is the requested distribution of work; the statement and maintainer metadata are unchanged. No assembly step exceeds 2000 characters.

## Not duplicates

lem-trf-blowup-base-change-preserved-open-diagram vs thm-nagata-blowup-flat-base-change: asserts only that the constructed blowup comparison is an isomorphism; the new node constructs the induced closed-subscheme fibre-product diagram and identifies its preserved opens and ambient projections.

lem-trf-blowup-base-change-preserved-open-diagram vs sk-lem-nagata-boundary-divisor: constructs an admissible blowup making an open dense with Cartier complement; neither new statement asserts such a construction.

lem-trf-blowup-base-change-preserved-open-diagram vs def-nagata-flat-pullback-rees-map: defines a graded algebra map, not the blowup/open/closed-immersion comparison diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs def-nagata-blowup-flat-base-change-map: defines c before factor exchange; it does not state the common-open identification or the closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-trf-marked-controlled-blowup-charts: The existing statement concerns Controlled transforms in smooth marked blowup charts; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-trf-smooth-center-blowup-geometry: The existing statement concerns Smooth-center blowups and reduced strict transforms; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-trf-modifications-zariski-refinement: The existing statement concerns Global refinement of modifications over a finite open cover; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-trf-log-blowup-normalization: The existing statement concerns Comparison of one saturated log blowup with normalization; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-trf-module-admissible-blowup-calculus: compares composite admissible blowups and module transforms; the new diagram has one flat base change and the new kernel statement involves no blowup or module transform.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-trf-nc-maximal-branch-blowup: The existing statement concerns Maximal geometric branch locus and its one-step blowup; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-trf-module-strict-transform-flat-pullback: asserts compatibility of ordinary module pullback and module strict transforms; the new diagram statement does not mention transforms, and the kernel-data statement assumes no flat maps.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-trf-etale-flattening-descent: The existing statement concerns Etale descent of local module flatifications; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-trf-marked-ideal-transverse-suspension: The existing statement concerns Transverse suspension of a marked ideal; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-trf-nc-coordinate-blowup-branch-drop: The existing statement concerns Coordinate blowup lowers the branch number; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-trf-strict-transform-flat-etale-base-change: is the parent and asserts equality of strict transforms after flat pullback; neither new node asserts that equality: one supplies its geometric diagram and the other a finite-center kernel criterion independent of flatness.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-trf-finite-eta-flatification: The existing statement concerns Finite generic flatification after a birational base modification; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-trf-finite-after-blowup: The existing statement concerns Finite locally free strict transform after an admissible blow-up; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-sfb-proper-pair-radicial-preparation: The existing statement concerns Proper normal pair preparation over a radicial constant extension; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-sfb-nodal-trait-rational-domination: The existing statement concerns Rational geometric fibres dominate modifications of a nodal trait curve; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-sfb-dvr-nodal-chart-blowup-calculus: describes explicit blowups of nodal DVR charts with etale persistence; the new diagram is for arbitrary schemes and ideals, with no DVR or nodal equation.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-sfb-regular-point-blowup-functions: The existing statement concerns Regular functions under a regular point blowup; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-sfb-regular-point-blowup-geometry: The existing statement concerns Geometry of a blowup at a regular surface point; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-sfb-exceptional-curve-count: The existing statement concerns Finite exceptional-curve count and strict decrease after a target point blowup; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-sfb-point-blowup-fibre-defects: The existing statement concerns Geometric fibre defects in regular surface point blowups; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-sfb-nested-open-regular-alteration: The existing statement concerns Regular alteration adapted to nested opens and a prescribed finite cover; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-sfb-nodal-trait-regularization: The existing statement concerns Regularization of smooth-generic nodal families; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-sfb-integral-blowup-projective-geometry: The existing statement concerns Integrality and projectivity of an ordinary finite-type blowup; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-per-normalized-blowup-completion-descent: The existing statement concerns Descent of normalized point blowups from completion; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-per-excellent-quasiprojective-normalized-blowup: The existing statement concerns Normalized blowups preserve quasi-projectivity over an excellent affine base; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-per-regular-flag-blowup-geometry: The existing statement concerns Conormal and strict-transform geometry for a regular flag; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-per-cartier-blowup-polynomials: The existing statement concerns Two polynomial terms on the blowup of a Cartier flag; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-per-surface-tower-discard-regular-centers: The existing statement concerns Discarding regular centers in a finite surface blowup tower; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-per-local-ordinary-point-blowups-globalize: The existing statement concerns Globalizing ordinary point-blowup towers from finitely many local schemes; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-per-surface-point-blowup-geometry: The existing statement concerns Regularity and projectivity of a point blowup on a regular surface; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-per-integral-blowup-projective-geometry: The existing statement concerns Integrality and projectivity of an ordinary finite-type blowup; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-per-proper-generic-curve-preparation: The existing statement concerns Compactification and inseparable preparation of a marked relative curve; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs lem-pur-noetherian-etale-section-specialization: The existing statement concerns Normalized section specialization for ordinary etale dualizing complexes over a Noetherian base; it does not state the canonical blowup comparison with the induced preserved-open and closed-subscheme diagram.

lem-trf-blowup-base-change-preserved-open-diagram vs thm-nagata-global-blowup-complement: gives the structure-map isomorphism for one blowup over its complement; it gives neither the flat comparison diagram nor the induced common open for Z.

lem-trf-finite-center-open-closure-kernel-data vs lemma-nagata-scheme-image-ideal-qc: gives the kernel description once quasi-compactness is known; it neither proves finite-center quasi-compactness nor states the closed-ambient recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs def-nagata-affine-gluing-coefficient-stage: The existing statement concerns Coefficient stage of an affine gluing presentation; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs lem-nagata-one-affine-subring-extension: extends marked affine subring models; its statement has no preserved-open closure kernel or blowup comparison.

lem-trf-finite-center-open-closure-kernel-data vs def-nagata-scheme-theoretic-closure: defines a closure for an already quasi-compact quasi-separated immersion; the new node proves applicability and specifies its exact kernel data and recognition in a closed ambient scheme.

lem-trf-finite-center-open-closure-kernel-data vs det-nagata-affine-opens-projective: The existing statement concerns Projective compactification of an affine piece; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs sk-lem-nagata-boundary-divisor: constructs an admissible blowup making an open dense with Cartier complement; neither new statement asserts such a construction.

lem-trf-finite-center-open-closure-kernel-data vs sk-lem-nagata-sketch-closure: assumes a quasi-compact immersion and a quasi-separated target; the new node proves the finite-center quasi-compactness without target quasi-separatedness and supplies the closed-ambient kernel criterion.

lem-trf-finite-center-open-closure-kernel-data vs lemma-nagata-separate-closed-subschemes: The existing statement concerns Properties of the closed-boundary separation blow-up, [stacks-project]; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs def-nagata-scheme-theoretic-image: defines the largest quasi-coherent kernel and image, without the finite-center quasi-compactness and recognition assertions.

lem-trf-finite-center-open-closure-kernel-data vs lem-weil-finite-duality-locally-closed-comparison: The existing statement concerns Locally closed exceptional comparison under site comparison; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs lem-sf-locally-closed-closure-adjoint-realization: The existing statement concerns Closure compactification realizes the immersion adjoint and its bounds; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs lem-trf-standard-ph-composite-refinement: The existing statement concerns Composites of standard ph families admit a standard refinement; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs lem-trf-semistable-normal-target-factorization: The existing statement concerns Factor a semistable marked modification through a finite normal target; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs lem-trf-dejong-arbitrary-base-marked-semistable: The existing statement concerns Marked semistable alteration over an arbitrary excellent base; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs lem-trf-strict-transform-composition: The existing statement concerns Strict transforms under a composition of blow-ups; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs lem-trf-finite-eta-modification-gluing: The existing statement concerns Finite-base reconciliation of local reduced generic modifications; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs lem-trf-stable-modification-flat-curve-pair: The existing statement concerns Stable modification of a flat multipointed relative curve; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs lem-trf-nc-coordinate-blowup-branch-drop: The existing statement concerns Coordinate blowup lowers the branch number; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs lem-trf-strict-transform-flat-etale-base-change: is the parent and asserts equality of strict transforms after flat pullback; neither new node asserts that equality: one supplies its geometric diagram and the other a finite-center kernel criterion independent of flatness.

lem-trf-finite-center-open-closure-kernel-data vs lem-trf-strict-transform-sheaf-kernel: concerns module strict transforms on an actual blowup; the new diagram node has no module/kernel assertion, and the kernel-data node treats arbitrary finite-center preimages without any blowup and recognizes arbitrary closed ambient factorizations.

lem-trf-finite-center-open-closure-kernel-data vs lem-trf-finite-eta-flatification: The existing statement concerns Finite generic flatification after a birational base modification; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs lem-trf-nodal-subcurve-boundary: The existing statement concerns Reduced nodal subcurves and their reduced boundary intersection; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs lem-trf-valuation-normalized-graph-model: The existing statement concerns Normalized graph image as an intermediate valuation-curve model; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs lem-trf-finite-after-blowup: The existing statement concerns Finite locally free strict transform after an admissible blow-up; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs lem-trf-geometrically-integral-curve-factorization: The existing statement concerns Factorization with a geometrically integral generic curve; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs lem-sfb-etale-locally-closed-extension-comparison: The existing statement concerns Étale closed/open interchange and closure-defined extension by zero; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs lem-sfb-semilinear-equivariant-chow-modification: The existing statement concerns Semilinear equivariant projective Chow modification; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs lem-sfb-equivariant-curve-pencil: The existing statement concerns Equivariant curve-pencil preparation over a field; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs lem-sc-picard-locus-closed: The existing statement concerns The invertible-module pullback locus is closed; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs lem-sc-picard-locus-closed-valuation-criterion: uses a valuative specialization condition to show an immersion has closed image; the new kernel-data statement assumes no valuation condition and gives a scheme-theoretic closure ideal.

lem-trf-finite-center-open-closure-kernel-data vs lem-per-equivariant-projective-envelope: constructs an equivariant projective compactification; the new statements have neither a group action nor a projectivity assertion.

lem-trf-finite-center-open-closure-kernel-data vs lem-per-projective-finite-group-quotient: The existing statement concerns Finite group quotients preserve relative projectivity; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs lem-weil-pbc-scheme-image-qc-kernel: assumes the morphism quasi-compact and describes affine image kernels and their universal factorization; the new node proves the finite-center hypothesis and states the dense-open and closed-ambient recognition data.

lem-trf-finite-center-open-closure-kernel-data vs lem-weil-pbc-chow-noetherian: The existing statement concerns Chow's lemma over a Noetherian base; it does not state finite-center quasi-compactness for arbitrary schemes together with the dense-factor and closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs lem-weil-pbc-closed-image-limit-system: constructs inverse systems of closed images under a limit; no such limit appears in either new statement.

lem-trf-finite-center-open-closure-kernel-data vs lem-weil-pbc-scheme-theoretic-image-proper: proves properness and surjectivity of a proper scheme image; neither new statement has properness or surjectivity hypotheses or conclusions.

lem-trf-finite-center-open-closure-kernel-data vs lem-pur-dnc-affine-blowup-complement: identifies an affine deformation chart by removing a specific strict transform; the new statements make no deformation-chart or polynomial-ring assertion.

lem-trf-finite-center-open-closure-kernel-data vs lemma-nagata-immersion-open-in-scheme-image: starts with an already quasi-compact immersion; the new node proves that hypothesis for an arbitrary finite-center inverse image and gives the closed-ambient kernel recognition criterion.

lem-trf-finite-center-open-closure-kernel-data vs lemma-nagata-dense-flat-pullback: is the existing flat-base-change theorem, reused without duplication; the new kernel-data node has no flatness hypothesis and instead supplies finite-center quasi-compactness and recognition of a proposed closed image.

## What could not be finished

Nothing in the requested stage-1 repair remains mathematically unresolved. The two children intentionally remain unsplit, for separate workers. Required delivery validation is recorded below when it finishes.
