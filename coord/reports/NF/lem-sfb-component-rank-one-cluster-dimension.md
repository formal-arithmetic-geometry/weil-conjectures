## Worker report

1. Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-component-rank-one-cluster-dimension.json` (statement, split, no Mathlib match); `dag/nodes/sec-six-functors-basics/lem-sfb-nodal-ideal-scalar-gluing.json` (one new statement-only prerequisite, unsplit, no Mathlib match); `citations.json` (one verbatim statement quotation per step/node pair). The supporting scripts and searches.jsonl are sandbox records only. No Lean was written and nothing was compiled.
2. Attachments: none. Searched the live `lean/WeilConjectures/` for the exact blueprint id, subcanonical, splitting index, and component rank-one terms. Hits concern subcanonical sites, finite-etale splitting or the unrelated Weil-character component modulus. No project declaration states this item. Mathlib hits were also read: general scheme normalization, local ideal membership, sheaf gluing/scalar operations, finite-flat morphism ranks and simplicial/valuation ranks do not state either the item or the new prerequisite.
3. WANTED: Franciosi--Tenni, *On Clifford's theorem for singular curves*, Proc. London Math. Soc. (2014), Lemma 3.6, printed pp.240--242, for this item. The local `literature/franciosi-tenni-clifford-singular-curves-2014.pdf` is absent. I read the author-hosted primary PDF at https://pagine.dm.unipi.it/franciosi/lavori/clifford.pdf through the web reader, particularly Definition 2.9, Definition 2.16/Proposition 2.17, and the whole proof of Lemma 3.6. The proof origin is therefore agent, as the worker brief requires for a missing local source.
4. Statement errors: none found; item statement and statement dependencies are unchanged. The imported item already carefully distinguishes actual canonical restriction images from tensor restrictions of an ideal with punctual torsion. I preserved that distinction. The proof does not assume the cluster is Cartier, reduced or supported in the smooth locus. The empty-cluster convention r(empty)=0 is important: I did not infer r=m-1 for an empty cluster merely from the partition definition. Step 6 proves the required m=1 using duality and two-connectedness.
5. Unfinished: the one new gluing lemma is intentionally statement-only under the one-level split contract. Its complete argument and source comparison are below. Nothing else remains within the requested split.

## Route and source reading

Read GOAL.md, SETUP.md's chapter/unit/node requirements, the worker role and stage-1 brief, stages/1-dag.md, the chapter and unit JSON, and delivery-errors B--E (both copies). The current blueprint is `literature/blueprint/latest`, with COMMITS.txt's latest main-20261023-1620, commit 7284bb09daf97437d544c51882b325f9c52cd345. I read the current detailed direct-images statement and proof at `sec-six-functors-basics/sk-thm-sf-ctf-stability/`. The inherited chain reaches the curve-linear-series inputs below the alteration prerequisite. The item is not a unit key node, so no unit record is changed. `blueprint_refs.py ancestor` explicitly returned None; the new node retains that null ancestor and prepends this item to the inherited via list, as required. Searches of the whole imported blueprint for splitting, splitting index, componentwise, scalar multiples, branchwise, branch, nodal, ideal sheaf and subcurve found no imported equivalent of the new ideal-gluing theorem.

For the new node I read Stacks curves.tex Tag 0CBW, `lemma-split-node` (two normalized branches and the completed k-algebra node model), varieties.tex Tags 0C1R and 0C3V (`lemma-prepare-delta-invariant`, `lemma-normalization-same-after-completion`, normalization/complete stalk comparison), and algebra.tex Tag 00MC (`lemma-completion-faithfully-flat`). These supply the geometric machinery, not a quoted theorem already saying our coefficient description. For the item I also read curves.tex 0BS2, 0BS3 and 0BS5 (duality and Euler duality), curves.tex 0E38 (`lemma-closed-subscheme-nodal-curve`, reduced rational boundaries), and varieties.tex `lemma-euler-characteristic-additive` and Tag 0AYT (`lemma-chi-tensor-finite`). The item proof uses existing DAG statements for these facts. No SGA is used.

## Argument retained for the new statement-only node

Let nu be the finite componentwise normalization. A tuple a of component scalars gives a section of nu^*L by multiplying nu^*s on each normalized component. Away from nodes it is already a section of I_T L, since it is a constant multiple of s. At a self-node both branches have the same scalar, so it is again that scalar times s. At a node on distinct components the completed candidate is (a f,b g) in the product of branch rings. The original ideal-twisted stalk embeds in that finite normalized line stalk. Membership in it is equivalent to membership after completion: the quotient is a finite module and completion is faithfully flat. The completed normalization and ideal identify this test with (a f,b g) in J, including the requirement to be in the equal-constant subring R.

The set of pairs (a,b) satisfying that membership is a k-vector subspace of k^2 containing the diagonal, because (f,g) is s in J. Since
(a f,b g)=b(f,g)+(a-b)(f,0),
this subspace is the diagonal when (f,0) is not in J, and all of k^2 when (f,0) is in J. The condition is symmetric, since (0,g)=(f,g)-(f,0). At every node this is exactly the equality constraint stated in the new node. A candidate passing these local tests belongs to I_T L on every stalk and hence globally; agreement and uniqueness follow from the injection into the normalized line. Its coefficients are unique since s is nonzero at each component generic point. A frame change multiplies both the ideal-twisted stalk and the candidate by the same unit, and a different nodal presentation only changes the branch coordinates, so the constraint is intrinsic. This argument is valid in arbitrary characteristic and for arbitrary finite colength ideals. It is longer than an elementary step, but it proves no statement about the dimension, splitting index, canonical degree, or two-connectedness of the item. It is a genuine generic prerequisite, not either item clause moved into a new node.

## Review by NF

I checked the split against the primary paper and the cited Stacks source paragraphs above with the node statements open. Here is what each step actually takes from those statements, including the hypotheses.

Step 1 uses projective-implies-proper and the nodal-completed-normalization theorem with the nonempty reduced pure-one-dimensional curve over the algebraically closed field in the item. The latter explicitly supplies Noetherianity and finite nodes/normalized components, so no finiteness or completeness assumption is invented. A reduced union of components is projective by composing its closed immersion with a projective embedding of X; it is reduced pure-dimensional one by construction. The finite-type coherent criterion and the closed-immersion coherent-cohomology theorem apply on these locally Noetherian schemes. The coherent kernel/cokernel/sum theorem is stated for ordinary modules and supplies precisely the needed coherence. Locally an invertible twist is a change of frame, not a new quasi-coherence theorem assumed without citation. The nodal line-duality theorem supplies the invertible omega, and the reduced-curve dualizing theorem explicitly states chi(omega)=-chi(O) and exclusion of coherent submodules with zero generic stalks. The definition of subcanonical supplies s; the rank-one hypothesis then supplies the unique scalar on each actual canonical component restriction. No tensor restriction of I_S is used.

Step 2 applies the new generic gluing statement with L=omega and T=S: its hypotheses need neither two-connectedness nor Cartier support, and its W_s is all of V_S by step 1. The equations are equalities of two scalar coordinates at actual nodes. The connected components of the constraint graph give the displayed indicator basis by writing any vector as its constant on each graph component times that component's indicator. This is an explicit linear-algebra computation, not a citation to the new node for a dimension assertion it does not make. A graph block is connected as a subcurve because a path consists of actual intersections. Self-nodes have the same coefficient on both branches, so they do not create extra blocks.

Step 3 rereads the exact admissible-partition definition. An indicator of a constraint graph component cannot be assembled from vectors supported on partition blocks cutting that component, because any such supported vector is zero there. Coarsenings do work by grouping indicator vectors. This proves the maximal partition count without replacing the source's notion by an arbitrary linear-matroid decomposition. The computation r=m-1 is explicitly restricted to nonempty S. It is a few-line consequence of step 2 and the definition, so no duplicate elementary node is created.

Step 4 uses the component-stalk theorem's reduced-union intersection-of-ideals clause and the closed-union theorem's explicit affine fibre-product ring identity. Restriction/difference therefore has kernel R/(I intersect J) and is onto R/(I+J); this proves the exact sequence, rather than assuming a tensor sequence stays exact. The boundary theorem applies because the selected and complementary subcurves are reduced pure-one-dimensional unions in the nodal curve; it explicitly gives a finite disjoint union of Spec k, not merely a set-theoretic intersection. Closed-pushforward cohomology and Euler additivity apply to coherent modules on proper subcurves. The zero-dimensional Euler theorem computes their intersection term. Adding the blocks counts each crossing once, since no node has three branches. The connected-edge lower bound is proved by growing the visited vertex set and recording one new edge for each new vertex.

Step 5 uses the reduced-dualizing theorem's generic exclusion to show the ideal of A_j kills s_j, so the map is really from i_*O_Aj, not an unsupported factorization through a subscheme. The component-stalk theorem states that a reduced scheme's component ideals intersect to zero; since the map is generically injective, this proves its actual injection. The coherent closure theorem gives its cokernel Q; its support is a proper closed subset on every one-dimensional component, hence zero-dimensional and finite on this Noetherian curve. The zero-dimensional Euler theorem says chi(Q)=h0(Q)>=0 and chi(O_S tensor omega)=chi(O_S)=length(S). Euler additivity applies to both written short exact sequences. Thus d=e+chi(Q)>=e>=m-1. This is the paper's degree induction written as a global evaluation sequence; it handles non-Cartier ideals without equating their tensor restrictions with their images. The arithmetic p_a=1-chi(O) and chi(omega)=-chi(O) gives precisely d=2p_a-2-length(S).

Step 6 checks the special convention S=empty rather than silently changing it. Evaluation at 1 identifies module maps out of O_A with sections killed by its ideal, and step 5's generic calculation identifies these with the supported canonical sections. The full nodal Serre-duality statement is for EVERY coherent F, so it can be used with i_*O_A, not merely invertible modules. The closed-immersion theorem then identifies H1 on X with H1 on A. Each block is nonempty connected proper reduced, as verified above, so the global-functions theorem gives h0=1; the Noetherian cohomology theorem gives vanishing above dimension one. Consequently chi(O_A)=0, and the Euler calculation yields chi(O_X)=-e. The line-duality theorem gives h0(omega)=h1(O_X)=p_a; hence m=e+1. If m>1 each block has nonempty complement, so the exact two-connectedness hypothesis applies. Reduced boundaries mean its length is its node count, and summing counts each crossing twice. It forces e>=m, a contradiction. This establishes m=1, the required empty-cluster equality, with no further degree assertion.

I reviewed B1--B10: the new node introduces k,X,C,L,T,s and its local coordinates, cites every nonstandard notion or defines it inline, is statement-only with empty proof/proof_deps and null proof_origin, has actual recorded searches and an explicit no-match verdict, and has filled blueprint fields. Existing fields outside the split's ownership are preserved. All TeX has a single backslash after JSON decoding. C1--C8: every non-elementary fact above is the full statement of a cited node, verbatim quotations were copied into citations.json, and generic off-unit scheme/cohomology tools are declared in split_report.tool_uses. No node depending on this item was used. D1--D5: the new lemma assumes no rank-one restriction and proves neither item clause; the six item steps contain the partition, Euler and empty-case arguments themselves. E1--E7: the checks above verify properness, Noetherianity, coherent hypotheses, generic nonvanishing, correct scheme-theoretic intersections, and distinguish actual ideal membership from tensor restriction. No mathematical dispute or source correction was needed. All six non-elementary step texts are below 2000 characters; none hides a long comparison.

Small cases checked by hand: for one irreducible component the coefficient space is k and every nonempty cluster has r=0, so the degree implication is vacuous. A smooth genus-one curve with S=empty has dim V=1 and r=0. A cycle of rational components has a connected constraint graph for its canonical space and also satisfies that empty case. Two smooth genus-one components meeting in two nodes, with S their reduced pair of nodes, have I_S omega equal to the pushforwards of their own canonical sheaves; V has dimension two, r=1, d=2, and e=2. Locally, J=R with a unit s imposes equality of scalars, J=(u+v) with s=(u,v) also imposes equality, J=(u,v) with s=(u,v) allows independent scalars, and the nonreduced ideal J=(u^2,v^3) with s=(u^2,v^3) also allows independence. These contrast the Cartier diagonal condition with non-Cartier split behavior. A self-node always has one component coefficient, even if its two branches could be separated formally. Characteristic two changes none of the subtraction or membership arguments. For m>1 two-connectedness actually gives e>=m, stronger than the connectedness e>=m-1 used for the degree clause.

## Not duplicates

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-flat-birational-normalization-comparison: the existing statement concerns canonical total-fraction comparison for a flat finite birational algebra; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-stacks-nodal-closed-subcurve: the existing statement concerns stacks lemma for a reduced closed subcurve of a nodal curve; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-normality-from-completed-monoid-chart: the existing statement concerns normality descends from saturated completed strict-local monoid models; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-test-sequence-order-recovery: the existing statement concerns recovery of point and boundary orders from test sequences on cosupport; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-split-node-component-normalization: the existing node constructs componentwise normalization and branch completions, not the allowable componentwise scalar tuples in an arbitrary finite-colength ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-implicit-taylor-coordinate-calculus: the existing statement concerns implicit transverse coordinates and regular coefficient calculus; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-completed-maximal-localizations-detect-zero: the existing statement concerns completed maximal localizations are complete local flat tests for zero derived objects; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-normalization-completed-product-comparison: the existing statement concerns recover normalization by intersection with normalized completed branches; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-normalization-completed-branch-lift: the existing statement concerns a closed normalization point lifts to a completed branch; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-normalized-curve-branch-coordinates: the existing statement concerns power-series coordinates on the actual normalized curve branches; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-normalization-singular-skyscraper: the existing statement concerns normalization quotient is supported at singular points; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-ordinary-point-delta-branches: the existing statement concerns ordinary curve points characterized by delta and branch number; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-semidualizing-rhom-conservative: the existing statement concerns derived hom from a semidualizing complex detects bounded coherent isomorphisms; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-curve-normalization-completion: the existing statement concerns normalization and completion of a reduced local algebraic curve; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-nodal-point-finite-separable-splitting: the existing statement concerns splitting a nodal curve point over a finite separable field extension; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-nodal-contraction-euler-defect: the existing statement concerns euler defect of contracting a nodal subcurve to a smooth point; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-nodal-curve-normalization-euler: the existing node computes chi of a nodal curve, not a coefficient space of sections of a specified ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-nodal-contraction-normalization-branches: the existing statement concerns normalization branches at a nodal contraction boundary; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-curve-delta-completion-data: the existing statement concerns local normalization defect and its canonical completion comparison; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-completed-conormal-resolutions: the existing statement concerns algebraic and formal conormal complexes resolve completed differentials; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-finite-dvr-branch-completion: the existing statement concerns completion of an injective finite algebra with dvr branches; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-depth-fitting-quadratic-lci: the existing statement concerns depth and first fitting ideal give a quadratic completion and lci neighbourhood; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-finite-colength-completion-comparison: the existing statement concerns canonical completion comparison for finite-colength algebra inclusions; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-generic-center-formal-normal-slice: the existing statement concerns generic smooth centers and completed normal coordinates; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-nodal-geometric-fibres-reduced: the existing statement concerns nodal geometric curve fibres are geometrically reduced; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-nodal-points-reduced-algebraically-closed: the existing statement concerns a curve with only smooth points and nodes over an algebraically closed field is reduced; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-geometric-node-fitting-depth: the existing statement concerns geometric node completion gives the fitting and depth conditions; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-nodal-normalization-quotient: the existing node identifies the structure-sheaf normalization quotient, not membership in an arbitrary cluster ideal multiplied by an invertible module.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-diagonal-taylor-faithful-flatness: the existing statement concerns faithfully flat taylor realization at the residue-field diagonal point; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-nagata-normalization-dvr-branches: the existing statement concerns finite normalization and dvr branches of a reduced nagata curve ring; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-nodal-family-split-point-neighbourhood: the existing statement concerns etale base neighbourhood making a prescribed nodal fibre point rational and split; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-local-completion-product-faithfully-flat: the existing statement concerns faithfully flat localization-completion cover; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-nodal-coefficient-straightening: the existing statement concerns straightening a coefficient field in the standard split node; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-trf-nodal-normalization-adjunction: the existing statement concerns normalization adjunction for a component of a nodal curve; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-nodal-completed-normalization-model: the existing node gives finite normalization, branch rings and their completion comparison; the new node uses these to characterize global rescaled sections of an arbitrary ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-nodal-branch-double-cover: the existing statement concerns the two branches of a nodal family form an etale double cover of its singular subscheme; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-nodal-completed-residue-denominators: the existing statement concerns regular denominators and residue coefficients descend from a completed series algebra; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-split-completion-local-invariant-descent: the existing statement concerns reducedness descends from a split completed geometric stalk; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-nodal-deformation-smoothing-parameters: the existing statement concerns local-to-global smoothing of proper nodal curves; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-nodal-geometric-branch-square: the existing statement concerns geometric scalar extension of the actual normalization residue algebra; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-smooth-marking-normalization-twist: the existing statement concerns smooth markings, normalization of the twist, and its component degrees; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-nodal-component-picard-gluing: the existing node classifies invertible sheaf classes and gluing scalars, not sections inside a possibly noninvertible cluster ideal.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-nodal-tangent-canonical-grading: the existing statement concerns canonical grading and degree-zero residue isomorphism; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-reduced-normalization-local-fibre: the existing statement concerns the fibre of componentwise normalization from local integral closure; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-nodal-graph-cone-fibre: the existing statement concerns the graph cone over a field and normalization branches; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-nodal-normalized-chart-uniqueness: the existing statement concerns uniqueness and residue compatibility of normalized tangent charts; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-nodal-completed-graded-model: the existing statement concerns completed normalization and associated graded model of a quadratic local ring; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-gieseker-component-interpolation: the existing statement concerns component interpolation under leading hilbert weight inequalities; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-integral-nodal-picard-normalization-action: the existing statement concerns picard-trivial automorphisms fix the normalized branches of an integral nodal curve; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs def-sfb-nodal-tangent-comparison-data: the existing statement concerns the actual local normalization, tangent grading and normalized comparison data; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-nodal-local-tangent-normalization: the existing statement concerns the tangent proj of a geometric node is its quadratic normalization residue algebra; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-branch-multiplicity-tangent-criterion: the existing statement concerns branch multiplicity, component degree, and the double-point tangent criterion; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-nodal-branch-quasi-split-spreading: the existing statement concerns branch-scheme criterion and generic spreading for quasi-split nodal fibres; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-nodal-derivation-local-descent: the existing statement concerns local extension and descent of derivations across a node; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-marked-nodal-infinitesimal-fields: the existing statement concerns infinitesimal marked automorphisms and normalized vector fields; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-nodal-quadratic-tangent-comparison: the existing statement concerns the local tangent comparison for a nondegenerate quadratic completion; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-nodal-section-dual-flat: the existing statement concerns flat dual of the ideal of a section of a nodal family; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs pqf-lem-fff-vanishing: the existing statement concerns formal functions vanishing over finite fibres; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-per-henselian-normal-completion-preparation: the existing statement concerns henselian normalization and normal completion of a quasi-excellent local ring; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-per-weierstrass-henselian-cylinder: the existing statement concerns weierstrass coordinate change and completion of a henselian cylinder; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-per-normal-punctured-hypersurface-connected: the existing statement concerns connected punctured principal slices of excellent normal local rings; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-per-finite-henselian-algebra-local-model: the existing statement concerns finite algebras over a local henselization have finite-type strict local models; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-per-catenary-completion-hyperplane: the existing statement concerns hyperplane reduction of a non-equidimensional completion; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-per-punctual-strict-completion-test: the existing statement concerns testing closed-point purity after strict completion; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-per-regular-model-completion: the existing statement concerns normal completion and completed regular birational model; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-per-local-cohomology-top-nonvanishing: the existing statement concerns nonvanishing of top local cohomology of a noetherian local ring; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-per-normalization-completion-base-change: the existing statement concerns normalization commutes with completion away from the special fibre; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-per-normal-surface-cover-completed-degree: the existing statement concerns normalization covers of regular surfaces and their completed local degrees; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-weil-pbc-g-ring-maximal-ideal-criterion: the existing statement concerns a noetherian ring is a g-ring if its maximal localizations have geometrically regular formal fibres; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-weil-pbc-fs-adic-local-flat: the existing statement concerns a formally smooth local homomorphism of noetherian local rings is flat; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-weil-pbc-g-ring-completion-regular: the existing statement concerns the completion of a g-ring along an ideal is a regular ring map; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-weil-pbc-local-completion-faithfully-flat: the existing node proves faithful flatness of local completion; it does not glue rescaled sections or impose the nodal ideal membership constraints.

lem-sfb-nodal-ideal-scalar-gluing vs lem-weil-pbc-analytically-unramified-n1: the existing statement concerns an analytically unramified local domain is n-1; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-weil-pbc-completion-dimension: the existing statement concerns the completion of a noetherian local ring has the same dimension; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs lem-exc-weakly-etale-g-ring: the existing statement concerns g-rings ascend along weakly etale noetherian ring maps; it does not characterize the global scalar coefficient tuples of sections of an arbitrary nodal ideal twist.

lem-sfb-nodal-ideal-scalar-gluing vs def-sfb-subcanonical-splitting-index: the existing node defines the splitting index.

lem-sfb-nodal-ideal-scalar-gluing vs lem-sfb-component-rank-one-cluster-dimension: the item proves canonical dimension and degree under rank-one restrictions; the new lemma is a generic local-to-global gluing prerequisite without those hypotheses or conclusions.

## Validation

Server review_split passed on the first draft. Final deliver.py --no-push and delivery results are recorded below when they finish.
