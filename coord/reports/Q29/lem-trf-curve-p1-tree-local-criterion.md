# Q29 stage-1 delivery: lem-trf-curve-p1-tree-local-criterion

## Files written

- dag/nodes/sec-trace-formula/lem-trf-curve-p1-tree-local-criterion.json: corrected statement and eight-step split; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-reduced-curve-normalization-genus.json: statement, unsplit; no Mathlib match. General normalization arithmetic-genus formula, including nonnodal and disconnected curves.
- dag/nodes/sec-trace-formula/lem-trf-ordinary-point-delta-branches.json: statement, unsplit; no Mathlib match. Local delta/branch inequality and its ordinary-point equality case.
- dag/nodes/sec-trace-formula/lem-trf-nodal-contraction-normalization-branches.json: statement, unsplit; no Mathlib match. Normalized noncontracted components, boundary branches, and reducedness of the actual fibre at an ordinary target point.
- citations.json: a verbatim statement quotation for every use in all eight proof steps.

## Attachments

None. Searches in /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the item tag, exceptional trees, multipointed curves and ordinary multiple points found no project declaration stating this item. The upstream master source was also searched as reference only; no sorry declaration is treated as finished evidence.

## Wanted literature

WANTED: literature/temkin-stable-modification-arXiv-0707.3953v3.pdf, Appendix B pp. 56--58 and Lemma 4.4.2 pp. 30--31, for this item and all three new nodes. The file is absent locally. I read the primary PDF online at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf (arXiv:0707.3953v3); no file was downloaded into the repository. proof_origin.by is agent, recording the expansion and the missing local archive. Local Stacks varieties.tex (delta-invariant section, Tags 0C3S and 0C3T) and curves.tex (Tag 0C6U, proposition-projective-line) were read as complementary sources, not substituted for the exact Temkin criterion. No SGA source is used.

## Statement dispute and repairs

STATEMENT-DISPUTED: the imported field-curve statement does not state the reduction in Temkin's proof. Appendix B Corollary B.2 explicitly assumes equal arithmetic genera. It uses a proper morphism isomorphic off a contracted connected curve, rather than a modification of curves over the field. The imported statement instead cites the multipointed-modification definition and omits the genus hypothesis.

There is a direct incompatibility in the literal imported hypotheses. For a modification of reduced curves, the inverse image of the isomorphism open is schematically dense in the source. A contracted one-dimensional fibre contains an irreducible component and its generic point. That generic point cannot belong to the inverse image of the isomorphism open. Thus the open cannot be schematically dense. Such a positive-dimensional fibre map is not a modification of the field curves; it is a fibre of a modification of relative curves. I corrected this mismatch to the proper surjective fibre-map hypotheses of B.2.

Under the intended fibre-map interpretation, equal genus is indispensable. Over k=C, attach a smooth elliptic curve E to P1 at one transverse node. Map the P1 component isomorphically onto P1 and map E constantly to the attaching point x. This is proper, surjective and an isomorphism off its connected reduced fibre E, and its source is nodal. The unmarked target is smooth at x, but E is not a projective-line tree. Its source arithmetic genus is one and target arithmetic genus is zero. This is a counterexample to the imported assertion under its intended contraction interpretation, not an example satisfying the incompatible literal modification hypothesis.

B.2 is unmarked. For the marked extension one must preserve the local marking length. A compatible map of finite marking schemes alone does not preserve it. On a rational tail contracted to a smooth point, take one reduced source marking on the tail and a target marking defined at x by the square of its parameter. The source marking maps compatibly to the target marking, and the tree has one boundary and one source mark, but the target marking is nonreduced, so the target pair is not semistable. The repaired statement explicitly assumes dim_k O_{D,x}=|D' intersect Z|, with zero for an absent marking. This is the local marking conservation needed by the relative-curve application; an isomorphism of marking schemes would imply it, but is not required.

I initially phrased this as the length of the fibre D times_C Spec k, then corrected it before delivery: a closed immersion's nonempty fibre over x is Spec k even if D is nonreduced. The relevant object is the local Artinian factor O_{D,x}. Step 7 now uses precisely that object and cites the existing Mathlib etale-algebra-over-field-product leaf for the converse etaleness implication.

The conclusion still refers to the scheme-theoretic Z. Reduction B is only an intermediate object in the genus calculation. The branch lemma proves Z=B when the target point is ordinary, so neither implication substitutes the reduced fibre without justification. The imported duplicate period and unused statement dependencies have also been removed.

The existing parent lem-trf-valuation-exceptional-local-criterion step 4 supplies the equal-genus argument, but its step 5 must apply this repaired fibre-map formulation and justify local marking-length conservation. Its step 2 cannot infer reducedness of an arbitrary scheme fibre merely from reducedness of the ambient curve fibre. That comparison is supplied here after ordinary-point detection. I did not edit the parent or any maintainer-owned field. These application changes need maintenance/review.

## Not duplicates

lem-trf-reduced-curve-normalization-genus vs lem-trf-nodal-curve-normalization-euler: the existing formula assumes a connected nodal curve and counts its nodes; the new formula applies to arbitrary reduced proper curves, using arbitrary local normalization-quotient dimensions. C may be singular and nonnodal at x, so the existing nodal formula cannot supply Step 3.

lem-trf-reduced-curve-normalization-genus vs lem-trf-nodal-contraction-euler-defect: the existing contraction formula requires the target point to be smooth. This split must characterize a target not assumed smooth, including a possible node or worse singularity. The new node concerns one curve and its normalization, not a contraction.

lem-trf-ordinary-point-delta-branches vs lem-trf-curve-normalization-completion: the existing node identifies normalization after completion and proves finite normalization; it does not give delta >= branches-1 or identify its equality case with ordinary multiple points.

lem-trf-nodal-contraction-normalization-branches vs lem-trf-nodal-subcurve-boundary: the existing node identifies nodes and smooth branches at a boundary inside one curve; it says nothing about the target's normalization branches or the pullback of its maximal ideal. The new comparison does not assume or conclude any tree property, equal genus or marked semistability.

lem-trf-nodal-contraction-normalization-branches vs lem-trf-smooth-target-modification-exceptional-tree: the existing node concerns a relative valuation-ring modification over a target smooth point and asserts the exceptional tree; the new comparison concerns a proper map of field curves and identifies normalization branches without rationality or genus conditions.

Whole-DAG text searches, blueprint_refs.py searches for arithmetic genus, normalization genus, ordinary n-fold/ordinary multiple points, boundary branches and nodal subcurve found no blueprint node stating a new input. Existing genus-zero projective-line nodes were reused, not recreated. The new nodes are statement-only. None restates the tree iff semistable criterion: the item carries genus subtraction, graph counting and the marking argument.

The first dry run flags 0707 in the Temkin arXiv filename as if it were a Stacks tag. I read every reported statement; these are shared-source matches rather than duplicate Stacks results. The following explicit pair comparisons satisfy that diagnostic without changing the source filename or the delivery tool. This parser issue is reported for maintenance.

lem-trf-reduced-curve-normalization-genus vs lem-trf-curve-p1-tree-local-criterion: the existing node states the full marked equal-genus tree criterion, whose argument remains in the eight steps; the new node states the normalization cohomology formula for an arbitrary reduced proper curve, which the existing statement does not supply.

lem-trf-reduced-curve-normalization-genus vs def-trf-birational-quasi-modification: the existing node states a definition of birational quasi-modification; the new node states the normalization cohomology formula for an arbitrary reduced proper curve, which the existing statement does not supply.

lem-trf-reduced-curve-normalization-genus vs def-trf-centred-valuation: the existing node states a definition of centred valuation morphisms; the new node states the normalization cohomology formula for an arbitrary reduced proper curve, which the existing statement does not supply.

lem-trf-reduced-curve-normalization-genus vs def-trf-modification: the existing node states a definition of modification and generic-base-change isomorphism; the new node states the normalization cohomology formula for an arbitrary reduced proper curve, which the existing statement does not supply.

lem-trf-reduced-curve-normalization-genus vs def-trf-multipointed-curve-modification: the existing node states a definition of relative multipointed modifications and stability; the new node states the normalization cohomology formula for an arbitrary reduced proper curve, which the existing statement does not supply.

lem-trf-reduced-curve-normalization-genus vs def-trf-multipointed-curve: the existing node states a definition of flat finitely presented marked curves; the new node states the normalization cohomology formula for an arbitrary reduced proper curve, which the existing statement does not supply.

lem-trf-reduced-curve-normalization-genus vs def-trf-multipointed-eta-modification: the existing node states a definition of relative generic modifications of pairs; the new node states the normalization cohomology formula for an arbitrary reduced proper curve, which the existing statement does not supply.

lem-trf-reduced-curve-normalization-genus vs def-trf-nodal-dualizing-datum: the existing node states a definition of normalized local adjunction data for a dualizing module; the new node states the normalization cohomology formula for an arbitrary reduced proper curve, which the existing statement does not supply.

lem-trf-reduced-curve-normalization-genus vs def-trf-rational-rank: the existing node states a definition of the rational rank of an abelian group; the new node states the normalization cohomology formula for an arbitrary reduced proper curve, which the existing statement does not supply.

lem-trf-reduced-curve-normalization-genus vs def-trf-schematically-dense-open: the existing node states a definition of an injective restriction on structure sheaves; the new node states the normalization cohomology formula for an arbitrary reduced proper curve, which the existing statement does not supply.

lem-trf-reduced-curve-normalization-genus vs def-trf-semistable-multipointed-curve: the existing node states a definition of semistable pairs; the new node states the normalization cohomology formula for an arbitrary reduced proper curve, which the existing statement does not supply.

lem-trf-reduced-curve-normalization-genus vs def-trf-semistable-multipointed-pair: the existing node states a definition of semistable pairs and geometric stability; the new node states the normalization cohomology formula for an arbitrary reduced proper curve, which the existing statement does not supply.

lem-trf-ordinary-point-delta-branches vs lem-trf-curve-p1-tree-local-criterion: the existing node states the full marked equal-genus tree criterion, whose argument remains in the eight steps; the new node states a local delta inequality and characterization of ordinary multiple points, which the existing statement does not supply.

lem-trf-ordinary-point-delta-branches vs def-trf-birational-quasi-modification: the existing node states a definition of birational quasi-modification; the new node states a local delta inequality and characterization of ordinary multiple points, which the existing statement does not supply.

lem-trf-ordinary-point-delta-branches vs def-trf-centred-valuation: the existing node states a definition of centred valuation morphisms; the new node states a local delta inequality and characterization of ordinary multiple points, which the existing statement does not supply.

lem-trf-ordinary-point-delta-branches vs def-trf-modification: the existing node states a definition of modification and generic-base-change isomorphism; the new node states a local delta inequality and characterization of ordinary multiple points, which the existing statement does not supply.

lem-trf-ordinary-point-delta-branches vs def-trf-multipointed-curve-modification: the existing node states a definition of relative multipointed modifications and stability; the new node states a local delta inequality and characterization of ordinary multiple points, which the existing statement does not supply.

lem-trf-ordinary-point-delta-branches vs def-trf-multipointed-curve: the existing node states a definition of flat finitely presented marked curves; the new node states a local delta inequality and characterization of ordinary multiple points, which the existing statement does not supply.

lem-trf-ordinary-point-delta-branches vs def-trf-multipointed-eta-modification: the existing node states a definition of relative generic modifications of pairs; the new node states a local delta inequality and characterization of ordinary multiple points, which the existing statement does not supply.

lem-trf-ordinary-point-delta-branches vs def-trf-nodal-dualizing-datum: the existing node states a definition of normalized local adjunction data for a dualizing module; the new node states a local delta inequality and characterization of ordinary multiple points, which the existing statement does not supply.

lem-trf-ordinary-point-delta-branches vs def-trf-rational-rank: the existing node states a definition of the rational rank of an abelian group; the new node states a local delta inequality and characterization of ordinary multiple points, which the existing statement does not supply.

lem-trf-ordinary-point-delta-branches vs def-trf-schematically-dense-open: the existing node states a definition of an injective restriction on structure sheaves; the new node states a local delta inequality and characterization of ordinary multiple points, which the existing statement does not supply.

lem-trf-ordinary-point-delta-branches vs def-trf-semistable-multipointed-curve: the existing node states a definition of semistable pairs; the new node states a local delta inequality and characterization of ordinary multiple points, which the existing statement does not supply.

lem-trf-ordinary-point-delta-branches vs def-trf-semistable-multipointed-pair: the existing node states a definition of semistable pairs and geometric stability; the new node states a local delta inequality and characterization of ordinary multiple points, which the existing statement does not supply.

lem-trf-nodal-contraction-normalization-branches vs lem-trf-curve-p1-tree-local-criterion: the existing node states the full marked equal-genus tree criterion, whose argument remains in the eight steps; the new node states a branch/boundary comparison for a contraction, with no tree or genus assertion, which the existing statement does not supply.

lem-trf-nodal-contraction-normalization-branches vs def-trf-birational-quasi-modification: the existing node states a definition of birational quasi-modification; the new node states a branch/boundary comparison for a contraction, with no tree or genus assertion, which the existing statement does not supply.

lem-trf-nodal-contraction-normalization-branches vs def-trf-centred-valuation: the existing node states a definition of centred valuation morphisms; the new node states a branch/boundary comparison for a contraction, with no tree or genus assertion, which the existing statement does not supply.

lem-trf-nodal-contraction-normalization-branches vs def-trf-modification: the existing node states a definition of modification and generic-base-change isomorphism; the new node states a branch/boundary comparison for a contraction, with no tree or genus assertion, which the existing statement does not supply.

lem-trf-nodal-contraction-normalization-branches vs def-trf-multipointed-curve-modification: the existing node states a definition of relative multipointed modifications and stability; the new node states a branch/boundary comparison for a contraction, with no tree or genus assertion, which the existing statement does not supply.

lem-trf-nodal-contraction-normalization-branches vs def-trf-multipointed-curve: the existing node states a definition of flat finitely presented marked curves; the new node states a branch/boundary comparison for a contraction, with no tree or genus assertion, which the existing statement does not supply.

lem-trf-nodal-contraction-normalization-branches vs def-trf-multipointed-eta-modification: the existing node states a definition of relative generic modifications of pairs; the new node states a branch/boundary comparison for a contraction, with no tree or genus assertion, which the existing statement does not supply.

lem-trf-nodal-contraction-normalization-branches vs def-trf-nodal-dualizing-datum: the existing node states a definition of normalized local adjunction data for a dualizing module; the new node states a branch/boundary comparison for a contraction, with no tree or genus assertion, which the existing statement does not supply.

lem-trf-nodal-contraction-normalization-branches vs def-trf-rational-rank: the existing node states a definition of the rational rank of an abelian group; the new node states a branch/boundary comparison for a contraction, with no tree or genus assertion, which the existing statement does not supply.

lem-trf-nodal-contraction-normalization-branches vs def-trf-schematically-dense-open: the existing node states a definition of an injective restriction on structure sheaves; the new node states a branch/boundary comparison for a contraction, with no tree or genus assertion, which the existing statement does not supply.

lem-trf-nodal-contraction-normalization-branches vs def-trf-semistable-multipointed-curve: the existing node states a definition of semistable pairs; the new node states a branch/boundary comparison for a contraction, with no tree or genus assertion, which the existing statement does not supply.

lem-trf-nodal-contraction-normalization-branches vs def-trf-semistable-multipointed-pair: the existing node states a definition of semistable pairs and geometric stability; the new node states a branch/boundary comparison for a contraction, with no tree or genus assertion, which the existing statement does not supply.

## Unfinished work

The three new inputs are intentionally unsplit, as required by the one-level stage-1 brief. There is no Lean work or compilation. The parent application's hypothesis reconciliation is reported above and remains outside this worker's permitted files. No other part of this item's split remains unfinished.

## Review by Q29

I read Temkin Lemma 4.4.2's proof through the equal-genus reduction, then Appendix B's ordinary-point discussion, Lemma B.1, the full proof of B.2 and the exceptional marked-tree definition. For the general normalization-genus node I checked B.1's exact sequence: taking dimensions gives 1-v plus normalized genera and the lengths of the skyscraper quotient; the formula uses p_a=1-chi, so it also holds for disconnected curves. For the ordinary-point node I read the residue-quotient surjection and equality argument on pp. 56--57. The field is algebraically closed here, so every branch residue is k; the delta invariant is a k-vector-space dimension. The local Stacks delta definition confirms this convention. For the branch node I read B.2's final paragraph: noncontracted normalizations map into C', their points above x reach the boundary, and two such points cannot land on a node with no contracted component passing through it because that would give an isolated component of the connected fibre.

The branch node's reduced-fibre refinement was checked separately. At a boundary node the completed source ring is k[[u,v]]/(uv), with u=0 cutting out B. Ordinary target branch parameters pull back to zero on the contracted branch and to a uniformizer on the unique outside branch; its maximal ideal therefore pulls back to (u), whose quotient is k[[v]]. At a point interior to B the map is constant on each reduced local branch, so its maximal ideal pulls back to zero. Thus the local fibre rings are reduced; faithful flatness of Noetherian local completion descends this statement. The existing normalization-completion and completion-faithfully-flat nodes confirm the standard completion facts for the future split, but they are not cited for stronger conclusions than their statements. This refinement is recorded as agent-stated in the new node's source. It is independent of genus or tree hypotheses and belongs in a separate node rather than hidden in a long proof step.

I opened the complete statement of every item citation. Step 1 uses reduced-induced-closed-subscheme for the actual reduction, nodal-subcurve-boundary for nodality and the boundary geometry, and reduced-curve-normalization-genus for smooth proper normalizations and finiteness. Its pure-dimension and nodal-neighbourhood hypotheses hold for B. Step 2 uses precisely the branch comparison's normalization and boundary clauses, without assuming the target is smooth. Step 3 uses both normalization formulas, the identification of retained component normalizations from the branch node, and the delta-one/zero assertions of the ordinary-point node. I checked the signs: equal genera give delta_C(x)=n-1+(e-v+1)+sum g_i, rather than the smooth-target Euler defect. Every off-fibre term cancels via the given isomorphism.

Step 4 explicitly builds a spanning tree and uses nonnegative vector-space dimensions; it uses no non-elementary uncited graph theorem. Step 5 uses nodal-subcurve-boundary on each reduced component to exclude singularities once self-nodes are excluded. Smooth-normal supplies normality, so normalization is that component; the existing genus-zero-smooth-proper-line theorem applies to its smooth proper connected curve. The converse uses projective-line-genus-zero, whose statement gives exactly H1(P1,O)=0. Step 6 uses the ordinary-point-delta equality test with b=n and the separate branch lemma's reduced-scheme-fibre clause. Neither theorem assumes the conclusion of this item.

Step 7 uses the two pair definitions for the marking and relative-smooth-locus requirements and the existing etale-algebra-over-field-product Mathlib leaf for etale => reduced local k-point. The local marking ring is an Artinian factor of a finite scheme; its single support point and algebraic closure leave exactly one k-factor. Dimension one conversely forces the scalar map k->A_x to be an isomorphism. The length hypothesis is essential and explicit, not inferred from mere compatibility of markings. Step 8 is the three-case integer calculation, and proves both implications.

I tested the statements on a single rational tail, a two-boundary rational bridge, an elliptic tail, an internal loop, a three-boundary rational tree contracted to an ordinary triple point, empty marking and a doubled target marking. Genus subtraction detects elliptic components and loops; the triple-point example has n=3 and fails the exceptional bound while remaining ordinary, exactly as required. A single rational tail and a bridge give reduced scheme fibres at their boundary nodes. In the disconnected genus formula, disjoint P1 components have p_a=1-v, so the constant term is correct. A smooth local ring has b=1, delta=0; a node has b=2, delta=1; a cusp has b=1, delta>0 and fails the ordinary equality test. The branch node excludes empty/zero-dimensional fibres and isolated fibre points by its connected pure-dimensional hypothesis.

All search records are from actual msearch.py calls; the queries and result digests are in searches.jsonl, with second phrasings for all three new inputs. I read the returned signatures and the relative-normalization source in Mathlib; generic properness, relative normalization, Weierstrass discriminants, PowerSeries DVR instances and cotangent exact sequences do not state these curve lemmas. No new Mathlib leaf is claimed. I checked delivery-errors B--E: self-contained statements and explicit notions, genuine non-duplicate auxiliary lemmas, exact citation uses, no proof sketches inside unsplit nodes, no assumption of a smooth target, no hidden reduction of Z, and no circular dependency on the criterion or its parent. All proof steps are below 2000 characters; the substantive normalization comparison is already a new node. Blueprint ancestry retains the historical semistable-alteration input, while the current unit's Varshavsky contracting-correspondence route is not replaced. The generic reduced-subscheme, smooth-normal and P1-genus facts from other units are declared tool uses.

After the first successful server preflight, I removed the unused scheme-theoretic-closure dependency: the boundary is an explicitly defined topological closure. I also named the existing reduced-induced-closed-subscheme construction in the new genus node, added the irreducible-component definition to the local ordinary-point node, and removed an unused cohomology definition from the branch node. These are dependency/citation corrections, with all mathematical arguments unchanged. I reran the final dry run on these exact files before pushing.
