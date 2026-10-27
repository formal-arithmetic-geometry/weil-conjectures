## Worker report

Files written:

- dag/nodes/sec-six-functors-basics/lem-sfb-space-blowup-finite-degree-ideal-descent.json: item, statement unchanged, split into five steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-proj-finite-degree-equations.json: new statement-only node, Stacks 085M; not a Mathlib match.
- citations.json: one verbatim statement quote for every node cited in each numbered proof step.

Attachments: none. The project declaration AlgebraicGeometry.Scheme.IdealSheafData.exists_finiteDegree_center_le_blowup, lean/WeilConjectures/Blowup/FiniteDegree/Main.lean:93, is for schemes, whereas the item permits algebraic spaces. Its exact scheme statement and proof were read; it is not an attachment for this item. Project searches for the item's blueprint tag and for finite-degree ideal descent found no algebraic-space declaration stating the item.

WANTED: none.

The imported statement is correct and is kept verbatim, including all hypotheses and the equality on the first blowup. No smaller hypothesis set, weaker conclusion, reducedness, density, or Noetherian assumption has been substituted. The split uses 085M, the finite-equation theorem without support control, because the support assertion of 085N is unnecessary here. This is the same relative-Proj route as 0860. The new node is a general projective-equation theorem, not an exceptional-power ideal equality or a restatement of a clause of this item. The genuinely global equation choice remains in this unsplit supporting node. The item itself derives the ideal equality by an explicit homogeneous-localization kernel calculation and multiplication on charts.

Nothing remains unfinished in this stage-1 split. The new node intentionally has no proof or proof dependencies. No Lean was written, no compiler/build tools were run, and no repository or launcher files were changed.

## Not duplicates

lem-sfb-space-proj-finite-degree-equations vs lemma-nagata-proj-closed-center-finite-degree-exists: the existing DAG statement is restricted to a Rees algebra over a scheme, with support control; its latest blueprint and project theorem instead give the exceptional-power equality over a scheme. Neither states finite-degree equations for an arbitrary quasi-coherent graded algebra over an algebraic space. The missing global equation theorem cannot be obtained by applying the scheme theorem separately on atlases without proving descent of finite-type submodules.

lem-sfb-space-proj-finite-degree-equations vs def-nagata-proj-closed-center-finite-degree: the existing node specifies the finite-degree choice for a scheme blowup and supplies no existence statement for general relative Proj over spaces.

lem-sfb-space-proj-finite-degree-equations vs lem-sfb-projective-closed-subscheme-homogeneous-ideal: the existing node reconstructs a closed subscheme of projective space over a ring by its full homogeneous ideal; it gives neither finitely many equations in one degree nor an algebraic-space base.

lem-sfb-space-proj-finite-degree-equations vs lem-sfb-space-relative-proj-scheme-tests: the existing node constructs relative Proj and proves base-change comparisons, without finite-degree equations for closed subspaces.

There was no existing node with source Tag 085M or label lemma-closed-subscheme-proj-finite. Searches of the whole DAG for 085M, 085N, the labels, homogeneous ideals and finite-degree equations, and blueprint_refs.py searches for those tags, closed subspace, homogeneous ideal, closed-center-finite-degree and finite-degree were read. The broad Proj/blowup searches identified the scheme nodes above. The new node's same_as is empty because those statements have a different range of objects. The item's same_as is also empty: the nearest blueprint statement is scheme-only. The ancestor command reports blueprint.from.node = None for this inherited non-blueprint chain; its existing null root and full via list are preserved, with the item prepended in the new node.

## Mathlib searches

All searches used the required msearch.py command and are in searches.jsonl. The item has LeanFinder searches with two phrasings, LeanSearch, Loogle, and an AlgebraicGeometry grep. The new Proj node has two LeanFinder phrasings, LeanSearch, Loogle, and two AlgebraicGeometry greps. The JSON entries reproduce the exact query strings and the logged hit lists, counts and digests. All services answered; none was treated as unavailable.

The hits were ordinary scheme ideal images, localization lemmas, Proj topology, and the finite-type/properness instances for ordinary Proj. I read Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean:132-168 and Topology.lean:65-96: finite-type/quasi-compactness instances and zeroLocus/vanishingIdeal do not give scheme-theoretic finite-presentation equations in one degree over spaces. The returned Ideal.FG.pow and fractional-ideal formulas only concern ordinary ring ideals. None is an exact match or a one-line specialization of either statement.

## Source error

In Stacks spaces-divisors.tex, Tag 0860, the sentence following the displayed exceptional-ideal equality says the equality is on X''. Both ideals and the following affine-chart calculation are on X', the first blowup. The item's existing statement already corrects this typo. We prove the equality on T_1 throughout. There is no new statement dispute or change to the item.

## Review by Q67

I read coord/delivery-errors.md B-E, the stage-1 brief and stage document, the three-level route restriction in SETUP.md, GOAL.md, the chapter/unit records, and the latest blueprint unit and finite-degree theorem/proof. The inherited unit is the constructible-six-functor stability unit, through its existing Chow modification prerequisite chain. This split changes no unit step. Its generic off-unit tools are declared in split_report.tool_uses for review; none substitutes another route. I read spaces-divisors.tex Tag 0860 in full, its 085N input, and the simpler 085M statement and proof. The new node states exactly the latter's existence theorem, with the closed subspace lying in P, not X. Its small-etale graded algebra, quasi-coherence, relative Proj, finite-presentation and size notions are introduced or cited explicitly. The source's proof reduces the assertion to schemes and enlarges a local finite-degree module globally; this is substantial and is not labeled elementary or assumed already proved.

For step 1 I opened every cited node statement. The affine-chart calculus computes images and tensor operations on quasi-coherent modules, the kernels/colimits theorem supplies the direct sum, the blowup-properties statement supplies properness, the ideal correspondence supplies V(J) with precisely J as kernel, and the finite-presentation criterion supplies the implication from finite type of J. T is qcqs by hypothesis, I and J are finite type by hypothesis, and the proper morphism is quasi-compact by the given definition. No finite type is inferred for an arbitrary submodule.

For step 2 the new 085M node supplies F in one positive degree and an equality of closed subspaces via the quotient map. Its hypotheses are established in step 1 or are hypotheses of the item. A submodule F of I^d is an ideal under its inclusion into O_T because it is stable under every local function; the finite-type property is the unchanged module property. This is an elementary reinterpretation, not a new lemma.

For step 3 I read the full statements of the affine-chart calculus, relative-Proj scheme-test comparisons, space-blowup chart properties, the Proj standard-open theorem and the ideal correspondence. They give the quotient algebra on U, the base-changed Proj objects, the cover by R[I/a], the degree-zero localized coordinate rings, and the ideal J on base changes, respectively. All base changes here are affine etale chart tests and the open chart inclusions. No arbitrary base change of a Rees algebra is used. No representability or closed-subspace equality is deduced merely from a topological image.

For step 4 I read the cited homogeneous-localization definition. The text proves, rather than cites, the needed quotient-kernel formula: lift homogeneous numerators, use the equality relation for a zero fraction, multiply by more powers to arrange the degree inequality, take the homogeneous component in the generated ideal, then divide each homogeneous product. This shows equality with the generated ideal of m/a^d, including all nilpotents, not just its radical. All exponents and degrees are specified. The standard-open identifications and quotient closed immersion were established in steps 2-3. This is routine algebra on the specified rings; it hides no global existence or descent argument.

For step 5 I read the tensor-pullback definition and checked that multiplication of local tensors gives exactly the extended ideals. The formulas x=a(x/a) and m=a^d(m/a^d) prove both the exceptional principal-ideal formula and the required product equality, without canceling a. Local equality of subsheaves on a covering gives both global inclusions by the sheaf membership condition. Every non-elementary ingredient is a cited statement, and citations.json quotes those statements verbatim for every use. The five step texts are all shorter than 2000 characters; no long step conceals another lemma.

I checked the new theorem for empty X/P/Z, Z=P (take F=0), and Z empty (finite positive-degree equations cover the quasi-compact Proj). The theorem allows graded algebras concentrated in degree zero, when P is empty and F=0 in any positive degree works. For the item: I=O gives p=id and H=J for d=1; I=0 or nilpotent I gives the empty Proj and H=0; J=0 gives H=0; J=O allows H=I^d. On R=k[x,y]/(xy), I=(x), the x-chart kills the x-torsion as localization requires, and the displayed m=a^d(m/a^d) identity remains valid. Thus neither density of the original complement nor regularity of a in the original ring was assumed. The statement is unchanged and the source typo is explicitly identified above. This is my review and signature under the split.
