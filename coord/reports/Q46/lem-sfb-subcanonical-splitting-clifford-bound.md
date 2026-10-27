# Stage-1 delivery: lem-sfb-subcanonical-splitting-clifford-bound

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-subcanonical-splitting-clifford-bound.json: split item, original statement unchanged, five proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-subcanonical-residual-duality.json: statement-only prerequisite, unsplit, no Mathlib match; false splitting-index clause removed.
- dag/nodes/sec-six-functors-basics/lem-sfb-extremal-cluster-residual-nesting.json: statement-only prerequisite, unsplit, no Mathlib match; union-stratum hypothesis explicit.
- dag/nodes/sec-six-functors-basics/lem-sfb-extremal-cluster-moving-component.json: retained statement-only prerequisite, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-component-rank-one-cluster-dimension.json: retained statement-only prerequisite, unsplit, no Mathlib match.
- citations.json: literal quotations from every node used by every proof step, renumbered for the repaired proof.

The returned proof and citations are preserved in returned-head.json, and its report in report.returned.md. Existing searches and all old Mathlib-search records are retained; the nesting node additionally records the five actual searches for its changed statement. These supporting scratch files are not extra DAG nodes.

## Attachments

None. Rechecked lean/WeilConjectures/ for the item tag, subcanonical clusters, residual clusters and Clifford bounds/indices. Hits for subcanonical Grothendieck topologies and Clifford algebras do not state the item or these prerequisites. No Lean was written or compiled.

## WANTED

WANTED: Franciosi--Tenni, On Clifford's theorem for singular curves, Proc. London Math. Soc. 108 (2014), 225--252, local file literature/franciosi-tenni-clifford-singular-curves-2014.pdf; Definition 2.10, Remarks 2.12--2.13, Lemmas 3.1, 3.3, 3.6 and Theorem 3.7, for the item and all four prerequisites. I read the author-hosted primary PDF at https://pagine.dm.unipi.it/franciosi/lavori/clifford.pdf online. Nothing was downloaded into the repository or sandbox. The missing local PDF and the agent correction are reflected in proof_origin.by = agent.

## Findings and route

The item's statement is retained verbatim. The correction is to a new auxiliary statement and a missing hypothesis in another auxiliary statement, not to the target inequality. The downstream lem-sfb-nodal-two-connected-clifford already uses this item and is deliberately not cited.

I compared the sandbox item with current main: main still has the unsplit item, no repair-note file is present, and no new field or statement change on main needs transplantation. Before editing I ran the required initial dry run on the retained delivery; it exited OK at 4a8f4151620. That was only a mechanical baseline, not a repair of the returned mathematical faults. The actual repair below changes two prerequisite statements, the section-selection argument, the citation file and this review.

I read the chapter and unit records, SETUP's three levels, GOAL.md, the worker brief, stages/1-dag.md and delivery-errors B--E in full, including the duplicated historical B--E. I read the current literature/blueprint/latest/ chapter text and sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. This auxiliary curve argument remains below the inherited stable-curve/direct-image route. The ancestor command still returns the inherited null provenance. The delivery preflight requires its literal result for the new nodes, so all five delivered nodes preserve blueprint.from.node = null, with the full inherited via chains and detailed places naming det-thm-sf-ctf-stability-direct-images retained. I tested an explicit anchor to that extant blueprint node, but the preflight rejected it as differing from the computed nearest ancestor; it has been restored to null. The unit is not realized by this auxiliary item; no unit record is changed.

## Source error

STATEMENT-DISPUTED: the returned residual-duality node's clause r(S*)=r(S) is false for def-sfb-subcanonical-splitting-index. I removed precisely this clause. I also read Remark 2.18 in the primary PDF; its asserted residual invariance cannot be imported for the DAG's supported-section-space definition.

Here is the maintainer's counterexample, checked against that definition. Let X be two smooth curves C1,C2 of genera g1,g2 at least one, meeting at two transverse nodes n1,n2. The curve is nodal and two-connected, and p=g1+g2+1. For S the reduced point n1, vanishing there kills its residues; the residue theorem then kills the residues at n2. Thus V_S=H0(K_C1) direct sum H0(K_C2), so r(S)=1. For generic s=(sigma1,sigma2), the residual has the maximal-ideal point at n1, a coupled Cartier scheme of length two at n2, and the divisors of sigma_i elsewhere. Its length is 2p-3 and its canonical section space is k times s. Consequently r(S*)=0. Its complementary length, section-dimension difference and Clifford index are exactly those retained in the repaired residual lemma. Double residual and h0(omega)=p are also retained.

Splitting index is not treated as monotone. On a three-cycle of smooth components, the empty cluster has index zero by the explicit convention, whereas the cluster consisting of one node has index two. Neither residual invariance nor monotonicity appears in the repaired item's argument.

## Repair of E1/route

Selection is explicitly over Sigma_R, the set of all subcanonical clusters of splitting index at most R=r(T). It does not assume this set is closed under residuals. Minimize c and then maximize length there, exactly as specified in the nesting lemma. This is possible because the residual numerical formulas bound the finite set of integer pairs (c,length). T belongs to the class, so the selected S has c(S)<=c(T)<0 and r(S)<=R.

The extra condition needed to apply maximality is now an explicit hypothesis of lem-sfb-extremal-cluster-residual-nesting: for the given residual, the scheme-theoretic union U=S union S* must be subcanonical and satisfy r(U)<=R. The lemma no longer asserts a generic-section open with that hypothesis concealed.

Here is a proof check of this corrected prerequisite, included for the future worker and independent reviewer; the node itself remains statement-only. Set B=S intersection S*. Both U and B lie in the canonical Cartier zero divisor D of s. Modulo its ideal, S and S* are mutual annihilators in the Artinian Gorenstein ring of D. The annihilator of their sum is the intersection of their annihilators, so B and U are mutually residual with respect to the same s. Thus their lengths sum to 2p-2 and c(B)=c(U). The canonical ideal sequence

0 -> F_U -> F_S direct sum F_S* -> F_B -> 0

is exact, with maps inclusion and difference. Left exactness on sections gives v(S)+v(S*)<=v(U)+v(B). For complementary residual lengths the two sides respectively equal p+1-c(S) and p+1-c(U). Therefore c(U)<=c(S). The explicit union-stratum hypothesis gives the opposite inequality by minimality, so equality holds. Maximal length in Sigma_R gives length(U)<=length(S). Since U contains S, their ideals are equal, and S* is contained in S. No bound on r(B) or r(S*) has been used. This repairs the precise gap in the source Lemma 3.1's stratum comparison, rather than presupposing its false Remark 2.18.

The item proves the missing union hypothesis by elementary finite-dimensional linear algebra. For each partition P with more than R+1 blocks, W_P is the direct sum of the supported subspaces of V_S. It is a proper subspace because otherwise P would be admissible for S. Choose s outside all these finitely many subspaces. The residual construction puts s in V_S*, by evaluating the inclusion F_S -> omega, so s is in V_U and makes U subcanonical. If U admitted P, its decomposition of s would put s in W_P, since V_U is contained in V_S. This is impossible. Hence r(U)<=R. This is a generic-section witness argument, not a monotonicity assertion about arbitrary subspaces or clusters.

## Not duplicates

lem-sfb-subcanonical-residual-duality vs lem-sfb-nodal-line-serre-riemann-roch: the latter gives Serre duality and line Riemann--Roch, without constructing residual clusters or their complementary-length and section formulas. The corrected node does not assert splitting-index invariance.

lem-sfb-subcanonical-residual-duality vs lem-sfb-reduced-curve-dualizing-module: the latter provides a representing dualizing module and generic torsion-freeness, not residual ideals and their numerical identities.

lem-sfb-extremal-cluster-residual-nesting vs lem-sfb-nodal-dual-support-dichotomy: the latter concerns collective generic support of Hom(M,omega) for an invertible M, not containment of an extremal cluster's residual under an explicit union-stratum bound.

lem-sfb-extremal-cluster-moving-component vs lem-sfb-general-section-cluster-strict-bound: the latter is a hyperplane-section multiplication input and does not assert the moving residual's length-two and section-dimension conclusion.

lem-sfb-component-rank-one-cluster-dimension vs lem-sfb-nodal-linear-series-base-colength: the latter concerns the base ideal and boundary colength for an invertible linear series, not dimension from rank-one canonical restrictions for arbitrary ideals or its residual-degree lower bound.

lem-sfb-component-rank-one-cluster-dimension vs def-sfb-subcanonical-splitting-index: the definition specifies supported summands and their largest admissible partition, not the rank-one dimension calculation or degree estimate.

All four prerequisites vs lem-sfb-subcanonical-splitting-clifford-bound and lem-sfb-nodal-two-connected-clifford: none states either Clifford inequality or a clause of the item. They supply residual numerical identities, conditional nesting, moving-component exclusion and rank-one dimension/degree. The downstream Cartier theorem is not used and no dependency cycle is created.

Whole-DAG and blueprint searches by subcanonical, residual, Clifford and the paper title were reused from the earlier attempt and repeated for the changed residual/nesting questions. Blueprint search returns no duplicate canonical-cluster theorem; broad residual hits concern unrelated sheaf or representation constructions. No Stacks tag is newly attached to a node, and there are no additional same-tag pairs. Stacks 0AYW reached through the splitting definition is the general degree-by-components fact, as accepted in the return; no trace formula or Poincare duality is used. No SGA source is cited.

## Review by Q46

I checked both numbered mathematical return points against the actual node files and the primary PDF. For residual duality I read Definition 2.10 and Remarks 2.12--2.13, retained the evaluation construction, complementary lengths, section dimensions, equal Clifford indices, double residual and finite-dimensionality, and explicitly excluded Remark 2.18's false assertion. For nesting I read Lemma 3.1 and replaced its unsupported stratum comparison by the union hypothesis and the proof check above. For the retained moving-component node I read Lemma 3.3, printed pp.236--238, including both rank hypotheses and its numerical conclusion; its statement is unchanged. For the rank-one node I read Lemma 3.6(i),(ii), printed pp.240--242, and used B=X, so the nonreduced extra-component arguments are unnecessary. I also read Theorem 3.7 (9) and Step 1 Cases 1--2, printed pp.242--244, to check the numerical assembly.

Step 1 uses the residual-duality statement's finiteness, h0(omega)=p and complementary-length bound, and the splitting definition's nonnegative integer index. The inequality v(U)<=p is the inclusion of ideal sections into canonical sections. The finite-pair extremum requires no Hilbert scheme or parameter-space compactness. The chosen S really satisfies all of the nesting and moving nodes' universal extremality hypotheses over the same Sigma_R, which I verified explicitly.

Step 2 uses the residual length and section-difference formulas for the endpoints; c(S)<0 then gives the nontriviality bounds required by the moving node. The splitting definition supplies precisely the supported subspaces and finite set of partitions used in W_P. The sum is direct because supports are disjoint and X is reduced; hence equality with V_S would mean admissibility. Properness follows from r(S)<=R. The moving node supplies the nonempty open also imposed on s. The finite-product-of-polynomials argument written in the step proves simultaneous choice, including over algebraic closures of finite fields, which are infinite. This is one routine linear-algebra selection argument, not a hidden geometric comparison theorem.

Step 3 uses the residual node's evaluation-at-s construction, not an unstated claim about which section makes the residual subcanonical: the inclusion F_S -> omega evaluates to s itself. The ideal intersection gives V_U=V_S intersection V_S*. I checked that a supported decomposition of s inside V_U is also one inside V_S, which is the precise reason for the union bound. Since U contains the nonempty S, the exceptional empty-cluster convention never intervenes in the largest-partition argument. The corrected nesting statement says exactly what is taken: union subcanonical, r(U)<=R, extremality and c(S)<0 imply S* contained in S. All those hypotheses have been proved before it is cited.

Step 4 uses ideal inclusion inside omega and hence inclusion of the actual restriction images on every component. It does not tensor-restrict a noninvertible ideal and discard torsion. The moving statement's two rank-at-least-two assumptions therefore follow if V_S has rank at least two. Its length-two and p-1-section conclusions give c(S*)=0, contradicting the corrected residual lemma's c(S*)=c(S)<0. Subcanonicity gives nonzero rank on every component, leaving rank exactly one. Although the source proof of Lemma 3.3 also refers to the invalid Remark 2.18, no residual-index equality is part of our retained statement or the item's application. For the strict-negative branch in force here there is also a direct consistency check: corrected nesting holds for an open set of s. Then every such s has all canonical zeros supported on the fixed finite S; on a component two independent restrictions would give a nonconstant ratio on its smooth normalization, whose general pencil members have zeros outside that finite set. Thus rank at least two cannot occur in this branch. This explains why retaining the moving conclusion does not reintroduce the refuted invariance.

Step 5 uses the rank-one node's two exact conclusions, v(S)=q+1 and d>=q for q>0; for q=0 the complementary length alone gives d>=0. I checked c=d-2q and the direction -q>=-R. The last comparison c(T)>=c(S) is the selection from step 1. The item is unchanged on Cartier/non-Cartier or reduced/nonreduced clusters.

Small cases: the supplied two-node counterexample now satisfies every retained residual formula, and its unequal indices are allowed. The three-cycle example is compatible with the proof because it makes no arbitrary monotonicity inference. For an irreducible curve there is no forbidden multiblock partition, and the construction reduces to ordinary generic section choice with r=0. If R is at least the number of components minus one, the forbidden-partition list is empty and the union bound is automatic. Empty and full-canonical-length clusters have c=0 and never enter the selected negative case. Genus zero admits no subcanonical cluster; genus one forces length zero. The argument allows non-Cartier node ideals, and characteristic two causes no division in k: halves in the final inequality are rational numbers.

For B--E: all four new nodes are self-contained statements only, with empty proof and proof_deps; their definition references and hypotheses were reread. No whole-inequality substitute or elementary extra node was introduced. The finite-partition argument stays in the item because it is directly the definition plus proper-subspace avoidance. All five steps are shorter than 2000 characters. All uses pairs have literal statement quotes in citations.json, verified locally as substrings. I retained the earlier searches after reading their actual results, and ran five additional searches for the changed nesting statement, including two semantic phrasings, Loogle, grep and LeanSearch. The new hits are covers, affine zero loci, transition limits, profinite constructions or unrelated convex duality; none is an exact theorem or a one-line specialization here. Existing searches cover the unchanged item, residual numerical formulas, rank-one and moving statements; no service failure is called absence. There are zero Mathlib leaves.

The initial baseline dry run and repaired server review_split both exited successfully. Intermediate full checks required formula quotations of at least 40 characters and preservation of the computed null ancestor; both diagnostics were repaired in the sandbox. Final full dry run and push are performed after this report is written; only the delivery tool's final output is treated as the delivery receipt. All writes are confined to this sandbox, and no repository git command, local forbidden checker, compiler, Lake or build command was used.

## Unfinished work

No part of the one-level split remains unfinished. The four prerequisites intentionally remain statement-only future items. The source-error correction is explicit and the target statement is unchanged.
