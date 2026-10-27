# Q46 stage-1 delivery: lem-sfb-qs-space-rational-point-topology

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-qs-space-rational-point-topology.json: original statement unchanged; four-step split.
- dag/nodes/sec-six-functors-basics/lem-sfb-qs-space-field-monomorphism.json: statement; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-reduced-singleton-field-factorization.json: statement; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-decent-algebraic-field-image-closed.json: statement; no Mathlib match.
- citations.json: a verbatim statement quote for every step/use pair.

## Attachments

None. Searched the project under lean/WeilConjectures both for the item tag and for rational points, algebraic spaces, decent spaces, residual spaces and singleton-image factorization. The relevant hits are scheme results or tangential docstrings; no declaration states all the algebraic-space clauses. No Lean was written or compiled.

## WANTED

None. All mathematical sources used are in literature/stacks-project/.

## Findings and unfinished work

The imported item is correct, including arbitrary K and the absence of finite-type and reducedness assumptions on Z. Its proof was empty. The blueprint ancestor tool prints None for this inherited chain; retained its null ancestor and inherited via chain, and extended that chain for children. Read the current latest unit and direct-image proof (3); the current file is sk-thm-sf-ctf-stability-direct-images.proof.md with frontmatter of = det-thm-sf-ctf-stability-direct-images. This general topology input supports the inherited alteration/moduli chain; no chapter or unit file changed.

The new inputs are deliberately unsplit statement-only nodes. No proof dependency is hidden inside their statements. Their eventual proofs follow the Stacks arguments below. No uncompleted work remains at this one-level split beyond those queued inputs and the maintainer's independent review.

## Review by Q46

I read delivery-errors B--E in both copies, the worker brief, stage-1 contract, the three blueprint levels in SETUP, GOAL, the recorded chapter/unit and the current latest blueprint unit/direct-image proof. I checked the algebraic-space definition, the atlas topology conventions, the full affine-spectrum interface, and the Stacks source around Tags 03JX, 03JV, 03I8, 03K4, 0H1R, 0H1T and 07U5 in decent-spaces.tex. The source supports general base schemes for the inputs; the relative quasi-compact diagonal is the hypothesis of quasi-separatedness used by 03JX. The definition tag was initially mistyped 03I9 and was corrected to 03I8 after checking tags/tags.

Step 1 uses lem-sfb-qs-space-field-monomorphism exactly for a quasi-compact monomorphism representing the selected point. Its base is Spec K, so the item's diagonal hypothesis is exactly the required one. def-weil-affine-spectrum explicitly identifies maps of affine spectra with ring homomorphisms, giving K to F.

Step 2 uses lem-sfb-reduced-singleton-field-factorization with Y = Spec K. Reducedness is proved directly: a nilpotent nonzero field element is invertible and cannot have zero power. Both a and b have image the chosen singleton. The child states factorization for any reduced space, not merely a field, and uniqueness over S. Its fixed monomorphism hypothesis is essential. The affine-spectrum node states the ring/morphism correspondence and its functoriality, so the over-K equation gives h composed with i equal to the identity.

Step 3 is elementary, not another node. The kernel/inverse argument is written out, as is the equality h' = h using surjectivity of i. The cited affine-spectrum statement supplies uniqueness of the corresponding affine morphism. A field embedding with retraction cannot have a proper image: i(h(u)) = u follows by injectivity of h. This is the missing arithmetic content between residual factorization and injectivity, rather than a relabelled injectivity clause.

Step 4 uses the field-monomorphism input for all points, exactly the decency condition imposed in the closed-image input. That latter statement is the full 07U5 result for an arbitrary closed base point and algebraic field extension, not the rational-point clause restated. The affine-spectrum node says Spec K has one point with residue field K. The singleton is the whole base and hence closed; identity K to K is algebraic by T-u. Thus no local-finite-type, Jacobson, or algebraic-closedness hypothesis is smuggled in. The conclusion is closedness in the atlas topology already fixed by the item.

For the field-monomorphism input I read 03JX's implication (eta) to (gamma) and 03JV condition (4). This is a genuine general representability assertion for arbitrary space points, not elementary or an item clause. For singleton factorization I read the complete 0H1T proof and 0H1R: the latter identifies the residual space with the given field spectrum; the former factors reduced-source maps into it. The proof reduces through a locally closed scheme stratum and then scheme factorization through a point; these nontrivial constructions remain the child's future split. For closedness I read the complete 07U5 proof: lift a specialization in an etale chart, pass to Spec L times_X U, use the finite separable chart residue extension and scheme closedness over an algebraic residue extension, then show the specialization is trivial. The decency formulation by field monomorphisms is 03JV(4) and 03I8, so its hypothesis is explicit rather than undefined jargon.

Small cases: empty Z gives empty rational-point set; Spec K and nonreduced dual numbers give the expected singleton and unique section. Infinite disjoint unions of K-spectra need no finite type. A doubled-origin line has distinct closed rational origins, so nonseparatedness is allowed without losing injectivity. The generic point of A1 over K has residue K(t), and supplies no K-map retraction, so does not contradict closedness. The closed-image input permits infinite algebraic extensions; the factorization input requires reduced Y, avoiding maps from dual numbers with nonzero tangent image. A K-field endomorphism need not be the identity abstractly, but over-K compatibility forces it here.

For B: each child introduces all its objects, defines monomorphism/quasi-compactness/reducedness or algebraicity inline, and cites the actual notion nodes. Tags and labels were checked; no SGA source is used. Searches are the exact command-log queries, with second natural-language phrasings. Scheme residue-field and closed-point hits were read in Mathlib AlgebraicGeometry/ResidueField.lean and AlgClosed/Basic.lean: they do not concern algebraic spaces; the latter also imposes locally finite type and algebraic closedness. PointsPi.lean concerns maps out of a product of rings, not the map in this item.

For C: every step's dependency statement was read and each citation quote is verbatim; proof_deps is the union of uses. The new children do not depend on the item, so no reverse cycle is introduced. The spectrum definition is a generic existing interface, declared as a tool use in split_report. For D: the injectivity calculation remains in the item; the children state field representatives, general reduced-source factorization, and general algebraic closed-base-point images. For E: checked hypotheses and objects as above. All four steps are below 2000 characters; none conceals an additional independent comparison argument.

## Not duplicates

lem-sfb-qs-space-field-monomorphism vs lem-sfb-space-topological-dimension-local-rings: The new assertion supplies a quasi-compact field monomorphism for every point; the existing statement concerns Topological dimension of a quasi-separated algebraic space as a supremum of local-ring dimensions. Its statement does not supply this general input.

lem-sfb-qs-space-field-monomorphism vs lem-sfb-quasiseparated-space-sober: The new assertion supplies a quasi-compact field monomorphism for every point; the existing statement concerns Sobriety of a quasi-separated algebraic space. Its statement does not supply this general input.

lem-sfb-qs-space-field-monomorphism vs lem-sfb-space-relative-dimension-base-change: The new assertion supplies a quasi-compact field monomorphism for every point; the existing statement concerns Geometric fibre dimension bounds for algebraic spaces under base change. Its statement does not supply this general input.

lem-sfb-qs-space-field-monomorphism vs lem-sfb-space-eventually-fibre-dimension: The new assertion supplies a quasi-compact field monomorphism for every point; the existing statement concerns Eventual geometric fibre dimension bound for finitely presented algebraic spaces. Its statement does not supply this general input.

lem-sfb-qs-space-field-monomorphism vs lem-sfb-quasiseparated-space-atlas-dimension: The new assertion supplies a quasi-compact field monomorphism for every point; the existing statement concerns Topological dimension computed on a surjective etale atlas of a quasi-separated space. Its statement does not supply this general input.

lem-sfb-qs-space-field-monomorphism vs lem-sfb-space-fibre-dimension-base-change: The new assertion supplies a quasi-compact field monomorphism for every point; the existing statement concerns Geometric fibre dimension bounds for algebraic spaces survive base change. Its statement does not supply this general input.

lem-sfb-qs-space-field-monomorphism vs lem-sfb-space-etale-maximum-degree: The new assertion supplies a quasi-compact field monomorphism for every point; the existing statement concerns Bounded fibres and the maximum-degree open of an affine etale atlas. Its statement does not supply this general input.

lem-sfb-qs-space-field-monomorphism vs lem-sfb-quasiseparated-space-dense-scheme-open: The new assertion supplies a quasi-compact field monomorphism for every point; the existing statement concerns A dense open scheme in a relatively quasi-separated algebraic space. Its statement does not supply this general input.

lem-sfb-qs-space-field-monomorphism vs lem-sfb-quasiseparated-space-etale-specializations: The new assertion supplies a quasi-compact field monomorphism for every point; the existing statement concerns Specialization lifting and noncollapse in etale charts of a quasi-separated space. Its statement does not supply this general input.

lem-sfb-qs-space-field-monomorphism vs lem-sfb-locally-separated-rational-point-closed-immersion: The new assertion supplies a quasi-compact field monomorphism for every point; the existing statement concerns Rational points of locally separated algebraic spaces are closed immersions. Its statement does not supply this general input.

lem-sfb-qs-space-field-monomorphism vs lem-sfb-qcqs-space-integral-scheme-cover: The new assertion supplies a quasi-compact field monomorphism for every point; the existing statement concerns Integral surjective scheme cover of a qcqs algebraic space. Its statement does not supply this general input.

lem-sfb-qs-space-field-monomorphism vs lem-sfb-space-etale-atlas-topological-dimension: The new assertion supplies a quasi-compact field monomorphism for every point; the existing statement concerns Topological dimension of a quasi-separated space is computed by an etale scheme atlas, including after base change. Its statement does not supply this general input.

lem-sfb-qs-space-field-monomorphism vs lem-sfb-adequate-geometric-fibres-submersion: The new assertion supplies a quasi-compact field monomorphism for every point; the existing statement concerns Topology and geometric fibres of an adequate moduli space. Its statement does not supply this general input.

lem-sfb-qs-space-field-monomorphism vs lem-sfb-decent-space-finite-field-map: The new assertion supplies a quasi-compact field monomorphism for every point; the existing statement concerns Finite residue extensions give finite maps to decent spaces. Its statement does not supply this general input.

lem-sfb-qs-space-field-monomorphism vs lem-sfb-space-weak-chow: The new assertion supplies a quasi-compact field monomorphism for every point; the existing statement concerns Weak Chow lemma for a separated finite-type algebraic space over an affine scheme. Its statement does not supply this general input.

lem-sfb-qs-space-field-monomorphism vs lem-sfb-locally-separated-space-decent: The new assertion supplies a quasi-compact field monomorphism for every point; the existing statement concerns Locally separated algebraic spaces are decent. Its statement does not supply this general input.

lem-sfb-qs-space-field-monomorphism vs lem-sfb-qs-space-rational-point-topology: The new assertion supplies a quasi-compact field monomorphism for every point; the existing statement concerns Topology of rational points of quasi-separated algebraic spaces. Its statement does not supply this general input.

lem-sfb-qs-space-field-monomorphism vs lem-sfb-space-quasifinite-source-dimension-bound: The new assertion supplies a quasi-compact field monomorphism for every point; the existing statement concerns Dimension bound for a scheme locally quasi-finite over a quasi-separated algebraic space. Its statement does not supply this general input.

lem-sfb-qs-space-field-monomorphism vs lem-sfb-space-qc-etale-fibre-bound: The new assertion supplies a quasi-compact field monomorphism for every point; the existing statement concerns Uniform geometric fibre bound for an etale scheme chart. Its statement does not supply this general input.

lem-sfb-decent-algebraic-field-image-closed vs lem-sfb-locally-separated-closure-equivalent-images: The new assertion is closedness for arbitrary algebraic residue extensions over a closed base point under the explicit decency condition; the existing statement concerns Locally separated targets identify closure-equivalent geometric points. Its statement does not supply this general input.

lem-sfb-decent-algebraic-field-image-closed vs lem-sfb-locally-separated-rational-point-closed-immersion: The new assertion is closedness for arbitrary algebraic residue extensions over a closed base point under the explicit decency condition; the existing statement concerns Rational points of locally separated algebraic spaces are closed immersions. Its statement does not supply this general input.

lem-sfb-decent-algebraic-field-image-closed vs lem-sfb-adequate-geometric-fibres-submersion: The new assertion is closedness for arbitrary algebraic residue extensions over a closed base point under the explicit decency condition; the existing statement concerns Topology and geometric fibres of an adequate moduli space. Its statement does not supply this general input.

lem-sfb-decent-algebraic-field-image-closed vs lem-sfb-decent-space-finite-field-map: The new assertion is closedness for arbitrary algebraic residue extensions over a closed base point under the explicit decency condition; the existing statement concerns Finite residue extensions give finite maps to decent spaces. Its statement does not supply this general input.

lem-sfb-decent-algebraic-field-image-closed vs lem-sfb-locally-separated-space-decent: The new assertion is closedness for arbitrary algebraic residue extensions over a closed base point under the explicit decency condition; the existing statement concerns Locally separated algebraic spaces are decent. Its statement does not supply this general input.

lem-sfb-decent-algebraic-field-image-closed vs lem-sfb-qs-space-rational-point-topology: The new assertion is closedness for arbitrary algebraic residue extensions over a closed base point under the explicit decency condition; the existing statement concerns Topology of rational points of quasi-separated algebraic spaces. Its statement does not supply this general input.

lem-sfb-reduced-singleton-field-factorization vs lem-sfb-adequate-geometric-fibres-submersion: The new assertion is reduced-source factorization through a fixed field monomorphism; the existing statement concerns Topology and geometric fibres of an adequate moduli space. Its statement does not supply this general input.

lem-sfb-reduced-singleton-field-factorization vs lem-sfb-qs-space-rational-point-topology: The new assertion is reduced-source factorization through a fixed field monomorphism; the existing statement concerns Topology of rational points of quasi-separated algebraic spaces. Its statement does not supply this general input.

Whole-DAG keyword and tag searches, plus blueprint_refs searches for rational point, decent, residual space, monomorphism and algebraic residue, found no existing statement that subsumes a new input. In particular the locally-separated rational-point closed-immersion statement assumes an immersion diagonal, absent here; finite-field-map needs finite rather than arbitrary algebraic extension and states finiteness rather than this general closed-image input. The dimension, sobriety and etale-chart specialization nodes do not state residual factorization.
