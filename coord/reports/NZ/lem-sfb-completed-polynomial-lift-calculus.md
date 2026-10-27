# Stage-1 delivery: lem-sfb-completed-polynomial-lift-calculus

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-completed-polynomial-lift-calculus.json: statement, now split; full statement unchanged; eight explicit steps; no full Mathlib match.
- citations.json: one verbatim statement quotation for each step/node citation.
- searches.jsonl: actual msearch records; prepare.py: sandbox-only preparation script.
- No new nodes and no new Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures for the item tag and for completed polynomial rings and continuous derivations. Algebra.polynomial_local_completion_formallySmoothAdic in WeilConjectures/RingTheory/PolynomialLocalCompletionFormallySmooth.lean:58 only gives adic formal smoothness for a one-variable polynomial localization over a Noetherian base. It does not state the continuous-derivation representation or the local-map restriction bijection, so is not an attachment of this item.

## WANTED

None. The relevant Stacks sources are present locally.

## Corrections and scope

No statement correction. In particular there is no identification of S with a power-series algebra over k or with a chosen residue-field section, and no separability assumption has been inserted. The source field may be imperfect and the maximal ideal may have an inseparable residue extension.

The imported node had no proof. The source pointers 07ED and 07NJ explain the formal-smoothness context, but neither alone states the differential representation. The submitted proof is accordingly marked agent-written: it assembles the existing polynomial/localization differential statements, the explicit 07PE extension, completion facts, and the direct quotient-coordinate construction. The square-zero lift is constructed on polynomial generators before localization and completion, avoiding any need to prove a general closed-ideal lifting theorem here.

Blueprint searches were made with tools/blueprint_refs.py for continuous derivations, completion, differentials, polynomial local, and complete module, and by whole-DAG concept/tag inspection. No blueprint node states this item. Read the latest blueprint unit and direct-images proof (3) in literature/blueprint/latest, and the chapter/unit DAG records. The inherited blueprint.from chain ends with node=null; tools/blueprint_refs.py ancestor confirms None. Its detailed place and via chain were retained. This is an inherited metadata limitation, not an invented ancestor; the current blueprint (3) is the direct-image preservation route, while this algebra input belongs to its inherited alteration/deformation refinement. No unit or chapter file is changed.

## Tool uses

lem-weil-pbc-derivation-extends is a generic algebra tool from sk-thm-p1: its statement gives the explicit shifted-coordinate extension of P-valued derivations to the completion. This unit has no derivation-extension statement; the generic tool does not replace a step of the six-functor route. It is declared in split_report.tool_uses. The other non-elementary inputs are existing Mathlib leaves.

## Not duplicates

No new nodes. Reused existing nodes for polynomial differentials, localization of differentials, finite-module completion, completion kernels, Noetherian permanence, and scalar-valued derivation extension. In particular no new node merely restates a clause of the item.

## Review by NZ

I read Stacks algebra.tex at 00RX (lemma-differentials-polynomial-ring), 00RT (lemma-differentials-localize), 05GG (lemma-hathat-finitely-generated), and 00MA (lemma-completion-tensor), and more-algebra.tex at 07PE (lemma-derivation-extends), 07ED (lemma-formally-smooth-completion), and 07NJ (lemma-lift-continuous). I checked the tag-label table. There are no new-node sources to review. I read the statement of every cited DAG node before writing the proof and copied those statements verbatim into citations.json; no step takes an object or a claim that occurs only in a cited proof.

Step 1 uses the existing finite-type and localization Noetherian leaves to show P is Noetherian, then the local-completion and module-completion leaves for the maximal ideal and every quotient kernel. The field case is elementary. The finite-generation hypothesis of the latter leaf holds because p is an ideal of Noetherian P. This supplies density and identifies the topology used later, rather than assuming these from the definition of an inverse limit.

Step 2 uses exactly the polynomial basis and localized differential isomorphism stated by the two cited leaves. Finite tuples commute with compatible sequences coordinatewise, so completing this particular free module requires no extra completion theorem. The r=0 tuple is allowed.

Step 3 uses the scalar-valued derivation-extends statement, not a purported module-valued generalization: coordinate projection of d gives actual P-valued derivations. Its stated formula R/I^(n+1) -> R/I^n proves the continuity estimate after Step 1. The extension vanishes on k coordinatewise. Density and separation of S^r prove uniqueness. Thus no generic continuous-differential lemma is hidden in this step.

Step 4 uses the canonical finite-module tensor/completion isomorphism for Noetherian B and finite M. The map's formula identifies it with the actual completion map of M after B equals its completion. This establishes separation for precisely the m_B-adic topology; I checked that nowhere is completeness for f(m_S)B inferred.

Step 5 explicitly identifies the base-changed finite free module with B^r, constructs the derivation and proves continuity using locality of f and the shifted-power estimate. The tensor universal property cited in this step supplies the coordinate map. Step 6 restricts a continuous derivation to P and uses the cited universal property of Kahler differentials with the already established basis. Equality is tested modulo each m_B^nM and then uses Step 4. The inverse formula and B-linearity are written explicitly, not left as an abstract transport.

Step 7 constructs h-hat in each quotient E/m_E^n. The hypotheses of locality and completeness are used respectively to form h_n and recover a unique element of E. Coordinatewise operations prove it is a k-map; the residue-field map is injective, which proves locality. The kernel computation of Step 1 proves continuity, and separation proves uniqueness. Restriction is therefore genuinely a bijection of local maps, without a residue-field isomorphism assumption.

Step 8 chooses polynomial lifts using surjectivity, proves every required denominator invertible via (1+j)^(-1)=1-j for j in the square-zero kernel, and writes the fraction map. Since a nilpotent ideal lies in the unique maximal ideal, E/J=B identifies the maximal ideals, proving that this particular lift P -> E is local. Step 7 then applies. The two resulting maps to B agree by density, and the quotient map is continuous because it is local. This proves the lifting clause without appealing to a theorem that only lifts discrete maps.

For the B-to-E map I checked the zero-kernel and nonzero square-zero cases; for the polynomial source I checked r=0, a k-rational maximal ideal, and k of characteristic p with q=(x^p-a), a not in k^p. In the last case the completed scalar derivation still has partial(x)=1 and partial(x^p-a)=0, so the proof does not smuggle in a separable coefficient-field splitting. M=0 gives zero on both sides. All eight steps are below 2000 characters (maximum 1061); none hides a new non-elementary comparison or an unstated lemma. The cited DAG branches go down to pre-existing definitions and contain no dependency on this item.

I checked delivery-errors B-E: statements and hypotheses are self-contained, TeX is singly escaped, no new nodes or fake searches were supplied, all citations say what the steps use, no clause has been renamed as a new node, and every non-elementary input is cited. Mathlib searches were run using msearch.py and the results read. The completion lift hits concern compatible maps into a completed target, and the derivation hits concern ordinary polynomial derivations; they do not give a full leaf for this item. I read the relevant actual declarations in AdicCompletion/Algebra.lean:361, AdicCompletion/RingHom.lean:48, Algebra/MvPolynomial/Derivation.lean, Etale/Kaehler.lean:63, Kaehler/Polynomial.lean:60, and AdicCompletion/AsTensorProduct.lean:328.

## Unfinished work

None in the split. The maintainer's independent mathematical review remains the normal next stage. No Lean was written and no compiler, Lake or build tool was run. All writes were confined to this item sandbox.

## Validation

The required server review_split check passed with zero new nodes. Full dry run and direct delivery follow this report.
