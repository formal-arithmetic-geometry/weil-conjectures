# Stage-1 split: lem-coef-infinity-pointwise-adjoint-criterion

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-pointwise-adjoint-criterion.json`: item, now split in four steps, statement unchanged; no Mathlib match for arbitrary infinity categories.
- `dag/nodes/sec-six-functors/lem-coef-infinity-pointwise-yoneda-evaluation.json`: new statement-only node, unsplit; no Mathlib match. It states evaluation against arbitrary space-valued presheaves, including the covariant form and the inverse formula.
- `citations.json`: verbatim statements for each citation in each of the four steps.
- `searches.jsonl`: actual searches recorded by msearch.py. The sandbox also contains the isolated JSON-writing script `write_split.py`; it is not a delivered project file.

One new node, zero Mathlib leaves. No unit record is changed: the item is a subsidiary foundation, not its unit's key statement.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag and the notion, and for the proposed new id. The project Yoneda/adjunction extensions are ordinary category results. They do not state this item for arbitrary quasicategories with equivalences of full mapping spaces. No Lean source was written or compiled; master sorry declarations were not treated as proofs.

## WANTED

WANTED: an archived copy of Lurie, Higher Topos Theory, Proposition 5.2.4.2 and Definition 5.2.2.7 / Proposition 5.2.2.8, for lem-coef-infinity-pointwise-adjoint-criterion. The item's existing online source was read at https://www.math.ias.edu/~lurie/papers/HTT.pdf .

WANTED: an archived copy of Kerodon Proposition 6.2.6.1 (https://kerodon.net/tag/02FV) and Proposition 6.2.1.17 (https://kerodon.net/tag/02F1), for lem-coef-infinity-pointwise-adjoint-criterion and its existing local-criterion dependency.

WANTED: an archived copy of Kerodon Proposition 8.3.1.3 (https://kerodon.net/tag/03M5), Notation 8.3.1.2, Definition 5.6.6.1 (https://kerodon.net/tag/038A) and Theorem 5.6.6.13 (https://kerodon.net/tag/038J), for lem-coef-infinity-pointwise-yoneda-evaluation.

These are infinity-category results, with no matching Stacks tags. The alphanumeric identifiers above are Kerodon identifiers, not Stacks citations. Nothing was downloaded or written to literature/. Since the supporting references are online rather than archived, the expanded proof has agent provenance, tied to the current blueprint paragraph.

## Problems and corrections

The imported item was unsplit and is mathematically correct. I did not change its statement. The covariant use of “representable” means corepresentable, namely Map_E(l_c,-), which the proof writes explicitly. There is no statement dispute.

The shared checkout's old DAG snapshot initially did not contain the assigned item. The current read-only mirror `/home/ubuntu/weil-nt-live-dag/nodes/` does, together with its recent foundational dependencies. I copied the item from that mirror and searched both snapshots. Delivery uses its own temporary worktree to check the current authoritative overlay.

The returned delivery reported that the identifier `lem-coef-infinity-yoneda-evaluation` already exists in the authoritative DAG, created by Q55 for a narrower contravariant evaluation statement. I therefore renamed this split's stronger node to `lem-coef-infinity-pointwise-yoneda-evaluation` and updated the item's proof, proof dependencies, citations, and review references. The existing Q55 node remains in place and is compared explicitly below.

A possible false shortcut was ruled out: lem-coef-infinity-yoneda-presheaf-limits states full faithfulness of Yoneda, not evaluation against an arbitrary presheaf. It therefore cannot justify extraction of the universal arrow here. The new general evaluation node supplies exactly that missing input. Neither ordinary Hom-set representability nor agreement only in a homotopy category is substituted for a space-valued assertion.

The blueprint ancestry ends at prop-coef-integral-exceptional-adjoint. I read the main-20261015 statement and proof: paragraph 2 forms a mapping-complex adjunction and its specified maps before the derived limit. This split supplies its general coherence foundation. It changes no chapter/unit route and uses no SGA source. The existing local criterion and new evaluation statement belong to the item's unit, so no off-unit statement tool use is needed.

## Not duplicates

lem-coef-infinity-pointwise-yoneda-evaluation vs lem-coef-infinity-yoneda-evaluation: the existing Q55 node treats a small category and only the contravariant evaluation equivalence, while this renamed node allows a locally small infinity category, gives the universal-element inverse formula, and includes the covariant dual clause. They are distinct statements.

lem-coef-infinity-pointwise-yoneda-evaluation vs lem-coef-infinity-yoneda-presheaf-limits: the existing node gives full faithfulness and limits; it does not give Map(h_a,P) ≃ P(a) for arbitrary P or the universal-element inverse formula. The new node is that general evaluation theorem, not another full-faithfulness node.

lem-coef-infinity-pointwise-yoneda-evaluation vs lem-coef-derived-enriched-yoneda: the existing theorem concerns dg categories over Z, dg modules and derived mapping complexes. The new theorem concerns arbitrary locally small quasicategories and arbitrary space-valued presheaves, with no dg/stability/enrichment hypothesis.

lem-coef-infinity-pointwise-yoneda-evaluation vs lem-pc-yoneda: the existing blueprint node is the ordinary set-valued functor-of-points theorem on schemes; it does not cover full spaces of coherent transformations on arbitrary quasicategories.

lem-coef-infinity-pointwise-yoneda-evaluation vs def-weil-exceptional-inverse-image: this blueprint search hit defines exceptional functors for schemes and coefficient systems. It does not state general evaluation of infinity presheaves.

lem-coef-infinity-pointwise-yoneda-evaluation vs lem-weil-pbc-affine-galois-base-change-fiber-transitivity: identifier collision only. That node cites Stacks 038A for scheme actions and proves transitivity on fibers of affine scheme base change; this node cites Kerodon 038A for corepresentable infinity functors.

lem-coef-infinity-pointwise-yoneda-evaluation vs lem-weil-pbc-galois-base-change-fiber-transitivity: identifier collision only. Stacks 038A in the existing node is a scheme-action equation, unrelated to Kerodon 038A and the new evaluation theorem.

The new node is not a clause of the item: it has no adjoint-existence conclusion and applies to all presheaves, independently of any F or i. The universal-arrow assembly is reused from the existing lem-coef-infinity-local-adjoint-criterion, not recreated. Searches of all DAG statements for infinity Yoneda and evaluation, blueprint_refs.py searches for Yoneda, Yoneda evaluation, 03M5, coherent adjoint, representable presheaf, and mapping spaces found no further statement to reuse.

## Review by Q12

I read the stage-1 contract, the worker brief, SETUP's three blueprint levels, GOAL, dag-sync, and delivery-errors B through E. I read the six-functors chapter and sk-prop-sf-biduality-general unit records before expanding the item, and the current main-20261015 ancestor statement/proof. This is a subsidiary general tool within that unit, so it neither realizes nor edits a key-unit statement.

For the item, I read HTT Proposition 5.2.4.2 and its preceding Lemma 5.2.4.1; the former characterizes existence via preservation of representable right fibrations. I also read Kerodon 02FV in full: its universal-arrow condition requires equivalences of full mapping spaces, and its sufficiency passes through a cartesian correspondence whose universal arrows make it cocartesian. I reused the existing DAG local criterion for this non-elementary assembly, rather than silently reproducing it as an elementary argument. Kerodon 02F1 confirms the mapping-space transpose from a unit.

For the new node I read Kerodon 03M5, its surrounding subsection 8.3.1 including Notation 8.3.1.2, and 038A/038J. The source is explicitly about infinity functors and equivalences of Kan mapping spaces; in particular it warns that objectwise formulas alone do not construct a coherent transformation. The new statement accordingly supplies the coherent evaluation theorem and inverse, not merely the pointwise formula. Applying its covariant version to E^op gives the contravariant version. The universes allow E to be large relative to U, with U-small mapping spaces; no small indexing category, presentability, or existence of unrelated limits is used.

Step 1 cites def-cbc-enhanced-diagrams-cones for coherent transformations and parameters, and uses only formal operations on the given adjunction data. I checked the two inverse formulas: naturality of epsilon moves F R(a) past epsilon, and naturality of eta moves R F(b) past eta; the appropriate triangle then removes the remaining composite. The equations are homotopies on full mapping spaces, because the input transformations and triangles are coherent. The same two calculations handle necessity for the left-adjoint case. This is elementary adjunction algebra, not an appeal to an uncited representability theorem.

Step 2 cites the new evaluation statement. Its inverse formula really says alpha_x(f) ≃ P(f)(alpha_a(id_a)), including coherent parameters. With P_d(c)=Map_D(Fc,d), its action is precomposition by F(t); hence epsilon_d F(t) is precisely the extracted comparison. I checked that the input theta_d is an equivalence of coherent presheaves, not a pointwise choice lacking naturality.

Step 3 cites lem-coef-infinity-local-adjoint-criterion. I opened its full statement and verified its conclusion gives the coherent left adjoint, mapping-space equivalences natural in both variables, and coherent unit/counit and both triangles. The assignment X=C^op, Y=D^op, R=F^op, u=epsilon^op has exactly the required variance: its universal map becomes t ↦ epsilon F(t). Opposite reverses composition and interchanges unit with counit. This is formal opposite-category duality, not an ordinary homotopy-category approximation. The initial representing choices are only objectwise, which the cited criterion explicitly allows. The resulting coherent right adjoint supplies compatible representing choices; no assertion of literal equality with arbitrary initial choices is needed.

Step 4 cites the new node's explicitly covariant clause and the same existing local criterion. At c the element extracted at id_lc is c → i(l_c), and the formula v ↦ i(v)u_c has exactly the variance of the local criterion. I checked every hypothesis: quasicategories, a coherent functor i, and the equivalence of full mapping spaces for every e. The resulting coherent transformations and triangle homotopies are precisely those in the cited conclusion, retaining their coherent-diagram interpretation. I do not assert an independently prescribed infinite list of unrelated higher homotopies.

Every citation has a verbatim quote in citations.json. The only non-elementary inputs used by the proof are the general Yoneda evaluation theorem and the existing universal-arrow assembly criterion. I checked their dependency closures against the item: neither returns to it, so this introduces no cycle. The new node remains statement-only with empty proof/proof_deps, and all its notions are introduced inline or covered by its two definition dependencies.

I tested the statements on the empty category, a terminal category, ordinary discrete categories, and one-object groupoids. If C is empty and D nonempty, the presheaf condition fails because there is no representing object, matching nonexistence of a right adjoint. When D is empty the condition is vacuous and the unique empty adjoint exists. For Yoneda at a terminal object-category the evaluation equivalence is Map(*,P) ≃ P; for a groupoid, equivariance is retained rather than replaced by a set of components. Empty values of P are allowed and no choice of their vertices is asserted. No false statement or missing hypothesis appeared.

Mathlib searches were run only with msearch.py and are recorded verbatim from its log. I tried two semantic phrasings before concluding absence. I inspected CategoryTheory/Yoneda.lean:39,724–743, Adjunction/PartialAdjoint.lean:197–210,294, and Quasicategory/StrictBicategory.lean:49–70. The first two require ordinary Category instances and Type-valued hom functors; the last constructs a bicategory but states no evaluation or adjoint-existence theorem. Thus none is an exact match or one-line specialization to the item/new node. The file-target grep has an odd display format because rg omits its filename on a single-file target; I retained the actual output/log and verified those source lines directly.

## Unfinished work

The new general evaluation theorem is intentionally unsplit, as required for a one-level split. No part of the item's argument is left unspecified. The requested independent second reading remains to be done by another worker; this worker does not push the delivery.

## Earlier second reading (a previous round; superseded)

- Item statement: checked every hypothesis and clause against Kerodon 02FV/02F1 and HTT Lemma 5.2.4.1, Proposition 5.2.4.2, Definition 5.2.2.7 and Proposition 5.2.2.8; verdict: exact pointwise right/left criterion with coherent mapping-space data, with no added presentability or completeness assumption.
- Step 1: checked the unit/counit composites against Kerodon 02F1 and the coherent-transformation definitions; verdict: correct, with both right and left calculations now written explicitly on full mapping spaces.
- Step 2: checked extraction of the universal arrow against Kerodon 03M5/03M4 and the new evaluation node; verdict: correct variance and inverse formula, including coherent parameters.
- Step 3: checked the opposite application against Kerodon 02FV and the local-criterion statement; verdict: correct, with the right-pinched mapping-space reversal and reversal of units, counits and triangles now spelled out.
- Step 4: checked the covariant extraction against Kerodon 03M5/03M4 and 02FV; verdict: correct covariant variance and universal unit, with no pointwise-only substitution.
- New node `lem-coef-infinity-pointwise-yoneda-evaluation`: checked self-contained universes, mapping-space conventions, contravariant and covariant clauses against Kerodon 03M5 (03M4 notation), 038A and 038J; verdict: statement-only, strictly smaller than the item, and correct on full coherent transformation spaces.

I changed step 1 to replace “identical calculation” with the complete dual unit/counit composites, satisfying E5. I expanded step 3 to exhibit the opposite mapping-space reversal and the reversal of coherent adjunction data, instead of leaving that transport implicit. I corrected the source places to name Kerodon 02FV/02F1 and HTT Lemma 5.2.4.1, and to include Kerodon Notation tag 03M4. I searched for duplicate Yoneda, opposite-mapping, and adjoint-criterion nodes across the DAG; none states this theorem. I tested empty and terminal categories, the empty and terminal space-valued presheaves, discrete one-object categories, and a one-object groupoid; all edge cases agree with the statements. No statement dispute or new node deletion was needed.

## Second reading by Q12

- Item statement: checked every hypothesis and clause against Kerodon 02FV/02F1 and HTT Lemma 5.2.4.1, Proposition 5.2.4.2, Definition 5.2.2.7 and Proposition 5.2.2.8; verdict: exact right and left pointwise representability criterion with coherent mapping-space data.
- Step 1: checked both unit/counit inverse calculations against the coherent transformation and triangle definitions in def-cbc-enhanced-diagrams-cones and Kerodon 02F1; verdict: elementary and complete on full mapping spaces.
- Step 2: checked the representing equivalence, identity evaluation, and extracted universal arrow against Kerodon 03M5/03M4; verdict: correct coherent Yoneda extraction, with the new node cited.
- Step 3: checked the opposite-category mapping-space identifications and reversal of adjunction data against Kerodon 02FV and lem-coef-infinity-local-adjoint-criterion; verdict: variance and hypotheses match, with no hidden presentability assumption.
- Step 4: checked the covariant Yoneda extraction and application of the local criterion against Kerodon 03M5 and 02FV; verdict: correct dual variance and coherent unit/counit conclusion.
- New node `lem-coef-infinity-pointwise-yoneda-evaluation`: checked its universes, both variance clauses, inverse formulas, and full coherent transformation assertion against Kerodon 03M5, Notation 03M4, Definition 038A, and Theorem 038J; verdict: self-contained statement-only auxiliary theorem, strictly smaller than the item.
- Duplicate and Mathlib checks: searched all DAG statements, blueprint references, and Mathlib Yoneda/adjunction declarations with recorded msearch.py queries; verdict: no existing node or exact Mathlib match.
- Changes made: appended this independent second-reading record; no mathematical or node-file changes were necessary because the first reading already expanded the dual calculation and opposite-category transport and recorded all citations and searches.
