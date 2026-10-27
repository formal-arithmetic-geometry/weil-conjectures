# Q56 stage-1 delivery: lem-sf-qbar-localization-common-stage

## Files written

- `dag/nodes/sec-smooth-purity/lem-sf-qbar-localization-common-stage.json`: statement node, now split into eight proof steps. No Mathlib match for the full item.
- `citations.json`: fourteen verbatim citation records covering every step/node pair.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No unit record is changed: this auxiliary item is not its unit's key statement.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, common-stage localization, cross-stage orthogonality, algebraically closed coefficients, scalar adjunctions and the localization operations. There is no project declaration proving all clauses. `SixFunctors/ClosedImmersionStages.lean:385-430` treats a constant-adic sheaf model and closed direct-image full faithfulness/unit statements, not this raw pair-category assertion. `CategoryTheory/StageSystem/{Functor,Shift,Exact}.lean` supplies generic machinery, not the entire item. No sorry declaration was treated as a finished proof.

## WANTED

None. All material needed for this split is already available locally.

## Statement corrected

STATEMENT-DISPUTED: the imported phrase “finite fields E contained in Qbar_l” is literally incompatible with characteristic zero if “finite” means finite cardinality. The cited coefficient-category definition explicitly means finite intermediate extensions of Q_l. Replaced only that phrase by “finite coefficient extensions E/Q_l contained in Qbar_l”. A finite field of cardinality l^r cannot embed as a unital subfield of characteristic zero, since its l-fold sum of 1 is zero whereas it is nonzero in Qbar_l. This is a terminology/type correction faithful to the source, without changing the intended domain, conclusions, maps or coefficient model. No target is edited.

## Proof and source audit

Read AGENTS.md, GOAL.md, roles/worker.md, the stage-1 brief and stage document, SETUP's three levels and tool-lemma rule, the chapter/unit records, and delivery-errors B–E (including the merged copy). The source route remains the algebraically closed-stage paragraph of the current main-20261015 localization proof:
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sf-localization/prop-sf-open-closed-triangle-all-stages.proof.md`.

Read the full statements of all seven distinct cited nodes. Sources checked include:

- The above localization proof's rational paragraph, for the existing sibling `lem-sf-rational-localization-triangle-orthogonality`.
- `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-pf-reduction/lem-fix-operation-reduction.md` and `.proof.md`, especially the final paragraph explicitly transporting adjunction units/counits to coefficient-field stages.
- The current scalar-extension exactness/composition blueprint texts and the full existing node statements `lem-weil-scalar-extension-exact-triangulated` and `lem-weil-scalar-extension-composition`.
- `literature/blueprint/slopmaster2/src/version/sketch/42_qbarl_triangulated_colimit.tex`, Definition def:pair-hom and Proposition prop:pseudocone-functor, Proposition on exactness, and Theorem thm:pair-universal; also sketch32's finite common-stage principle, lines 1340 onward. The usable abstract additive/transformations assertion is the existing `lem-sbc-coherent-pair-functor-descent`, whose statement is not restricted to the proper-base-change finite stages. The sketches also discuss envelopes; only their raw pair-category portions are used here.
- The full common-stage definition `def-weil-algebraically-closed-coefficients` and the explicit representative/equality criterion in `def-weil-directed-colimit-abelian-groups`.

The proof is agent-written following the blueprint; it does not pretend that a Stacks tag states this adic common-stage theorem. No SGA source is used.

## Mathlib searches

The existing item's earlier searches are preserved. Q56 ran the logged LeanFinder, Loogle, LeanSearch and grep queries in `searches.jsonl`, using the required msearch.py wrapper. A second semantic phrasing tested filtered-colimit orthogonality and recollement. Searches returned module scalar adjunctions, generic adjunction constructors, filtered-colimit/finite-limit interchange and triangulated orthogonal properties; none states this coefficient-stage localization theorem. Read `Mathlib/CategoryTheory/Adjunction/Basic.lean:424-470`: `Adjunction.mkOfHomEquiv` and `Adjunction.mkOfUnitCounit` require the natural adjunction data already supplied and do not provide descent, exactness or cross-stage vanishing. The second grep recorded these declarations at lines 436 and 461. All service calls succeeded; no unavailable service was recorded as an absence result. No unrun query was inserted.

## Not duplicates

No new nodes are proposed. Whole-DAG keyword searches and `tools/blueprint_refs.py search` for common-stage, descent-functors, scalar-extension, localization data and cross-stage orthogonality found the generic descent tools and the rational sibling already cited. No blueprint node states the full present assertion; `same_as` remains empty. `tools/blueprint_refs.py ancestor` confirms the existing ancestor `prop-sf-open-closed-triangle-all-stages`.

## Review by Q56

I checked the argument against C1 and C4 by opening the statements, rather than using dependencies or proof internals of a cited node. Step 1 uses the rational sibling's actual functors, adjunctions and cross-object Hom vanishing at every finite extension E/Q_l. Its hypotheses exactly match the fixed separated finite-type scheme, complementary immersions and ell different from p. No unsupported assertion of arbitrary constructible preservation is made.

In step 2, `lem-fix-operation-reduction` explicitly covers pullback, ordinary direct image and compact support and says the comparisons preserve associativity maps, units and counits. The open immersion has compactification (j,id_X), so its compact-support comparison is the open-extension comparison. The separate scalar exactness and composition nodes are stated for precisely the raw rational category of this item, on any scheme. I checked the unit and tower equations under balanced tensor, and the degree-zero/cochain sign calculation for shift compatibility. These are the supplied scalar comparisons, not choices of isomorphisms between their values. No finite-Tor hypothesis is taken from the finite-quotient-only portion of the coefficient theorem: this use is at finite coefficient-field stages.

Step 3 uses the abstract additive pair-descent node: its displayed conjugation formula agrees with the object's raw Hom-colimit convention, with beta inverse at the target. Its transformation and composition clauses are also part of its statement. I checked identity transitions, the tower equation and the small directed index of finite intermediate fields. Step 3 explicitly normalizes the identity transition through its canonical unitor: conjugation at the two endpoints and inverse conjugation give the same representative classes and composition. Thus the abstract lemma's literal-identity hypothesis does not silently require tensor with E over E to be definitionally the identity. Its Karoubi conclusion is not used.

Step 4 writes the actual shift naturality calculation over a representative field. Both sides conjugate to the finite-stage naturality equation. Exactness then follows in two applications of definitions: represent a distinguished triangle at a finite field, and apply the exact finite-stage functor. This is an elementary verification from the cited category definition and steps 1–3, not a new theorem hidden in a long step.

Step 5 invokes the same abstract node's explicitly stated descent of compatible transformations and preservation of their equations. Thus the two triangle identities descend along with the finite units and counits. Its naturality assertion is for arbitrary common-stage representatives; it is not a test only on original-field arrows. Step 6 uses the definition's distinguished-triangle convention and finite-stage scalar exactness. Images of the given finite-stage triangle therefore have exactly the prescribed counit and unit, not merely isomorphic vertices with unidentified maps.

In step 7, I checked the sources and targets of a_L, b_L and the formula b_L h a_L^{-1}. The shift is on j_!N, with scalar shift comparison inserted before the open comparison. For a larger field the scalar associators are inserted at both endpoints. The comparison tower equation makes conjugation commute with these Hom transitions; taking the directed colimit therefore gives the exact formula in the item. This is the elementary two-sided conjugation calculation from step 2, not an unnamed comparison theorem. Step 8 invokes the rational sibling on arbitrary independently extended source and target objects at L. Every representative is then zero, by the concrete colimit representative statement. No faithfulness, preservation of infinite products, commuting Hom with derived limits, integral lattice for arrows, or Karoubi completion is assumed.

During this audit I rejected the tempting direct citation of `prop-weil-pbc-descent-functors`, its shift-coherence child and the specialized Verdier theorem: their statements use the PBC integral category with extra compatible etale-origin witnesses. I read `def-weil-pbc-bounded-constructible-complete` and compared it with `def-weil-derived-complete-integral-detailed`; no equality or equivalence between these categories is asserted here. The chosen generic additive lemma and the direct distinguished-triangle calculation avoid that C4 error entirely.

Small cases checked: E=F=L makes beta the identity and recovers the finite-stage formulas; proper enlargement L'/L uses the tower equation with the correct inverse at the source; m=0 and negative m have the same vanishing; N=0 or M=0 gives zero; U empty or Z empty reduces to the zero/identity immersion functors; a ramified finite extension does not use flatness of a quotient reduction or a claimed common uniformizer. The interval/boundedness hypotheses are inherited from the rational sibling, not from an unrestricted ambient direct image. The finite index poset is nonempty (it contains EF), including the empty finite-diagram case (choose Q_l). No new statement or definition needs a separate edge-case audit. Every proof step has fewer than 2000 characters; there is no long step hiding another lemma.

Off-unit uses are declared in split_report.tool_uses: coefficient normalization, exact scalar transitions, scalar composition and abstract pair descent are generic tools. They do not replace the localization unit's route. No new node restates a clause, no definition is cited as a substitute for a theorem of scalar compatibility, and no literature citation serves instead of a needed node.

## Validation and unfinished work

The server's review_split check passed with zero new nodes, and check_dag found no finding introduced by the sandbox or its nodes. The first deliver.py --no-push exited OK at 146e44bd126. A final clarification of identity-transition normalization is followed by another complete required dry run before delivery. There is no unfinished mathematical part of this split. Downstream proof obligations remain owned by their existing DAG nodes.
