# Worker report: lem-a1-local-boundary-duality

Group Q84; stage 1; 2026-10-17. Direct delivery by the dispatched author, with independent mathematical review left to the maintainer as instructed. No agents, Lean edits, compiler invocations, library builds, or manual git operations were used.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-a1-local-boundary-duality.json: statement node, split into ten steps. Mathlib verdict: no match for the geometric theorem. No new nodes and no new Mathlib leaves.
- citations.json: one verbatim statement quotation for each of the 27 citations in the ten proof steps.
- searches.jsonl: actual search-command receipts, retained in the sandbox; the item records the exact tools and queries. write_split.py is a sandbox-only generation script, not a delivery file.

## Attachments

None. I searched WeilConjectures for the item tag, local-boundary-duality terminology, and the recorded declaration. AlgebraicGeometry.exists_linearEquiv_dual_stalk_higherDirectImage, WeilConjectures/DeligneLaumon/AffineLine/LocalDuality.lean:77, ends in sorry at line 91. It is not an attachment. The declaration states the existence of the stalk isomorphism and its explicit Frobenius factor, under a quasi-compact dominant open immersion and smooth relative dimension one. It does not state a canonical isomorphism of boundary complexes. Its original docstring uses the unit tag sk-i-dl-a1-local rather than the individual item tag.

## WANTED

None: the proof is marked agent-written and follows the available current blueprint proof. All supporting facts are existing DAG statements; no missing literature was silently substituted. No SGA source was used. The inherited purity dependency follows its existing lecture-notes route.

## Statement updated to current blueprint

The imported statement asserted a canonical boundary-complex isomorphism and then the stalk pairing. The blueprint_update for main-20261015, and the current statement file in literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-i-dl-a1-local/, assert the stalk pairing, explicitly spelling out e(F_s a)(F_s b)=q_s e(a)(b). I used that current statement verbatim, as the brief requires. This is an application of the recorded upstream update, not a new proposed weakening or statement dispute. The stronger intermediate complex comparison is still proved in step 6.

## What needed correction

The imported first proof step combined setup with three different duality arguments and exceeded the long-step limit. More seriously, prop-weil-open-closed-recollement-adjunctions only states finite-coefficient j_! adjunction and i^*i_*; it does not state j^*Rj_* = id at Qbar coefficients. I removed that citation and used lem-exc-open-fully-faithful at finite levels, then wrote out the open-restriction/derived-limit transport. The inherited appeals to finite-stage recollement and the separate closed-unit nodes are redundant after citing the actual all-stage statements, so they were removed.

The lisse coefficient dual now has its own applicable existing citation, lem-per-dual-lisse-tensor with K the unit. The point-duality comparison is taken from lem-pod-point-dualizing-complex, which actually states the fibre formula, rather than inferred solely from a formula for the dualizing object. Geometry of the boundary is justified by existing finite-complement and residue-field lemmas. Finally, prop-pur-rational-purity-trace-coherence alone does not explicitly say that the purity orientation is Weil-equivariant. Step 9 cites the theorem that explicitly states the equivariance square, together with the coefficient duality equivariance corollary.

## Existing-node and blueprint search

I searched the full DAG, not only the target reach, for boundary duality, open counits, lisse duals, finite complements, point dualizing objects, and Tate Frobenius. The blueprint_refs.py searches included boundary duality, lisse, open closed and finite projective; ancestor confirms that the item is its own blueprint ancestor. Boundary-duality-discharge is a different finite-coefficient comparison for closed supports; it does not state this curve boundary pairing. No other blueprint node found states the whole item, so blueprint.same_as is empty. The lisse-tensor lemma, the finite-level open counit, point duality and finite-complement facts already exist, and were reused instead of creating nodes. Therefore no new-node duplicate/tag comparisons are required.

The Mathlib searches ran through msearch.py only: two semantic phrasings, a Loogle Verdier-name query, a general-source grep and a more focused AlgebraicGeometry grep, plus LeanSearch. The hits were ordinary perfect-pairing linear algebra, scheme structure-sheaf restriction, sheaf Ext cohomology and Verdier localization categories; none gives the lisse etale curve statement. The focused geometry grep returned zero hits. These are not one-line specializations to this theorem.

## Route and tool uses

I read the chapter record sec-deligne-laumon-a1 and the complete unit record sk-i-dl-a1-local, together with the current unit statement. Steps 1–2 of that unit are realized by the exchange/biduality, recollement, smooth-curve duality and stalk calculation here. Its independent third step, Artin–Schreier ramification, is not claimed by this item; no unit realization record is rewritten as though this node proved both clauses.

Generic off-unit tools are declared in split_report.tool_uses, with a reason for each: finite-dimensional dual cohomology, lisse-tensor duality, the boundary's finite support and residues, point fibre duality, finite-stage open restriction and its product/limit preservation, coefficient duality equivariance and the Tate Frobenius scalar. They supply the local unit's stated argument; no unit step is replaced by another theorem proving the item wholesale.

## Review by Q84

I read the current item statement and its complete .proof.md, and compared them with blueprint_update, the chapter/unit records, and the Lean declaration and docstring. The finite field, prime invertibility, geometric cohomology, lisse finite rank, ordinary j_* and geometric rather than arithmetic Frobenius are retained. No purity-of-weight, properness, unramifiedness or Frobenius-stable integral lattice hypothesis was introduced. The sources for the support lemmas are their current DAG statements; the current blueprint proofs for lisse tensor duality, the open counit, coefficient dual cohomology, point dualizing objects and the cyclotomic scalar were also opened. Every cited node statement was opened before constructing citations.json.

Step 1 uses precisely the Qbar Verdier anti-equivalence and exceptional formula from thm-coef-qbar-verdier, the preservation clause (1) of prop-sf-localization-all-stages, and the field-stage equality of categories in def-weil-finite-tor-amplitude. This prevents applying biduality to a complex without bounded constructibility. The geometric schemes and immersion morphisms satisfy the separated finite-type hypotheses.

Step 2 uses the displayed exchange of thm-sf-verdier-exchange with M=D_U G and the biduality formula of thm-coef-qbar-verdier. I checked the functor directions: applying the contravariant dual to D_C j_! D_U G = Rj_*G gives D_C Rj_*G = j_!D_U G. Inserting D_C K into i^! = D_Z i^* D_C gives the other comparison. No smoothness of a boundary complex is required.

Step 3 uses lem-exc-open-fully-faithful only for its actual derived open counit at finite levels. The immersion-limit-preservation statement says that restriction is exact and preserves products. These are exactly what is needed to preserve the explicit shifted-cone limit model in the two coefficient-operation definitions. The argument then rationalizes and passes to common finite stages; it does not use a finite-coefficient statement directly as a field-coefficient theorem. Exactness here also explains the later use of i^* on triangles and cohomology.

Step 4 uses the full Qbar recollement triangle of prop-sf-open-closed-triangle-all-stages and precisely clause (4) of prop-sf-localization-all-stages, which states both the vanishing and the exceptional closed unit. The dualities in thm-coef-qbar-verdier and the exact restriction in step 3 make i^! exact. The remaining computation of the zero-middle-term triangle is elementary. I checked that its arrow has target (i^!j_!G)[1], so the resulting boundary formula has shift [-1], not [1].

Step 5 applies smooth purity to the structure map of a smooth curve with the constant coefficient lattice and relative dimension one. The lisse-tensor node is applied to the unit, not to an arbitrary nonperfect constructible sheaf: it explicitly permits the finite-rank lisse factor F and gives its ordinary coefficient dual. This supplies D_UF=F^vee(1)[2].

Step 6 only composes the preceding isomorphisms. Its use of the twist and direct-image definitions is a finite-dimensional scalar calculation written out in the step: a basis turns the specified line comparison into the identity, and rescaling cancels on both sides. It is marked elementary because it is this one-line scalar-line comparison plus composition and [2]+[-1]=[1], not an additional duality theorem. The comparison itself is defined independently of the temporary basis.

Step 7 takes finiteness and closedness from lem-sc-dense-open-finite-complement and the residue identification from lem-weil-pbc-closed-point-residue-field-base. The reduction assumption is essential: on a one-point reduced scheme its ring has unique prime equal to the nilradical, hence zero, so it is the residue field k. The actual point fibre formula comes from lem-pod-point-dualizing-complex. I do not identify arbitrary pro-etale sheaves on a geometric point with vector spaces; the statement is used on the bounded constructible coefficient category named by that lemma.

Step 8 applies lem-pod-cohomology-of-dual-over-field at a finite E-stage of the stalk complex, then extends scalars. Its quoted formula has degree -i on the dual, so i=1 gives the required degree -1. On the other side the [1] shift gives degree zero, and left exactness in def-weil-derived-direct-image identifies its H^0 with the ordinary j_* by the explicit kernel calculation. Finite-dimensionality is furnished by the point duality/fibre statement, not by an assumption on an arbitrary sheaf stalk.

Step 9 distinguishes operation equivariance from orientation equivariance. lem-fix-weil-operations supplies the former, cor-coef-verdier-weil-equivariance explicitly includes evaluation and biduality and lifts the constructible exceptional adjunction, and the two all-stage support nodes explicitly say their arrows and unit are Weil-equivariant. thm-pur-weil-equivariance-of-purity-and-trace explicitly states the smooth-purity square at the rational and common-field stages. Inverting the connecting isomorphism therefore preserves equivariance. This step does not assert that Weil pairs form a triangulated category.

Step 10 uses exactly m=-1 of lem-wf-tate-twist-frobenius, giving q_s rather than q_s^{-1} in the target. The finite-dimensional dual identification of step 8 gives perfectness in both factors. Choosing a basis of the Tate line produces the existential linear isomorphism e; the pairing itself does not depend on a choice of that basis. This checks every clause of the updated statement, including its explicit scalar formula.

I tested the zero sheaf and empty complement: both sides and all stalk requirements vanish appropriately. For a constant rank-one sheaf on the punctured smooth local curve, H^0 is the coefficient field and H^1 is the (-1) line, giving the target (-1) line and the same q_s factor. This tests the two possible sign/shift errors in the imported reasoning. No semisimplicity of local monodromy was used. No new statements were created, so there are no untested new hypotheses or new leaves masquerading as conclusions of the item.

All ten steps are below 2000 characters. The previous oversized paragraph was separated by its mathematical operations. None of the retained steps hides a new comparison lemma: every non-elementary comparison has the cited existing statement, and the remaining compositions, cone with a zero vertex, coefficient-line scalar comparison and transpose into a pairing are written explicitly. The review corrected the finite-only counit citation and the equivariance gap described above; it did not split the statement into copies of its own clauses.

## Unfinished work

None in this stage-1 split. The existing downstream nodes remain their own items. Server dry-run results and the final push are recorded by deliver.py.
