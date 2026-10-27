# Q42 stage-1 report: lem-fd-integral-inverse-scalar-cocycle

## Files written

- dag/nodes/sec-fourier-transform/lem-fd-integral-inverse-scalar-cocycle.json: existing statement node, now split in six proof steps; statement and statement dependencies unchanged; not a Mathlib leaf.
- citations.json: verbatim statement excerpts for every node cited in every proof step.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean files written or compiled.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and inverse scalar/cocycle terminology. The field-scalar cocycle in SixFunctors/ProEtale/FieldCoefficient/ExtendScalarsComp.lean:267 is about ordinary field-module scalar adjunctions, not the actual strict quotient-tower completion comparison, its inverse, or its completeness unit. It does not attach this item.

## WANTED

None. This auxiliary argument is agent-written, not a numbered theorem claimed from the literature. Its blueprint source and all reused node statements are available locally.

## Audit findings and corrections

The live item was statement-only, with searches inherited from Q14. There was no earlier sandbox proof/report. I copied that item and retained its statement, source, blueprint ancestry and historical searches. The inverse equation cannot be obtained by reversing the displayed factors and cancelling alone: its middle factors are differently whiskered. Step 3 now writes the naturality equation at b_{L/E,K}^{-1}, identifies the displayed inverse two-stage comparison with D^{-1}, and only then cancels. Steps 5 and 6 expand both repeated-field substitutions rather than saying they follow formally. No statement dispute or change of unit/chapter route was needed.

I briefly misdirected an edit to the read-only repository item and a temporary script outside the sandbox. I immediately restored the repository item from the preserved original, removed the outside temporary script and the redundant sandbox-root node, and retained all substantive changes solely at the sandbox's required relative path. No git command was run in the repository. Subsequent writes use absolute sandbox paths. The restored repository item is unsplit and has its original statement and metadata.

## Searches

I read the inherited searches and retained them as inherited records, not as searches performed by Q42. Q42's actual new queries and returned results are in searches.jsonl and appended verbatim by tool/query to mathlib_searches. LeanFinder was tried with two phrasings, together with LeanSearch, Loogle and two source greps. All services returned successfully.

Loogle's CategoryTheory.NatIso.naturality_2 is at Mathlib/CategoryTheory/NatIso.lean:152; I read it and the neighboring inverse-naturality identity. LeanSearch's inverse-monoidal-transformation instance was read in CategoryTheory/Monoidal/NaturalTransformation.lean. These justify recognizing step 3 as elementary categorical algebra; neither states this whole completion-normalized derived-sheaf assertion. LeanFinder's ModuleCat.extendScalarsComp and module adic-completion results concern ordinary module categories, not the specified quotient cocones in derived sheaf categories. No new lemma was created for naturality or inverse cancellation.

Before deciding against new nodes, I searched the whole DAG for inverse cocycles and conjugated completion associators, and ran blueprint_refs.py ancestor and searches for "completion associator", "inverse scalar" and "scalar extension". The existing completion-associator node supplies precisely the non-elementary forward comparison required here.

## Not duplicates

No new nodes. In particular I reused lem-fix-scalar-completion-associator and lem-weil-finite-free-completed-scalar-comparison instead of extracting special cases of their statements. The item additionally states the inverse whiskered comparison and its two explicit unit substitutions; I proved these inside the item's steps.

## Review by Q42

I read the current main-20261015 def-fd-trace-function.md, its sk-def-trace unit and sec-fourier-transform chapter records. The final sentence assigns the Frobenius trace to the PBC coefficient category; the current item is the retained agent-written auxiliary comparison behind that sentence. I also read the ordinary PBC scalar-extension statement in the main blueprint and lem-fix-operation-reduction.proof.md, whose field-stage transport paragraph motivates the completion-associator auxiliary. These do not give a verbatim proof of the inverse identity: the naturality calculation is mine, marked proof_origin.by = agent. No SGA source was used. There are no new nodes requiring separate source audits.

For step 1 I opened the complete statement of lem-fix-scalar-completion-associator: it states the forward equation with the same actual chi maps, representative independence and unit equations. Its input hypothesis is derived completeness, satisfied by the stipulated integral full categories. It imposes no extra dimension, constructibility or Noetherian condition; our scheme assumptions are stronger. The item's explicit normalization identifies its chosen framework associator with this associator. I use its statement, not an implicit construction from its proof.

For step 2 I opened prop-weil-pbc-scalar-extension: its integral ambient functor is ordinary change of completed coefficient rings, whose constructible restriction and raw rationalization is the PBC scalar functor, and its specified associator is derived tensor balancing. The scheme and coefficient hypotheses coincide. The item assumes presentation transport fixes tensor generators; checking (x tensor l) tensor m maps to x tensor lm on both presentations establishes that this is the same balancing, not merely some associator. The quoted statement in citations.json contains the integral restriction/rationalization clause.

Step 3 uses the forward equation already established and only naturality and inverse identities. I checked the arrows: D maps C2 C1 K to U2 U1 K; C2(b1^{-1}) b2_{U1 K}^{-1} maps in the reverse direction. Naturality at b1^{-1} identifies it with b2_{C1 K}^{-1} U2(b1^{-1}), so it is exactly D^{-1}. Thus the inverse equation has the claimed whiskering and order. No unproved comparison identification is hidden in the word cancellation.

For step 4 I opened lem-weil-finite-free-completed-scalar-comparison: its last sentence states that for equal fields chi is the natural completeness map after multiplication. This gives b = eta mu, with eta the specified natural completeness unit. Inverting and cancelling mu gives the normalized inverse unit. Finite E/Q_l, completeness of K and the actual-map hypothesis are all present. I deliberately did not use the sibling normalized-comparison node merely to obtain this already available special case.

For steps 5 and 6 the statements of lem-fix-scalar-completion-associator and prop-weil-pbc-scalar-extension explicitly give the multiplication/completeness unit laws. I used these statements for the two displayed forms of A^U and A^C, and wrote out the resulting naturality squares. For L=E, naturality of b^{-1} at eta_E^{-1} is exactly the first square. For M=L, naturality of mu_L at b^{-1} cancels mu_L and its inverse and gives the second square. citations.json records both source nodes for both steps, including the elementary step 6. When all fields coincide, multiplication and completeness normalize the squares to the identity square. These checks do not assume distinct adjacent fields.

I checked the B–E return criteria against the node and sources: no new statement-only tasks with hidden proofs; no duplicate or clause-restatement nodes; every non-elementary input is cited by statement; no added hypotheses, missing completeness, unsupported finite Tor-amplitude condition or changed coefficient category; no cycle introduced via the parent or sibling. The statement and stmt_deps are identical to the live original. All six steps are shorter than 2000 characters (largest 742), and the inverse calculation and unit computations are elementary steps rather than new tasks. I tested the zero complex, an identity tower, each single repeated-field case, all three fields equal, and repetitions adjacent to strict extensions. Since the argument is categorical, none requires freeness of K or a special K-flat representative.

The off-unit uses are declared in split_report.tool_uses: the general completed associator, ordinary PBC balancing, and identity normalization of finite-free scalar comparison are generic coefficient tools, not replacements for a geometric route of this unit. The key trace-function definition/unit is not my item, so its realization fields are not changed.

## Unfinished work

None at this split level. The existing cited nodes remain their own tasks; this delivery does not claim to prove them. The server review_split check passed before report completion. The required deliver.py dry run and final delivery are performed after this report.
