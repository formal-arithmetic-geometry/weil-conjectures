# Stage-1 report: lem-pod-hom-chain-uncurried-transport

## Files written

- `dag/nodes/sec-six-functors/lem-pod-hom-chain-uncurried-transport.json`: existing statement, split into five explicit steps; no whole-item Mathlib match.
- `citations.json`: one verbatim statement quotation for each of the five step/node citation pairs.
- `report.md`: this report. `searches.jsonl` is the search command's own log.

New nodes: 0. New Mathlib leaves: 0. No unit record changed: this item is not the unit's key statement.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id and for uncurried/Hom-chain terminology, then the six-functors and monoidal directories for projection and adjunction terminology. No project declaration states all four successive-image formulas together with the projection square. Existing module-sheaf and tensor–Hom formulas cover different objects or only one part, so are not attachment candidates.

## WANTED

None. Both blueprint proofs used are present locally.

## Findings and changes

The imported statement is unchanged. It already supplies the exceptional adjunction as in `fix-prop-adjunctions`; the proof uses that supplied adjunction, including its conditional hypothesis, and does not deduce an unrestricted ambient exceptional adjoint. Likewise no new assertion of internal-Hom reduction compatibility is needed.

Read the chapter and package unit records, the item, its creating item `lem-pod-hom-chain-counit-formula`, and the statements of all seven statement dependencies. Read `fix-lem-tensor-adjunction.proof.md` Step 1 in main-20261015 and `thm-pod-identification-of-the-comparison.proof.md`, especially the paragraph beginning “These bijections are induced”. The five steps carry the ordinary counit, evaluation, exceptional counit and projection part of those Hom chains. No chapter or unit route changes.

The existing `lem-pod-closed-uncurry-laws` is already a Mathlib leaf. Its `uncurry_eq` clause supplies evaluation and its source is Mathlib's closed-monoidal file, lines 145–194, read locally. Mathlib's adjunction file, lines 159–175, defines inverse Hom transport by functor application followed by the counit. This is an elementary unpacking here, not grounds for a new node. The whole-item searches find these individual operations, exponentiable-morphism slice adjunctions, and rigid tensor duality; they do not give the complete specified composite and projection square as one declaration or a one-line specialization. The original item's searches have been retained. The interrupted leanfinder call completed and left its results in `searches.jsonl`; its top declarations were read in the exponentiable-morphism file rather than rerunning it. Fresh loogle, leansearch, scoped and unscoped grep, and a second semantic phrasing are also logged. No unsuccessful service call was reported as absence.

Whole-blueprint searches for “uncurried transport”, “inverse adjunction”, and “Hom chain” found no equivalent statement. The inverse-adjunction search hit `def-trf-trace-class-source`; its statement was read and defines a single correspondence trace-class mate, not this composite. The creating counit-formula node is stronger and uses this item, so cannot be cited back. `same_as` remains empty. No new node requires a duplicate comparison.

## Not duplicates

No new nodes. In particular the elementary inverse-adjunction calculation, tensor functoriality and final reassociation remain proof steps, rather than duplicating existing nodes or restating clauses as new lemmas.

## Review by Q41

I checked delivery-errors B–E against the sources and the actual node statements. There are no statement-only children to audit or Mathlib leaves to certify. The original statement's coefficient definitions and construction references were read and retained: completed integral operations, raw rationalization, and common finite coefficient stages are used exactly as stipulated.

Step 1 uses `det-thm-sf-ctf-stability-adjunctions` for the restricted functors and adjunction domains and `fix-prop-adjunctions` for the ordinary adjunction and its named unit and counit. The former explicitly says these are adjunctions on the full finite-Tor subcategories; this supplies the domains of the internal Hom and pushforward. The latter states the triangle identities. I wrote the inverse-adjunction formula and its verification by unit naturality and the triangle identity, so the step does not assume a new unproved transport theorem.

Step 2 uses precisely the evaluation clause in the statement of `lem-pod-closed-uncurry-laws`, with left factor M. Replacing u_t by its formula then factors the tensor morphism by ordinary functoriality. I checked that the tensor order is M first throughout; there is no unmentioned braiding or sign. Step 3 uses clause 2 of `fix-prop-adjunctions`: its exceptional counit is Rf_!Rf^!N to N and its inverse Hom formula has the source Rf_!(M tensor Lf^*T). The supplied exceptional adjunction and restricted tensor domain, rather than any unconditional ambient existence assertion, justify that application.

Step 4 uses the actual statement of `fix-prop-projection-formula`, which explicitly says natural in K and L. With K=M and L ranging from T to A_N, naturality is exactly the square printed in the item. I checked both second arguments belong to the finite-Tor domain and M belongs to the bounded constructible first-input domain. The direction is P_T from C tensor T to Rf_!(M tensor Lf^*T); the Hom map precomposes with P_T. Step 5 displays the entire functoriality and associativity calculation, ending with the definition of p_N. It depends only on the previous steps, with no hidden exchange or coefficient-comparison lemma. All step/node citations have literal quotations in `citations.json`; I verified each quotation occurs in the corresponding current statement.

I tested the formulas at t=identity (u is the ordinary counit, v=q_N, and w=p_N), and for the identity morphism f with identity ordinary and exceptional adjunctions and identity projection (the formulas reduce to evaluation composed with 1 tensor t). Zero objects and the zero input arrow yield zero maps in these derived categories. These tests also check the orientation of the projection square. The argument does not require f to be proper, a purity isomorphism, or any SGA source. Every step is below 2000 characters; the final algebra is explicit and no step hides a separate lemma. I preserved the original statement, citations and searches and filled the proof, proof-dependency union, agent proof origin, and split report. Off-unit inputs for restricted adjunction domains and projection naturality are declared in `split_report.tool_uses`, with their exact role, for maintainer review.

## Unfinished work

None in the requested one-level split. The underlying adjunction and projection nodes remain independent obligations, as required by stage 1.
