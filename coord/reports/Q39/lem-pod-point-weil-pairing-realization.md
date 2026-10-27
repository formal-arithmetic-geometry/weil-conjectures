# Q39 stage-1 report: lem-pod-point-weil-pairing-realization

## Files written

- `dag/nodes/sec-poincare-duality/lem-pod-point-weil-pairing-realization.json`: statement, now split in seven steps; no Mathlib match; statement and statement dependencies retained verbatim from the current repository.
- `citations.json`: 18 step/node entries, each checked against the actual cited statement.
- `report.md`: this report. `searches.jsonl` is the search command's log.

There are 0 new nodes and 0 Mathlib leaves. No chapter or unit record is changed. All writes are inside this item's sandbox. No Lean is written and no compiler, Lake, local DAG checker or git command is run.

## Attachments

None. I searched WeilConjectures for the item id, its blueprint tag, point transport, pairing and Frobenius. `AlgebraicGeometry.Etale.IsWeilPairing.degreewisePairing_frobeniusOperator`, `WeilConjectures/SixFunctors/Etale/Derived/WeilFrobenius.lean:289`, proves the Hom-level equation in the ordinary etale derived module category with constant coefficients. The adjacent unit-scalar and shifted-datum lemmas are likewise useful partial analogues. They do not state the equivalence with the specified rational adic point fibre, its canonical transport through completed integral coefficients, or the two support realizations. Thus they do not state every clause of this item. I read their signatures and proofs, including the file's coefficient assumptions, rather than claiming an attachment from the docstrings. The pairing applications under EtaleCohomology/PoincareDuality/Frobenius also do not supply that missing point realization.

## WANTED

None. This is an agent-written explicit calculation using the existing coefficient statements. I read Deligne, Weil II (1.1.3), (1.1.7), (1.1.10)--(1.1.11), printed pp. 150--152, from the local PDF, for scalar localization and the distinction between geometric Frobenius transport and Weil structures. Those paragraphs give conventions, not a complete proof of the derived calculation, so proof_origin is agent.

## What was wrong or incomplete

The item had no proof. The corrected statement made during the review of Q47's parent delivery already specifies both direct-image Weil data; I preserved that correction exactly. In particular the final claim is not an assertion for arbitrary unrelated data on Ra_!K and Ra_*L.

The inherited source path and unit association say sec-poincare-duality/sk-lem-finite. In the current blueprint (latest, main-20261024, ef6f9619fdbffa59e88528fb56483d76c70258c8), prop-weil-operations is under sk-thm-frobenius. I read that current proof in full. Its last two sentences concern equivariance of the formal exchange and its smooth pairing form; the item's retained Step 10 is the coefficient-point calculation needed to read that pairing on cohomology. I cite that current location in the proof and make the blueprint.from.place precise. I did not rewrite the project's inherited unit metadata or alter a chapter/unit route. I also read the recorded chapter and sk-lem-finite unit, and the three-level rule in SETUP.md.

A potential false inference was avoided: the equivalence of point categories alone does not assert a tensorator, and the point tensor theorem is stated for finite-Tor objects. The present item assumes only rational bounded constructibility. Step 1 instead uses only the unit evaluation and ordinary field derived Hom; the pairing is constructed on Hom from the unit throughout. No stronger statement about an integral representative is assumed.

## Searches and reuse

There was no earlier item copy, split or report in this sandbox. I retained the current item's Q47 searches and appended only the five searches actually run with the required msearch command for Q39. LeanFinder was tried first with the canonical rational adic transport description, then with the more general strong monoidal pullback/Hom formulation. Results were isocrystals/perfectoid rings for the former and rigid tensor-Hom bijections for the latter. LeanSearch returned isocrystals, the adjunction projection morphism called frobeniusMorphism, Grothendieck transports and a tensor-power pairing. Loogle returned no hits. Grep returned affine-space point-transport comments. None gives this theorem or a one-line specialization. All services answered successfully, so no unavailable result has been recorded as absence.

I searched the entire DAG by the item id and the concepts point transport, point tensor/unit, shifted pairing, cohomology represented by Hom, and pullback/tensor shifts. I ran blueprint_refs searches for Frobenius pairing, point transport, Weil pairing and cohomology transport, and its ancestor command. There is no same-statement blueprint node; existing general tools are cited, not recreated. No new node therefore has a duplicate pair needing a distinction.

## Not duplicates

No new nodes. In particular I did not turn the representation formula, the unit identity, or the main invariant-pairing clause into a new restatement node.

## Review by Q39

I read delivery-errors B--E in full and checked the split against those substantive failure modes. I read every cited node's statement, not only its proof or title. The proof follows the current blueprint's requested point realization, with the underlying calculation written out rather than hidden in “transport”. No source other than the permitted blueprint and Deligne conventions is used; there is no SGA route.

Step 1 uses the actual unit comparison Gamma_s B = R from lem-sf-point-ringed-evaluation-model and the rational fibre formula in def-weil-finite-coefficient-point. It then uses exactly the derived-Hom/cohomology bijection in lem-trf-field-complex-cohomology-splitting, with source E[0], followed by full faithfulness and shifts of lem-weil-point-fibre-equivalence. The field is the finite coefficient field E and all complexes lie in its indicated bounded finite-dimensional category. This gives both the cohomology/Hom identification and End(U) = E. I checked that none of these cited statements promises a tensor comparison that I silently use. The field splitting lemma is ordinary linear algebra; its chapter name does not make this a use of the trace formula.

Step 2 reads the restriction/coprojection and rationalization in def-weil-frobenius-point-transport, the explicit comparison z -> (0,theta(z)) and finite x -> x tensor 1 in def-weil-inverse-image-pullback-comparison, and the zero-twist coefficient datum in def-weil-frobenius-coefficient-twists. These compute the unit transport on 1, including completion, so F(c)iota_U = 1 is justified. The equality F(Px)iota_U = iota_{A[i]}F(x) is exactly the rational-arrow naturality statement of lem-weil-frobenius-point-transport-natural. Its applicability to arbitrary rational arrows is explicit in that node. Solving for iota_U gives c^{-1}, not c. No Frobenius-stable integral lattice is introduced.

Step 3 supplies the shift check used by Step 2: termwise restriction and coprojection, followed by the signed mapping-fibre shift (b,a) -> ((-1)^r b,a), leave the zero cone coordinate of kappa zero. The normalized total-tensor shift coefficient is copied from lem-pur-total-tensor-signed-coherence; the quotient transitions and the matching cone comparison are supplied by lem-sf-completed-tensor-shift-right and the actual completed construction in def-weil-derived-pullback-tensor-hom. Both routes multiply the same shifted bidegree by (-1)^{vp}; pullback is degree zero. This is a direct equality of the specified representative maps, so it survives the product/cone and rationalization. It does not assert an unexplained comparison of two derived constructions. The calculation works for negative integers too.

Step 4 takes naturality and unit coherence from the statement of lem-pur-derived-pullback-tensor-iso, valid for arbitrary bounded constructible rational inputs. It identifies c with the coefficient unit comparison of def-weil-frobenius-coefficient-twists. I checked the types of mu P(j)c^{-1} and (c^{-1} tensor c^{-1})j: both go from U to PU tensor PU. Multiplying the unit-coherence equation by the two inverses proves the formula, so no separate lemma node is needed for this one-line manipulation.

Step 5 uses the same tensor theorem's naturality, and Steps 2--4. I wrote the entire substitution: form y tilde in (D[n])[-i], extract the total shift, substitute each Frobenius representative, use mu naturality, then the unit equation. This gives z_F = (theta_A tensor theta_D[n])mu P(z)c^{-1}. Applying the assumed Weil equation of B cancels mu and gives cP(Bz)c^{-1}. The ordered inputs are never permuted, so an extra Koszul sign is not inserted. The sole external citation in this step states the required naturality; all other inputs have already been proved here.

Step 6 uses the E-linear morphism formula in def-weil-derived-pullback-tensor-hom, exactly as stated, and End(U) = E from Step 1. Thus cP(lambda id)c^{-1} = lambda id. This proves equality of endomorphisms, which is the scalar pairing equality under the same point equivalence. All operations are derived functors, so the formula does not depend on chain representatives. Zero objects and arbitrary rational Weil data are addressed explicitly.

Step 7 reads each of the two displayed definitions in def-weil-frobenius-cohomology-transport. Substituting the exact theta_A and theta_D from the item gives the two displayed action equations separately. X_0 has exactly its required separated finite-type hypotheses. It does not use properness or identify the two direct images. This step neither needs nor asserts a new base-change theorem.

I checked small cases: U in degree zero with theta_A = t and theta_D = t^{-1}, B the unit pairing, gives (tx)(t^{-1}y) = xy, including t = ell (no stable integral lattice). With A = E[-i] and D = E[-(n-i)], their shifted tensor has total degree zero and the two Frobenius scalars still cancel; i = -1, n = 1 tests negative and successive shifts. If the second scalar is t instead, a nonzero unit pairing is not a Weil arrow unless t^2 = 1, as required. A = 0, D = 0, and a vanishing degree produce zero on both sides. For X = s, the two action substitutions agree with the point calculation; for nonproper X they remain two independent substitutions. These checks reveal no statement dispute.

I checked graph reachability from every proof dependency using a read-only traversal; none reaches the item. proof_deps is exactly the union of the step uses. All 18 citations.json quotes are verbatim portions of the node statements. Each step is under 1200 characters, so there is no long step hiding a lemma. The elementary steps are substitutions, explicit representative-sign checks, or identities from the stated cited inputs; the sole non-elementary Hom calculation is explicitly cited. Off-unit generic tools are declared in split_report.tool_uses with their specific roles. No unproved property has been moved into an unsplit definition or a duplicate/clause node.

## What could not be finished

Nothing in the mathematical split. Required server dry run and direct delivery follow this report; their actual results are appended below.

## Validation log

The initial dry runs rejected five short citation excerpts (under the required 40 characters). I expanded them to verbatim context from the same actual statements, with the step-3 quote specifically giving the functorial shifted-cone construction rather than only the rational morphism formula. No mathematical statement or proof change was needed.

The next server preflight read the mathematical shift notation D[n-i] in step 5 as a nonexistent node citation [n-i]. I inserted spaces in that shift index (D[n - i]); its mathematical content is identical.

The required server dry run exited 0: `OK (not pushed) deliver/Q39/lem-pod-point-weil-pairing-realization at 0db648620ee: preflight passed`. The delivery command runs the server preflight, including check_dag and review_split. I am delivering the same node and citation files with this validation result recorded in the report.
