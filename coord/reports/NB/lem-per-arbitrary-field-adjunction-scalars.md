# Worker report: lem-per-arbitrary-field-adjunction-scalars

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-arbitrary-field-adjunction-scalars.json`: existing item, split with 8 proof steps; no new nodes.
- `citations.json`: verbatim statement excerpts for every cited node at every proof step.
- `report.md`: this report.

All Mathlib searches for the item were run through `msearch.py` and are recorded in `searches.jsonl`. They found only generic adic completion or sheaf adjunction declarations, so the item remains a project statement rather than a Mathlib leaf.

## Attachments

None. I searched the slopmaster2 source under `WeilConjectures/` for the item id, its displayed mate equations, and the notions “adjunction scalar” and “coefficient extension”; no sorry-free project declaration states this item.

## WANTED

None. The cited Bhatt–Scholze PDF is present at the source path and was read at Lemma 6.7.2, Proposition 6.8.14(1),(2), and Remark 6.8.15.

## Existing-node and duplicate checks

The whole DAG and blueprint were searched for the item id, the ambient mate equation, and scalar-adjunction terms. The closest existing statement is `lem-pur-ordinary-adjunction-scalar-compatibility`, but it assumes (k=\overline{\mathbf F}_q), uses derived-complete integral categories, and has a different direct-image setting; it cannot state this arbitrary-field raw-rationalized item. `lem-pur-finite-coefficient-adjoint-comparisons` is likewise a finite-coefficient exceptional-adjunction statement over positive characteristic and is not a duplicate. No new node was created.

## What was checked and corrected

The imported statement was retained verbatim. I checked that finite-type schemes over a field are Noetherian and finite dimensional, that a finite-type morphism over a field is finitely presented, and that the field makes the coefficient prime invertible; these are exactly the hypotheses needed for the cited Bhatt–Scholze pushforward/constructibility result. The proof now has nine complete steps: finite-stage setup and realization; ambient coefficient-adjunction normalization; the balanced-tensor mate calculation; restriction through the continuous realization; the two displayed Hom identities; linearity, shifts, identities, and tower coherence. Every non-elementary dependency is named in the step using it, and `proof_deps` is the union of those uses.

I checked the cited statements directly. In particular, `lem-a1-rational-direct-image-realization` supplies the actual finite-stage units and counits and their ambient identification; `lem-per-continuous-rational-derived-realization` supplies the tensor pullback model and finite-extension compatibility; `lem-pur-sheaf-ring-derived-coefficient-adjunction` supplies the normalized unit and tensor-Hom formulas; `lem-weil-pbc-ringed-topoi-derived-pushforward-composition` supplies the ambient composition comparison; and `prop-weil-pbc-scalar-extension` supplies the specified (a,b), associators, identity, and shift coherences. The pullback and derived-direct-image triangle/shift facts are taken from `lem-cbc-completed-pullback-triangles` and `lem-pc-right-derived-functor-triangulated`, while raw localization is justified by `prop-weil-pbc-rational-transport`. `citations.json` records a verbatim quote for every such use.

I tested the statement on (E=L), (f=\mathrm{id}), the empty schemes, (B=0), and a ramified finite extension: the comparisons become identities or the zero map, and the displayed mate equations reduce to the ordinary adjunction identities. Characteristic zero fields are allowed because only invertibility of (\ell) is assumed.

## Review by NB

I read the current item node, the fixed chapter and unit records, the route ancestor `lem-per-artin-gabber-affine-curve`, and the full Bhatt–Scholze passages named above. The item statement agrees with the imported statement clause by clause: (k,\ell,f,X,Y,E,L), raw (D^b_c) stages, completed pullback, rationalized direct image, the specified (a,b), both Hom equations, the ambient (J_W) formulation, coefficient-adjunction unit and composition comparison, linearity, shifts, and identity/tower compatibility are all retained.

For Step 1 I checked the finite-type and invertibility hypotheses against `def-weil-scheme-morphism-properties`, `lem-weil-pbc-finite-type-over-noetherian`, and `lem-kun-dimension-finite-type`. Step 2 uses exactly the constructions and actual units/counits stated by the two realization nodes, with the cited triangle and localization nodes for exactness. Step 3 uses the coefficient-adjunction unit formula and the ringed-topos composition comparison, which state the inputs used. Step 4 writes the balanced-tensor reassociation and applies the normalized tensor-Hom formulas; no unmentioned comparison is assumed. Step 5 checks that the ambient equality restricts to the specified (a,b) through the two realization statements and scalar-extension comparison. Steps 6 and 7 are the direct cancellation calculations giving the displayed forward and inverse Hom identities. Step 8 checks linearity and shifts against the cited derived-functor and scalar-extension clauses. Step 9 checks the identity and pentagon/associator clauses against the scalar-extension node, so successive extensions and the ambient normalization agree.

I also checked the small cases listed above and verified that no new statement duplicates an existing finite-field or exceptional-adjunction node. The only correction was replacing the empty imported proof with these explicit steps and recording the required Mathlib searches and citations; the mathematical statement and all hypotheses were unchanged.

## What could not be finished

Nothing remains for this stage-1 split. No Lean file was written and no compiler or Lake/build tool was run, as required.
