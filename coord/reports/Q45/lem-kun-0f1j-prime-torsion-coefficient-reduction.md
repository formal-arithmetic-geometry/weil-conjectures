# Worker report: lem-kun-0f1j-prime-torsion-coefficient-reduction

## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-0f1j-prime-torsion-coefficient-reduction.json`: statement, eight-step split; not a Mathlib leaf. No new nodes and no new Mathlib leaves.
- `citations.json`: one literal statement quotation for every use in every step.

## Attachments

None. Searches in the read-only slopmaster2 project for the blueprint id, Tag 0F1J, punctual-base-change vocabulary, and coefficient/restriction vocabulary found no declaration stating all clauses of this item. The ordinary-module change-of-rings node and generic Kunneth declarations do not state this sheaf comparison with both normalized morphisms. Upstream master is reference material only.

## WANTED

None. The current blueprint and the relevant Stacks source files are present.

## Errors and changes

The original statement is retained exactly. Its initial empty proof needed the coefficient categories and the actual comparison map checked, rather than just the equality of tensor objects. The main-20261015 blueprint supplies the same prime-torsion paragraph as the earlier snapshot. The source Stacks Tag 0F1J, label `lemma-punctual-base-change-upgrade`, has the coefficient identification and says “Similarly for the other term”; the eight steps supply the details of those identifications and their map normalization.

The existing `lem-kun-change-of-rings-tensor` states a theorem about ordinary modules, not sheaves; I did not cite it as though it supplied the sheaf theorem. The quotient/balancing calculation works directly for sheaves and is short, so it stays in Step 1. A draft helper node was removed before delivery after checking the rule against elementary new nodes. No new node remains.

I corrected a draft inference that treated an arbitrary R-model of Rg_*F as degreewise killed by ell. The final Step 5 first uses the canonical restriction comparison to a k-model, which is the justified coefficient choice. I also corrected the draft adjoint's source: the counit is g^{-1}Rg_*F to F on T and is pulled back by e^{-1}; its tensor with A_Y is the map from h^{-1}L_R to B_R. No statement dispute or route departure is involved.

Mathlib searches were run with msearch.py for the item in two natural-language phrasings, with Loogle, LeanSearch, and grep. Hits for ordinary Module.Flat tensor exactness, TensorProduct restriction identities, and SheafOfModules.restrictScalars were read; they do not state the derived etale coefficient comparison or its counit compatibility. Existing inherited searches were preserved, including recorded unavailable services. The searches for the removed draft helper remain in its search log but are not claimed as a delivered node.

## Review by Q45

I read the item, its parent `lem-kun-0f1j`, its unit and chapter records, the current blueprint proof, and the Stacks source for Tag 0F1J. I also read Modules on Sites Section 03EK (the sectionwise tensor, its sheafification, and the bilinear universal property), and Cohomology on Sites Tags 06YQ, 03FD, 0D6J, 07A7 and 0G7E where relevant. For flat pullback I read Modules on Sites Tag 05VD and its existing DAG statement. Only the blueprint/Stacks route is used; no SGA source is used.

Step 1 uses the definitions of sheaf tensor, scalar restriction and sheafification. Its mutually inverse formulas are locally well-defined: quotient sections and coefficient scalars need only local lifts. The term ell z tensor y vanishes because ell y=0. This explicitly avoids the false assertion that every quotient sheaf section lifts globally. Step 2 uses the precise forgetful lemma saying kernels and sheafified cokernels agree, and the definition of flatness; exact scalar restriction then lets the natural quotient tensor formula prove flatness of E/ell E. These are elementary deductions, not new lemmas.

Step 3 applies the actual flat-module pullback statement to the geometric inverse images p and ph with constant R and k coefficients. The cited set inverse-image lemma gives the geometric-morphism hypothesis; the module inverse-image statement supplies the constant-ring identification, exactness, and equality with module pullback. Its cokernel clause gives the needed quotient identifications. No properness, finite type, or flatness of the scheme maps is inserted. Step 4 uses exactly clause (1) of `lem-kun-kflat-criteria` for flat sheaves in degree zero, then the derived-tensor definition and derived-category localization. The displayed differential equation checks chain compatibility; inversion of quasi-isomorphisms proves naturality on derived roofs. This also verifies bounded-below membership when used later.

Step 5 uses the statement of `lem-sbc-canonical-restrict-scalars-functor-comparisons` for g and f', not any assertion that scalar restriction preserves injectives. The definition of direct image gives the bounded-below codomain, and the derived inverse-image definition gives the termwise model. Step 6 applies the same canonical comparison for e and h to the degree-zero tensor sheaf on Y. Every input is bounded below, matching the cited theorem's scope.

Step 7 uses derived inverse-image monoidality and the adjunction-compatible site composition to identify h^{-1}(f')^{-1} with e^{-1}g^{-1}; it then uses the exact counit identity stated in `lem-sbc-restrict-scalars-derived-adjunction-identities` for g. Naturality of the quotient tensor map in the second variable gives the displayed equation of adjoints. Step 8 uses the same cited node's unit identity for h and the definition of a mate to derive b kappa_R = U(kappa_k) a explicitly. It does not infer equality of derived maps from an unproved faithfulness claim. Every cited statement was opened; citations.json quotes its literal text, including the actual unit/counit formulas, so each use can be checked without following a node's proof.

I checked the small cases n=ell, n=ell squared, zero E, zero F, and empty sites. For n=ell squared the ring quotient k is not flat over R, and the argument still works because only E and its quotient as a k-sheaf need be flat. When n=1 there is no prime dividing n, so the hypotheses have no instance. The balancing and mate calculations also hold for ell=2 and for disconnected schemes. The qcqs and invertibility hypotheses are retained from the item's context but are not needed by the purely formal coefficient calculation. No finite-type or constructibility hypothesis is added.

The generic off-unit tools (flat pullback, exact forgetful/inverse-image facts, site composition, coefficient comparison and the adjunction identities) are declared in `split_report.tool_uses`. They support this unit's coefficient reduction and invoke no smooth base-change theorem. I checked all eight step lengths: each is below 2000 characters, and none conceals a standard comparison lemma beyond its cited statements.

## Not duplicates

No new nodes are delivered. The ordinary-module tensor node is reused as reference material only; its elementary sheaf analogue is written in the proof rather than duplicated.

## Unfinished work

No mathematical part of this one-level split is left open. Required server dry run and push are performed after this report.
