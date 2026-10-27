# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-hopf-reduced-core-nilpotent-fibre.json: item, unchanged statement, six-step split; not a Mathlib leaf.
- dag/nodes/sec-six-functors-basics/lem-sfb-hopf-nilpotent-rational-annihilator.json: one new statement-only node; no Mathlib match; exact existing project theorem recorded in lean_candidates. No new proof should be scheduled before the attachment is checked.
- citations.json: verbatim statement excerpts for every citation of every item step.

## Attachments

HopfAlgebra.exists_apply_eq_one_mul_eq_zero_of_isNilpotent belongs to lem-sfb-hopf-nilpotent-rational-annihilator, lean/WeilConjectures/RingTheory/HopfAlgebra/Cartier.lean:787 (through line 799). This is a new smaller local input, not an attachment of the whole item. Its implicit assumptions are Field k, CommRing A, HopfAlgebra k A, CharZero k and IsNoetherianRing A. The theorem takes any g:A →ₐ[k] k and any nilpotent b and supplies t with g(t)=1 and tb=0. I read the proof and its translation formula; there is no sorry in the entire Cartier module. The existing lem-ag-cartier-reduced audit records the downstream HopfAlgebra.isReduced_of_charZero as closed. The maintainer should check transitive closure and attach the local theorem. Per tools/node_fields.py, this delivery records lean_candidates rather than claiming the maintainer's lean_audit field.

## WANTED

None.

## Findings and corrections

The item statement is true and retained, including both characteristic clauses, finite generation and all restricted Hopf identities. Milne, Algebraic Groups (2017), Theorem 3.23, printed pp.70–71, Proposition 3.29, pp.72–73, and the kernel O(M) in Theorem 3.31, p.74, were read. Proposition 3.29 only sketches uniform nilradical nilpotence; step 3 writes the generator argument and step 6 proves the augmentation fibre nilpotence omitted in 3.31, with an explicit exponent. The proof is marked agent-expanded.

The earlier maintainer note suggests citing lem-sfb-affine-group-frobenius-smooth-image. That node now cites this item in its proof, so it cannot be used here. Its characteristic-zero and Frobenius-image conclusions are geometrical consequences of this split, not independent prerequisites. I inspected its whole proof/dependency list and excluded it to avoid a cycle.

The current latest blueprint statement of lem-ag-cartier-reduced is much broader than its stored DAG statement. The latter only concerns closed matrix groups over the fixed field Q_l-bar. Although the attached Lean HopfAlgebra.isReduced_of_charZero proves the general algebraic theorem, citing the stored matrix-group statement for arbitrary k and arbitrary A would violate C4. Instead, the one new statement isolates the strictly smaller rational-point annihilator already proved in the same module. No definition, statement, or theorem is rewritten in Lean. This local input does not assert reducedness, a reduced subalgebra, finite generation, or any augmentation quotient.

Read the current chapter/unit records, latest sk-thm-sf-ctf-stability and det-thm-sf-ctf-stability-direct-images statement/proof. The supporting algebraic-group route remains the inherited route. The ancestry command returns None, as in the parent accepted delivery: retained blueprint.from.node=null and the complete inherited via/place trace. The item is not the unit's key node, so no unit file is edited.

## Searches and Not duplicates

All new Mathlib searches used the required msearch.py command and are in searches.jsonl, with their actual result records copied into the node. LeanFinder, LeanSearch, Loogle and grep all ran successfully. Two semantic phrasings for local Cartier annihilation found only exponentials, antipode identities, nilradical nilpotence and unrelated quotient results. These do not produce t with a prescribed rational value and tb=0. Whole-item searches likewise found no reduced-core-with-nilpotent-fibre theorem. Existing item searches were retained. Read Mathlib's HopfAlgebra class and its antipode identities; they contain no Cartier assertion. The local source theorem is in WeilConjectures, not Mathlib, hence it is not marked a Mathlib leaf.

Whole-DAG statement/title/declaration searches included Hopf, Frobenius, Cartier, nilradical, nilpotent, annihilator, and exists_apply_eq_one_mul_eq_zero_of_isNilpotent. Whole-blueprint searches used blueprint_refs.py for Hopf, Frobenius image, nilradical, nilpotent, Cartier lemma, nilpotent vanishes, characteristic zero, annihilator and rational point. The new id was checked absent before writing. Project Lean was searched for the item tag and Hopf/Frobenius/nilpotent terminology. No project declaration states the complete item. Mathlib matches defining Frobenius and preserving Noetherianity are reused as existing leaves; no new versions are created.

## Not duplicates

lem-sfb-hopf-nilpotent-rational-annihilator vs lem-ag-cartier-reduced: the new statement is local annihilation of a nilpotent at any rational point of an arbitrary Noetherian Hopf algebra; it has neither algebraic closedness nor finite generation hypotheses, and states neither global reducedness nor smoothness. The existing stored statement is for finite type closed matrix groups over Q_l-bar; even its newer blueprint global theorem does not state this local result for general Noetherian Hopf algebras.

lem-sfb-hopf-nilpotent-rational-annihilator vs lem-sfb-affine-group-frobenius-smooth-image: the latter asserts smoothness and the eventual smooth scheme-theoretic Frobenius image for finite type group schemes, and depends on this item. It does not state a rational-point annihilator in a Noetherian algebra.

lem-sfb-hopf-nilpotent-rational-annihilator vs lem-sfb-hopf-reduced-core-nilpotent-fibre: the new statement supplies a single annihilator t at an arbitrary rational point, without any global reducedness, finite type or quotient assertion. Step 2 combines it with proper-ideal maximal extension and the Nullstellensatz to prove characteristic-zero reducedness; steps 3–6 independently construct and verify the positive-characteristic core and augmentation fibre. The item has not been moved into a new node.

## Review by Q10

I checked B–E with the node statements and Milne pp.70–74 open. The only new node is statement-only, introduces k,A,g,b,t, spells out the complete commutative Hopf convention and nilpotence, and cites the Noetherian definition and tensor-product construction it actually uses. Its source records the exact existing project theorem and lines; no unsupported claim of a Mathlib match or new proof is made. Characteristic zero and Noetherianity are essential in that theorem, and both are available at its use. I checked its source statement at Cartier.lean:787–799 and implicit variables at 669 and 783; the theorem is public, and its proof has no sorry. Nothing was compiled.

Step 1 uses exactly the finite-type-over-Noetherian theorem, the definition that every ideal in a Noetherian ring is finitely generated, and the definition of finite algebra generation. The field case is proved inline by the zero/whole-field ideal alternatives. Stacks 00FN, algebra-lemma-Noetherian-permanence, was opened and agrees with that use.

Step 2 uses the proper-ideal/maximal-ideal leaf for Ann(b), clause (1) of the affine Nullstellensatz node to identify M as the kernel of g:A→k, and the new local annihilator theorem to produce t. I checked that clause (1) assumes finite type and algebraic closedness but not reducedness; clause (2) is never used. The new theorem needs Noetherianity (step 1), characteristic zero (this branch) and a rational point g (the preceding citation). The contradiction t∈Ann(b)⊆ker(g) and g(t)=1 is written out. The quotient when C=A has zero counit kernel by definition. The Nullstellensatz is declared as an off-unit generic tool, not a replacement for the unit's route.

Step 3 is the explicit finite-generator monomial argument: nilpotents form an ideal by the written binomial estimate; finite generation comes from step 1; every product of total degree 1+sum(e_i−1) vanishes. This is elementary and creates no additional nilradical lemma. Empty generators give exponent one, so the already reduced case is covered.

Step 4 cites the Frobenius node for its actual ring homomorphism and iterates, and the algebraic-closure definition for roots of T^q−lambda. I verified the scalar-root argument is necessary: a power image need not be a k-subalgebra over an imperfect field. Here k is algebraically closed. The displayed polynomial calculation proves finite generation by x_i^q. If (a^q)^h=0 then a is nilpotent; step 3 kills a^q, proving reducedness. No smoothness or faithful-flatness theorem is used.

Step 5 uses the same Frobenius ring identity inside the commutative tensor ring and the given multiplicativity of Delta and S. The injection of tensor powers is justified by extending a vector-space basis; it does not assume A is finite dimensional. Thus the restricted comultiplication is unambiguous, and injection into A, A⊗A and A⊗A⊗A verifies the specified algebra maps, two counit laws, coassociativity and both antipode laws. This is one direct restriction-of-identities argument, not an omitted comparison lemma.

Step 6 checks K=C^+A lies in ker(epsilon), so the quotient counit is defined. The augmentation ideal of A is generated by y_i=x_i−epsilon(x_i), as the explicit polynomial subtraction shows; its image is exactly the quotient counit kernel. Each y_i^q is in C^+ and dies in D. A degree 1+m(q−1) monomial must contain a qth power, so the entire ideal power is zero. This gives ideal nilpotence rather than merely elementwise nilpotence. No Noetherian quotient, finite-dimensionality, or scheme-theoretic fibre identification is silently assumed.

Small cases: A=k, including the empty generator family; A=k[t] with additive Hopf law (C=k[t^q], D=k[t]/(t^q)); A=k[t,t^{-1}] with multiplicative Hopf law (C=k[t^q,t^{-q}], augmentation at t=1); A=k[t]/(t^{p^e}) with additive Hopf law (r≥e gives C=k, and the augmentation ideal of D=A is nilpotent); and a finite product of copies of k (power image equals A). The zero ring is excluded by the unital counit to the field, not by an added hypothesis. Positive characteristic p=2 causes no change to the Frobenius or antipode checks. The false shortcut of using the smooth-image node was removed, and no statement was changed. All six steps are under 2000 characters. The elementary steps carry their actual calculations, not citations for hidden conclusions. No SGA source is used.

## Unfinished

No mathematical step remains in the item. The new local input already has a project proof; the maintainer's independent attachment/axiom audit remains part of normal review. Server dry-run and direct push are the final delivery checks.
