# Q28: lem-per-tame-inertia-surjective-group-trace

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-tame-inertia-surjective-group-trace.json`: item, statement, split in seven steps; no matching project declaration or Mathlib theorem for the full trace assertion.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-monoid-characters-linear-independent.json`: new statement, Mathlib leaf `linearIndependent_monoidHom`, `Mathlib/LinearAlgebra/LinearIndependent/Basic.lean:498`.
- `citations.json`: exact statement quotations for all six node citations, indexed by proof step.
- `report.md`: this report. The unit and chapter records are unchanged; this item is not their key statement.

## Attachments

None. The project-source search by blueprint id, tame inertia, group trace, trace surjectivity and character independence found no project declaration with this statement. `PointCountBound.lean` uses character independence to bound the number of ring homomorphisms, and `Mathlib/FieldTheory/Fixed.lean` bounds algebra maps; neither states the new leaf. No upstream master sorry declaration was treated as finished evidence.

## WANTED

None. All sources used are available locally.

## Problems corrected and route

The item was statement-only and its source described a semilocal argument without providing that proof. The statement is correct and is unchanged, including the absence of Noetherian and finite-type assumptions. I supplied a direct proof at maximal ideals of the invariant ring. Orbit-polynomial integrality, the maximal-prime lemma and CRT replace any need to assume the ring is finite as a module over its invariants. One only needs the finite orbit of the chosen maximal ideal, not a theorem identifying the whole fiber or a localization/base-change comparison. The source place now identifies the actual inputs; it does not pretend that Stacks 0BRI or 0BRJ states trace surjectivity.

I also found a metadata error in the reused CRT node: its source calls Tag 00U3 Chinese remainder, whereas tags/tags identifies 00U3 as algebra-lemma-etale-over-field. The correct CRT source is Tag 00DT, algebra-lemma-chinese-remainder, which I read and cite in Step 6. The existing node has the correct mathematical statement and the matching Mathlib declaration; I report its source-tag error without editing another worker's node.

The unit/chapter and the current main-20261015 ancestor proof were read. This is a generic algebra input below the recorded tame admissible quotient branch from `lem-per-artin-gabber-affine-curve`, not a replacement of a unit step. All reused algebra results are existing Mathlib leaves, so no off-route statement tool declaration is needed. No SGA source is used.

## Searches

The item was searched through the required logged msearch command with LeanFinder, Loogle, LeanSearch and grep, followed by a second plain-language formulation. Hits on inertia, stabilizer maps, arithmetic Frobenius and separable field traces do not state the group-trace assertion for an arbitrary commutative ring. The inherited search records are retained and the new actual searches appended.

For the new leaf, the four actual logged queries searched field-homomorphism independence and multiplicative-character independence. Loogle and LeanSearch gave `linearIndependent_monoidHom`; grep located its declaration at line 498, which I read through its signature and proof. Its target may be any commutative domain. Restricting the independent family of all monoid homomorphisms to the finite list of distinct characters and specializing that target to a field gives exactly the node. LeanFinder gave related algebra-homomorphism versions rather than the exact character declaration; the record says so. Searches in the whole DAG and blueprint by 0CKL, 0CKM, character-independence names and concepts found no existing node stating the new leaf. The existing project uses of the Mathlib theorem do not attach a project theorem with this assertion.

## Not duplicates

lem-per-monoid-characters-linear-independent vs lem-sc-matrix-descent-invariants-span: the latter asserts spanning of a semilinearly invariant matrix algebra, not independence of distinct multiplicative characters; the match is only an ingredient in its proof.

lem-per-monoid-characters-linear-independent vs lem-exc-finite-galois-tensor-decomposition: the latter gives a tensor-product decomposition and sheaf-section bijection for a finite Galois extension, not the independent-family assertion.

lem-per-monoid-characters-linear-independent vs lem-sc-galois-invariant-vectors-span: the latter gives spanning by invariant vectors for a locally constant semilinear cocycle, not character independence.

lem-per-monoid-characters-linear-independent vs lem-per-log-regular-chart-monomial-tor: the latter is a Tor-vanishing result for log-regular monomial charts, not character independence. Its search metadata generated a keyword hit only.

No existing node was found with source tag 0CKL. The new node is neither a clause of the trace assertion nor a renaming of that assertion: it is a general theorem about monoid maps, with no group action on a ring, invariant ring, primes, inertia or trace-surjectivity conclusion.

## Review by Q28

On resuming the retained sandbox, I first ran the prescribed dry run. It rejected the new character-independence leaf because its statement had no definition-node citation. I opened the existing `def-weil-field`, whose statement is exactly the nonzero commutative-ring-with-inverses definition used here, and added that citation and statement dependency. I also spelled out the monoid axioms inline; character homomorphisms and linear independence were already defined by the displayed equations. These are definition clarifications, so the character theorem and the logged Mathlib search question did not change. I updated the verbatim Step 5 quotation in `citations.json`. The seven proof steps and all earlier searches are retained.

I reread the six cited statements against the seven proof steps and compared the item with the current repository: only the intended split fields differ, and the mathematical statement is identical. The project-source search still finds no attachment; the only character-independence use is in `PointCountBound.lean`, where the conclusion bounds ring homomorphisms.

I read Stacks `more-algebra.tex`, Tags 0BRH (lemma-base-change-invariants), 0BRI (lemma-one-orbit) and 0BRJ (lemma-one-orbit-geometric), especially the orbit-polynomial integrality and finite-orbit CRT construction. For the new node I read `fields.tex`, Tag 0CKL (lemma-independence-characters), its full induction proof, and Mathlib's `linearIndependent_monoidHom` signature at Basic.lean:498--499 and its proof. I also read Algebra Tags 00GQ (lemma-integral-overring-surjective), 00GS (lemma-integral-over-field), 00DT (lemma-chinese-remainder), and 00E0 (lemma-Zariski-topology), including the proper-ideal maximal-ideal argument. The proof is marked agent-written because the assembly proving this trace assertion is my argument, with those local source inputs.

For Step 1 I checked the reindexing of the finite sum and A-linearity directly, so its image really is an ideal of A, rather than merely an additive subgroup. For Step 2 I checked that every coefficient of the monic orbit polynomial is fixed and that the identity factor makes r a root. These are elementary calculations, not new nodes.

For Step 3 I opened both cited existing node files. `lem-weil-pbc-integral-injective-lying-over` says every base prime lifts under an injective integral map, and the inclusion of invariants is indeed injective and integral by Step 2. `lem-weil-pbc-integral-prime-over-maximal-maximal` says exactly that the resulting prime is maximal when its contraction is maximal. Neither node assumes Noetherianity or finite generation. Automorphisms preserve maximality and the orbit is finite simply because G is finite.

For Step 4 I opened `def-weil-pbc-localization-at-prime`, which explicitly defines the residue field as the quotient of the prime localization. I wrote the maps identifying it with R/p at a maximal ideal, including why denominators become invertible. The induced D-action therefore has kernel exactly the inertia subgroup used in the hypothesis. The equal fiber cardinalities are proved by the explicit coset bijection with I_p; no faithfulness of G on R is presumed.

For Step 5 the new character-independence statement gives precisely the absence of nontrivial coefficient relations among the distinct image automorphisms. It is applied to the multiplicative monoid of k and coefficients all equal to 1. H is nonempty since it contains the identity, and k is a nonzero field, so this really produces an element b with a nonzero automorphism sum, even when the characteristic divides the order of H.

For Step 6 I opened `lem-pc-crt-ideal-quotient-product`: it provides the canonical quotient-to-product isomorphism for any finite pairwise coprime family, with no Noetherian assumption. I wrote why distinct maximal ideals are comaximal, then composed the isomorphism with the quotient map to obtain the required element of R. The index is the finite set of distinct ideals in the orbit, not the possibly repeated list indexed by G. I checked the inverse in g^{-1}(p) explicitly: terms outside D vanish because r belongs to g^{-1}(p), whereas terms in D act on b. Counting the kernel cosets gives precisely |I_p| times the sum over H. The inertia hypothesis at this particular maximal prime makes that nonzero; no invertibility of |G| or of |D/I_p| is assumed. Nonzero reduction at p implies that the invariant trace is outside m because p contracts to m.

For Step 7 I opened `lem-weil-pbc-proper-ideal-contained-in-maximal`: its statement supplies exactly the maximal ideal that would contain a proper image ideal. This proves the global surjectivity rather than just a residue-wise statement. The preimage-of-one equivalence uses A-linearity explicitly.

I checked small and degenerate cases: the zero ring has no maximal ideals and T(0)=0=1; a trivial group has T equal to the identity; a trivial action has I_p=G and the hypothesis is exactly the expected residue-characteristic obstruction. For a nonfaithful action the kernel is counted within inertia, rather than silently discarded. A permutation action on a finite product of fields can have group order divisible by the field characteristic and still have tame inertia; the supported CRT element, unlike T(1), works in that case. Character independence remains valid for n=0 (the assertion is empty) and n=1 (evaluation at 1), in positive characteristic and on arbitrary monoids.

I checked B--E of delivery-errors against the files: the only new node is statement-only and self-contained; source tags and Mathlib lines are explicit; all searches were run and their actual results retained; every non-elementary proof input is a cited node and every quotation in citations.json is copied from its statement; no use of another node's proof as an interface, no new clause-restatement, and no circular dependence is introduced. All seven steps have fewer than 2000 characters. The subgroup/kernel and residue identifications are explicit elementary arguments, rather than hidden comparison lemmas.

## Unfinished work

No mathematical step remains open in this split. The new dependency is a Mathlib leaf, not an unsplit obligation. No Lean was written and no compiler, Lake or local DAG checking tool was run. Delivery validation is through the prescribed remote dry run.
