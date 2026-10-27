## Worker report

Group Q28, stage 1, item lem-per-finite-character-fourier-kernel, 2026-10-24. No prior item, split, or report was present in this sandbox. The live item was unsplit, and no released repair note was found. Only files in this sandbox were written. No Lean was written and no compiler, Lake, or build command was run.

### Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-finite-character-fourier-kernel.json: item, split into five proof steps; its statement and statement dependencies are unchanged.
- dag/nodes/sec-deligne-laumon-a1/lem-per-finite-character-dual-cardinality.json: statement, Mathlib leaf, specializing CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, with finiteness also supplied by CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity.
- citations.json: one verbatim statement quotation for every node cited by each item step.
- searches.jsonl: actual search-command records; the JSON search entries reuse these records without inventing queries or verdicts.

### Attachments

None. Searches of lean/WeilConjectures for the item tag, card_monoidHom, exists_apply_ne_one_of_hasEnoughRootsOfUnity and sum_hom_units found no attachment. The concept search found AddChar.sum_const_mul_eq_ite and AddChar.sum_compTrace_sub_mul in WeilConjectures/Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean (read in full): these sum a given additive character, or specialize a finite-field trace pairing, rather than the full character group with arbitrary cyclic target. They do not state this item. The new cardinality fact is in Mathlib, not a project attachment.

### WANTED

None. The ILO source and all Mathlib sources used were available locally.

### Corrections and source scope

The imported statement is valid and was retained. The former item had no proof. ILO, Travaux de Gabber, VIII Lemma 5.3.5 proof, printed p.124 / PDF p.130, was read directly: it diagonalizes an abelian cotangent action when the field contains the relevant roots and averages parameter lifts. It does not itself state this scalar Fourier formula. Accordingly proof_origin.by is agent, as the original source record already requires. The scalar expansion is supplied here, with its non-elementary character-count and separation inputs cited as DAG nodes. No SGA route is used.

Read the fixed chapter sec-deligne-laumon-a1 and unit sk-p-dl-a1-perverse, and the newest blueprint ancestor lem-per-artin-gabber-affine-curve and its proof under literature/blueprint/latest. This is a descendant scalar-algebra prerequisite of the inherited regular-local purity/modification branch, not a replacement of the unit's Fourier/perverse route. Blueprint provenance retains that chain and records the exact ILO averaging paragraph.

The full-DAG searches included the relevant declaration names, finite-character/annihilator/cardinality concepts, the Mathlib Duality source path, and root-of-unity facts. Whole-blueprint searches with blueprint_refs.py used character, character group, annihilator, monoidHom and roots of unity; ancestor returned lem-per-artin-gabber-affine-curve. No equivalent blueprint node was found. Existing lem-per-finite-character-annihilator-duality, lem-exc-field-roots-cyclic-bound and lem-sfb-finite-additive-group-card-annihilator were reused. The latter two are Mathlib leaves despite being filed in other units, so no route exception is needed.

### Unfinished work

None for this one-level split. The sole new node is already a Mathlib leaf and carries no proof steps or proof dependencies.

## Not duplicates

lem-per-finite-character-dual-cardinality vs lem-per-finite-character-annihilator-duality: the new leaf asserts the cardinality of the entire character group; the existing node asserts the inverse annihilator correspondence on subgroups and contains no character-cardinality conclusion. Their Mathlib source file is the same, but the new source declaration is lines 95-97, whereas the old source declaration is lines 176-207. The existing node is cited for separation rather than duplicated.

lem-per-finite-character-dual-cardinality vs lem-per-finite-character-fourier-kernel: the new leaf is a general counting theorem under exponent-root hypotheses and contains no sum, evaluation point, inverse, or cyclic-target comparison. It is a genuine Mathlib ingredient. The item itself supplies the comparison, separation application, reindexing and cancellation.

## Review by Q28

I read the item against ILO VIII 5.3.5 at printed p.124, the current latest ancestor and unit, the statements of all four cited nodes, and the exact Mathlib declarations behind the new leaf. The source's implicit scalar splitting argument is identified as an agent expansion; it has not been attributed to a nonexistent Stacks tag. The retained field, finite abelian group, cyclic group, equal order N, positive N, injective embedding, and nonzero N in the field are exactly the imported hypotheses. The proof actually needs less of the characteristic hypothesis, but it is retained. There is no statement dispute.

Step 1 uses precisely the existing finite additive group cardinal-annihilator statement, read in full. To apply it, write the same multiplication operation additively; its N-fold addition is the Nth power. This applies both to H and C, without requiring commutativity for that cited theorem. The subsequent Euclidean-division proof that the least common annihilating exponent divides N is written out, so no exponent-divisibility theorem is smuggled in through that citation.

Step 2 uses precisely the field root-bound node: it supplies finiteness, cyclicity and the bound for every positive root order, and k is a field. A generator of C has exact order N by counting its distinct periodic powers, and injectivity of iota preserves that order. Thus the N known roots already exhaust a group of at most N roots. The exponent e is positive by its definition and divides positive N by Step 1, so d=N/e is positive; the equality ed=N and cancellation of positive d prove that z^d has exact order e. Cyclicity for that e is a separate direct application of the cited node. No algebraic closure or embedding of k into the complex numbers is assumed.

Step 3 uses precisely the new cardinality statement. I read Mathlib/GroupTheory/FiniteAbelian/Duality.lean lines 41, 58, 81-97: the stronger multiplicative equivalence gives finiteness and the cardinality theorem gives the equality. I also read EnoughRootsOfUnity.lean lines 27-29: the two root conditions written in the new statement are its two fields, with primitive root meaning exact positive order. Specializing M=k needs only field instances. The step verifies those conditions from Step 2 before applying the leaf. The bijection from C-valued to field-unit-valued homomorphisms is proved explicitly: N annihilates H, every value lies in mu_N(k)=iota(C), and uniqueness of preimages proves multiplication preservation. This comparison is why the item is not a one-line Mathlib leaf.

Step 4 uses precisely the existing annihilator node, not the proof of that node. Its stated forward formula sends the trivial subgroup to the whole character group; its inverse formula sends that whole group to the intersection of its kernels. Since the correspondence is a bijection with the stated inverse, that intersection is the trivial subgroup. This supplies a separating character for h unequal to 1; Step 3 supplies its C-valued preimage. The exponent-root assumptions required by the existing statement were verified in Step 2. No extra character-extension theorem is used.

Step 5 is elementary finite-sum algebra. I checked the actual bijection chi maps to chi_0 chi and its inverse, and the inverse-value multiplier iota(chi_0(h)) inverse. The sum equation yields a product equal to zero. A nonidentity unit has nonidentity inverse, so the first factor is nonzero and field cancellation applies. At identity, all N terms are 1. The sign and inverse in the original formula are thus accounted for explicitly.

For B1-B8, the new node introduces its own E, k, e, roots and character group; its field notion cites def-weil-field, and all remaining group/character/exponent terms are written inline. It is statement-only with empty proof and dependencies, a real source declaration with file and read lines, and a Mathlib match. The new node's three search kinds and Loogle query were actually run through msearch.py, and its exact records are preserved. The other candidate hits (complex AddChar duality and MulChar/DirichletCharacter results) have different interfaces; the direct group-homomorphism declaration was read rather than inferred from its name. The new statement has no finite-character-sum clause of the item. There are no new unsplit nodes, no unquoted non-elementary input, and no step exceeds 2000 characters.

Small cases checked: N=1 gives the trivial H and C, e=1 and the one-term sum 1; H cyclic of order 2 over a field of characteristic different from 2 gives 1+(-1)=0 at its nonidentity element; H=(Z/2)^2 with N=4 has e=2, so the proof must not confuse exponent with group order, and gives four characters. An infinite splitting field and a finite splitting field both work because only the root subgroup is bounded, not the field. Positive characteristic prime to N causes no division by N in the calculation. For the new leaf E trivial gives exactly one homomorphism; a field without a primitive e-th root does not satisfy the hypotheses and is not used. The proof never assumes H cyclic, and the noncyclic order-4 example checks that distinction. No second worker was used under the direct-delivery brief; this is my own signed review.

The first dry run required a longer verbatim quotation for the finite-group annihilator: the original exact formula was below the tool’s 40-character minimum. I replaced it with the whole cited statement, including the additive-group assumptions and the meaning of repeated addition. No mathematical change was needed.
