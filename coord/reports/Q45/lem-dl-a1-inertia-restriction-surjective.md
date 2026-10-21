## Worker report

Files written: dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-inertia-restriction-surjective.json, split with six proof steps; dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-galois-prime-residue-lifting.json, statement-only non-Mathlib input; dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-galois-over-intermediate.json, exact Mathlib leaf. citations.json contains the seven verbatim step citations. All writes are in the Q45 item sandbox.

Attachments: none. I searched WeilConjectures for the exact blueprint tag and inertia/restriction/surjectivity vocabulary. Ideal.exists_mem_inertia_eqOn in WeilConjectures/Mathlib/RingTheory/Invariant/Profinite.lean:142 has an actual proof but requires a maximal ideal; the item allows arbitrary primes. The residue-automorphism and invariant-action declarations in that file are inputs, not an exact statement of inertia restriction in a tower. No claim of closure based merely on a declaration name is made.

WANTED: none.

The statement agrees with Stacks 0BSX and is unchanged. Its empty imported proof needed a real split: Stacks ends with 'in exactly the same way', so the residue correction had to be written out. No statement dispute or departure from the unit route was found. The current main-20261015 conventions paragraph and unit sk-d-dl-a1-setup identify the inertia application; 0BSX is the algebraic input already chosen by the parent split.

Nothing mathematical is left unfinished in the item's proof. The new 0BRK input is intentionally statement-only, as required for a one-level split. The other new node is already a Mathlib leaf. No Lean was written, and no compiler, Lake, local DAG check, or git command was run.

## New nodes

- lem-dl-a1-galois-prime-residue-lifting: statement, unsplit, Stacks 0BRK parts (1) and residue-surjectivity part of (2), allowing infinite Galois extensions. Not a restatement of the item: it concerns one extension and its prime and residue actions, with no inertia restriction map or field tower.
- lem-dl-a1-galois-over-intermediate: statement, mathlib, IsGalois.tower_top_of_isGalois, Mathlib/FieldTheory/Galois/Basic.lean:152 (ambient hypotheses at 145-147). Exact match with no finiteness requirement.

## Searches

All current Mathlib searches were run through the required batch2/msearch.py command and are in searches.jsonl. I read the actual hits. The 0BRK searches used both 'possibly infinite Galois extension ... transitive on primes ... decomposition group' and 'profinite Galois group ... prime stabilizer ... fraction field of the quotient', plus Loogle, LeanSearch and grep. Finite-group results do not establish the infinite case. The profinite invariant-ring results at Mathlib/RingTheory/Invariant/Profinite.lean:61 and :175 require continuous action and invariant-ring hypotheses; establishing these for an integral closure and comparing quotient fraction fields is mathematical content, not typeclass-only one-line specialization. I opened that file and the project integral-closure specialization. Accordingly 0BRK stays unsplit, with the candidates documented rather than mislabeled as a leaf.

For the upper Galois tower node, LeanFinder and LeanSearch both returned IsGalois.tower_top_intermediateField and IsGalois.tower_top_of_isGalois; grep gave Basic.lean:152, which I opened through the full signature and its proof. Loogle's broad IsGalois query showed the class and its projections. The exact theorem's Stacks annotation is 09I2, so I used that precise tag rather than the normality-only 09HN or separability-transitivity 09HB.

The item was re-searched by inertia restriction in a tower; the returned field restriction and residue automorphism surjections are inputs, not the simultaneous inertia lift. I preserved the prior item's recorded Q151 searches and added the current Q45 searches, without inventing unavailable or unrun queries. Additional exploratory searches for integral-closure normality found an existing exact DAG leaf, which is reused.

Before creating nodes I searched the whole dag/nodes tree by 0BRK, 09I2, prime-transitivity vocabulary, residue-automorphism vocabulary, tower_top_of_isGalois and integral-closure fraction-field matches. I also ran tools/blueprint_refs.py ancestor and searches for inertia, Galois, integral closure, 0BRK, 09I2, prime, residue, 09HN and 09HB. Broad searches contained only cover/sheaf statements or special cases, not either proposed node. same_as is empty for the item and new nodes. The provenance is rem-dl-a1-conventions with the existing intervening chain retained and this item prepended for its children.

## Not duplicates

lem-dl-a1-galois-prime-residue-lifting vs lem-exc-finite-galois-prime-residue-lifting: the existing 0BRK node assumes a finite Galois field extension; the new node allows infinite extensions, which are needed when M/L is infinite. It is a genuine generalization, not a special case of the existing node.

lem-dl-a1-galois-prime-residue-lifting vs lem-exc-dvr-galois-degree-data: the latter assumes a DVR and a finite normal separable field extension, and concludes finite prime and valuation/degree data. The new node assumes an arbitrary normal domain and possibly infinite Galois extension, and includes residue automorphism lifting for arbitrary primes.

lem-dl-a1-galois-prime-residue-lifting vs lem-exc-finite-tame-character-tower: the latter is a finite Galois tower over a DVR in positive residue characteristic, concerning tame characters and inertia comparison. It does not give prime transitivity and residue lifting for an arbitrary normal domain and infinite extension.

lem-dl-a1-galois-over-intermediate vs lem-per-galois-compositum-restriction: that node assumes a finite Galois subfield K/k and a compositum equality K vee F=E and concludes restriction injectivity. The new node assumes E/F Galois without finiteness, and only enlarges the base to an arbitrary intermediate field.

lem-dl-a1-galois-over-intermediate vs lem-zl-geometric-irreducibility-transitive: that node is transitivity of geometric irreducibility, not Galois permanence under an intermediate base; its 09I2 occurrence is in a proof, not its statement.

lem-dl-a1-galois-over-intermediate vs new-lem-sbc-finite-field-closed-component-descent: that node is descent of closed component subsets of schemes after a finite field extension, not a field-theoretic Galois tower statement.

lem-dl-a1-galois-over-intermediate vs lem-weil-pbc-separable-closure-exists-galois: that node requires a separably closed upper field in its second clause. The new node needs any Galois upper field, even a finite non-separably-closed one.

lem-dl-a1-galois-over-intermediate vs lem-weil-pbc-normal-extension-normal-over-intermediate: the existing lemma states only algebraicity and normality, allowing inseparable extensions; the new exact Mathlib leaf includes separability and therefore supplies the full Galois hypothesis required by 0BRK.

## Review by Q45

I read more-algebra.tex, lemma-one-orbit-geometric-galois-compare (0BSX, lines 32869-32895), and checked the statement's normal base, both Galois extensions, arbitrary chosen prime, and both quotient fraction fields against it. The item needs only its inertia clause; no decomposition surjectivity is assumed as a black box. I read the preceding lemma-one-orbit-geometric-galois (0BRK), its two assertions and proof, for the new infinite prime/residue input. I read fields.tex lemma-galois-goes-up (09I2, lines 2694-2702) and Mathlib's exact upper-tower theorem for the new leaf. Neither source assumes finite extensions, Noetherian rings, DVRs, or separable residue extensions.

Step 1 cites the full statement of lem-weil-pbc-integral-closure-algebraic-extension-normal, which explicitly gives the fraction field AND integral closedness in that field for any algebraic extension. I read that node's full statement and its sources 00GO/0308/034L and the denominator argument. Applied twice it gives B normal with Frac(B)=L and C integrally closed in M. Together with the definition of integral closure this proves C is also the integral closure of B in M: a monic equation over B is one over C, so integral closedness of C suffices. There is no unstated elementwise transitivity theorem hidden here. Contraction gives the quotient injection and the fraction formula gives the residue embedding. The step is marked non-elementary because it applies the cited theorem.

Step 2 is elementary from the given normality and monic-equation definitions, with def-weil-pbc-integral-closure cited for the latter. I checked use of both g and its inverse in the stability equalities, and the restriction of the residue identity through the injective residue field map. This proves the homomorphism is well-defined, not merely its set-theoretic surjectivity.

Step 3 cites lem-weil-pbc-normal-subextension-automorphism-extends for exactly the automorphism extension it states, and the new upper Galois leaf for M/L. I opened the extension node and checked that both of its normality hypotheses hold. Its lack of finiteness is essential here. The step refers back to the already proved ring identifications, rather than taking such identifications from a definition node. These two cited statements are quoted verbatim in citations.json.

Step 4 cites part (1) of the new 0BRK input, with base B and fraction field L. I checked the explicit equation tau(r) intersect B=h(q)=q, the primality of an automorphism's image, and that rho fixes L. The product order is rho tau, so d(r)=r and d restricted to L is h.

Step 5 cites part (2) of the same input, not a Yoneda-style or definition-only substitute. The explicit fraction calculation verifies that the residue automorphism of d is over kappa(q). All 0BRK hypotheses were established in steps 1 and 3. Its conclusion supplies epsilon in Gal(M/L) fixing the prime AND inducing precisely that automorphism; no normality or separability of residue extensions is silently assumed.

Step 6 is elementary group multiplication. I checked epsilon inverse d rather than d epsilon inverse: the residue action is identity and the restriction is still h. It concludes both clauses in the definition of I_r, then surjectivity for the arbitrary h chosen.

Small cases checked: L=K gives a trivial lower inertia group, and M=L makes the correction groups trivial and lifts h itself. When A is a field the only prime is zero and both inertia groups are trivial, as the residue fields are L and M. At a generic prime of a general domain the residue action condition likewise gives no spurious inertia. Unramified primes give trivial lower inertia; totally ramified finite extensions reduce the residue correction to the identity. Infinite extensions, nonmaximal primes, and inseparable residue extensions remain covered by 0BRK exactly as stated; none was excluded by the split.

Against delivery-errors B-E I checked that every new object and Galois condition is explicitly introduced, all notions either have definition dependencies or are defined inline, every non-elementary use is a cited statement, the children are strictly different from inertia restriction, no cycle is introduced, and no off-route theorem of another unit is used except existing Mathlib leaves. I corrected my preliminary thought that the project's maximal-ideal inertia lift might attach to this item: it cannot. I also chose 09I2 after reading the Mathlib annotation, and reused the old integral-closure leaf instead of creating its duplicate. No non-elementary step exceeds 2000 characters. The new nodes remain statement-only and every citation quote is a literal substring of its cited statement.
