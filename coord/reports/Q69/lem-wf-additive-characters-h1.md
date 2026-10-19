## Files written

- dag/nodes/sec-purity-real-sheaves/lem-wf-additive-characters-h1.json: item, statement, split; six proof steps, no Mathlib match for the whole item.
- citations.json: exact statement excerpts for all eight step citations.
- searches.jsonl: five actual msearch invocations, all successful; their returned records are retained in the item.
- report.md: this report.

No new nodes, no new Mathlib leaves, no unit edit.

## Attachments

No attachment for the item. I read WeilConjectures/Mathlib/NumberTheory/Padics/RingHoms.lean, especially the definitions and theorem surrounding lines 121–180. PadicInt.continuousMonoidHomEquiv and PadicInt.continuousMonoidHomEquiv_comp are closed in the pinned slopmaster2 sorry map (s=false, ts=false). They prove only the group-theoretic correspondence and its precomposition naturality, not the identification with all the etale H1 groups. The occurrences in FundamentalGroup.lean use this correspondence for character vanishing on curves and do not assert the item for arbitrary geometrically connected separated finite-type schemes. Therefore neither is an exact attachment. No Lean was written or compiled.

## WANTED

None. The current blueprint, the cited DAG statements and the Mathlib source supplying the existing residue leaf are available locally.

## Findings and changes

The imported single paragraph had an implicit assertion that compatible residues give a unique adic integer, and it checked continuity only through kernels without writing the neighbourhood argument. I replaced it by six steps. The finite-level naturality square is written explicitly; the residue lift is obtained by applying the EXISTING ring universal-property node to the ring of compatible tuples; local constancy proves continuity of reductions, and inverse images of single residue classes prove continuity of the lifted map at every source point. The inverse identities, additivity, pointed-scheme naturality and the exact inverse-conjugation Frobenius convention are checked separately.

The mathematical statement is unchanged. Its only textual addition explicitly points to def-weil-l-adic-numbers for the topology on the adic integers, with the corresponding statement dependency. The finite base field and prime-coefficient conventions remain those of the source and its definition nodes. No smoothness, dimension-one, properness, or invertibility of ell on U is added: the finite constant torsor statement applies without these assumptions. Only ordinary inverse limits occur; there is no claim comparing derived inverse limits with H1.

The item is not the key statement of sk-p-real-rankone; its six steps realize the additive-character portion of that unit's third step. Neither the unit record nor its route is changed. The current main-20261015 statement/proof agree with the older imported text for this item.

## Existing-node and blueprint searches

I searched the whole DAG for continuousMonoidHomEquiv, ofCompatible, ext_of_toZModPow, inverse-limit rings, and the additive-character and residue vocabulary. I ran tools/blueprint_refs.py search with compatible, Z_\\ell, residue universal, additive characters and residue, and its ancestor command for the item. The broad compatible/residue results were read for candidate statements; none states another copy of this full H1 tower correspondence. The search found lem-exc-padic-residue-universal-property, which supplies the ring-lifting, residue-separation and norm/kernel clauses actually needed; I reused it, rather than introducing a generic character-equivalence node. def-tate-module-abelian-group describes compatible residues but does not supply the topology comparison, so it is unnecessary here. The Fourier additive-character nodes concern multiplicative-valued characters and are different statements. The item has no other blueprint node stating the same result, so blueprint.same_as is empty.

## Mathlib searches

All five queries in the item were run using the mandated msearch.py command with this group and item, and the queries match searches.jsonl exactly. Two LeanFinder phrasings, LeanSearch, Loogle and a grep were read. LeanSearch's groupCohomology.H1IsoOfIsTrivial (Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean:1014) is algebraic group cohomology, not the etale/continuous identification. PadicInt.continuousAddCharEquiv (Mathlib/NumberTheory/Padics/AddChar.lean:102) has the adic integers as its source and multiplicative-valued characters; it is not this correspondence. The Galois-group projective-limit hits likewise have the wrong objects. The ring-residue results are genuine ingredients already covered by the existing Mathlib leaf. I read toZModPow (:447), ker_toZModPow (:459), zmod_cast_comp_toZModPow (:478), lift (:658), lift_spec (:684), lift_unique (:693), ext_of_toZModPow (:713) in Mathlib/NumberTheory/Padics/RingHoms.lean, and norm_le_pow_iff_mem_span_pow (:470) in PadicIntegers.lean. No service failure is treated as absence.

## Review by Q69

I read the current blueprint's lem-wf-additive-characters-h1.md and its .proof.md, the chapter and sk-p-real-rankone unit records, the complete statements of lem-wf-finite-constant-h1-pi1, lem-exc-padic-residue-universal-property, def-wf-weil-group and def-weil-l-adic-numbers, and the Mathlib signatures listed above. There are no new nodes whose sources or hypotheses require a separate audit. The existing residue leaf explicitly warns that Stacks 00M9 is a completion convention rather than a verbatim source for its assertions; I checked its actual Mathlib sources and do not attribute this character theorem to that tag. No SGA source is used.

For step 1, the finite-constant lemma states a natural isomorphism for every finite abelian M on exactly the same U and pointed fundamental group. Each A_n is such a group. Its naturality gives the coefficient-reduction square used in the step; applying inverse isomorphisms verifies the inverse-limit compatibility rather than assuming it. This is the only cohomological input to the correspondence. For step 2 I checked that the residue lemma takes a commutative unital R, so one cannot directly apply it to the nonabelian source Pi. The proof instead constructs the commutative ring R of compatible residue tuples and applies it to coordinate projections, which genuinely are unital ring maps. Residue separation then verifies the two identities. This is a direct specialization of the cited universal property, not an uncited theorem about inverse limits of topological groups.

For step 3 the same residue statement supplies both ker(rho_n)=ell^n Z_ell and the norm criterion, not merely the definition of a valuation ring. Its bound proves local constancy on an open metric ball, so continuity to the discrete finite target follows. Composition with a continuous b and the cited residue compatibility then produce the compatible characters. For step 4 I checked the homomorphism equation at every residue and the exact neighbourhood V=f_n^{-1}({f_n(g0)}). It is open because f_n is continuous with a discrete target. Equality of residues gives the kernel membership, and the cited norm bound puts all b(V) in an arbitrary prescribed ball about b(g0). Thus no compactness, finite generation or surjectivity of f_n is being assumed. The ring construction in step 2 supplies lifts even when there is no surjectivity hypothesis on characters.

For step 5 the separation clause really concerns points of Z_ell, so it applies pointwise to both possible lifts. Additivity is inherited from the finite-level group isomorphisms and residue maps; naturality reduces to equality at each finite coordinate. For step 6 I used the finite-constant lemma's STATEMENT, which explicitly gives f(g) -> f(s^{-1}gs), rather than borrowing a descent calculation only present in its proof. def-wf-weil-group defines degree by geometric Frobenius, so choosing degree one agrees with the stated action. The displayed computation shows why reducing commutes with this exact inverse conjugation. Every uses entry has its own verbatim excerpt in citations.json, checked against the current source statement.

I tested the trivial fundamental group (both sides vanish), the zero family (its unique lift is zero), a finite fundamental group (any compatible family lifts by the same argument even though every adic character must vanish), and the index-zero case (Z/1 contributes a unique coordinate). The argument also handles ell=2 and never divides by a residue-class representative. Changing a degree-one lift by a geometric element changes precomposition only by an inner automorphism, which an additive character kills, consistent with the natural Frobenius action. None of these tests required extra hypotheses or a statement correction.

Against delivery-errors B–E: there are no new statements, clause-restatement nodes or duplicate nodes; the exact coefficient/topology notions are cited; every non-elementary input is a uses entry whose statement was opened; the residue leaf is a Mathlib tool, not a detour from the unit; and no step imports a proof-only construction from another node. The only auxiliary ring is defined in the step itself and used in a direct instance of the ring universal property. The former implicit continuity and inverse assertions are now explicit arguments. All six steps are shorter than 1000 characters and contain no separate omitted comparison lemma. I have not edited another worker's node, any source checkout, project tools, coordination files or the unit. The server checks below will test the actual dependency graph and delivery.

## Not duplicates

No new nodes. The existing residue universal-property leaf is reused unchanged.

## What remains unfinished

No mathematical part of this stage-1 split remains unfinished. Its cited finite-coefficient lemma is an existing DAG dependency whose own proof is outside this item.

## Server validation

The first deliver.py --no-push invocation exited successfully with OK at 5980f03a20 (preflight passed). The report citation-count typo was then corrected from nine to eight; the item and citations were unchanged. The final dry run is run after this correction, before pushing.
