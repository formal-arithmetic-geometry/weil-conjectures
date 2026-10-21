# Worker report: lem-dl-a1-galois-prime-residue-lifting

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-galois-prime-residue-lifting.json: item, split, statement unchanged; six proof steps.
- dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-profinite-invariant-ring-primes.json: statement, Mathlib leaf; integral extension, prime transitivity and quotient-automorphism lifting for a continuous profinite invariant-ring action.
- dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-finite-group-limit-profinite.json: statement, Mathlib leaf; topology of the compatible-family limit of finite discrete groups.
- citations.json: verbatim statement quotations for every step-node citation.

## Attachments

None for the item. I searched the live WeilConjectures tree by the blueprint tag and by prime, residue, Galois and decomposition/stabilizer terminology. Algebra.continuousSMul_integralClosure and Algebra.isInvariant_integralClosure in WeilConjectures/Mathlib/RingTheory/Invariant/Profinite.lean:62 and 79 have actual proofs. Ideal.Quotient.stabilizerHom_surjective_integralClosure at line 103 likewise has a proof but states quotient-ring automorphism lifting, not the fraction-field assertion in this item, and does not supply prime transitivity. Thus these do not qualify as an exact item attachment. Their proofs motivated the explicit setup in steps 1-2, not an uncited black box.

## Literature and WANTED

No WANTED documents. I read Stacks more-algebra.tex, Tag 0BRK, lemma-one-orbit-geometric-galois, both clauses and the proof (including the residue normality detail); Tags 0BRI/0BRJ, lemma-one-orbit and lemma-one-orbit-geometric, explain the finite invariant-ring step and localization at the base prime. I also read fields.tex, Tag 0BMJ, lemma-galois-profinite, including the topology defined by the action on the discrete field and the compactness proof. I read the current main-20261015 rem-dl-a1-conventions and the chapter/unit records. The split stays below the convention's existing inertia chain and changes no unit or chapter.

The proof is marked agent: it implements the source's invariant-ring mechanism through Mathlib's profinite theorems instead of reproducing the source's Zorn argument. This is a node-level choice; the unit is conventions with no prescribed proof steps.

For the two new leaves I read the actual pinned Mathlib sources, not just search result descriptions: RingTheory/Invariant/Profinite.lean:39-64,175-179, and Topology/Algebra/Category/ProfiniteGrp/Basic.lean:80-86,223-227,317-328,336-348,380-385. Their declarations and exact source lines are recorded in mathlib_match. Each leaf has actual LeanFinder, Loogle, LeanSearch and grep queries, recorded from searches.jsonl. Some grep calls on single files return misleading file columns; the later directory searches give the correct file/line entries. No unavailable service was counted as a negative search.

## What was wrong or incomplete

The imported node was an unsplit statement. Its statement is correct against 0BRK and was kept verbatim. The finite Galois normalization leaf cannot be used for a possibly infinite extension. More subtly, quotient-ring automorphism lifting is insufficient on its own for fraction fields. Steps 4-6 supply the missing base localization and prove that the quotient becomes the full residue fraction field. No finite-type, Noetherian, maximality of the original prime, or separability of the residue extension is added.

## Not duplicates

lem-dl-a1-profinite-invariant-ring-primes vs lem-exc-finite-galois-prime-residue-lifting: the existing leaf requires a finite Galois extension and its integral closure; the new leaf permits arbitrary profinite groups acting on arbitrary discrete commutative rings with specified invariants, and lifts quotient-ring automorphisms rather than asserting the item's residue-fraction-field statement.

lem-dl-a1-profinite-invariant-ring-primes vs lem-exc-finite-invariant-quotient-normal-action: the existing leaf assumes a finite group and maximal ideals, and also states residue normality; the new leaf allows an infinite profinite group and arbitrary prime ideals, and states integrality and prime transitivity as well as quotient lifting. Neither replaces the other as stated; in particular finite-group assumptions cannot be inferred here.

lem-dl-a1-finite-group-limit-profinite vs lem-exc-galois-krull-finite-limit: the existing leaf identifies a Galois group with a particular limit but does not state the topological compactness theorem for an arbitrary inverse system. The new leaf is the general topology input used after that identification, with no fields or Galois group and no surjectivity assumption on transition maps.

I searched the whole DAG by the declarations, profinite/invariant-ring terminology, inverse-limit terminology and Stacks tags, and used blueprint_refs.py search for Galois/prime, invariant/prime, profinite/ring and finite/group/limit. The hits are convention or geometry/sheaf statements, not these general algebra/topology statements. The ancestor is rem-dl-a1-conventions; the new nodes retain the entire inherited via chain, prefixed by this item. same_as is empty. These are existing Mathlib results exposed as leaves, not restatements of item clauses disguised as new unsplit lemmas.

## Review by Q75

I checked the split against delivery-errors B-E with each cited node's statement open. B: the two new nodes are self-contained statement-only Mathlib leaves with no proof, complete action/topology hypotheses and source line mappings. I ruled out existing DAG and blueprint statements before creating them. The fraction/localization calculations stay in the item rather than becoming elementary nodes. C: citations.json copies the exact statements or relevant verbatim sentences, not text from the proofs of cited nodes.

Step 1 uses precisely the topological inverse-limit identification and nonempty directed indexing from lem-exc-galois-krull-finite-limit, then the generic compact/totally-disconnected limit result from the new topology leaf. The index is a set of intermediate subfields of E, so no large diagram is involved. The pointwise-discrete description is the definition of the Krull topology used in Fields 0BMJ. Step 2 uses the definition of integral closure to restrict automorphisms, the existing fixed-field theorem with intermediate field F to place a fixed element in F, and the normal-domain definition to put it in R. Its continuity argument is written through orbit maps and open slices; it does not invoke an unstated theorem about integral closures.

Step 3 uses exactly the prime-transitivity clause of the new invariant-ring leaf, after compactness, continuity and S^G=R have been checked. Step 4 constructs the localization, prime and action explicitly inside E: nonzero denominators in T permit cancellation, and the displayed kernel proves primality and contraction. G fixes T, so the action formula and the invariant-ring identification are valid. This step is elementary and cites no theorem merely for a tag.

Step 5 uses the exact general quotient-localization formula of lem-weil-pbc-localization-quotient-by-prime twice, once for A and once for B. It applies the integrality clause of the new invariant-ring leaf to the newly verified A subset B; reducing a monic relation proves quotient integrality. The elementary least-degree relation argument explicitly inverts every nonzero quotient element. Thus its fraction-field identification neither assumes that S/s was already a field nor confuses the fibre S/pS with S/s. Step 6 uses exactly the quotient-automorphism surjectivity clause of the new invariant-ring leaf. It then contracts the stabilizer equality and writes the action on fractions, so the lift realizes the originally prescribed residue-field automorphism and not a different quotient action. These citations all say what the steps take from them. All cross-unit inputs are existing Mathlib leaves; no unapproved off-unit theorem is required.

D: the proof carries the continuous invariant-ring setup and the residue comparison; no new node simply restates a clause in the same Galois-normalization setting. E: the proof works for E=F, R a field and p=0 (then B=E), the zero prime of a general normal domain, and nonmaximal primes. I checked the generic invariant theorem with a trivial group (forcing A=B), a nonfaithful action and a zero ring (its prime clauses are vacuous). I checked the topology leaf on a singleton index, trivial groups and nonsurjective maps; compatible families always contain the identity and no surjectivity is used. Residue extensions may be inseparable; the proof only uses automorphisms and integral algebraicity, not a Galois assertion about those residues. All six steps are below 2000 characters; there is no hidden long comparison argument.

## Unfinished work

None in this stage-1 split. The new nodes are Mathlib leaves; no Lean was written and no compiler, Lake, build or local preflight/checker was invoked. The required server dry run and delivery are recorded by deliver.py.

## Dry-run repair

The first server preflight required a notion-node citation in the topology leaf, whose initial statement defined its own topology and displayed the compatible families but cited no node. I added def-weil-directed-colimit-abelian-groups solely for its explicit definition of a nonempty directed set (any two indices have a common upper bound), retaining the elementwise formulation. I read its statement; its abelian-group colimit assertions are not used. No mathematical statement or proof route changed.
