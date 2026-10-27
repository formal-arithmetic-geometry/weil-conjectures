# Stage-1 report: lem-sfb-ind-etale-jacobi-zariski-left-injective

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-ind-etale-jacobi-zariski-left-injective.json: statement, split; statement unchanged; no exact Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-syntomic-polynomial-kernel-koszul-regular.json: statement, unsplit; kernels of arbitrary finite polynomial presentations of syntomic algebras are locally Koszul-regular; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-conormal-intersection-koszul-regular-ideal.json: statement, unsplit; locally Koszul-regular quotient ideals imply the conormal intersection identity; no Mathlib match.
- citations.json: one verbatim statement quotation for every cited node in every proof step (13 entries).
- report.md: this report. searches.jsonl contains the actual search-command log; search-results.json retains the returned results. Local scratch scripts only write inside this sandbox.

Two new nodes, zero Mathlib leaves. New nodes are statement-only, with empty proof and proof dependencies. No unit record is changed: the item is not the unit's key statement.

## Attachments

None. I searched the project Lean source for the exact blueprint tag and the ind-etale/Jacobi-Zariski/cotangent notions. The regular-sequence finite-presentation theorem in WeilConjectures/RingTheory/JacobiZariskiRegularSequenceLeftInjective.lean is not this item: it assumes a globally regular presentation and does not cover the ind-etale filtered limit. The corresponding regular-quotient conormal declaration likewise does not provide local Koszul regularity over arbitrary rings. No exact closed project declaration was found for a new node either. Mathlib declarations are assessed as potential leaves, not project attachments.

## WANTED

None. All sources used are present under literature/stacks-project/ and the latest blueprint.

## Problems found and corrections

The imported item was unsplit, not false. Its statement, including termwise tensor over B, arbitrary A-to-B, and the explicit canonical conormal map, is preserved verbatim. Its two Stacks references alone did not supply a proof. The split now writes the finite-stage intersection calculation, its use in the conormal injection, the comparison with the canonical presentation on generators, and the two eventual-zero advances in the filtered diagram.

A global regular sequence would be an unjustified replacement for a locally Koszul-regular ideal without Noetherian assumptions. I consequently did not reuse the existing global-regular-sequence theorem as if it covered this case. The new syntomic-kernel and intersection nodes use precisely the local Koszul hypotheses in Stacks 07D3 and 07CX. I also avoided a smooth-only auxiliary node: a general syntomic kernel statement is the source result and is distinct from the existing smooth-pair regular-immersion theorem.

The colimit argument must allow noninjective transition maps. Neither a directed union of subalgebras nor flatness of C over an arbitrary stage is assumed. The existing tensor-colimit lemma handles arbitrary small filtered diagrams. The live cotangent-colimit comparison node now provides the canonical derived comparison. Its quasi-isomorphism is used directly: a degree-minus-one cycle whose class is zero must itself be zero, because the complex has no degree-minus-two term. The existing general module-colimit elementwise lemma then supplies a later-arrow witness. This is a short argument within step 4, not a new node or a per-degree isomorphism assertion.

I read the current latest direct-images proof, especially clause (3), and the latest six-functors Ctf-stability proof. This item supports the recorded local-algebra/strict-henselization chain in that clause; the split keeps that chain. The inherited ancestor chain currently has blueprint.from.node null, and blueprint_refs.py ancestor prints None. I retained that inherited value and via chain, specified the current blueprint place, and searched the whole blueprint for alternative exact statements. No same_as node was found.

## Unfinished work

No unfinished stage-1 argument. The two new statement-only lemmas are deliberately left unsplit for the queue. No Lean file was written, no compiler or build tool was run, and the shared repository and launcher files were only read.

## Searches and route audit

I read delivery-errors B through E and checked their mathematical issues against this split. Before creating nodes I searched DAG ids, statements, source tags 07BQ/07D3/07CX and related cotangent, syntomic, regular-ideal and conormal terms; blueprint_refs.py searches covered the corresponding terms and tags. The new nodes are neither clauses of the item's injectivity assertion nor elementary tensor rearrangements. Tensor symmetry, restricting a commuting square to kernels, restricting a homotopy identity to a kernel, and equality checked on generators/pure tensors stay inside the item's steps.

Each delivered node and the item has actual msearch.py LeanFinder, LeanSearch, Loogle and Mathlib-grep searches, with a second semantic phrasing. I retained the imported search history and recorded each new query as run. For the subsequently removed eventual-vanishing candidate I additionally searched exactly that question in both semantic services; these actual searches remain in the log. All services answered. The closest new hit, CategoryTheory.Limits.Concrete.colimit_rep_eq_zero, applies to a module diagram already known to be a colimit; obtaining that diagram from canonical polynomial conormal modules is the missing substantive assertion, so it is not a one-line specialization. The cotangent zero and map lemmas returned by the other search do not supply it.

I read the relevant candidates in Mathlib/RingTheory/Etale/Kaehler.lean: tensorH1CotangentOfFormallyEtale requires a bijection on presentation kernels in addition to formal etaleness/flatness, and tensorH1CotangentOfIsLocalization only concerns localization. Neither states the item. Standard-smooth chart results do not state regularity of arbitrary syntomic presentation kernels. Ideal.cotangentIdeal_square, elementary cotangent quotient identities, coprime-ideal facts, Noetherian Artin-Rees and regular-element facts do not state the local Koszul quotient-ideal intersection theorem.

The off-unit conormal-injection, presentation-homotopy, tensor-colimit and module-colimit lemmas are explicitly declared in split_report.tool_uses. They are general algebra tools and leave the unit's route intact. The etale affine criterion and presentation functoriality are Mathlib leaves; syntomic composition is already in this unit.

## Not duplicates

lem-sfb-conormal-intersection-koszul-regular-ideal vs lem-weil-pbc-conormal-intersection-regular-quotient: the existing node assumes global regular-sequence generation of the quotient ideal; the new node assumes only local Koszul regularity, with no Noetherian hypothesis.

lem-sfb-conormal-intersection-koszul-regular-ideal vs lem-weil-pbc-projective-symmetric-coefficient-intersection: the existing node is a coefficient-ideal calculation in a symmetric algebra on a projective conormal module; the new node is for arbitrary T and L contained in K with a locally Koszul-regular quotient ideal, without that symmetric-algebra structure.

lem-sfb-conormal-intersection-koszul-regular-ideal vs lem-weil-pbc-jacobi-zariski-regular-sequence-left-injective: the existing node gives cotangent-H1 injectivity for a tower with a global regular-sequence presentation; the new node states an ideal-intersection identity for arbitrary ring/ideal pairs, allowing locally Koszul-regular quotient ideals.

lem-sfb-syntomic-polynomial-kernel-koszul-regular vs lem-pur-smooth-pair-regular-immersion: the existing node is for a pair of smooth schemes over a base, whereas a syntomic algebra in the new node may be singular over the base; the conclusion applies to every finite polynomial presentation, with a local Koszul condition.

No existing node has source tag 07D3. The unit's local-kernel and fibre-kernel generator nodes give numbers or lifts of generators, not Koszul regularity. The algebraic-space lci-composition node gives chartwise factorizations, not regularity of every chosen polynomial presentation kernel.

## Review by NP

For the item I read Stacks more-algebra.tex, lemma-transitive-lci-at-end (07D4), lemma-transitive-colimit-lci-at-end (07D5), and the following henselization application, as well as the current blueprint ancestor context. For the syntomic-kernel node I read lemma-syntomic-lci (07D3), the local-complete-intersection definition and lemma-koszul-independence-presentation. These justify the kernel assertion for every finite polynomial presentation, not just one chart. For the intersection node I read lemma-conormal-sequence-H1-regular-ideal (07CX) and its preceding local sequence argument: all positive Koszul homology vanishing includes H1 vanishing, which is exactly the hypothesis used by that source. For the reused cotangent comparison I read algebra.tex lemma-colimits-NL (07BQ), including its proof in the canonical polynomial presentation, and the full live comparison statement. It specifies the actual canonical chain map, its quasi-isomorphism, and the derived isomorphism, with arbitrary transitions and a small filtered category. I also opened the full existing module-colimit elementwise statement; its explicit eventual-zero clause is what step 4 uses. The common containing universe and small index category are explicit in step 1.

In step 1 I opened all four cited statements. The ind-etale definition supplies the filtered diagram and finite-presentation etale stages. The ring/affine criterion supplies the affine etaleness required by the syntomic-composition statement, whose last sentence explicitly makes such a ring map syntomic. The new syntomic-kernel statement then applies with R=B and E=C_i to the chosen finite presentation. Finite presentation entails finite generation, which is all that is needed to choose that presentation. No condition on A-to-B enters.

In step 2 I checked that q is surjective, L is contained in K, and K/L is exactly the kernel from step 1. Thus the local Koszul hypothesis of the new intersection node is satisfied in T/L, giving L intersect K squared equals LK. The existing composed-conormal statement explicitly allows arbitrary variable sets and assumes just this equality; its tensor order is reversed by tensor symmetry. The functoriality statement explicitly supplies the differential square, so the restriction to cycles is an injection. The quotient identifications are consequences of the two surjections; no flatness theorem is hidden here.

In step 3 I checked the chosen comparison T-to-A[C_i] generator by generator against evaluation. The existing homotopy-equivalence statement covers any commuting presentation map and gives the two homotopy identities, so on degree-minus-one kernels they are inverse identities. The functoriality statement supplies the induced conormal maps. Their composite sends [g] tensor c to c[phi-sharp(g)], exactly the formula in the item. Applying a transition map to both formulas gives the same expression on every pure tensor; this proves the compatibility required in step 4. This checks the canonical map, rather than merely exhibiting an unspecified isomorphism of kernel modules.

In step 4 I checked both uses of the existing tensor-colimit statement: N is first the fixed B-module I/I squared and then the fixed free B-module on the b's; both are permitted with arbitrary transitions. The first use represents x. Since x is a cycle, the differential of its representative dies in the limit, and the second use kills that differential at a later stage. The existing cotangent comparison then applies with R=A. The image z of u_j(t_j) in its degree-minus-one colimit module is a cycle with zero image in target H-minus-one. Quasi-isomorphism makes its class zero, and there are no degree-minus-two boundaries, so z itself is zero. The existing module-colimit elementwise lemma kills the representative at a later stage. The compatibility already proved identifies its later image with u_k(t_k). Finite-stage injectivity now kills t_k and hence x. This argument needs no unquoted exactness or flat base-change lemma.

I tested the statements at the zero ring, identity extension, empty-variable/empty-sequence presentation and a constant filtered diagram. Zero-algebra primes are vacuous and the kernel quotient source of the item is zero when C is zero. For K/L zero, the empty regular sequence gives K=L and the intersection identity reduces to L squared equals L squared. At primes outside V(K/L), K is the unit ideal locally, making the same identity automatic; the stated local condition only needs primes containing K/L. Noninjective transition maps cause no loss because both advances use arrows and eventual vanishing, not embedded subrings. I corrected the initial temptation to use global regular sequences and, after the dry run exposed a newly live comparison node, removed my redundant colimit candidate and reused that derived comparison plus the existing module-colimit elementwise lemma. All four steps are below 2000 characters and no step hides a separate comparison or local-to-global lemma. Every cited node's needed conclusion was read and has a verbatim quotation in citations.json.

## Dry-run repair

The first dry run stopped at its duplicate gate: another delivery had made lem-sfb-filtered-colimit-naive-cotangent-comparison live. I opened that complete statement, removed my proposed colimit node, and cited the live comparison instead. I also found and opened lem-weil-pbc-filtered-colimit-modules-elementwise. Step 4 now gives the no-boundaries argument explicitly and applies its eventual-zero clause. This reduces the delivery from three to two new nodes. No claim that the overlapping nodes are distinct was used to bypass the duplicate gate. All 13 final citation quotes were checked against the statements.
