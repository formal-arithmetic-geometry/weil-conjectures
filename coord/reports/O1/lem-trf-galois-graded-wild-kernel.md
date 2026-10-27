# Stage-1 delivery: lem-trf-galois-graded-wild-kernel

## Files written

- dag/nodes/sec-trace-formula/lem-trf-galois-graded-wild-kernel.json: item, split into seven explicit steps; mathematical statement unchanged.
- dag/nodes/sec-trace-formula/lem-trf-valued-initial-form-automorphism-bound.json: statement-only structural lemma, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-finite-group-prime-power-cardinality.json: statement-only Mathlib leaf, IsPGroup.iff_card at Mathlib/GroupTheory/PGroup.lean:102, using the definition at lines 25–27.
- citations.json: one literal statement quotation for each step/node citation.
- searches.jsonl: the msearch command's actual search log. Existing searches on the imported item were retained.
- report.md: this report.

## Attachments

None. Searches of lean/WeilConjectures for the item tag, wild inertia, ramification groups, and initial-form valuation actions found no declaration stating this item. In particular KummerInertia.lean supplies conditional Kummer-character calculations, not this general non-discrete valued-field result. The two new statements have no exact project declaration. I read the Mathlib valuation RamificationGroup file: it defines decomposition and inertia but explicitly leaves higher groups as a TODO.

## WANTED

WANTED: Michael Temkin, Stable modification of relative curves, arXiv:0707.3953v3, §2.1 and Lemma 2.1.5, for lem-trf-galois-graded-wild-kernel. The expected local PDF is absent. I read https://arxiv.org/html/0707.3953v3, especially the discussion preceding Lemma 2.1.5 and its proof.

WANTED: Ofer Gabber and Lorenzo Ramero, Almost Ring Theory, sixth release, §6.2.8–6.2.12, for lem-trf-galois-graded-wild-kernel and lem-trf-valued-initial-form-automorphism-bound. I read the author-hosted PDF https://pro.univ-lille.fr/fileadmin/user_upload/pages_pros/lorenzo_ramero/releaseLNM.pdf, PDF pages 209–211, printed pages 207–209. No local archival copy exists. The proof is consequently marked agent-written, as required for missing local literature; no download or repository write was made.

The new Mathlib leaf's source is the local Mathlib source itself, which was read at its exact lines.

## Corrections and mathematical choices

The item statement is unchanged. It already includes completeness, a nontrivial rank-one absolute value and extension of that value to finite extensions. No discreteness, residue perfection or additional normality assumption was introduced. The previous source place “printed pp.159–162” does not locate §6.2.12 in the author-hosted sixth release I read; it is now recorded as printed pp.207–209. This is a citation correction, not a statement dispute.

Proposition 6.2.12 itself assumes separably closed residue field. I do NOT apply its surjectivity statement over an arbitrary residue field, or assume an unproved descent from strict henselization. Its final averaging proof works without that hypothesis and is written out in step 2. Only the general inertia pairing of §6.2.8, together with elementary finite character counting, is needed for the structural bound. This avoids making the new node a copy of any clause of the item.

The whole blueprint and DAG were searched by “wild inertia”, “inertia”, “ramification”, “valuation character”, “inertia character”, “initial forms”, “initial form”, “finite group prime power”, and “prime-power exponent”; all blueprint matches were inspected for relevance. Exact proposed ids, the Gabber–Ramero subsection numbers, the Cauchy declaration, and IsPGroup matches were also searched in dag/nodes. Existing Cauchy, normal-fixed-quotient, Galois envelope, uniqueness, degree bound and inseparable tower nodes were reused. latest is the 20261024 snapshot recorded in COMMITS.txt. Its locality node now uses contracting correspondences, rather than the older auxiliary semistable branch; the existing ancestry was retained without changing the unit or chapter.

The seven step texts all have fewer than 1000 characters. There is no step longer than 2000 characters hiding an unextracted comparison.

## Not duplicates

lem-trf-valued-initial-form-automorphism-bound vs lem-trf-galois-graded-wild-kernel: the new statement bounds an arbitrary finite isometric automorphism group modulo its initial-form kernel, with neither completeness nor Galois hypotheses; it asserts no p-group theorem or property of a fixed field. The item must still prove the p-group assertion, orbit-product power membership and faithfulness on the fixed field before the bound can be used.

lem-trf-valued-initial-form-automorphism-bound vs lem-exc-finite-dvr-tame-inertia: the existing statement requires a DVR, normality and positive residue characteristic, and concerns the uniformizer character. It does not bound arbitrary initial-form actions for non-discrete fields or arbitrary residue fields. The new bound also has no character surjectivity assertion.

lem-trf-valued-initial-form-automorphism-bound vs lem-per-tame-radical-kernel: that node treats the absolute Galois subgroup fixing roots of a uniformizer over a strictly henselian DVR; the new node treats finite valued-field automorphisms without a uniformizer or strict henselianity and gives only an upper bound.

lem-trf-finite-group-prime-power-cardinality vs lem-sfb-finite-group-prime-power-exponent: the existing statement concerns finite matrix subgroups. Our application is the abstract finite quotient Gamma_N/Gamma_T, with no matrix realization in the item. The new node is the exact general Mathlib statement, not another matrix-subgroup node; using the old one would require an additional faithful linearization not in its statement. There was no node stating IsPGroup.iff_card for arbitrary groups.

## Review by O1

I read Temkin §2.1, the four clauses and proof of Lemma 2.1.5, and Gabber–Ramero §6.2.8, (6.2.9), the hypotheses of §6.2.10, Proposition 6.2.12 and its final averaging argument. Temkin's henselian-field discussion explains the expected tame fixed field, but it does not by itself identify our explicitly defined P. The split supplies that identification through orbit products and the initial-form bound. I read every cited node's statement and checked it against the use, not against its proof or title.

Step 1 uses the finite-Galois-receiving node with one extension, so it gives the normal/separable finite envelope requested in the item. The embedding is injective because its source is a field. The uniqueness node applies because K is complete and its absolute value is nontrivial and real-valued. Pullback of the chosen absolute value by each automorphism is exactly another extension, making each automorphism an isometry. The fixed-field node asserts the required finite automorphism group. Subgroup closure and conjugation normality are the displayed two-term ultrametric calculation, with no ramification theorem used.

Step 2 uses exactly the existing Cauchy node, which explicitly concerns finite subgroups of field automorphisms. Thus it applies to P, not merely to a separately introduced abstract group. The proof that a prime q different from the residue characteristic has |q|=1 uses its nonzero residue and the integer bound |q|≤1. The finite average differs from q times the identity by a strict smaller-norm error. Applying its injectivity to z−sigma z is the full argument excluding prime order q. This covers mixed characteristic and residue characteristic zero. Prime factorization then gives |P|=p^a, including a=0.

Step 3 uses no external theorem. The finite orbit product is fixed because a group element permutes its factors. Multiplying factors of the form 1+epsilon, |epsilon|<1, shows the error from 1 lies in the maximal ideal. This gives both its value and the residue p^a-th power. The empty-error case, P=1, gives b(x)=x.

Step 4 uses the exact fundamental inequality node for N/T. T is an intermediate K-subfield, so N/T has finite dimension; completeness of T is not needed by that node. Its statement supplies both finite value index and finite residue degree. The new abstract-group Mathlib leaf applies to the quotient of multiplicative value groups, since the orbit-product identity kills every element by p^a. The cited purely inseparable tower node assumes positive characteristic p and finite dimension, both true for the residue extension just shown; it states degree p at every step, so multiplying degrees proves the p-power assertion. For p=0 I use the already proved P=1 directly. I do not use ef≤n to infer divisibility or integrality of defect.

Step 5 uses the normal-fixed-quotient node with the normal subgroup established in step 1. Its statement explicitly gives both Galoisness of T/K and the isomorphism acting by restriction; thus it supplies the actual lift of an automorphism, not just equality of cardinalities. The existing fixed-field node supplies |Aut_K(T)|=[T:K] with these Galois hypotheses. Finiteness of T/K follows from its being an intermediate vector subspace in finite N/K.

Step 6 again cites the restriction-normalized quotient node, so lifting tau is justified by its statement. With m=|P|, the three strict estimates for b(x), sigma(b(x)) and tau on b(x) all use the same norm |x|^m. Their sum proves the displayed power comparison. Reduction gives ubar^m=1. In characteristic p with m=p^a, the identity (ubar−1)^(p^a)=0 forces ubar=1; there is no assertion about p-power roots of unity in the mixed-characteristic field itself. Consequently sigma belongs to the P actually defined in the item. This proves the new kernel trivial and is not being assumed from the statement of the new structural bound.

Step 7 uses the new bound exactly for E=T, F=K, the whole finite Galois group H and the now-trivial kernel. All automorphisms are isometries by step 5, and e,f are finite by the separately cited degree bound. Its statement gives the inequalities s≤f, [H:Q]≤e's and the equivalence s=f iff residue separable. The resulting chain starts with the fundamental inequality in the correct direction ef≤[T:K]. Equality forces e'=e and s=f, which are exactly the prime-to-p and separability clauses needed. No discrete ramification result or defect theorem is smuggled into this step.

For the new structural statement I checked the intended proof independently: let I be the kernel of H's residue action. For h in I the map |x| mod Gamma_F ↦ residue(h(x)/x) is well-defined, since replacing x by a times a valuation-unit factor changes the quotient by an element with residue 1. It is multiplicative in both arguments; h acts trivially on residue units. Its kernel is exactly Q. Thus I/Q injects into Hom(Gamma_E/Gamma_F,k_E^×). The finite abelian value quotient's p-primary part has no nontrivial character in characteristic p; decomposing its prime-to-p part into cyclic factors and counting roots of X^n−1 gives at most e' characters. The residue action H/I has at most s elements, since distinct automorphisms give distinct embeddings into an algebraic closure. Hence [H:Q]≤e's. The finite field embedding count gives 1≤s≤f and equality precisely for separability. This is a real separate character-count lemma; its internal field-embedding and finite abelian-group tools are intentionally left for that statement-only node's future split. It is not a replacement for the parent proof.

For the new prime-power cardinality leaf, I read IsPGroup's definition (25–27) and IsPGroup.iff_card (102–106). The new statement is its forward implication with the definition expanded, so the application is one line with precisely the prime and finite hypotheses given. The earlier matrix-only leaf is insufficient without a representation, explaining the separate general leaf.

Edge cases checked: N=K gives P=1,T=K and all degrees one; P=1 in positive residue characteristic allows a=0 and makes the same argument work; in residue characteristic zero the average excludes every nonidentity torsion element and T=N. For imperfect residue fields the upper residue extension is allowed to be nontrivially purely inseparable, and the lower separability follows only from the equality chain. Noncyclic and nondiscrete value groups are allowed: their finite quotient, not a uniformizer, is used. For the structural bound H=1, a trivial value quotient and an inseparable residue extension satisfy the stated inequalities. For the group leaf A=1 gives b=0. No source error requiring a statement change was found.

This review also checks delivery-errors B–E: new nodes have standalone statements with inline group/separability notions and valuation/closure definition citations; they have empty proof/proof_deps; search records are real command outputs; unavailable services would be marked unavailable; TeX uses one backslash; all cited statements were opened; quotations are literal; the parent has an actual argument rather than clause replacements; all non-elementary inputs have nodes. There are no SGA citations. Nothing was written to the shared repository or launcher, and no Lean or build tool was run.

## Unfinished work

None in this one-level split. The structural automorphism-bound child remains unsplit by design. Delivery status is recorded by the required dry run and push below.

## Delivery checks

The first dry run refused two literal but short citation excerpts (uniqueness and the inseparable tower). Both now quote the full cited statement, including all hypotheses and the conclusion. No mathematical step changed.

The second dry run required an explicit notion citation in the abstract-group leaf. I read def-sfb-finite-infinite-set and cited it for its finite underlying set; the group operations remain defined inline. This adds no hypothesis and does not alter the Mathlib match.
