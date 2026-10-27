# Q20: lem-pur-finite-tensor-presentation-reduction

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-finite-tensor-presentation-reduction.json: statement, split into nine proof steps; Mathlib verdict no match.
- citations.json: one verbatim statement quote for every citation of every step.
- report.md: this report.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searched the actual WeilConjectures source for the blueprint tag and for Tate/coefficient/reduction/tensor terminology. Read PullbackIntTensorFamily.lean: its composition and product laws concern fixed coefficients, not the prescribed finite quotient comparison. TateModuleDual.lean concerns character coordinates of abelian groups. OrientationDatum.lean bundles coefficient comparisons as parameters; it does not prove the present comparison. None states the whole item.

## WANTED

None.

## What required correction or expansion

The item had no proof. Its statement is retained. The blueprint Step 2 only said that compatibility with the invertible twist follows by associativity, leaving negative powers, Koszul signs and the identification of the actual comparison maps unwritten. These are now separate explicit steps. I used the ordinary specified O_E(1) line and its actual quotient tensors, rather than choosing arbitrary isomorphisms between rank-one objects. I did not use any exceptional inverse image or purity theorem to prove this tensor constituent.

The root charts require care for ramification: the level n is the uniformizer exponent, but ell^n still annihilates O_E/varpi^n because the ramification index is at least one. A primitive ell^n root therefore provides a chart by the integral line, even when n is not a multiple of the ramification index. No replacement by a residue ring of the form Z/ell^n is made.

## Blueprint and duplicate searches

Read the current main-20261015 finite-reduction proof, the chapter record and the sk-thm-purity-transport unit record, including its Step 1 first constituent. Ran blueprint_refs.py ancestor on the item and whole-blueprint searches for Tate and finite reduction. Searched all DAG statements/titles for scalar monoidality, signed lines, dual evaluation and tensor shifts, and read each candidate used. The existing generic nodes supply these tools, so no nodes were created. The full finite-reduction theorem includes purity itself and is not used as a dependency. Its source Step 2 is expanded here. The chapter and unit route remain unchanged.

## Not duplicates

No new nodes.

## Mathlib searches

Preserved the inherited searches. Added the six actual queries recorded in searches.jsonl, reading their hits. The two semantic phrasings returned ordinary free-sheaf pullback, Ext shift and cotangent results. Read Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean:118 and Mathlib/Algebra/Category/ModuleCat/Monoidal/Adjunction.lean:45: they supply ordinary free-module and scalar monoidality facts, not the required derived pro-etale Tate normalization. Neither makes the full item a leaf. The search interrupted by a provider failure completed and recorded both its leanfinder and grep results; these were recovered from the log instead of rerun.

## Review by Q20

I read the current blueprint finite-reduction proof Step 2 as the source of the item, and Stacks sites-cohomology.tex lemma-pullback-tensor-product (07A4), lemma-symmetric-monoidal-derived (0FPT), sites-modules.tex section-tensor-product (03EK), section-internal-hom (04TT), lemma-internal-hom (03EM), and more-algebra.tex item-shift-tensor (0FNH). The expanded proof is marked agent-written because the blueprint only sketches these coherences. There are no new node sources to review.

Step 1 uses det-sp-scalar-extension-functor clauses 1–2 for the target action, exactness and constructibility, and lem-sf-reduction-flat-model for the same interval. The K-flat resolution node actually provides flat terms; the independent change-of-rings node actually preserves flat-term K-flatness; the tensor-descent node actually gives the resolving equivalence and uniqueness of natural transformations. Thus the representative computations are legitimate for nonflat quotients.

Step 2 cites the cochain pullback tensor coherence and its explicit monoidal equations, whose statements give the actual forward/inverse pure-tensor formulas, symmetry signs, unit and associator equations, and composition. The tensor-descent statement, not merely the definition of derived tensor, supplies passage to the derived category. I checked the identity topos and map of commutative constant ring sheaves satisfy their hypotheses.

Step 3 reads the twist definition literally: A(1)=I tensor A and B(1)=I tensor B. The twist-local-freeness statement supplies degree-zero rank-one freeness and finite local constancy. Clause 3 of scalar extension computes a rank-one line by ordinary tensor. The balanced maps in the step prove its identification with the specified B line and are inverse on generators. This is an elementary calculation after these cited statements.

Step 4 explicitly inducts on positive integers with base zero and base one, and uses the dual-local-isomorphism statement only for invertible modules. Its map is justified by the dual-evaluation statement, which really supplies the formula on every slice. No claim about base change of arbitrary internal Hom is inferred. All negative twist inputs are locally free rank one and meet the invertibility hypothesis.

Step 5 verifies the addition squares on local basis sections and dual sections, including mixed signs, then glues equations of sheaf maps. Binary coherence supplies the product formula; dual evaluation supplies cancellation. The rank-one local-freeness node supplies the local bases. I explicitly avoid the invalid inference that equality of arbitrary derived arrows follows from local equality: the equalities here are of degree-zero sheaf arrows, and only afterwards are tensored with L.

Step 6 uses the scalar shift node for the normalized exact structure and the cochain tensor-shift node for its compatibility with scalar pullback. The derived shift-descent node states the actual derived bifunctor shifts and their integer addition and sign laws. I checked negative shifts use inverse comparisons and that reduction preserves (-1)^{sp}, even in characteristic two. The displayed composite constructs the requested isomorphism, rather than assuming it.

Step 7 uses the finite-level part of the derived pullback definition, not its integral or rational clauses. The ringed-topos K-flat pullback statement supplies preservation for the chosen representatives. The derived coefficient-adjunction statement gives the scalar unit and the adjunct formula used to identify the given mate; the finite comparison definition specifies that mate. The cochain coherence statement includes composable topoi and coefficient squares. The explicit section formula and resolving descent give the composition claim for arbitrary inputs; no flatness of the quotient is introduced.

Step 8 checks the chart rather than choosing a new normalization. The twist-local-freeness statement identifies reductions of the integral line with finite root modules. The recursive chart-calculus definition specifies the ordered powers and unit-step; Steps 4 and 6 use exactly those composites. Compatible primitive roots exist over the fixed algebraically closed k; reducing an integral basis to level m uses the prescribed root power transition. The lift-independence argument concerns its reductions, not equality of integral lifts. All these calculations remain valid at ramified levels.

Step 9 expands tau as the inverse second-factor tensor shift and applies the precise shift compatibility from Step 6 and naturality. The twist definition, cochain shift and derived shift-descent statements cited here supply exactly those operations. The M comparison is already identified with the actual mate in Step 7. This proves the final square without referring to purity or its adjoint.

Checked edge cases T empty, L zero, r=0, r=-1, s=0 and negative s, m=n, d=0, residue characteristic two, and genuinely nonflat quotients such as Z/ell^2 to Z/ell. Unit maps and signs have the required values. No new hypothesis was added. Each step is under 2000 characters; none hides a separately hypothesized comparison lemma. Every cited statement was opened and its full verbatim text is recorded in citations.json. Existing generic results outside the unit are declared as tool uses in split_report, never as replacement routes.

## What could not be finished

Nothing in the split. Server validation and delivery are recorded by the delivery command.
