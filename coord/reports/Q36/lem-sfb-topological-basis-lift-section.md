# Stage-1 report: lem-sfb-topological-basis-lift-section

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-topological-basis-lift-section.json`: statement, now split; the statement is unchanged. No exact Mathlib match; eight explicit elementary steps, using the existing free-module definition.
- `citations.json`: the one proof citation, step 1 to `def-weil-pbc-free-module`, with a verbatim statement excerpt.
- `report.md`: this report. `searches.jsonl` was written by the required search command.

New nodes: 0. New Mathlib leaves: 0. No unit record changes are needed: this item is a supporting node, not the unit's key statement.

## Attachments

None. Searched all `lean/WeilConjectures/` for the exact blueprint tag and the basis/lift/continuous-section concepts. The existing project `Mathlib/LinearAlgebra/Basis/Exact.lean` constructs adapted algebraic bases in an exact sequence, not continuous splittings with these hypotheses. No project declaration states every clause of the item. The item has no recorded Lean declaration or open Lean dependency to attach.

## Wanted literature

None. The construction is proved directly from the supplied finite basis and topology hypotheses. It does not require a new textbook result.

## Findings and corrections

The statement is sound and was retained verbatim, together with its statement dependency and all inherited provenance and searches. The missing proof was supplied. The source is the current `main-20261015` blueprint's `sk-lem-stratified-lattice.proof.md`, final paragraph headed “Pushing down by the trace”, read along with its unit and chapter records and the parent `lem-sfb-continuous-lattice-sum`. That paragraph identifies the image of the sum of lattices with the continuous module of their sum without writing the continuous lifting argument. This item is precisely the general coordinate calculation supplying that argument. The blueprint gives the application, not a separate proof of this general lemma, so `proof_origin.by` is `agent`.

Blueprint searches for `basis lift` and `topological basis` returned no blueprint node stating the same lemma. Whole-DAG searches for coordinate homeomorphisms, topological modules and finite continuous linear combinations found the parent and the adjacent `lem-sfb-continuous-frame-sheaf-comparison`, which is about frame isomorphisms and scalar extension of continuous coefficient sheaves, not sections of general surjections. `lem-sfb-topological-module-condensation` concerns internal module objects on the profinite site; no such result is needed here. Neither is cited or duplicated.

The new searches were actually run through `msearch.py` and their results read: LeanSearch, Loogle, two differently phrased LeanFinder queries, and two grep queries. All services answered. The hits `Module.Basis.constrL`, `constrL_apply`, `constrL_basis`, and `ContinuousLinearMap.exists_right_inverse_of_surjective` live over a nontrivially normed scalar field; reading `Topology/Algebra/Module/FiniteDimension.lean` lines 95–100, 434–450 and 582–590 verifies the extra scalar hypotheses. `LinearMap.splittingOfFunOnFintypeSurjective` at `LinearAlgebra/Finsupp/Pi.lean:171–185` only proves an algebraic splitting. Neither is an exact match or a one-line specialization for arbitrary topological rings with prescribed lifts and the continuous-function clauses. The second grep used a file as the subdirectory argument, so the search command's printed file/line fields are malformed; the query and output summary are retained as actually logged, and the source was then read directly at the cited lines. The six inherited Q46 search records remain intact; they are not represented as searches run by Q36.

## Unfinished work

None in this stage-1 split. No Lean was written, compiled or built.

## Review by Q36

I read delivery-errors B–E in full and audited this item against each kind of failure. No new nodes were created: B's standalone-node, tag, leaf-line and duplicate obligations therefore introduce no new records. The item's own objects and topological-module assumptions are spelled out, its only named notion is the already existing free-module definition, and its statement is unchanged. The blueprint ancestry is retained and `same_as` is empty after the recorded searches. No SGA source or route replacement was used.

For step 1 I opened `def-weil-pbc-free-module` and read its statement: it says that each element has a unique finite expansion in the basis, including the empty basis. This is exactly what yields additivity, scalar compatibility and the basis-vector coordinates after applying beta; the verbatim quote is in `citations.json`. I do not take continuity or a splitting theorem from that definition. Step 2 substitutes these identities into the given finite sum and distributes, explicitly giving the additivity and scalar formulas. Step 3 applies the given linear q to that finite sum, uses q(m_i)=b_i, and evaluates at a basis vector. Thus these three steps contain the algebraic argument, rather than appealing to a renamed clause of the item.

Step 4 uses the actual hypothesis that beta is a homeomorphism, hence its inverse is continuous. Product projections are continuous by the product topology. The constant-coordinate pair map is checked on open rectangles, its composite with the assumed scalar action is continuous, and the finite-sum continuity argument includes its induction base and induction step. This is a short elementary calculation from the topology assumptions; no automatic-continuity theorem over a field is being used. Step 5 uses surjectivity only to choose finitely many basis lifts, and explicitly treats the empty family, where the basis condition forces N=0. The preceding construction handles any given lifts independently of that existence choice.

Step 6 checks that each pointwise ring/module operation stays continuous by pairing and composition with the assumed operations, and checks the axioms by evaluation at each point. Step 7 uses the assumed continuity of q and the continuity of s already proved, writes the pointwise linearity equations for postcomposition, and proves q_* s_*=id by evaluation. Step 8 writes both precomposition squares as associativity equalities, and notes the restriction of scalars a to a composed with u. These steps cite no external statement because their calculations are included. In particular they do not use sheaf descent, compactness of Z, or any topology on the spaces of maps.

I tested the empty basis (unique zero section, no nonexistent lift), N=0, Z empty, and rank one with q:A×A→A and lift (1,t), where the section is a↦(a,at). The proof also applies to rings with zero divisors, for example Z/4Z, since it never divides or assumes linear independence over a field. It remains valid for the zero ring and for non-Hausdorff topologies satisfying the given homeomorphism and operation hypotheses. No completeness, separation, openness of q, or projectivity theorem is assumed. Every clause is addressed, all uses are accounted for, the only proof dependency is a Mathlib definition leaf, and no dependency points back to the parent. Each step is below 2000 characters; there is no long step concealing a separate lemma. This is the elementary-node exception of the brief: adding nodes for these distributive identities, continuity of a finite sum, or associativity would create the very elementary and clause-duplicate nodes prohibited by B and D.

The remote dry run and delivery are the remaining mechanical verification recorded by the delivery tool; this report is the mathematical self-review of the concrete split.
