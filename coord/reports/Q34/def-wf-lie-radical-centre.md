# Worker report: def-wf-lie-radical-centre

## Files written

- dag/nodes/sec-algebraic-groups-lie-algebras/def-wf-lie-radical-centre.json: existing definition; Mathlib leaf covering every clause, including radical solvability and maximality. No new nodes.
- citations.json: empty list; this leaf has no proof steps or proof-step node citations.
- report.md: this report.

## Attachments

None. The dispatcher explicitly rejected the previous attachment and instructed delivery as a Mathlib leaf. The read clone now contains WeilConjectures/Mathlib/Algebra/Lie/Radical.lean, including isGreatest_radical and mem_center_iff_forall_lie_eq_zero; I read these as useful guides only and do not repeat the rejected ATTACH claim. The leaf is justified by Mathlib itself.

## Wanted literature

None. No external theorem or SGA route is used.

## Corrections and observations

The imported statement ends with a pointer to properties instead of asserting them, while blueprint_update and the current main-20261015 source explicitly assert that the sum is solvable and therefore the unique largest solvable ideal. I adopted the exact current-blueprint statement, preserving both properties. This is synchronization to the supplied update, not a weakening or a disputed mathematical statement. The source and all import/blueprint metadata are preserved. Removed stmt_dep def-wf-semisimple-lie-algebra: the statement never uses semisimplicity, and the sole definition dependency def-wf-lie-algebra supplies the field, bracket, ideal and solvability notions.

The earlier sandbox contained only searches.jsonl and dispatcher brief markers, with no node or report to resume. I retained the log and reused the previous radical/centre grep evidence; the new records copy the exact tool/query strings from that log. Later narrower searches establish the exact declarations and instances. Queries with no hits remain recorded as no match for those queries; there was no unavailable service and no inference of overall absence.

## Unfinished work

None. All clauses have a Mathlib match, so no child nodes and no natural-language proof split are needed.

## Not duplicates

No new node was created. Whole-DAG keyword searches and blueprint_refs.py searches for radical and centre found sk-d-lie, which includes these definitions in a larger bundle, and the central-radical representation/quotient and group-centre lemmas, which are different statements using these notions. No other blueprint node states precisely this item, so same_as is []. This item is not the sk-d-lie unit's key node; no unit record is changed.

## Review by Q34

I read the current blueprint source literature/blueprint/main-20261015/blueprint/sec-algebraic-groups-lie-algebras/sk-d-lie/def-wf-lie-radical-centre.md in full, compared its final sentence to blueprint_update and the imported pointer, and read the sk-d-lie unit and algebraic-groups-lie-algebras chapter. The unit defines radicals and centres by exactly the same formulas; the leaf follows that route. I also read the complete statement of def-wf-lie-algebra: it defines a Lie algebra over a field, ideals, derived series and solvability, exactly the notions the remaining statement dependency supplies. Semisimplicity supplies no clause here and was removed.

For the radical clause I read Mathlib/Algebra/Lie/Solvable.lean:365-380: radical is the sSup of the solvable Lie ideals, radicalIsSolvable says that this same radical is solvable under IsNoetherian, and the full declaration name LieAlgebra.LieIdeal.solvable_iff_le_radical says every solvable ideal lies below it. Thus the final source assertion is actually covered, not inferred from a definition alone. Supremum in the Lie-ideal lattice is the sum; containing all solvable ideals and being solvable gives largestness, and order antisymmetry gives uniqueness. These last identifications are elementary and need no separate nodes.

For the centre clause I read Mathlib/Algebra/Lie/Abelian.lean:165-174 and 283-287. The centre is the maximal trivial submodule for the adjoint action, whose membership formula is forall y, [y,x]=0. I checked lie_skew at Algebra/Lie/Basic.lean:179-181: negating a bracket changes its order, so neg_eq_zero converts this membership formula to the source's forall y, [x,y]=0 in one line, also in characteristic two. This is the only convention difference and it is explicitly accounted for in mathlib_match.

I checked the only extra Mathlib hypothesis rather than silently assuming it: FiniteDimensional at LinearAlgebra/FiniteDimensional/Defs.lean:75-76 is Module.Finite; the base field is a DivisionSemiring and is principal by DivisionSemiring.isPrincipalIdealRing at RingTheory/PrincipalIdealDomain.lean:72-77, hence Noetherian by PrincipalIdealRing.isNoetherianRing at 115-117. The instance isNoetherian_of_isNoetherianRing_of_finite at RingTheory/Noetherian/Basic.lean:324-328 then supplies IsNoetherian k L. No characteristic-zero or algebraic-closure condition was added. I checked the zero algebra (radical = centre = 0), abelian finite-dimensional algebras (radical = centre = the whole algebra), and the centre formula in characteristic two. No new statement was introduced that could fail a small-case check.

I checked delivery-errors B through E against this leaf. There are no new unsplit nodes, no hidden proof sketches, no new duplicate or restatement nodes, no off-unit tool uses, and no proof steps whose cited statements or hidden hypotheses could mismatch. The definitions, solvability theorem, ideal-containment theorem and instance declarations are each named with the verified source lines in mathlib_match. The empty citations list is appropriate because proof and proof_deps are empty, as required for a Mathlib leaf. There are no long proof steps. Only the sandbox files were written; no Lean, compiler, Lake, build or repository git operation was used.
