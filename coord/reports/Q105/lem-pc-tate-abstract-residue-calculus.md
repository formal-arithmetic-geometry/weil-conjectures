# Q105: lem-pc-tate-abstract-residue-calculus

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-tate-abstract-residue-calculus.json`: statement, split into thirteen steps; no complete Mathlib match.
- `citations.json`: verbatim statement quotations for every citation in every step.
- `searches.jsonl`: unmodified output log of the required msearch command.
- `report.md`: this report. `write_split.py` is a sandbox-only preparation script, not a delivered node.

New nodes: **0**. New Mathlib leaves: **0**. The statement is unchanged.

## Attachments

No complete attachment claimed for the item. I searched the exact blueprint tag and the Tate/residue notions in `lean/WeilConjectures/`. The implementation in `RingTheory/TateResidue/Residue.lean` is substantial and has no literal sorry, but its projection theorem `TateResidue.res_smul_D_proj` (line 358) concerns `[π f, π g]`, whereas this item expressly asserts finite-potence and the formula for `[π f, g]`. The source files also do not give a named theorem directly stating the full ambient restriction and pair-isomorphism assertions in this item's form. Consequently the existing code is partial coverage, not an exact attachment of the complete item. I did not infer that the complete item is closed from absence of a literal sorry in one theorem.

For the reused trace node, the file `RingTheory/TateResidue/FinitePotent.lean` contains `Module.End.tateTrace_eq_trace_restrict` (143), `tateTrace_eq_trace` (163), `tateTrace_eq_zero_of_pow_eq_zero` (174), `tateTrace_smul` (184), `tateTrace_sum` (213), `tateTrace_comp_comm` (267), and `tateTrace_eq_add_of_exact` (299). These explain the strong existing Lean coverage of that node. I leave its attachment/audit to its owner; I edited no part of that node.

## WANTED

None. Tate's paper is present locally and was read, not downloaded. No prohibited source is used.

## Findings and changes

The item was an unsplit child of the Tate adelic-reciprocity argument. Its statement agrees with Tate, §2 Theorem 1, the Remark and formula (*), and the relevant parts of R1–R2. I found no statement dispute. The current `main-20261015` chapter and Serre-duality unit still require this Tate-residue route; this split supplies its abstract algebraic component and does not replace a unit step or modify a target.

During this session the shared read clone acquired the existing node `lem-pc-finite-potent-trace-calculus`, created for the DVR residue item. I opened its complete statement and reused it. I also found the existing Mathlib leaf `lem-trf-vector-subspace-complement`. No new trace, projection, operator-ideal, or Kähler-presentation node is needed. In particular the Kähler definition node actually states the free-module presentation, so the descent step cites that statement rather than a presentation hidden in its proof.

The proof keeps the basic ideal estimates and the trace-zero computations as elementary steps: each is a few lines from explicit finite-dimensional image bounds and the cited trace theorem. They are not new nodes or postponed claims. Every step is below 2000 characters. The lift construction, the single-lift comparison, the differential-relation descent and the finite quotient calculation are all written out. Restricted additivity is checked by proving every pairwise product of operators in E₀ has finite rank; unrestricted additivity of finite-potent traces would be false and is never used.

## Not duplicates

No new nodes, hence no same-tag pairs to justify. Whole-DAG statement searches and whole-blueprint searches for finite potent, finite-potent, commutator, residue, trace, operator ideals, Kähler, and projection located the already available facts. I reused the finite-potent trace node and the vector-subspace complement leaf, and kept the algebraic quotient presentation already in `def-weil-pbc-kahler-differentials`. The other Tate residue nodes concern DVR residue calculations, field extension, lattice identities or reciprocity; none gives this abstract construction and all of its invariances.

## Review by Q105

I read Tate, *Residues of differentials on curves*, printed pp. 149–153, especially T1–T5, Propositions 1–2, Theorem 1, the finite calculation (*), and R1–R2. I also read the current blueprint chapter and unit, the two stage-1 documents, the three blueprint levels in SETUP, GOAL, and delivery-errors B–E (including the repeated isolated-run copy). There are no new nodes whose sources need independent justification. The three existing statements cited by this split were all opened in the live DAG, and `citations.json` copies their actual text verbatim.

For step 1, the trace node explicitly gives a well-defined trace on stable finite-dimensional subspaces, nilpotent vanishing, stable-subspace additivity, scalar multiplication, cyclicity across two vector spaces, and additivity under pairwise finite-rank products. Those are precisely the trace properties used here. The complement node imposes no finite-dimensionality hypothesis; its direct-sum conclusion defines the projection by taking the A-component. I checked `Submodule.exists_isCompl` at Mathlib/LinearAlgebra/Basis/VectorSpace.lean:280–283.

Step 2 proves its own finite-window algebra estimates. I checked both orders of multiplication for E₁ and E₂, with E₁ and E₂ contained in E, rather than silently assuming closure in all of End(V). In step 3, the trace node's finite-product hypothesis follows from SV contained in A+U and TA finite-dimensional. The first zero-commutator case uses TS and ST in E₀; the second uses the additional finite-rank estimate for ST. Thus the cited cyclicity and restricted linearity really apply, even in infinite dimension. Step 4 proves the lift properties with the correct order of composition and checks that reduction modulo E₂ is allowed inside E.

Steps 5 and 6 use only the trace statements already quoted: lift differences in E₀ for two E₁ lifts, and the E₁/E₂ trace-zero calculation for replacing the second lift by the actual multiplication. This second calculation is essential to the item's formula and is why the existing two-projection theorem alone was not an attachment. Scalar multiplications commute with k-linear operators, so q(f,c)=0, including in positive characteristic.

Step 7 uses the exact operator identity [F,GH]=[FG,H]+[HF,G], not an invalid identity that would require the arbitrary lifts to commute. The three commutators are in E₀ by step 4, satisfying the trace node's hypotheses via step 3. The Kähler node explicitly gives the free C-module on symbols modulo additive, Leibniz and base-scalar relations. Our functional kills all C-multiples of those relations; no nonexistent C-action on k is assumed. Step 8 uses the same presentation only to check that f dg spans over k, proving uniqueness and projection independence.

In step 9 I checked the two component images separately: fB=fA+fgA and fgB=fgA+fg²A modulo A. Admissibility applies to f, fg and fg² because they all belong to the given commutative k-algebra. The resulting quotient B/D is finite-dimensional, S maps all of V into B, and S kills D. Thus B and D are stable, both successive extra trace terms are zero, and the cited stable-subspace trace formula gives the ordinary trace on B/D. This is the concrete finite calculation of Tate, not an unspecified transport lemma. In step 10 the C-stability and inclusion A⊆W guarantee that B, D and the quotient operator are literally the same for W and V. Its citation of the Kähler node uses precisely the spanning assertion derived in step 8.

Step 11 uses cyclicity with a=u and b=S u⁻¹; ba=S is already finite-potent, so the trace node applies without any dimension assumption on V or V'. The pair isomorphism carries A and the multiplication operators to the required ones. Step 12 handles the finite A case by zero lifts, and the finite-codimension case by the original, commuting multiplication operators as lifts, checking their E₁ membership with finite quotient representatives. I corrected an unnecessary preliminary finite-window expression in this step during self-review, leaving only the explicit valid bound A+U_f+fU. Step 13 checks commuting lifts fπ,gπ on every vector when both f and g preserve A.

For edge cases I checked A=0 (zero lifts), A=V (multiplications themselves), V=0, finite-dimensional V, f=0, g a scalar, and characteristic 2. All required vanishing formulas follow without division or invertibility assumptions. For the nonzero test example V=k((t)), A=k[[t]], f=t⁻¹, g=t, the commutator has ordinary trace 1 on the constant coefficient, giving the expected positive residue; this also checks the commutator sign. Invariance uses C-linear isomorphisms and C-stable W exactly as assumed, not arbitrary k-linear identifications or arbitrary intermediate subspaces. I found no hidden smallness, separability, perfectness, Noetherian, or finite-dimensional-ambient hypothesis.

The msearch log records every search made in this session. Both semantic phrasings were read; the trace hits are ordinary finite-dimensional trace results, the residue hits are local residue fields or Kähler constructions, and none states the whole residue theorem. Complement searches correctly found the auxiliary fact already in the DAG. The grep of `finite.?potent|tateTrace|TateResidue` returned zero Mathlib hits. Earlier search records inherited from the item were retained. No repository, launcher file, Lean file, compiler, Lake, global build, or local DAG checker was modified or invoked.

## Unfinished work

None for this one-level split. The existing finite-potent trace node remains its owner's item; this delivery does not split or edit it. Required server dry run and direct delivery are performed after this report is written.
