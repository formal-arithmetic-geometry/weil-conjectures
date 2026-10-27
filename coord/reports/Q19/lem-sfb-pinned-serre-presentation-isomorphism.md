# Worker report: lem-sfb-pinned-serre-presentation-isomorphism

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-pinned-serre-presentation-isomorphism.json`: split item, with seven proof steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-sl2-primitive-string-vanishing.json`: Mathlib leaf; `IsSl2Triple.HasPrimitiveVectorWith.pow_toEnd_f_eq_zero_of_eq_nat`, `Mathlib/Algebra/Lie/Sl2.lean:217--226`.
- `citations.json`: verbatim citations for every node used by every proof step.
- `searches.jsonl`: tool-generated Mathlib search log.

## Attachments

None. I searched `WeilConjectures/` for the blueprint tag, the presentation terminology, and likely Lie declarations; no sorry-free project declaration states the item.

## WANTED

- `Serre, Complex Semisimple Lie Algebras`, Chapter VI appendix, for the direct proof of the Weyl-relations/Serre quotient theorem. This is already recorded as the source wanted by `lem-sfb-serre-rational-presentation`; the present item cites that existing node rather than duplicating its proof.

## Not duplicates

- `lem-sfb-sl2-primitive-string-vanishing` vs existing `lem-sfb-integrable-sl2-reflection-automorphism`: the existing node gives the exponential reflection automorphism for a locally nilpotent triple, whereas the new Mathlib leaf gives finite-dimensional primitive-vector string termination.
- `lem-sfb-sl2-primitive-string-vanishing` vs existing `lem-sfb-serre-rational-presentation`: the existing node constructs and analyzes the abstract Serre quotient; the new leaf is only the sl2 representation calculation used to show that a prescribed root-vector assignment kills the Serre ideal.
- `lem-sfb-pinned-serre-presentation-isomorphism` vs existing `lem-sfb-serre-rational-presentation`: the existing node proves that the abstract quotient is a split semisimple Lie algebra with the prescribed root system; this item proves that the quotient map to a given split semisimple algebra is an isomorphism for the particular chosen simple-root vectors.

## Review by Q19

I read the item and the unit/chapter records, the source declaration search in `WeilConjectures/`, the full statements of `lem-sfb-serre-rational-presentation`, `lem-sfb-integrable-sl2-reflection-automorphism`, `lem-sfb-serre-graded-triangular-quotient`, and the definition nodes for rational Lie algebra and semisimple Lie algebra. I also read Milne, Section 23h (Theorem 23.63, pp.503--504 and the characteristic-zero extension on p.508) and Appendix C.19--C.22 (pp.611--612).

Step 1 handles the empty base explicitly and checks the zero Lie algebra edge case. Step 2 checks weight brackets by Jacobi, local nilpotence from the finite weight decomposition, and the normalized rank-one triples. Step 3 uses the cited reflection-automorphism statement exactly for its weight-space transport, then supplies the invariant-form argument identifying the resulting reflections with the given crystallographic coroots; this verifies the hypotheses needed by the existing rational Serre presentation node. Step 4 applies that node and checks that its Cartan matrix is exactly the item's `a_ij`, including the zero-weight and one-dimensional weight conclusions used later. Step 5 checks both mixed-root brackets and both Serre relations. For the latter, I searched Mathlib and read `Mathlib/Algebra/Lie/Sl2.lean:42--46,82--85,217--226`; its theorem specializes to the new leaf with `R = Q`, finite-dimensional `M`, and eigenvalue `n`. Step 6 gives the finite root-height descent for arbitrary reducible root systems and the empty/ rank-one cases. Step 7 shows the image contains the Cartan and all root spaces by reflection transport, hence is surjective, and compares dimensions to obtain injectivity.

I verified every cited-node quote against the source JSON and wrote it verbatim in `citations.json`. I ran LeanSearch, LeanFinder, Loogle, and Mathlib grep for the item and all four required searches for the new leaf; the generated records are retained in `searches.jsonl`. The item searches found only the abstract `Matrix.ToLieAlgebra` quotient and local `sl2` facts, so the item remains a split statement. The latest blueprint was searched for Serre-presentation and primitive-vector duplicates; none was found. No Lean or compiler/Lake command was run.

## Validation

The first dry run required a longer citation quote for the new leaf. I replaced every citation quote with the complete cited statement so its hypotheses and all used conclusions are available verbatim. I also corrected the Mathlib notation line reference from 143 to 147 after reading the numbered source.

The second dry run requested a structured `mathlib_match.line` field despite the line already appearing in `how`; added `line: 217`, verified in the pinned source.
