## What changed

Proved `ExteriorAlgebra.koszulConormalVector_linearIndependent_and_span` in
`lean/Sheaf/RingTheory/KoszulConormalVectorBasisData.lean`, with its signature,
visibility, existing docstrings, and both public imports unchanged. Five proved
private helpers implement degree-one coordinates, contraction on degree-two
wedges, coefficients of exact relations, expressions in the square ideal, and
spanning of the conormal classes. The node `lem-sc-koszul-conormal-basis-data`
now records these explicit steps of the same H₁/exterior-power argument.

The proof uses H₁ vanishing to express exact relations as boundaries. Coordinates
of boundaries belong to the generated ideal. For a conormal relation, lift its
coefficients and subtract an expression with coefficients in I for its value in
I²; the resulting exact relation shows that all quotient coefficients vanish.
Spanning follows by span induction and surjectivity of `Ideal.toCotangent`.

Validation: the single-file `lcompile.py` compile is clean. The argument handles
r = 0, I = ⊤, and the zero ring without nontriviality or proper-ideal hypotheses.
Mathlib searches found regular-sequence definitions and polynomial-presentation
cotangent bases but no matching result. LeanSearch returned an unavailable-service
error. Read the first paragraph of Stacks Tag 062I on the Stacks website; its local
TeX source is absent from this checkout. No source download or new node was needed.

## Proved and sorry left

Closed the sole original hole:
`ExteriorAlgebra.koszulConormalVector_linearIndependent_and_span`
(node `lem-sc-koszul-conormal-basis-data`).

No sorry remains in the module; no hole was added or split off. This is a complete
proof, including the H₁ coefficient argument, rather than a decomposition. All
five private helpers are proved.

## No longer needed

None. Both original public imports are needed by the existing statement and proof.
No additional module, node, or unproved theorem is used. The temporary coefficient
module used during development was removed after its proof was integrated into
the original module. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The original one-step node plan omitted
the explicit conversion from a relation modulo I² to an exact relation: lifting
coefficients alone does not yield a cycle. The completed proof subtracts an I-valued
coefficient expression for the element of I² before applying H₁ exactness. The
updated proof plan records this glue and the spanning argument separately.

## Second reading by K2

1. Compared the only delivered Lean module with the repository using `diff`.
   The existing theorem signature, visibility, docstring, and public imports are
   byte for byte unchanged. The additions are five private proved helpers and the
   replacement of the original proof. No definition or interface changes and no
   change records are needed. Verdict: pass.
2. Independently compiled the delivered file with `lcompile.py`: clean, 4.5 s.
   Compiled a scratch copy with `#print axioms` for
   `ExteriorAlgebra.koszulConormalVector_linearIndependent_and_span`: exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   Read all helper proofs; no sorry, axiom declaration, unsafe or opaque code,
   external implementation, or definition with postponed data occurs.
   `Classical.axiomOfChoice` only lifts quotient coefficients inside a theorem
   proof, using proved quotient surjectivity. Verdict: pass.
3. No statements were split off and no new public statements or nodes were added.
   Checked the private coefficient lemma directly: H₁ exactness expresses an
   exact relation as a boundary; the computed two-wedge boundary has every
   coordinate in the generator ideal; span induction extends this to all of
   degree two. Product-ideal induction proves the square-coefficient helper,
   and quotient surjectivity and span induction prove the spanning helper.
   For r = 0 the coordinate assertion is vacuous and the generated ideal is
   zero; for I = top the quotient and cotangent are zero; the zero ring likewise
   causes no obstruction. For r = 1, the relation lemma specializes to the
   injectivity of multiplication forced by H₁ vanishing. Verdict: pass.
4. Read Stacks Tag 062I, `lemma-H1-regular-quasi-regular`, first proof paragraph
   at https://stacks.math.columbia.edu/tag/062I. Its exact sequence and formula
   for the second differential specialize to precisely the argument here with
   M = A. In the main proof, membership of the lifted sum in I² is converted
   into an exact relation by subtracting the I-valued square coefficients;
   there is no erroneous assumption that lifting alone gives a cycle.
   Independently searched Loogle for `Ideal.Cotangent, LinearIndependent`
   (zero hits), and searched Mathlib and the upstream source for conormal and
   H1Regular results. Mathlib's cotangent quotient lemmas supply the quotient
   steps but no shorter Koszul result was found; the repository's conormal
   basis theorem depends on this item and cannot be used here. Both public
   imports are required by the existing signature: one supplies the conormal
   vector and the other the regularity hypothesis. The original proof dependency
   is still used, so `No longer needed: None` is complete. Read
   `dag/units/sk-thm-picard-duality.json`: its realized statement and step lists
   are empty, and this proof changes no unit route. Verdict: pass.
5. Compared the node JSON with the repository and read its three dependency
   nodes. Only `proof`, `proof_deps`, and `proof_origin` changed. The four steps
   match the coefficient, square-ideal, independence, and spanning arguments;
   the dependency list is their union and includes the regularity definition,
   actual Koszul complex, and conormal vector definition used in Lean.
   There are no new nodes requiring additional metadata. Verdict: pass.

Second reading changed only this report by adding the independent review.
No mathematical, Lean, import, or node repair was necessary. Confirmed net holes
closed: one; holes added: zero; split off: zero; imports pruned: none.
