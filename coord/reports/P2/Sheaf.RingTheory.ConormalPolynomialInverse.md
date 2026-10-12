## What changed

Proved `Algebra.conormal_bijective_iff_polynomialCertificate` directly in
`Sheaf.RingTheory.ConormalPolynomialInverse`. No statement or definition changed. The second reader removed the redundant public import
`Mathlib.RingTheory.Ideal.Quotient.Operations`, already provided through `Ideal.Cotangent`.
The proof follows the recorded inverse calculation: transport scalars through the quotient
isomorphism, expand conormal elements using the ideal generators, choose lifts of coordinate
vectors for the forward implication, and verify the two inverse identities for the reverse.
Mathlib searches via LeanFinder, Loogle, and grep found cotangent quotient and finite ideal
span ingredients, but no theorem stating this equivalence. The source proof of Tag 07RI was
read in the local Stacks algebra source, lines 47635–47662.

## Proved and sorry left

Closed the sole original hole, `Algebra.conormal_bijective_iff_polynomialCertificate`
(node `lem-weil-pbc-conormal-polynomial-inverse`). No holes remain and no holes were added.
Both implications are proved using Mathlib only and the existing certificate definition.
The finite-sum proof imposes no nonempty-index or nonzero-ring hypotheses.

## No longer needed

Removed the redundant direct import `Mathlib.RingTheory.Ideal.Quotient.Operations`;
its declarations remain available transitively through `Mathlib.RingTheory.Ideal.Cotangent`.
No DAG proof dependencies were removed (the original list is empty), and no module becomes
unreachable through this removal. No new modules or nodes are needed.

## Where the brief, the DAG or earlier work was wrong

None. The recorded proof plan is realized without changing the theorem's signature.

## Second reading by P2

1. **Visible declarations unchanged: PASS.** Compared the only delivered module with
   the repository using `diff -u`. The original theorem signature and docstrings are
   byte-for-byte unchanged; the sole original `sorry` is replaced by its proof.
   There are no definitions, added declarations, changed hypotheses, or statement/definition change records.
   The import removal below preserves declarations transitively available to downstream users.
2. **Proof and axioms: PASS.** Locally compiled the complete file without errors or warnings.
   A scratch copy with `#print axioms Algebra.conormal_bijective_iff_polynomialCertificate`
   reports exactly `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, forbidden
   declaration forms, or hollow definitions occur. In particular, the chosen coefficients
   come from proved surjectivity and finite ideal-span membership inside a theorem proof,
   not from any unproved existence theorem or public data definition.
3. **Split statements: PASS (none).** There are no split-off statements or new nodes.
   Checked the empty-index cases: when n = 0 the right identity is vacuous and the
   second certificate asserts each f_j lies in J²; generation then gives J/J² = 0.
   When m = 0, J = 0 and the first certificate forces Sⁿ = 0, exactly the condition
   for the zero-source map to be bijective. If S is the zero ring, J is the whole
   polynomial ring, J² = J, and both modules vanish. No nonzero or nonempty assumption
   is used in the Lean proof.
4. **Route and pruning: PASS after one import repair.** Read Stacks Algebra
   `lemma-colimit-etale` (Tag 07RI), lines 47625–47662, in the local source copy
   `/home/ubuntu/c1-stacks-review/algebra.tex`, and compared its two inverse checks
   with `hdG`, `hsecond`, `hright`, and `hleft`. The generator expansion `hgen`
   uses `Ideal.toCotangent_surjective` and `Ideal.mem_span_range_iff_exists_fun`;
   quotient scalar compatibility is explicitly proved in `hsmul`. Searches for
   cotangent inverses and bijectivity in Mathlib, upstream, and `lean/Sheaf` found
   no shorter matching equivalence. Read Mathlib's
   `PreSubmersivePresentation.isUnit_jacobian_of_cotangentRestrict_bijective`:
   it assumes a basis of relation classes and proves a Jacobian is a unit, so
   it does not replace this argument with possibly dependent generators.
   Read `dag/units/sk-thm-p1.json`: this auxiliary node is not itself a realized
   statement or step, and the direct inverse calculation changes no unit route.
   Tested import removal in scratch copies: `Ideal.Cotangent` is required by
   the signature; `Ideal.Quotient.Operations` is redundant and was removed.
   The certificate module is required by the conclusion. The pruning list above is complete.
5. **DAG agrees with Lean: PASS.** Read
   `dag/nodes/sec-proper-base-change/lem-weil-pbc-conormal-polynomial-inverse.json`
   and the certificate definition. Its surjective algebra map, finitely generated kernel,
   quotient-induced S-action, derivative compatibility, and both certificate identities
   are precisely the unchanged signature. The recorded proof lifts coordinate vectors,
   checks the two identities, and extends the generator identity by linearity, exactly
   as the Lean proof does. Its empty `proof_deps` and document `proof_origin` remain
   correct: only Mathlib ingredients and the statement's existing certificate definition
   are used. No node edits are necessary.

Changed only the redundant direct import and this report; preserved the correct proof.
The preflight requires an import change record, provided at
`coord/changes/conormal-polynomial-inverse-redundant-import.md`; it lists every
transitive downstream module, with no adaptation needed.
