## What changed

Proved `FieldTheory.pIndependent_insert_of_not_mem_span` without changing its signature,
public imports, or existing docstring. All supporting arguments are fully proved private
helpers in the assigned module:

- `pMonomial_span_eq_adjoin` reduces arbitrary exponents modulo p, proves multiplication
  closure by two span inductions, and constructs the intermediate field using
  a inverse = (a^p) inverse times a^(p-1).
- `pIndependent_powers_of_not_mem_span` applies the span equality, injectivity of
  Frobenius, `X_pow_sub_C_irreducible_of_prime`, and `linearIndependent_pow`.
- `pIndependent_insert_core` splits bounded exponent functions using `Equiv.Set.insert`
  and `Finsupp.comapDomain`, proves injectivity and the product identity, and applies
  `linearIndependent_smul` followed by restriction along that injective map.

Added only the private proof import `Mathlib.FieldTheory.KummerPolynomial`.
The second reading removed the redundant direct imports of
`Mathlib.RingTheory.AlgebraTower` and `Mathlib.Algebra.CharP.Reduced`;
their required declarations are already available transitively.
Updated the existing node's proof, proof dependencies, and proof origin to match.

## Proved and sorry left

Closed the one original hole, `FieldTheory.pIndependent_insert_of_not_mem_span`
(node `lem-weil-pbc-p-independent-insert-outside-span`). Added no holes; no `sorry`
remains in any delivered declaration. The three private helpers are proved completely.
This is a proof, not a decomposition into unproved intermediate statements.

The complete final module compiled without errors or warnings through `lcompile.py`.
The dry run also checks the module's axioms and unchanged public interface.

## No longer needed

No original Lean import was removed and no Sheaf or WeilConjectures module is pruned.
Second-reading compilation confirmed that both added direct imports
`Mathlib.RingTheory.AlgebraTower` and `Mathlib.Algebra.CharP.Reduced` can be removed
together. `Mathlib.FieldTheory.KummerPolynomial` is necessary: removing it makes
the irreducibility and minimal-polynomial lemmas unavailable.
The node no longer directly cites `def-weil-algebraic-element`: the proof identifies the
minimal polynomial from an explicit irreducible monic polynomial that annihilates x.
Its Mathlib definitions remain available transitively, so this is removal of a DAG proof
edge, not a claim that the corresponding module leaves the targets' import closure.

The original translation and coefficient argument for the minimal polynomial is replaced
by the existing Mathlib leaf `lem-weil-pbc-x-pow-p-minus-t-irreducible` (Stacks 09HF).
The existing simple-extension power-basis node is retained for its power-independence
consequence. No new intermediate modules or nodes are required.

## Where the brief, the DAG or earlier work was wrong

No existing statement required correction. Stacks Tag 07P2, third proof paragraph, was
read on the Stacks website; its displayed polynomial uses x where x^p is required, as
already corrected in the assigned module's docstring. The Lean proof uses X^p-C(x^p).
The change to the degree-p argument is below the unit level and retains the unit route.

The independence needed for grouping the relation is over L=F(T), not merely over F.
The final helpers explicitly use the former coefficient field. Empty T is covered by
the zero exponent monomial and its span; p=2 is covered by the prime's one_lt bound;
the inverse-closure proof handles a=0 separately. Infinite T requires no finiteness
assumption because every exponent function and every linear relation has finite support.


## Second reading by S1

1. **Unchanged interface — pass.** Compared the complete module with the repository
   version using diff. The existing theorem signature is byte for byte identical,
   its docstring and four public imports are unchanged, and there are no existing
   definitions to alter. The additions are three private proved helpers and a
   private proof import. No statement change or change record is needed.
2. **Proof and trust — pass.** Compiled the delivered module using lcompile.py,
   without errors or warnings. A scratch copy with
   `#print axioms FieldTheory.pIndependent_insert_of_not_mem_span` reports exactly
   `propext`, `Classical.choice`, and `Quot.sound`. Source scanning finds no sorry,
   axiom, unsafe, opaque, implemented_by, extern, or kernel-check bypass. The
   intermediate fields are explicitly constructed from the span and proved closure
   properties; no arbitrary witness is chosen from an unproved existence theorem.
3. **Intermediate statements — pass.** There are no split-off holes or new public
   statements. Read all three private helpers: exponent reduction, multiplication
   and inverse closure, Frobenius injectivity and degree p, and injective splitting
   of the insertion indices establish strictly smaller parts of the argument.
   Empty T gives the span of 1; p=2 still has 1<p; zero is explicitly separated in
   inverse closure; infinite T is handled by finite-support exponent maps. The
   span equality does not assume independence, as required. Independent searches
   used LeanFinder for truncated monomials and purely inseparable insertion, Loogle
   for linearIndependent_smul, and rg for span/adjoin and p-independence in Mathlib
   and the project. They confirm the employed generic tools and yield no direct
   replacement for this insertion theorem.
4. **Route and pruning — pass after import cleanup.** The proof uses the existing
   irreducibility Mathlib leaf and linearIndependent_pow before doing the necessary
   exponent-index calculation. Checked dag/units/sk-thm-p1.json and its realized
   statement and steps: this item is a lower auxiliary node and bypasses none of
   them. The removed old proof dependency def-weil-algebraic-element is reported;
   no project module is claimed pruned. Removed two redundant added proof imports
   and compiled with both absent; the remaining KummerPolynomial import is needed.
5. **DAG agreement — pass.** Diffed the node against the repository: only proof,
   proof_deps, and proof_origin changed. Its statement and Lean signature remain
   identical. The proof steps follow the three helpers, and proof_deps is exactly
   the union of their cited node dependencies. Both cited nodes are existing
   Mathlib leaves, not unproved project statements. No new nodes are needed.

Second reading changed only the removal of two redundant private proof imports
and the report's import/pruning description. The mathematical proof is retained.
