## What changed

Replaced the sorry in `RingTheory.pBasisComplementMonomialBasis_spanning` by a complete
proof with the original signature. The proof shows the prime-field/pth-power adjoin
is contained in kJ, splits each original basis monomial with `Finsupp.filter`, puts
the complementary product into kJ, and applies the finite basis-coordinate expansion.
Updated the existing DAG node proof to describe finite-sum closure without grouping.
All Mathlib declarations needed are already available through the existing public
imports; no imports were added or removed.

## Proved and sorry left

Closed: `RingTheory.pBasisComplementMonomialBasis_spanning`
(node `lem-weil-pbc-p-basis-complement-monomial-basis-spanning`).
One original hole closed; zero holes added. No sorry remains in the delivered module.
The proof uses only Mathlib and the supplied basis hypothesis, with no holed library
theorem. Empty J, empty I, zero exponents, and zero basis coordinates are covered by
the same finite-product and finite-sum argument.

## No longer needed

None: no original import, node, or module is pruned. Grouping repeated J-exponents is
unnecessary for span membership: each basis-expansion summand belongs individually
to the submodule, which is closed under finite sums.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The stated monomial splitting route is
retained, with finite-sum closure used instead of explicitly collecting coefficients.
No statement, definition, visibility, or other module changed.

## Second reading by M4

1. Interface: PASS. Compared the sole delivered module with the repository by
   `diff -u` and checked the text before `:= by` for byte equality. The module
   header, four public imports, visibility, universe parameters, docstring, and
   complete theorem signature are unchanged. In particular the arbitrary index
   type I, basis hypothesis hpb, finite J, and exact closure hypothesis hkJ remain;
   the conclusion is the original top-to-span inequality. No definition or other
   module changed, and there is no change record to review.
2. Proof: PASS. Compiled the module locally through lcompile.py without warnings
   or errors. Compiled a scratch copy with
   `#print axioms RingTheory.pBasisComplementMonomialBasis_spanning`: exactly
   propext, Classical.choice, Quot.sound; no sorryAx. Scanned the delivered Lean
   for sorry, axiom, unsafe, opaque, implemented_by, and extern: none. The proof
   explicitly embeds F in kJ using the closure universal property and natural
   casts for the prime field. Its complementary product has generators outside J;
   the J-filtered product extends to J by zero exponents. Scalar multiplication
   and the actual basis coordinate expansion then prove membership for every x.
   No data is chosen from an unproved existence statement: b is obtained from hpb.
3. Split statements: PASS, none added or left. The local facts hF, hc, hsplit,
   and hm are all proved in the theorem body. For empty J the J product is 1;
   for empty I all products are 1; zero exponents contribute 1, and zero basis
   coordinates are harmless in the finite sum. No special case is excluded.
4. Route and pruning: PASS. Independently searched LeanFinder for restriction of
   multiplicative monomial bases after scalar enlargement, Loogle for
   `Module.Basis, Submodule.span`, and rg for monomial spans and scalar restriction
   in Mathlib and both library roots. Basis.span_eq and Basis.mem_span provide
   generic spanning facts, but do not supply the complementary monomial splitting
   over kJ. The existing coordinate expansion uses Basis.Defs directly and avoids
   additional imports and scalar-tower setup. No shorter complete replacement was
   found. All four public imports support the signature: IntermediateField.adjoin,
   Module.Basis, the field instance on ZMod p, and ZMod.algebra respectively.
   The two old proof dependencies are the field and basis notions still used;
   none is pruned. Read dag/units/sk-thm-p1.json including realized: this node is
   an internal tool below its listed steps, and the unit route is unchanged.
5. Nodes: PASS. The sole existing node retains its statement and lean statement
   verbatim. Its changed proof and proof_origin accurately describe hF, the two
   filtered products, their span membership, and the finite basis expansion.
   proof_deps equals the union of the step uses and retains exactly the field and
   basis definition leaves. No new node fields or split-node searches are needed.

Second-reader changes: appended this review only. The Lean proof and DAG metadata
needed no repair. One original hole is closed, zero holes are added; this is a
proof, not a decomposition.
