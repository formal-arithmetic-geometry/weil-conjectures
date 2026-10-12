## What changed

Proved `Polynomial.linear_formalFiber_hypersurface` with its signature unchanged.
Added the proved theorem `Polynomial.linear_fiber_quotient` in the new module
`Sheaf.RingTheory.PolynomialLinearFiberQuotient`, for arbitrary polynomial algebras S.
The quotient equivalence is constructed by explicit inverse tensor maps. The original
module extends the polynomial derivative to the local ring, completion and coefficient
generic fibre, proves it kills coefficient fractions, and computes D(X - ξ) = 1.
Only proof imports were added. The existing public imports remain unchanged.
Updated the original node's proof route and supplied a node for the proved quotient lemma.

Both modules compile without warnings via lcompile.py --all. The proof also covers zero
fibres, as it never requires nontriviality of the tensor product or of S. Fraction-field
equivalences and derivation extensions are explicit constructions from proved results;
no data are selected from an unproved mere-existence statement. The axiom probe is run
by the delivery dry run. No targets, units, existing definitions or signatures changed.

## Proved and sorry left

Closed the original hole `Polynomial.linear_formalFiber_hypersurface`
(node `lem-weil-pbc-polynomial-linear-formal-fibre-presentation`).
Also proved the new `Polynomial.linear_fiber_quotient`
(node `lem-weil-pbc-polynomial-linear-fibre-quotient`) using only Mathlib.
The private helper `Polynomial.extend_absolute_derivation` is proved from the existing
proved localization derivation construction.

Original holes closed: 1. New holes added: 0. Sorries left in either delivered module: none.
This is a proof, not a decomposition into new holes. The completion extension theorem
already has a complete proof, and no holed dependency was introduced.

## No longer needed

Removed proof import `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso` and dependency
`lem-weil-pbc-localization-prime-residue-field-iso`: the canonical fraction-field equivalence
comes directly from Mathlib's IsLocalization.algEquiv. No prime-local-ring correspondence
is needed.

Removed proof dependency `lem-weil-pbc-tensor-cancel-base-change`: inverse maps from the
tensor universal property prove the quotient presentation directly, without tensor
associativity or base-change cancellation. Its Mathlib module was never a separate import
of this item. `lem-weil-pbc-algebra-tensor-pushout-universal-property` remains needed through
the new quotient theorem, and `lem-weil-pbc-localization-base-change` remains needed for
the derivation extension. No unit realization is bypassed; this item is below the unit level.
These are pruned from this argument; other callers may still need them.

## Where the brief, the DAG or earlier work was wrong

No false statement or tool failure was found. The quotient can be proved directly by
universal properties, so the planned polynomial division, local-prime residue-field
comparison, and tensor cancellation are unnecessary. The original assumptions hr and hrA
are preserved but are not needed once κ(r) is already assumed to be a fraction field of A.
LeanSearch was unavailable; LeanFinder, Loogle and local source searches were completed.
The cited Stacks TeX file is absent from this machine's read-only literature directory;
the Tag 07PU proof was read from its official Stacks webpage.

## New nodes

`lem-weil-pbc-polynomial-linear-fibre-quotient` records the fully proved quotient presentation
for arbitrary commutative A[X]-algebras S. It fixes ξ via the canonical fraction-field
isomorphism and proves that quotienting κ(0_A) tensor over A with S by X - ξ gives the
polynomial-prime fibre. It has no completion or derivation hypothesis and no sorry.
No change record is needed because no existing interface was changed.

## Second reading by G1

1. **Interfaces: PASS.** Compared the delivered presentation module with the repository
   using diff and a byte comparison of the complete existing theorem signature. The
   signature is identical, including hr, hrA and the let-bound instances. No existing
   definition or public import changed; the added helper is private and the new theorem
   has its own module. No change record or forced adaptation is needed.
2. **Proof and axioms: PASS.** Independently compiled both modules in import order with
   lcompile.py: no errors or warnings. Scanned both sources: no sorry, axiom, unsafe,
   opaque, implemented_by, extern or kernel-check bypass. Compiled scratch copies with
   #print axioms for Polynomial.linear_fiber_quotient and
   Polynomial.linear_formalFiber_hypersurface: each uses exactly propext,
   Classical.choice and Quot.sound, with no sorryAx. The quotient maps are explicit;
   all existential derivation witnesses come from proved theorems. No arbitrary data
   are selected from an unproved existence statement.
3. **New statement: PASS.** No open statement is split off. Read the new proved quotient
   theorem and its full proof docstring: it establishes only the quotient part of the
   argument, without the completion or derivation conclusion. Checked the zero algebra,
   zero tensor fibre, and evaluation-algebra cases: the inverse maps and balancing
   relation require no nontriviality. Independently searched LeanFinder for base change
   of polynomial evaluation and Loogle for Polynomial.eval₂RingHom, and searched the
   library and Mathlib sources for quotient/evaluation tensor identifications. The
   results provide presentation machinery and evaluation maps, not a shorter direct
   theorem with this statement. The explicit universal-property proof is appropriate.
4. **Route and pruning: PASS.** Read the quotient construction, localization extensions,
   completion extension and coefficient-annihilation argument from the top down. Each
   new plain import supports these proofs; public imports support their signatures.
   The two abandoned dependencies are listed under No longer needed. The original
   pushout-universal-property dependency moves from the presentation node's direct
   proof_deps to the new quotient node's proof_deps; it remains transitively used and
   is not pruned. Checked dag/units/sk-thm-p1.json realized: neither this item nor its
   removed dependencies realizes a unit statement or step, so no unit route is bypassed.
5. **Nodes: PASS.** The existing node differs only in proof, proof_deps and proof_origin.
   Its new dependency union is exactly the proof-step uses. The new node includes its
   source, proof steps, dependency union, searches, creation metadata, blueprint route,
   chapter/unit and verbatim Lean signature. Both routes match the Lean implementations.
   Compared the mathematical argument with the displayed linear quotient and derivation
   argument in [Stacks Tag 07PU](https://stacks.math.columbia.edu/tag/07PU).

Second reading changed only this report: added the independent review and clarified the
transitive retention of the tensor pushout dependency. The Lean proofs and nodes needed
no repair. Original holes closed: 1 of 1; new holes added: 0; split-off open statements: 0.
