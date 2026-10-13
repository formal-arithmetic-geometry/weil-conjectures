## What changed

`Sheaf.AlgebraicGeometry.FormalKernelProductSection` now proves
`AlgebraicGeometry.formalKernel_product_section_existsUnique` without changing its signature.
The proof establishes restriction stability, uniqueness by simultaneous local lifts and
injectivity, compatibility on intersections, gluing, and the formula for arbitrary
representatives on every smaller open. It reuses the already proved private transition-epi,
local-lifting, and kernel-injectivity helpers through a proof-only `import all` of
`Sheaf.AlgebraicGeometry.FormalKernelBilinearActionAssociative`.

One new module, `Sheaf.AlgebraicGeometry.FormalKernelRepresentativeProduct`, isolates
kernel membership and independence for actual coefficient and transition representatives.
It assumes that these representatives have already been supplied. It asserts neither
local lifting of arbitrary quotient sections, gluing, restriction compatibility, nor
uniqueness. The target combines it with the independently proved sheaf argument; this is
not a renaming of the target. Its import is proof-only. No definitions or existing
statements changed, and all transparency options are scoped to individual declarations.

Both modules compile together through lcompile.py with no errors or warnings. The source
was read online at Stacks tags 087Z and 0EHN; the local coherent.tex is absent on this
machine. Searches used LeanFinder, Loogle, LeanSearch, Mathlib grep, both library roots,
and the DAG. LeanSearch returned an internal server error, recorded as unavailable.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.formalKernel_product_section_existsUnique`
(node `lem-weil-pbc-formal-kernel-product-section`). The private predicate `ProductEquation` is explicit, and all five private helper
theorems are proved; no partial proof contains sorry.

Added one hole:
`AlgebraicGeometry.formalKernel_representative_product`
(node `lem-weil-pbc-formal-kernel-representative-product`). Its whole proof is `by sorry`.
It isolates the original plan's stalk quotient algebra, kernel membership, and independence
calculation. This is a decomposition: one hole closed, one hole added, net zero.

Edge cases checked mathematically: for m=n=0 the transition and kernel inclusion are
identities and I annihilates F_1; for m=0 or n=0 the same ideal-power calculation uses
I^0=O; for I=0 positive coefficient powers and positive kernels vanish; for I=O every
formal level vanishes; zero modules cause no exception. On the empty open, the subtype
cover is empty and Mathlib's sheaf gluing and separation still apply. Kernel membership
chooses no data in a definition: the only choices occur within theorem proofs.

## No longer needed

No existing import was removed, and no module or node is globally pruned.
The parent's direct use of `lem-weil-pbc-ideal-module-product-stalk` moves into the new
representative algebra node; that node and its module remain needed there, so this is
not claimed as pruning. The parent does not need the stronger nonadjacent stalk quotient
identification to prove transition epimorphisms: adjacent quotient isomorphisms suffice.
No affine-completion equivalence, finite-generation theorem, algebra structure, or action
existence theorem is imported to construct the product. The associativity theorem itself
is not applied: its module supplies proved generic local-lifting helpers. This is a tool
use within the same unit, not a replacement of any unit step.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found. The plan's algebraic steps were not supplied by
an existing declaration with the required product membership and independence signature;
they are now explicit in the new node. The unit's statement and realized steps stay
unchanged. Blueprint search for "kernel product representatives" found no matching node.
The ancestor helper reports None for this generated node, although its existing record
explicitly names thm-weil-pbc-finite-etale-lifting; the new node retains that recorded
ancestor and prepends the parent to its recorded via chain.

## New nodes

`lem-weil-pbc-formal-kernel-representative-product`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-formal-kernel-representative-product.json`,
states kernel membership and equality of products of actual representatives. The node
and docstring explain the downward nested-quotient induction, the ideal-power membership,
the difference expansion, and the sectionwise kernel construction. Its source is the
associated graded argument of Stacks 087Z and the defining conditions of 0EHN. It is
strictly the representative algebra part of the parent, before local lifting and gluing.
No change record is needed because no existing interface changed.

## Second reading by Q1

1. PASS: Read both delivered modules in full and diffed the existing module against
   the repository. The signature of `formalKernel_product_section_existsUnique`,
   from `theorem` through the text preceding `:=`, is byte-identical. Its public
   import, visibility, universes, hypotheses, and conclusion stay unchanged. The
   only added definition is the private, explicit predicate `ProductEquation`.
   There are no changes to existing definitions, targets, or other groups' files.

2. PASS: Compiled both modules together in import order with lcompile.py: no errors
   or warnings. A scratch copy with `#print axioms` checked the public theorem, all
   five private helper theorems, the private predicate, the new representative
   theorem, and the imported transition-epi, local-lift, simultaneous-lift, and
   kernel-injectivity helpers. Only propext, Classical.choice, Quot.sound, and the
   reported representative theorem's sorryAx occur. In particular uniqueness and
   the imported lifting helpers have no sorryAx. The sole textual sorry is the
   whole proof of `formalKernel_representative_product`; there is none in data or
   any partial proof. No forbidden declaration or kernel-check bypass occurs.
   All choices of product sections occur inside theorem proofs.

3. PASS: The split-off statement supplies representatives as hypotheses and proves
   membership and independence on a single open. It omits local lifting of arbitrary
   quotient inputs, restriction compatibility, gluing, and uniqueness, which the
   parent proves separately. It is strictly the algebra part, not a restatement.
   Read its docstring and matching node against the adjacent quotient and
   annihilation conditions in Stacks 0EHN and the graded construction in 087Z.
   Downward nested-quotient induction identifies the nonadjacent transition kernel;
   the difference expansion kills both error terms by I^(m+n+1). For n=0 use
   I^0 M=M; for m=0 the transition is the identity; for m=n=0 the kernel inclusion
   is the identity and I kills F_1. The zero ideal, unit ideal, zero modules and
   empty open introduce no exception. Independent msearch LeanFinder searches for
   an ideal filtration inducing graded scalar multiplication found filtration and
   adic-completion results, without the sheaf representative assertion. Loogle
   searches for quotient scalar multiplication found no applicable result (the
   first query's Submodule.Quotient name was unrecognized). Direct rg searches of
   both library roots and Mathlib's filtered algebra and quotient bilinear modules
   found no existing statement of the required membership/independence result.
   Closing the remaining hole requires formalizing the stalk quotient induction,
   not a replacement available in a few minutes.

4. PASS: Read the proof from the public theorem downward: local simultaneous lifts,
   representative product, restriction, independently proved uniqueness, overlap
   compatibility, sheaf gluing, and separation for arbitrary representatives on
   smaller opens. The unchanged public import is needed by the signature; both
   added imports are proof-only and used. The import-all dependency supplies only
   proved generic helpers, not an assumed action. The old direct proof dependency
   `lem-weil-pbc-ideal-module-product-stalk` is explicitly accounted for under
   No longer needed: it moves to the representative node and remains in the import
   closure. No pruning is claimed. Inspected sk-thm-p1's realized statement and
   four step lists; none is removed or bypassed by this refinement below unit level.

5. PASS: Existing-node differences are exactly proof, proof_deps, and proof_origin.
   The steps and dependency union follow the actual Lean reduction, including the
   explicit import-all helper use. The new node's Lean signature matches its
   theorem, and its statement, source, complete proof steps, dependency union,
   origin, searches, creation record, blueprint ancestry, chapter and unit are
   present. Its status is split. The report lists the closed and added holes by
   declaration and node, and correctly counts one-for-one decomposition, net zero.

Second-reading changes: clarified that the six private declarations consist of
one explicit predicate and five proved helper theorems, and added this independent
review with compilation, axiom, source, edge-case and search evidence. No Lean or
DAG repair was needed. The axiom scratch copy was removed before delivery.
