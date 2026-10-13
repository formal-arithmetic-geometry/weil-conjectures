## What changed

Replaced the hole in Polynomial.formalFiber_finiteExtension_reduction by a compiling
reduction to two strictly narrower statements. The original signature and visibility
are unchanged. No dependency module is adapted.

Polynomial.exists_finite_coefficient_model constructs a finite A-subalgebra B of L
and a prime s with residue field L, recording compatibility on every polynomial from
A[X]. It needs neither a maximal q nor completeness, localness, positive characteristic,
or pure inseparability. The proof invokes the existing domain clause of
Algebra.finite_over_complete_local_product to supply B's Noetherian, local and
complete structures.

Polynomial.completed_fibre_compatible_product supplies the tensor/completion product
for a specified finite coefficient algebra B and compatible residue-field equivalence.
It does not construct B or assert any fraction-field structure. The item's proof
combines these parts and constructs the constant families B_i=B and s_i=s explicitly.

The item's plain imports of CompletionFiniteExtension and
LocalizationPrimeResidueFieldIso are replaced by the two new modules.
FiniteOverCompleteLocalProduct remains directly imported and is used in the proof.
A declaration-local unused-variable linter setting preserves the original signature,
whose existential complete witness is intentionally not referenced in its body type.
All three delivered modules compile without compiler warnings.

## Proved and sorry left

Closed in the item's module: Polynomial.formalFiber_finiteExtension_reduction,
node lem-weil-pbc-polynomial-formal-fibre-finite-reduction. No sorry remains there.

Added named holes:

- Polynomial.exists_finite_coefficient_model, node
  lem-weil-pbc-polynomial-residue-finite-coefficient-model.
- Polynomial.completed_fibre_compatible_product, node
  lem-weil-pbc-polynomial-completed-fibre-compatible-product.

This is a decomposition, not a completed axiom-free proof: one upper hole closed,
two lower holes added, net minus one. Both are whole public theorem proofs with
source-backed proof docstrings. Existing imported holes are unchanged. No definition
chooses data from either existential theorem: witnesses are eliminated only within
the proof of the original proposition.

## No longer needed

Removed direct imports from the item:

- Sheaf.RingTheory.CompletionFiniteExtension: needed by the new compatible-product
  step and still imported there, and by FiniteOverCompleteLocalProduct.
- Sheaf.RingTheory.LocalizationPrimeResidueFieldIso: needed by the coefficient-model
  step and still imported there.

No original node or module is claimed globally pruned: all eight original proof
inputs remain in the plans of the two new statements or the existing local-complete
argument. The original node now records its three immediate dependencies rather
than conflating them with the substeps. No unit statement or route is bypassed.
The two invalid nodes and data/isomorphism modules from the rejected attempt remain
only under scratchpad and are excluded from this delivery.

## Where the brief, the DAG or earlier work was wrong

The rejected isomorphism step quantified over arbitrary families satisfying only
unrelated coefficient-ring properties. Such a family, especially n=0, cannot imply
an isomorphism to the actual extended fibre. It is not reused.

The new first step records B as a subalgebra of the given field L, with its
A-algebra structure fixed by A[X] to kappa(r) to L. Its equivalence has a compatibility
equation for every f in A[X]. The second step requires that equation and
chooses its own primes; it does not claim the isomorphism for arbitrary output data.
For n=0, it must prove that the source is the zero ring through removal of zero
factors. A field base A is allowed in the first step (then B can be L). Nonzero r
and contraction to zero are essential there; neither is dropped from the
original statement. The second step allows fibres that vanish and does not assume
nontriviality of any tensor product. No original statement is disputed or changed.

Searches found no complete shorter route. LeanSearch returned Internal Server Error;
LeanFinder, Loogle and grep located fraction-field and tensor components, not the
combined theorem. The online Stacks proofs of Tags [07PU](https://stacks.math.columbia.edu/tag/07PU),
[07N9](https://stacks.math.columbia.edu/tag/07N9) and
[0325](https://stacks.math.columbia.edu/tag/0325) were read because this machine's
clone does not contain the fetched literature tree.

## New nodes

lem-weil-pbc-polynomial-residue-finite-coefficient-model records the first step and
evaluation part of the second step of the original plan. Its module is
lean/Sheaf/RingTheory/PolynomialResidueFiniteCoefficientModel.lean.

lem-weil-pbc-polynomial-completed-fibre-compatible-product records the completion,
tensor and zero-factor removal steps for specified compatible coefficient data. Its
module is lean/Sheaf/RingTheory/PolynomialCompletedFibreCompatibleProduct.lean.

Both nodes carry exact Lean signatures, self-contained mathematical statements,
source-backed proof steps, the searches actually run, and blueprint ancestry.
No change record is needed: no existing signature, definition or public import changes.

## Second reading by K3

1. Interface preservation: PASS. Compared every delivered module with the repository.
   The only existing module is PolynomialFormalFiberFiniteReduction; its theorem
   signature is byte-for-byte identical, including all hypotheses, existential
   structures, universes and the conclusion. Its public imports and docstrings are
   unchanged. The other two modules are new. No definition or target is changed,
   and no change record or forced adaptation is needed.

2. Proof and axioms: PASS as a decomposition. Compiled all three delivered modules
   in import order with lcompile.py, without warnings or errors. Printed axioms of
   all three declarations from a scratch module explicitly importing each module:
   only propext, Classical.choice, Quot.sound and sorryAx occur. Exactly the two
   reported public theorem proofs contain sorry; there are no definitions, hidden
   holes, forbidden declarations or nonstandard axioms. The upper proof eliminates
   existential witnesses inside a proposition; it defines no data by choosing an
   arbitrary witness from an unproved existence theorem.

3. Split statements: PASS. Read both full signatures and their mathematical proof
   docstrings against [07PU](https://stacks.math.columbia.edu/tag/07PU),
   [07N9](https://stacks.math.columbia.edu/tag/07N9) and
   [0325](https://stacks.math.columbia.edu/tag/0325). For the coefficient model, the
   zero contraction makes A inject into L; a scaled integral fraction-field basis
   generates a finite subalgebra whose fraction field is L. Evaluation has nonzero
   prime kernel because a nonzero polynomial of r remains nonzero over B. This also
   works when A is a field (take B=L), and requires no separability or completeness.
   For the product step, the compatibility equation supplies the required polynomial
   algebra map; tensoring the finite completion product and discarding zero factors
   proves the conclusion even when r is not below q. If no prime containing s remains,
   every factor is zero, so the source is zero and the empty product is legitimate.
   Neither lemma restates the original item: one supplies compatible coefficient
   data without completions; the other takes those data as input and proves only
   the completion presentation, without constructing a finite domain model.
   Independent searches used LeanFinder with "finite field extension admits module
   finite subring with fraction field equal extension", Loogle with "IsFractionRing,
   Module.Finite, Subalgebra" (service unavailable), and grep with
   "piRight|exists_is_basis_integral|residueFieldMapCAlgEquiv", plus rg on both library
   roots. Found component lemmas, not either complete statement. The existing
   FiniteSubalgebraFractionField theorem has specialized power-series/polynomial
   coefficients and cannot supply this arbitrary-domain model. Neither remaining
   hole can be closed by a short application of a result found in these searches.

4. Route and pruning: PASS. Read the original eight proof dependencies and the
   unit sk-thm-p1 realized fields. The new proof uses the coefficient-model theorem,
   the already proved domain clause of finite_over_complete_local_product, and the
   compatible-product theorem, then explicitly supplies the constant families.
   All three direct proof imports are needed; proof-only imports are plain imports.
   The new lemmas retain imports for their documented proof plans. The two removed
   direct imports remain in those subplans, as do all eight old dependencies; no
   module is globally pruned. No realized unit statement or step is bypassed.

5. Node agreement: PASS. The existing node changes only proof, proof_deps and
   proof_origin. Its three immediate dependencies are precisely the declarations
   used in Lean. Both new nodes have the required source, statement dependencies,
   proof steps, search records, split status, creation record, blueprint ancestry,
   chapter, unit and Lean record. Checked that every proof_deps list is exactly the
   union of the steps' uses and that each referenced node exists. Their Lean records
   agree with the delivered signatures.

Second-reader changes: added this independent review and its search/edge-case
findings to the report. No Lean or node repair was required. Counts remain one
original hole closed and two strictly smaller holes added (decomposition, net -1);
no globally pruned modules.
