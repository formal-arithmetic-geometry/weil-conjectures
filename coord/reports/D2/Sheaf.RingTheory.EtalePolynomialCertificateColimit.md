## What changed

Proved `Algebra.exists_stage_etalePolynomialCertificate` without changing its signature,
definitions, or existing docstrings. Expanded membership in the relation ideal and its square
into finite coefficient sums; encoded the two certificate families as one explicit finite
polynomial equation system; descended its solution and reconstructed the certificate.

Added `Sheaf.RingTheory.TensorPolynomialEquationsColimit`, containing the proved theorem
`Algebra.exists_stage_tensorPolynomialEquations`. Its private, proved helper first combines
finite representative lifting with finite eventual vanishing for a compatible system of ring
maps. The public proof applies this to tensor products on the nonempty upper tail of the ring
diagram. `MvPolynomial.rTensorAlgEquiv` transfers between tensor products with the polynomial
algebra and polynomials over the tensor coefficient ring. Coefficient compatibility is proved
coefficientwise, and tensor ring maps are compared with the existing linear tensor maps by
induction on tensors.

The original module now imports this theorem privately, and privately imports
`Mathlib.Algebra.MvPolynomial.CommRing` for evaluation of subtractions. The new module has only
its statement dependencies as public imports. All private helpers are proved. Updated the
original node's proof, proof dependencies, and proof origin to match the implementation.

Both modules compile without warnings through `lcompile.py --all`. The original declaration's
signature and the module's exported interface are unchanged according to `diff_module`.
The proof handles empty variable and equation sets using the nonempty upper tail and finite
upper bounds; no positivity assumption on n or m, no nonzero-ring assumption, and no finite
presentation assumption on B₀ was introduced.

## Proved and sorry left

Closed the one original hole: `Algebra.exists_stage_etalePolynomialCertificate`
(node `lem-weil-pbc-etale-polynomial-certificate-colimit`).

Also proved the new theorem `Algebra.exists_stage_tensorPolynomialEquations`
(node `lem-weil-pbc-tensor-polynomial-equations-colimit`). This is a completed supporting
lemma, not a decomposition into remaining holes. Holes added: none. Every private helper is
proved. No `sorry` remains in either delivered module.

## No longer needed

Removed direct proof imports from the original module:

- `Sheaf.Paper.DirectedColimitBaseChangeElementwise`: the new equation-descent module uses it;
  its node `lem-weil-pbc-directed-colimit-base-change-elementwise` is still needed transitively.
- `Mathlib.RingTheory.TensorProduct.MvPolynomial`: the new equation-descent module uses it;
  the Mathlib module is still needed transitively.

The original route's nodes `lem-weil-pbc-tensor-cancel-base-change` and
`lem-weil-pbc-polynomial-scalar-extension` are unnecessary for this proof.
`MvPolynomial.rTensorAlgEquiv` gives the polynomial tensor identification directly, without
`Algebra.TensorProduct.cancelBaseChange` or `MvPolynomial.algebraTensorAlgEquiv`.
These two nodes are Mathlib leaves, so no project module needs deletion. The unit's own
statement and realized steps are untouched.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The planned polynomial identification had an
unnecessary detour through tensor cancellation and polynomial scalar extension;
`MvPolynomial.rTensorAlgEquiv` supplies the exact identification used here.

The local checkout lacks `literature/stacks-project/algebra.tex`. Read the actual source proof
at https://stacks.math.columbia.edu/tag/07RI and checked the finite lifting and eventual
identity argument against it. LeanSearch returned Internal Server Error, recorded as
unavailable; LeanFinder and the Mathlib grep ran successfully. Neither returned an exact
finite-equation descent theorem. The new theorem spells out the finite-equation argument
implicit in the source; it adds no unproved dependency.

## New nodes

`lem-weil-pbc-tensor-polynomial-equations-colimit`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-tensor-polynomial-equations-colimit.json`, records
`Algebra.exists_stage_tensorPolynomialEquations` in
`lean/Sheaf/RingTheory/TensorPolynomialEquationsColimit.lean`. It abstracts exactly the
simultaneous lifting and eventual vanishing component of the certificate argument, with
arbitrary finite variable and equation index sets. Its only project proof dependency is the
existing, proved elementwise tensor-colimit descent theorem. The proof is complete; this
node creates no new work item with a hole. Three search kinds and the blueprint ancestor are
recorded. No change record is required because no existing exported interface changed.

## Second reading by D2

1. Compared the complete original module with the repository version using `diff` and
   checked the original theorem's signature byte for byte through its `:= by` boundary.
   Verdict: unchanged. Its public imports, definition dependencies and existing docstrings
   are unchanged; the two replacement imports are private. There are no changed definitions
   or undeclared statement changes, and no change record is needed.
2. Compiled both delivered modules in import order with `lcompile.py --all`: no errors or
   warnings. Searched both sources for sorry and prohibited declarations: none. Scratch
   copies printed axioms for both public theorems and all five private helpers. Every output
   contains only propext, Classical.choice and Quot.sound (tensor_map_linear needs only
   propext and Quot.sound); none contains sorryAx. Verdict: both are complete proofs.
3. No statements are split off with sorry. Read the proved supporting theorem and its node:
   finite arbitrary variable/equation sets, fixed polynomial coefficient algebra, arbitrary
   B₀, and stage above i₀ agree between Lean and prose. The helper finite_equations_descent
   first lifts entries to a common stage, then kills evaluated equations at a common later
   stage using transition composition; it does not assume injective transition maps. Empty
   variable/equation sets are covered by Finite.exists_le on the nonempty upper tail; n=0,
   m=0 and zero rings introduce no extra assumptions. Read Stacks Tag 07RI online, including
   both inverse identities. Its argument supports this abstraction, without requiring B₀
   finitely presented. Repeated LeanFinder search using "finite tuple in a tensor product"
   and "polynomial relations vanish", and grep using rTensorAlgEquiv, finite_equations and
   exists_finite_data. Also searched project and upstream sources. The project theorem
   CommRingCat.exists_finite_data_stage is still sorry and concerns integer equations in
   the ring colimit, not the present tensor coefficient algebra. Mathlib's finite-presentation
   factorization results require building a finitely presented quotient and identifying the
   tensor diagram's ring colimit; Polynomial.exists_of only lifts a univariate polynomial.
   None provides a shorter direct proof here. Verdict: no duplicate or disguised remaining
   hole; the completed supporting theorem isolates the equation-descent part and the original
   module performs the actual certificate expansion and reconstruction.
4. Read the proof from the certificate down: square_span_range identifies precisely the
   square ideal's generators; certificate_iff_equations uses finite ideal-span coefficients
   with the correct subtraction signs. The explicit sum-indexed system preserves both
   families, and pderiv_map justifies its fixed derivative coefficients. The supporting
   proof uses the already proved elementwise tensor descent and rTensorAlgEquiv, avoiding
   the planned cancellation detour. Import roles match the code: colimits, tensor ring maps
   and eval belong to signatures; tensor equivalence, finite upper bounds, elementwise
   descent and subtraction evaluation serve proofs. The report accounts for all three old
   proof dependencies: cancellation and scalar extension are unused, and elementwise descent
   remains transitively used. Read dag/units/sk-thm-p1.json realized statement/steps; neither
   pruned Mathlib leaf realizes a unit step. Verdict: pruning and the unit route are correct.
5. Compared the old node JSON with the delivered version: only proof, proof_deps and
   proof_origin changed. The certificate node now cites the equation theorem; its expansion
   and reconstruction steps describe the Lean. The new node's dependency union is exactly
   the proved elementwise tensor-colimit theorem; its source, searches, creation, blueprint,
   chapter/unit and Lean record are present and agree with the module. Verdict: DAG agrees.

Second reading changed no Lean proof or node: no fault was found. Added this independent
review and repeated the searches, clean compilation and axiom checks. Closed original hole:
Algebra.exists_stage_etalePolynomialCertificate; holes added: none; split off with sorry:
none. The new Algebra.exists_stage_tensorPolynomialEquations is also proved.
