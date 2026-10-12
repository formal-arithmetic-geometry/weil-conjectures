## What changed

Replaced the sole sorry of `Sheaf.RingTheory.CompletionTensorLocalMapsInjective` with a complete
Lean proof from quotient separation and finite quotient detection. All existing signatures,
visibility, public imports and docstrings are preserved. Proof imports add tensor finiteness and
the two new modules. No definitions, instances or target statements were changed.

`CompletionTensorQuotientSeparated` has a complete proof: the evaluation kernel formula,
tensor right exactness and Krull intersection over the Noetherian local completion separate
its finite tensor module. It uses the existing `AdicCompletion.isNoetherianRing` theorem;
that theorem's existing proof dependencies remain part of the closure.

The main proof takes a finite tensor sum, selects representatives at the uniform depth supplied
by quotient detection, computes its local images using S-linearity and the hypothesis on f,
and reduces the depth using compatibility of completion coordinates. It proves kernel zero and
then applies that result to the difference of two tensors.

## Proved and sorry left

Closed: `AdicCompletion.completion_tensor_localMaps_injective`
(node `lem-weil-pbc-completion-tensor-local-maps-injective`), the item's only original hole.

Also proved: `AdicCompletion.completion_tensor_quotient_separated`
(node `lem-weil-pbc-completion-tensor-quotient-separated`).

Added and left as exactly `:= by sorry`:
`AdicCompletion.local_tensor_quotient_detection`
(node `lem-weil-pbc-local-tensor-quotient-detection`). This is solely a finite-level assertion
about ordinary localizations, finite sums and a uniform exponent; it has no completion or map f.
Thus the original theorem is decomposed, with one upper hole closed and one lower hole added
(net zero before effects of the import closure), rather than a fully sorry-free proof.
There are no sorries left in the item's module or in the separation module.

## No longer needed

No original public import was removed. The redundant proof import of
`Mathlib.RingTheory.TensorProduct.Maps` was removed from the item after the new helper modules
made its declarations available; the module is still needed for the tensor map construction.

The original route's `lem-weil-pbc-completion-finite-module-tensor`
(`Mathlib.RingTheory.AdicCompletion.AsTensorProduct`) is unnecessary: Krull separation replaces
the completion-tensor comparison and handles the independent universes directly.
`lem-weil-pbc-finite-after-completion` (`Sheaf.RingTheory.FiniteAfterCompletion`) is unnecessary:
only the radical-power argument is needed, without constructing or identifying local completions.
Neither module is imported by the delivery. Their elementary finite-level ingredients are kept
in the detection node. All other old planned dependencies remain needed there, including tensor
cancellation for the ordinary quotient identification. No claim is made that the two omitted
modules disappear from every other target route.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The existing proof-dependency interfaces state
product decomposition, localization comparison and completion comparison separately, and do
not state the finite quotient detection interface needed for this glue. The new node makes that
step explicit. The original theorem docstring is retained as its existing API; its updated DAG
proof records the implemented route.

Checked new statements at n=0, the zero algebra S, empty Q and empty finite sums. At n=0 the
quotient A/m^0 is zero. If Q is empty, the ordinary quotient product is zero. For ramified
extensions it is essential to allow k greater than n: N_q^n need not lie in m^n S_q. The chosen
uniform k is at least all n*c_q, and is independent of the finite sum.

Mathlib search used LeanFinder, Loogle and source grep. LeanSearch returned Internal Server
Error, recorded as unavailable. Searches of all blueprint nodes found no matching quotient
separation or finite quotient detection statement. The inherited blueprint ancestor is
`thm-weil-pbc-finite-etale-lifting`; the ancestor tool printed None despite the explicit valid
ancestor in the existing node, so both new nodes retain that inherited ancestor and extend its
via chain. No unit statement or unit proof step was bypassed.

Sources read: Stacks Tags 07N9, 00MA and 00JA via the official pages; the relevant Mathlib
source declarations and the existing DAG nodes for the other ingredients. The finite-level
proof follows the quotient decomposition of 07N9 and spells out the uniform cofinal exponent.

## New nodes

`lem-weil-pbc-completion-tensor-quotient-separated`, in
`lean/Sheaf/RingTheory/CompletionTensorQuotientSeparated.lean`, is proved. It isolates tensor
separation using the completed local ring's Noetherianity, evaluation kernels and Krull
intersection, without any local factors.

`lem-weil-pbc-local-tensor-quotient-detection`, in
`lean/Sheaf/RingTheory/LocalTensorQuotientDetection.lean`, is the single new hole. Its complete
natural-language proof and DAG steps describe the finite product decomposition, cofinal ideal
powers, a uniform maximum and the quotient tensor identification.

No change record is required: no existing interface was changed.

## Second reading by G3

1. Compared the delivered target module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof text and proof-only imports changed. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`. The target and the quotient-separation helper compile without errors; the sole remaining `sorry` is the named split theorem `AdicCompletion.local_tensor_quotient_detection`. No forbidden declarations or hollow definitions were introduced. Verdict: pass.
3. Checked the two added statements against their Lean declarations and the cited Tags 07N9, 00JA, 00CT and 0394. The quotient-separation statement is proved; the finite quotient-detection statement is a strictly lower-level finite-sum reduction and its edge cases (n=0, empty Q, empty sums) are documented. No duplicate library statement was found. Verdict: pass.
4. Checked the proof route and pruning. The target proof uses exactly the two helper declarations; the old completion-finiteness and finite-after-completion dependencies are removed from the target route, while the unit route is retained through the target node. Verdict: pass.
5. Checked the DAG records against the Lean proofs, including `proof`, `proof_deps`, `proof_origin`, new-node metadata, and the unchanged target statement. Verdict: pass.

Changed during second reading: no Lean declarations or DAG statements; added this review record only.
