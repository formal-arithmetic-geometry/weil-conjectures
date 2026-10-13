## What changed

Replaced the sole sorry in `Sheaf.RingTheory.RegularPresentationFlatFiber` with a complete
Lean proof assembling the parameter quotient, its local R-algebra structure, flatness,
completeness, the double-quotient/first-isomorphism closed-fibre equivalence, and the
formal-smoothness transport. The existing theorem signature and public imports are unchanged.
Both delivered modules compile without warnings using the prescribed launcher.
The second reading narrowed the new module’s public quotient import to
`Mathlib.RingTheory.Ideal.Quotient.Basic`; quotient operations are proof machinery.

Added `Sheaf.RingTheory.RegularFiberKernelParameterLift` for the remaining geometric
construction. Its conclusion is only a proper ideal J with ker(v)=J+m_R S and a regular
sequence of base parameters on S/J. It does not give a model, flatness, completeness,
a fibre equivalence, or formal smoothness. Unlike the original theorem, it has no A, q,
residue-field isomorphism, completion hypothesis, or formal-smoothness hypothesis;
it assumes only regularity of E. The original theorem proves regularity of E separately.
Thus this is a strictly smaller construction lemma, followed by a real assembly proof.

Proof imports added to the original module: `RegularLocalOfFormallySmoothAdic`,
`RegularFiberKernelParameterLift`, and `FormallySmoothAdicRingEquiv` under
`Sheaf.RingTheory`. Updated its DAG proof, proof_deps, and proof_origin to the actual route.

## Proved and sorry left

Closed the original hole in
`RingHom.exists_flat_complete_model_of_regular_presentation`
(node `lem-weil-pbc-regular-presentation-flat-fiber`). There are no sorries left in the item.

Added one hole:
`RingHom.exists_regular_fiber_kernel_parameter_quotient`
(node `lem-weil-pbc-regular-fiber-kernel-parameter-lift`), in the new module.
Its proof is exactly `:= by sorry`; the docstring and DAG supply the complete argument.
This delivery is a decomposition: one original hole closed, one strictly lower hole added,
net zero holes removed. Existing imported dependencies may still rest on their own holes.

Edge cases checked for the new statement: when the fibre map is an isomorphism, use J=0;
when the base is a field, its parameter list is empty and the assertion reduces to the
regular-quotient kernel construction; when E is a field, all fibre parameters are killed;
when either dimension is zero the relevant list is empty. The proper-ideal requirement
follows from containment in the kernel of a map to the nonzero regular local ring E.
The kernel identity is necessary for the quotient equivalence and is used explicitly.

## No longer needed

Removed direct proof imports from the original module:

- `Mathlib.RingTheory.LocalRing.Module` (needed only in the new construction's planned proof).
- `Sheaf.RingTheory.FormallySmoothAdicGeometricallyRegular`.
- `Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence` (now used below the new node).
- `Sheaf.RingTheory.RegularLocalQuotientKernelParameters` (now used below the new node).

The original route through `lem-weil-pbc-fs-adic-field-geometrically-regular` and
`Sheaf.RingTheory.FormallySmoothAdicGeometricallyRegular` is unnecessary for this item:
we apply `lem-weil-pbc-fs-adic-field-regular-local` directly. Geometric regularity and
its tensor-product argument are not needed to show that E is regular local.
No claim is made that other target branches cease to reach these modules.
The kernel-parameter, Nakayama, cotangent-dimension, and regular-sequence nodes remain
necessary below the new construction node; they have not been pruned from this argument.
All remaining direct proof imports of the item are used.

For completeness, the old direct proof dependencies removed from the item are exactly:
`lem-weil-pbc-fs-adic-field-geometrically-regular`,
`lem-weil-pbc-regular-local-quotient-kernel-parameters`,
`lem-weil-pbc-nakayama-local-generators`,
`lem-weil-pbc-regular-local-cotangent-dimension`, and
`lem-weil-pbc-regular-local-generators-regular-sequence`.
Only the first is pruned from this argument; the latter four are used by the new node.
The existing module’s public imports are preserved byte for byte.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The DAG's geometric-regularity step was stronger than needed;
its regular-local consequence is already a separate library theorem. The rest of the
parameter-quotient route is retained, including its still-unproved cotangent lifting step.
No unit statement or realized unit step was bypassed. No signatures, definitions,
public visibility, or modules held by other groups were changed.

The local copy of `literature/stacks-project/more-algebra.tex` is absent on this machine.
Read the primary source online at https://stacks.math.columbia.edu/tag/07NR, in particular
the first two proof paragraphs identifying and removing the kernel parameters.
The new lemma generalizes that construction away from the coefficient-ring special forms;
its complete cotangent argument is written in the docstring and node.
WANTED: local Stacks More on Algebra source, Tag 07NR, for the new construction node.
LeanSearch returned Internal Server Error; it is recorded as unavailable. LeanFinder,
Loogle, pinned Mathlib grep, library grep, DAG search and blueprint search found no exact
existing theorem for the construction. Blueprint searches for `kernel parameters` and
`regular system of parameters` found no matching blueprint node.

## New nodes

`lem-weil-pbc-regular-fiber-kernel-parameter-lift`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-regular-fiber-kernel-parameter-lift.json`,
states the proper kernel ideal and regularity of the base sequence after quotienting.
The new module is `lean/Sheaf/RingTheory/RegularFiberKernelParameterLift.lean`.
It realizes the first two parameter-removal paragraphs of Stacks 07NR below the existing
regular-presentation node. Its proof depends on the existing regular-quotient kernel,
Nakayama, cotangent-dimension, and regular-sequence nodes; three kinds of actual Mathlib
search are logged (including unavailable LeanSearch). No change records are needed.


## Second reading by N1

1. Compared the complete existing module with the repository by `diff` and compared
   its declaration prefix through `:= by` byte for byte: the signature, universes,
   hypotheses, conclusion and public visibility are unchanged. The public imports of
   the existing module are unchanged. No definition or target changed, and no change
   record is required. The existing node changes only `proof`, `proof_deps` and
   `proof_origin`. Verdict: pass.

2. Compiled both delivered modules in import order with `lcompile.py --all`: no errors
   or warnings. Scanned both for forbidden declarations and hidden proof holes:
   the only sorry is the exact named construction theorem reported above. Neither
   module defines data from an unproved existence theorem: `T` is explicitly `S/J`
   inside a proposition proof, and the algebra and fibre equivalence are constructed.
   A separate scratch module printed the axioms of both declarations: the assembly
   theorem and construction theorem both use only `propext`, `Classical.choice`,
   `Quot.sound`, `sorryAx`. These are allowed while the construction and imported
   statements remain open. Verdict: pass, decomposition rather than an axiom-free proof.

3. Read Stacks Tags [07NR](https://stacks.math.columbia.edu/tag/07NR),
   [00NR](https://stacks.math.columbia.edu/tag/00NR) and
   [00NQ](https://stacks.math.columbia.edu/tag/00NQ), with the new Lean and DAG open.
   Checked every hypothesis: regular local S and E, surjectivity, annihilation of
   m_R S, and the extension of the base parameters. The quotient has the same residue
   field as S, so the cotangent independence argument uses one field throughout.
   The generated ideal J lies in ker(v), is proper since E is nonzero, and satisfies
   the exact kernel equality needed by the double quotient. After putting kernel
   parameters first, the remaining base sequence is regular on S/J by 00NQ.
   Tested the empty base list (R a field), the empty kernel list (fibre map an
   isomorphism, J=0), and E a field (kill all fibre parameters). For example
   R=k[[t]], S=k[[t,x]], E=k gives J=(x), while R=k, S=k[[x]], E=k gives J=(x)
   and the empty regular sequence. The helper assumes neither completeness nor
   formal smoothness and concludes neither a complete flat model nor an equivalence;
   it is a genuine smaller lemma. Independent LeanFinder, Loogle and pinned Mathlib
   grep searches used different terms; searched both library roots with rg and read
   RegularSequenceFlatClosedFiber and upstream RegularLocalRing.Defs. These provide
   parts of the argument, not this construction. Its formal proof still requires
   cotangent and list transport work beyond a few-minute closure. Verdict: pass.

4. Read the proof from regular locality of E down to formal-smoothness transport.
   Checked `flat_of_regular_parameters`, `quotient_complete_local`,
   `isRegularLocalRing_of_formallySmoothAdic` and `FormallySmoothAdic.of_ringEquiv`
   against their actual signatures. The local quotient and flatness instances meet
   their hypotheses; the explicit first-isomorphism/double-quotient equivalence
   evaluates to v on every representative. The base equivalence and scalar tower
   establish algebra compatibility, and the maximal-ideal/power calculation supplies
   exactly the vanishing condition for the transported lifting problem. No shorter
   exact library result was found. Proof dependencies removed directly are now all
   enumerated under No longer needed, including the four relocated below the helper.
   Read dag/units/sk-thm-p1.json `realized`: none of these tool nodes realizes a unit
   statement or step; the unit route is preserved. Verdict: pass.

5. Matched each existing-node proof step and uses list to the actual Lean proof;
   their union is exactly proof_deps. Matched the new node’s full lean.statement to
   its declaration. Its source, complete three-step proof, dependency union,
   proof_origin, creation, chapter/unit, blueprint origin and actual search records
   are present. The two parameter theorems say what their cited steps take from them;
   the Nakayama and cotangent-dimension dependencies are existing Mathlib leaves.
   No new hole is merely the original theorem renamed. Verdict: pass.

Changes by this reading: narrowed the new public quotient import from Operations to
Basic, added its missing module blueprint tag, fixed two docstring word joins,
made the residue-field identification and base-span equality explicit in the helper’s
proof docstring and DAG, aligned the existing docstring with the direct 07EI route,
marked the failed LeanSearch as unavailable, and completed the exact pruning inventory.
No theorem signature, definition or proof term was changed.
