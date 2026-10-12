## What changed

Completed and checked the earlier sandbox reduction of
`AlgebraicGeometry.Scheme.Modules.closedImmersion_unit_quotient`.
The original signature and docstring remain unchanged. Its proof uses the new
geometric theorem `closedImmersion_unit_kernel`: the unit is epi and the
multiplication-image inclusion is its kernel. Mathlib's
`Abelian.epiIsCokernelOfKernel` makes the unit a cokernel of that inclusion.
Uniqueness of cokernels supplies the quotient isomorphism with the required
factorization equation. Conjugating the pullback-pushforward map by these
isomorphisms and applying unit naturality proves both quotient squares.

Preserved every original public import, including `TensorPullbackAdjunction`;
the earlier attempt unnecessarily replaced that public import by `TensorPullback`.
Added only plain proof imports of `ClosedImmersionUnitKernel` and
`Mathlib.CategoryTheory.Abelian.Basic`. Added the missing copyright and module
docstring to the new kernel module. The parent node records the categorical
reduction, while the kernel node records the original geometric argument.
No existing statement, definition, visibility, or target signature changes.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.Scheme.Modules.closedImmersion_unit_quotient`
(node `lem-weil-pbc-closed-immersion-unit-quotient`).
No sorry remains in the item's module.

New hole left:
`AlgebraicGeometry.Scheme.Modules.closedImmersion_unit_kernel`
(node `lem-weil-pbc-closed-immersion-unit-kernel`), in
`Sheaf.AlgebraicGeometry.ClosedImmersionUnitKernel`.
This is a decomposition: one original hole closed and one strictly smaller hole
added, net zero. The geometric epi/kernel calculation is not proved. The quotient
construction and naturality are complete Lean proofs conditional on it.
There are no other holes added and no definitions containing sorry.
The selected quotient isomorphisms are determined uniquely by their factorization
through the epi cokernel projection, rather than arbitrary data witnesses.

Both delivered modules compile with `lcompile.py --all`. The axiom probe and
mechanical checks are also run by the final `deliver3.py --no-push` dry run.

## No longer needed

Removed the parent's plain proof imports of
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`,
`Sheaf.AlgebraicGeometry.ClosedPushforwardStalks`,
`Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk`, and
`Sheaf.AlgebraicGeometry.TensorPullback`.
The first is already available through the statement imports; the last is already
publicly available through the unchanged `TensorPullbackAdjunction` import.
The two stalk modules are proof-plan dependencies of the remaining kernel theorem.

The parent no longer directly needs the nodes
`lem-weil-pbc-module-iso-on-stalks`,
`lem-weil-pbc-locally-surjective-iff-stalks`,
`lem-weil-pbc-closed-pushforward-stalks`, `def-weil-closed-immersion`,
`def-sbc-closed-immersion-ideal-sheaf`,
`lem-weil-pbc-module-stalk-pullback`, and `def-pur-sheaf-tensor-product`.
These remain dependencies of the kernel node; `def-pc-module-pullback` remains
also a direct parent dependency. No module is pruned from the transitive import
closure. No realized statement or step of `dag/units/sk-thm-p1.json` is bypassed:
the parent is an auxiliary node, and the original geometric route remains.

## Where the brief, the DAG or earlier work was wrong

The supplied earlier attempt already contained a compiling categorical reduction,
so its proof was retained after checking it against Mathlib's cokernel API.
Its report included a second-reading section; this worker report removes it so
that the independent second reader writes their own findings.
Its replacement of a public import was unnecessary and is reverted.
The new module lacked a module docstring and copyright header; both are supplied.

Read Stacks `spaces-morphisms.tex`, lemma-i-star-equivalence (04CJ), part (1),
and `modules.tex`, lemma-i-star-equivalence (08KS), in the local source copies.
04CJ is stated on the small etale site; the ringed-space stalk argument of 08KS
supplies the Zariski proof relevant here. The helper's docstring gives the full
local tensor-quotient calculation for arbitrary modules, not just modules
annihilated by the ideal. It also compares the canonical adjunction of the stalk
formula with the adjunction chosen in the statement: their units differ by
postcomposition with a natural isomorphism, which preserves epi and kernels.

Checked small cases of the remaining statement: the identity immersion has zero
ideal and an invertible unit; an empty closed subscheme has unit ideal and zero
target, with kernel all of F; F=0 gives the zero kernel and an epi between zero
objects. No quasi-coherence of F is used. Library and Mathlib searches found no
existing scheme-module theorem closing the geometric epi/kernel calculation.
A fresh Loogle search for `epiIsCokernelOfKernel` confirms that the categorical
part is already in Mathlib. Existing Lean Finder, Loogle, and grep searches for
the geometric statement are retained in its node and the sandbox search log.

## New nodes

`lem-weil-pbc-closed-immersion-unit-kernel`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-closed-immersion-unit-kernel.json`,
states only the epi/kernel part of the original argument. It contains neither
quotient isomorphisms nor naturality. Its own module contains its exact Lean
signature, source, blueprint tag, and full natural-language proof. The node carries
the original geometric proof dependencies and recorded searches.
No change record is needed because no existing interface changes.

## Second reading by Q1

1. Compared both delivered modules with the repository. The existing quotient theorem's
   signature and all existing declarations are unchanged byte for byte; the kernel module
   is a new split-off declaration, and no undeclared interface change was found. Verdict:
   pass.
2. Compiled both modules with `lcompile.py --all`; there are no compiler errors, no
   `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations, and the
   only remaining `sorry` is the named kernel theorem. The quotient proof uses only the
   permitted categorical axioms through its imports. Verdict: pass, conditional on the
   explicitly split geometric theorem.
3. Checked the split-off statement
   `AlgebraicGeometry.Scheme.Modules.closedImmersion_unit_kernel` against its node and
   the source argument. It is strictly smaller than the quotient target (epi plus kernel
   fork), has a complete source-based docstring, and its node records the declaration,
   dependencies, source, and searches. Small cases (identity immersion, empty closed
   subscheme, and zero module) are consistent. No existing library or Mathlib theorem
   duplicates it. Verdict: pass.
4. Checked the proof route and pruning. The quotient proof uses the kernel theorem,
   `Abelian.epiIsCokernelOfKernel`, cokernel uniqueness, and unit naturality; removed
   stalk imports are still retained by the kernel module, and no shorter categorical route
   was missed. The realized unit route is preserved because the parent is an auxiliary
   quotient node and the geometric argument remains in the kernel node. Verdict: pass.
5. Checked DAG agreement: the parent node's proof and `proof_deps` match the categorical
   proof, while the new kernel node matches the remaining `sorry`; the report lists the
   one hole closed and one strictly simpler hole added. Verdict: pass.

Changed during this second reading: added this review section only. No Lean code,
statements, definitions, imports, DAG nodes, or dependencies were changed.
