## What changed

Proved `ModuleCat.residue_kernel_unit_minor_base_change_free` with its signature unchanged.
Added proof-only imports `Mathlib.RingTheory.LocalRing.Module` and
`Mathlib.RingTheory.Flat.Stability`. Registered the supplied finite/projective instances,
unfolded scalar extension, aligned its action with the ring homomorphism's algebra,
and applied `Module.free_of_flat_of_isLocalRing` to each tensor product.
Updated the node proof and proof_origin to record the actual Mathlib argument.

The final module compiles without warnings. The argument also covers the zero module:
the Mathlib finite-flat freeness theorem imposes no nontriviality assumption on the module.
No hypotheses, universes, visibility, definitions, or target statements changed.

## Proved and sorry left

Closed one original hole: `ModuleCat.residue_kernel_unit_minor_base_change_free`
(node `new-residue-kernel-unit-minor-base-change-free`). No sorry remains in the item.
Added zero holes; split off zero statements. This is a complete proof, not a decomposition.

## No longer needed

None. No original import, node, or module was removed. The original plan had no
proof dependencies; the whole argument is supplied by proved Mathlib declarations.
Both added proof-only imports are needed: the local-ring theorem and flat base change.

## Where the brief, the DAG or earlier work was wrong

The recorded searches missed the applicable Mathlib theorem
`Module.free_of_flat_of_isLocalRing` in `Mathlib.RingTheory.LocalRing.Module` (Tag 00NZ).
Loogle and Lean Finder now both find it. No mathematical error or unit-route change.
The small implementation issue is that scalar extension's `Module.compHom` action
requires choosing the algebra `(algebraMap R (Localization.AtPrime 𝔭)).toAlgebra`
after exposing the tensor product; no interface adaptation is required.

## Second reading by H2

1. **Diff and interfaces.** Compared the delivered module with the repository version.
   The theorem signature, hypotheses, conclusion, visibility, and definitions are byte-for-byte
   unchanged; only two proof-only imports and the proof body differ. Verdict: pass.
2. **Compilation and axioms.** Compiled the module with `lcompile.py` and checked
   `#print axioms ModuleCat.residue_kernel_unit_minor_base_change_free`; it reports only
   `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry`, `axiom`, `unsafe`,
   `opaque`, `extern`, or `implemented_by` declarations. Verdict: pass.
3. **Statements and split nodes.** The existing theorem is proved directly from finite
   projectivity and localization flatness using Mathlib's finite-flat local-ring freeness
   theorem. No new statement or split-off hole was added, and the existing node's statement
   remains unchanged and true, including the zero-module case. Verdict: pass.
4. **Pruning and route.** Both added imports are used only by the proof, while all original
   public imports remain needed by the theorem's interface. The unit route and realized node
   are preserved; no proof dependency or module can be pruned. Verdict: pass.
5. **DAG agreement and source check.** The node's proof and proof origin describe the same
   finite-flat-over-a-local-ring argument used in Lean, with no hidden library theorem or
   altered target. The Mathlib theorem was checked in the imported source and its assumptions
   are supplied by the local instances. Verdict: pass.

I changed only this report section; no Lean declarations, node statements, or definitions were
changed during the second reading.
