## What changed

Proved `AlgebraicGeometry.torsionControlled_descended_source_comparisons` in
`Sheaf.AlgebraicGeometry.TorsionControlledDescendedSourceComparisons`, with its
signature and docstring unchanged. Constructed the restriction isomorphisms,
proved coherence locally, glued the algebraic arrow, verified the normalized
quotient maps and their overlap equations, and applied
`compatible_quotient_formal_comparisons`. Naturality of `overFunctorEquiv` proves
the final local intertwining equation.

Changed the proof-only import of `Sheaf.Topology.GlueSheavesOfModules` to
`import all` to use its existing proved private `module_hom_gluing_exists`
helper. The supplied global source requires only morphism gluing. Used the
public isomorphism-invariance clause of
`RingedSpace.coherent_kernel_cokernel_sum`, so the proof remains usable through
the upstream-sync re-export wrapper.
Updated the item's node proof to describe the Lean assembly. No public imports,
statements, definitions, or consumer modules changed.

Single-file compilation passed in 8.2 seconds. A temporary `#print axioms` probe
of the result against the published compiled dependencies reported only
`propext`, `Classical.choice`, and `Quot.sound`; the probe was then removed.
The proof works uniformly for empty covers and zero/unit ideals; it introduces
no extra hypotheses, witnesses chosen from unproved existence statements, or
case exclusions.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.torsionControlled_descended_source_comparisons`
(node `new-stage3-torsion-controlled-descended-source-comparisons`).

Zero holes remain in the delivered module; zero holes added; zero split-offs.
This is a proof from existing library declarations, not a decomposition.
The current shared source of the existing dependency
`AlgebraicGeometry.compatible_quotient_formal_comparisons` still contains a
`sorry`; it is unchanged and not part of this delivery. The axiom-probe result
above is specifically for the published compiled dependency versions.

## No longer needed

No imports or modules removed; all existing dependency modules are used.
No DAG dependency removed. The object-gluing clause of
`glue_sheaves_of_modules` is unnecessary here: the already supplied M is kept,
and only the proved morphism-gluing helper is used. Only the
isomorphism-invariance clause of `coherent_kernel_cokernel_sum` is used. These are unused clauses, not claims that their modules are globally
pruned. The proof-only coherence import no longer needs `all`.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or interface repair was needed. The existing plan
assembles directly from its named dependencies. The shared source currently
contains upstream-sync re-export modules while the published build still has
some earlier module implementations; compilation therefore uses the existing
Sheaf imports of the assigned file. A trial direct upstream import of
`WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum` lacked a published
object file and was removed. The delivered file keeps the original coherence
import and compiles against the published build. The node recommended the
private `coherent_iso` helper through `import all` of the Sheaf module, but the
new re-export wrapper hides that private name. A small sandbox-only module-system
check confirmed this. The final proof uses the public isomorphism-invariance
clause instead, and that version also passes the standard-axioms probe.


## Second reading by Q2

1. **Interfaces — pass.** Compared the complete delivered module with the shared
   repository using `diff`. The existing theorem signature and docstring are
   byte-for-byte identical, and the node's `lean.statement` is that signature.
   Only the theorem proof and two proof-only import modes differ; no definition,
   public import, existing declaration, or consumer module changes. No change
   record is required.
2. **Proof and trust — pass.** Independently compiled the delivered file without
   errors or warnings (6.9 seconds). Compiled a separate scratch copy with
   `#print axioms AlgebraicGeometry.torsionControlled_descended_source_comparisons`:
   exactly `propext`, `Classical.choice`, and `Quot.sound`. The delivered module
   contains no `sorry`, forbidden declaration mechanism, or definition. The
   gluing helper constructs the arrow by unique section gluing; no arbitrary
   data are selected from an unproved mere-existence theorem.
3. **Split statements — pass (none).** No new statements, nodes, or holes were
   introduced. Checked that the constructed local isomorphisms have the correct
   direction, overlap equations follow from the supplied transition equations,
   and the normalized quotient equations match the existing comparison theorem.
   Empty covers force X empty and are handled by the existing cover-gluing and
   coherence theorems; J = 0 and J = 1 require no extra cancellation assumptions.
4. **Route and pruning — pass.** Read the four dependency interfaces and the
   morphism-gluing helper. A fresh LeanFinder search for compatible morphism
   gluing found section-gluing and extensionality tools, with no shorter exact
   replacement; repository searches confirmed the existing helper is the direct
   interface needed. Each import is used. All four old `proof_deps` remain used,
   so `No longer needed` correctly removes none. Read `dag/units/sk-thm-p1.json`:
   its statement and realized steps remain intact; this proof assembles only the
   already-planned local-descent subargument below that route.
5. **DAG — pass.** Only `proof` and `proof_origin` differ in the existing node.
   Read each proof dependency's statement and Lean record. The node's four steps
   match respectively local coherence, morphism gluing, elementary quotient-map
   calculations, and the existing formal-comparison theorem plus naturality.
   Their `uses` union is exactly the unchanged `proof_deps`. No new node fields
   or unit-route changes are needed.

Second reading changed only this report (including a wrapped line). The Lean
proof and DAG update were correct and have been retained as written. Independently
confirmed: one original hole closed, zero holes added, zero split-offs, and no
modules pruned. The axiom result concerns the published compiled dependencies;
the existing shared-source comparison hole noted above is not silently counted
as closed by this delivery.
