## What changed

Proved `RingHom.exists_limit_module_presentation_cokernel_data` in
`Sheaf.RingTheory.LimitModuleModuleDataConstruction`, retaining its exact signature.
The construction lifts the specified matrix to one stage, restricts to the requested
later tail, and forms actual finite-free quotients at every stage. Local private
helpers adapt the proved construction of
`Sheaf.RingTheory.FinitePresentationModuleBaseChangeDiagram`: the quotient is small
in `max u v` without finite-type-over-ℤ assumptions, and its Shrink equivalence also
provides the required presentation with exactly s relations and t generators.
Tensor right exactness proves both base-change comparisons and pure-tensor formulas.
`Module.baseChange_diagram_elementwise` supplies representatives and eventual zero;
the additive colimit universal property is proved directly from them.

Added proof-only imports of matrix, final-functor, tensor right-exactness,
tensor finite-power, ring filtered-colimit, concrete-colimit Mathlib APIs and
`Sheaf.RingTheory.BaseChangeDiagramElementwise`. The original public import is kept.
Updated the item's node proof, proof dependencies and proof origin to this route.
No public declaration, definition, signature or visibility changed.

Source read: [Stacks 00QX](https://stacks.math.columbia.edu/tag/00QX), the presentation
matrix and later-stage cokernel paragraph, and
[Stacks 00R1](https://stacks.math.columbia.edu/tag/00R1), its non-local analogue.
The local literature checkout lacks algebra.tex; the official pages were read.
Searches run through msearch: LeanFinder for finite presentation matrix cokernel
descent (presentation-cokernel APIs, no whole diagram); Loogle `Module.Presentation`
(presentation API, no whole diagram); grep for stage relation/base-change cokernel
lemmas (no hits). Direct rg and source reading found the proved nearby construction
and the base-change elementwise criterion used here.

## Proved and sorry left

Closed the sole original hole:
`RingHom.exists_limit_module_presentation_cokernel_data`
(node `lem-weil-pbc-limit-module-essentially-finite-presentation-over-system-module-data`).
One hole closed, zero holes added; none split off. Every new private helper is proved,
and no sorry remains in the delivered module. All stage objects are actual quotient
constructions transported through proved linear equivalences; no object is selected
from an unproved existence statement.

Edge cases checked in the proof: empty matrix dimensions use the empty Finset branch;
zero modules use the same quotient/exactness argument; a directed preorder need not
be antisymmetric (only thin-category morphism uniqueness is used). The larger module
universe is handled by the automatic Small instance and Shrink.linearEquiv.

## No longer needed

Second reading removed the redundant newly added proof-only import
`Mathlib.Algebra.Module.Shrink`; its API is already available through the remaining
imports. Removing any one of the other seven added imports fails compilation.

No pre-existing import, node or module was pruned: the original node had no proof
 dependencies and the module only had its statement's public import. The nearby
`FinitePresentationModuleBaseChangeDiagram` and `FinitePresentationModuleDiagram`
modules are not imported: their public theorems require finite-type integer stage
rings and do not provide the exact prescribed later-tail presentation. Their proved
quotient and colimit implementation patterns were adapted as private helpers here.
No claim is made that these modules are globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The original four proof steps had no dependency citations. The node now records the
ring representative, final-subcategory, tensor right-exactness, finite-product and
base-change representative facts actually used. The construction needs neither the
local-ring assumptions nor the ring-localization assumptions: they remain unchanged
in the public signature. The supplied ring colimit is sufficient for this module
construction, and the original s-by-t presentation is preserved.

`BaseChangeDiagramElementwise` is used as a generic tool; it is already proved and
belongs to the same unit sk-thm-p1. No unit statement or unit step is bypassed.

## Second reading by C1

1. **Interface: pass.** Compared the complete delivered module and node with the
   repository using diff, and checked the existing theorem signature byte for byte.
   The signature, docstring, visibility, public import and node statement are unchanged.
   Read the landed change record for the earlier later-tail interface correction;
   this delivery introduces no further interface change.
2. **Proof and axioms: pass.** Read every helper and the final proof. Compiled the
   module cleanly through lcompile.py. A scratch copy with `#print axioms
   RingHom.exists_limit_module_presentation_cokernel_data` reports exactly propext,
   Classical.choice and Quot.sound, without sorryAx. The source has no sorry or
   forbidden declaration mechanism. Quotients and their transported actions are
   explicit constructions; chosen matrix entries and representatives come from
   proved colimit facts, and the presentation equivalence is a hypothesis.
3. **Split statements: pass, none.** No hole or public theorem was added. Checked
   the private coordinate, exactness, matrix-lifting and colimit arguments, including
   zero rows, zero columns, a singleton index and non-antisymmetric preorders.
   Independent LeanFinder search for scalar-extension cokernel diagrams returned
   fixed-ring ModuleCat colimits and cokernel APIs, not this varying-ring diagram.
   Read FiniteRelationMatrixLift and FiniteRelationCokernelColimit: they require
   PartialOrder and the canonical colimit, and do not supply the whole tail diagram.
   Read the nearby finite-presentation diagram theorem: its finite-type-over-integers
   hypothesis is unavailable here. Its private helpers cannot be imported by name.
4. **Route and pruning: pass after import cleanup.** The matrix lift, actual stage
   cokernels, tensor right exactness and representative criterion follow the
   presentation paragraph of [Stacks 00QX](https://stacks.math.columbia.edu/tag/00QX)
   and its non-local analogue [00R1](https://stacks.math.columbia.edu/tag/00R1),
   both read independently. Checked sk-thm-p1's realized statement and four steps;
   this construction changes none of them. Original proof_deps was empty, so no old
   dependency is omitted from No longer needed. Tested deleting each added import
   separately: only Mathlib.Algebra.Module.Shrink was redundant, and removed it.
5. **DAG: pass.** Checked every proof dependency's statement and Mathlib match or
   Lean declaration against the actual proof. The four proof steps and proof_origin
   accurately describe the matrix lift, tail restriction, explicit quotient diagram,
   tensor comparisons and additive colimit. No new node or change record is needed.

Second reading changed only the redundant Shrink import and this report. One original
hole closed, zero holes added, zero split off; the mathematical proof required no repair.
