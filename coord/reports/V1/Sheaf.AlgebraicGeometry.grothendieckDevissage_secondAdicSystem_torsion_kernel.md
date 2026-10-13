## What changed

The assigned module now proves
`AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_torsion_kernel`
with its original signature. At each level, `coherentMap_reduction_torsion`
gives the K^(2t) bound after reduction modulo K^(e+1). The actual comparison
square induces kernel and cokernel isomorphisms via Mathlib's `kernel.mapIso`
and `cokernel.mapIso`. A proved private helper transports zero ideal products
along these isomorphisms by `formalModuleQuotient_factor` and cancellation.
The K-adic object conditions supply annihilation of both coherent terms by
K^(e+1), and the fixed-thickening reflection theorem gives exponent 2*(2t)=4t.

Added the proof-only imports `Sheaf.AlgebraicGeometry.CoherentMapReductionTorsion`
and `Sheaf.AlgebraicGeometry.CoherentMapCompletionTorsionKernelReflection`.
Added the latter module with one public theorem and its DAG node. Updated the
assigned node's proof, proof dependencies and proof origin to match the Lean.
All definitions, existing signatures, universes, public imports and the existing theorem's docstring are unchanged. The new reflection module also has proof-only imports for
each module in its documented proof plan, including the Mathlib tensor-completion
and flatness input.
Both modules compile through lcompile.py in approximately two and four seconds.
Explicit types for the comparison isomorphisms prevent costly elaboration.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_torsion_kernel`
(node `lem-weil-pbc-devissage-second-adic-system-torsion-kernel`). No sorry remains
in the assigned module, including its proved private helper `product_zero_of_iso`.

Added one hole:
`AlgebraicGeometry.coherentMap_completion_torsion_kernel_reflection`
(node `lem-weil-pbc-coherent-map-completion-torsion-kernel-reflection`), in its own
module. Its proof is exactly `:= by sorry`, with the source and full argument in
its docstring. This is a decomposition, one hole closed and one added, with net
zero holes removed. The reduction theorem used by the proof also depends on the
existing kernel reduction obligation; this delivery does not claim to prove it.

The new reflection statement is strictly the second stage of the argument: it
has one ordinary coherent map on a fixed thickening, no second adic system,
no alpha, no comparison isomorphisms, and no comparison square. Its hypothesis
is the already established bound on reductions of that coherent map. The Lean
proof deriving this hypothesis from alpha and the supplied square is complete.

## No longer needed

Removed direct proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence`
- `Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated`
- `Sheaf.RingTheory.KernelCokernelAnnihilatedModIdeal`

Every old direct proof dependency absent from the new assigned node's
`proof_deps` is accounted for:

- `lem-weil-pbc-kernel-cokernel-annihilated-mod-ideal`: replaced here by the
  existing sheaf-level reduction theorem; the ring-level input remains below it.
- `lem-weil-pbc-formal-systems-annihilated-by-power`: its broad TFAE interface is
  replaced by the precise fixed-exponent affine-limit input
  `lem-weil-pbc-formal-annihilation-affine-limit` in the new reflection plan.
- `lem-weil-pbc-closed-immersion-coherent-equivalence`: moved to the new reflection
  module's proof plan and retained there as a proof-only import.

These are removals of direct imports/dependencies in the assigned module, not a
claim that their modules leave the targets' import closure. The new module imports
its still-open proof-plan inputs so that the closure includes the remaining work.
No whole-target-closure module pruning is claimed. No unit statement or realized
unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original one-step plan bundled reduction, transport and reflection but its
three declarations did not directly expose a fixed-thickening reflection
interface. The existing `coherentMap_reduction_torsion` does expose exactly the
first bound and is reused rather than duplicated. The newly isolated theorem
states only the missing second estimate.

The local literature checkout lacks `literature/stacks-project/coherent.tex`.
Read the actual source at https://stacks.math.columbia.edu/tag/088A and
https://stacks.math.columbia.edu/tag/0888, particularly the two consecutive
quantitative estimates and Remark 0888's inverse-limit scalar maps. The proof
keeps the source's use of a global equivalence on the closed thickening: it
assumes no faithfulness of completion of an individual affine ring.

`blueprint_refs.py ancestor` returned None because the chain uses module-valued
created.item fields. The existing item's explicit blueprint.from record supplies
the finite-etale-lifting ancestor and via chain instead. Blueprint search
`completion torsion kernel` returned zero matches.

## New nodes

`lem-weil-pbc-coherent-map-completion-torsion-kernel-reflection` states the generic
fixed-thickening reflection step from Stacks 088A, second use of 0888. Its proof
plan descends the coherent map to V(K^q), passes uniform component bounds to an
affine limit, uses finite-module tensor completion and flatness to identify the
completed ideal-action image on the coherent kernel, reflects zero by the global
completion equivalence, and pushes back to X. Each substantive input is an
existing cited node, and the docstring spells out the scalar maps and image
identification. Searches were actually run: LeanSearch unavailable, LeanFinder
returned ring-level completion hits, msearch grep returned zero matches; local
rg and blueprint search found no existing generic statement.

Edge cases checked mathematically before statement: the empty scheme has zero
modules; K=0 makes both the bound and conclusion automatic for positive exponents;
K=unit forces F=G=0 by the fixed-thickening support hypotheses. For I=unit the
completion equivalence forces the coherent category on the thickening to be zero.
No completeness or Jacobson hypothesis on individual affines is smuggled in.
The positive q and s exclude ill-typed or vacuous exponent-zero extrapolations.
No change record or forced adaptation is needed.

## Second reading by V1

1. Compared each delivered module with the repository. The only existing Lean
   module changed is the assigned item; a literal substring comparison confirms
   its theorem signature is byte-for-byte identical. Its public imports,
   universes and visibility are unchanged. The private helper is new and proved.
   Restored the original declaration docstring; no change record is required.
   The reflection module and its node are new. Verdict: pass.
2. Compiled both modules in import order using lcompile.py after the repairs,
   with no errors or warnings. Inspected all delivered Lean source: precisely one
   `sorry`, in the reported public reflection theorem; no forbidden declaration,
   holed definition, or arbitrary choice from an unproved existence statement.
   Scratch copies with `#print axioms` show the private helper uses exactly
   propext, Classical.choice and Quot.sound. The assigned theorem and reflection
   theorem additionally use sorryAx, consistently with the reported open work.
   Verdict: valid decomposition, not an axiom-free proof of the target.
3. Independently read Stacks Tags 088A and 0888. The fixed-thickening lemma is
   the second estimate alone: descend the coherent map to V(K^q), transfer
   reductions, take the affine limits using canonical scalar reverse maps,
   identify finite-module completion with flat tensor completion, and reflect
   vanishing of the coherent ideal-action image by the global equivalence.
   The two composites of each scalar reverse map are multiplication by f*g;
   independence of lifts also gives transition compatibility. Exact closed
   pushforward returns the kernel and ideal image on X. This is strictly smaller
   than the original theorem and is not its renamed restatement. Checked zero
   source/target, empty X, I=0, K=0, K=unit, and I=unit: the statement is valid;
   for I=unit the equivalence forces the coherent category on the thickening to
   be zero. Repeated Mathlib search with the different query “An equivalence of
   coherent sheaf completion reflects vanishing of an ideal multiple of a kernel”
   via msearch LeanFinder, and grep “completion.*kernel|kernel.*completion”;
   inspected returned ring-level completion results and local rg results in both
   Lean roots. No existing fixed-thickening reflection statement was found.
   The ext-zero theorem detects maps under a pre-existing torsion hypothesis and
   does not supply this bound. Closing the geometric reflection in a few minutes
   would require substantial new sheaf/completion infrastructure; retained its
   documented hole. Verdict: true, needed, source-backed split.
4. Read the existing reduction theorem and the old direct dependencies. The proof
   reuses that theorem and Mathlib kernel.mapIso/cokernel.mapIso, with no new
   reduction or transport hole. The supplied comparison square has the correct
   orientation; both system conditions supply exponent e+1, and 2*(2*t)=4*t.
   Checked dag/units/sk-thm-p1.json realized: no unit statement or realized step
   is removed or bypassed. Completed the No longer needed list for all three old
   direct proof dependencies. Added the new reflection module's proof-only
   planned-dependency imports, which the first worker had omitted; public imports
   still supply only its signature. Verdict: route preserved; no global pruning
   claim and no shorter available library theorem identified.
5. Compared node JSON to Lean: the existing node changes only proof, proof_deps
   and proof_origin; its dependency set is exactly the union of its proof steps.
   The new node has the required source, complete plan, dependency records,
   searches, split status, creation/blueprint provenance, chapter, unit and Lean
   record. Its Lean signature matches the delivered theorem literally and its
   dependency set is the union of the plan's uses. Verdict: pass.

Second reading changed: restored the existing docstring, added seven proof-only
imports for the new reflection plan, and made the report account for every old
proof dependency and distinguish direct-import removal from whole-closure pruning.
The Lean proof bodies and theorem signatures needed no repair. One original hole
closed, one strictly smaller hole added; this remains a net-zero decomposition.
