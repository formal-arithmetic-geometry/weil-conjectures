## What changed

The original declaration `AlgebraicGeometry.Scheme.CompletionGluingData.completedRingMap_injective`
now has a complete Lean proof from two separate formal-gluing steps. Its signature is unchanged.
The two new modules are imported privately by the item. The node's proof and proof dependencies
now record this decomposition. No definitions or existing interfaces changed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.CompletionGluingData.completedRingMap_injective`.
Added two holes:

- `AlgebraicGeometry.Scheme.CompletionGluingData.completedRingMap_kernel_torsion`
  (`lem-sbc-completed-matching-ring-map-kernel-torsion`). This is the principal-chart
  localization step: every kernel element is maximal-ideal-power torsion.
- `AlgebraicGeometry.Scheme.CompletionGluingData.completedRingMap_torsion_kernel_zero`
  (`lem-sbc-completed-matching-ring-map-torsion-kernel`). This is injectivity restricted
  to maximal-ideal-power torsion, via torsion-submodule base change and the matching equalizer.

This is a decomposition, not a net decrease in holes: one closed, two added.
Neither new theorem states unrestricted injectivity. The item combines them by obtaining
an annihilating exponent and then applying torsion-kernel vanishing, followed by the
additive-homomorphism injectivity criterion. All three modules compile.

Edge cases checked in the arguments: exponent zero forces x=0 by taking a=1; if the
punctured spectrum is empty the local Noetherian ring is Artinian, the maximal ideal
is nilpotent, and the torsion comparison applies to every element. Empty component schemes
and zero component rings obey the same equalizer and tensor calculations. There is no
nontriviality or nonempty-chart hypothesis in either new statement.

## No longer needed

No imports removed and no modules pruned. The original four definition dependencies remain
necessary to the statements and construction; they were moved into the two split steps'
proof plans. No surjectivity or cokernel-descent step is needed for this injectivity proof.
The generic formal-gluing injective-approximation module is not imported: its existential
public interface does not identify its H with h0 or specify the prime projection, so it
cannot directly identify its injective map with completedRingMap.

## Where the brief, the DAG or earlier work was wrong

The previously missing compiled CompletedMatchingRingMap dependency is now present in the
published build. The unchanged original module compiles against it. Temporary dependency
copies used during diagnosis were removed; none are part of this delivery.

The original proof plan names only definitions and omits the scheme-to-formal-gluing
interface needed to apply the generic ring-theoretic API. The two new statements isolate
that work at the localization and torsion stages. The private kernel-torsion calculation
and the proved torsion-submodule base-change theorem provide the mathematical route;
no need to prove the full formal-gluing equivalence or the surjective comparison here.

An initial kernel-equals-bottom restatement was discarded: it was not a reduction.

## New nodes

`lem-sbc-completed-matching-ring-map-kernel-torsion`, module
`Sheaf.AlgebraicGeometry.Morphisms.CompletedMatchingRingMapKernelTorsion`, records the
localized comparison and finite-generator annihilation argument from Stacks 05ER and 0BLH.

`lem-sbc-completed-matching-ring-map-torsion-kernel`, module
`Sheaf.AlgebraicGeometry.Morphisms.CompletedMatchingRingMapTorsionKernel`, records the
05EC torsion-submodule base-change argument applied to matching sections. Its conclusion
only concerns elements already annihilated by a maximal-ideal power.

No change records are needed: all existing signatures and public imports are preserved.

## Second reading by Q2

1. Compared the delivered item with the repository using diff and an exact substring
   check of its theorem signature: byte-identical. Only its proof and two private
   imports changed. No definitions changed. The two other modules are new. The
   existing node differs only in proof, proof_deps and proof_origin. Verdict: pass.
2. Compiled all three modules locally in import order. Compiled scratch copies with
   #print axioms for all three declarations: exactly propext, Classical.choice,
   Quot.sound and sorryAx. The latter is expected from the two explicitly listed
   new holes. No forbidden declarations, hollow definitions or hidden holes occur
   in the delivered modules. Verdict: valid conditional proof, a decomposition,
   not a completed axiom-free proof of injectivity.
3. Read the two split statements against Stacks 05ER, 05EC (1) and 0BLH, and the
   actual matching-ring and comparison constructions. Kernel torsion is the
   localization step; vanishing on torsion is the independent torsion-submodule
   comparison step. Neither restates unrestricted injectivity. Checked exponent
   zero, empty generators, empty punctured spectrum and empty component schemes.
   Searched again with leanfinder (support of a scalar-extension kernel), loogle
   (AdicCompletion, Function.Injective), and grep (primaryComponent and formal
   gluing), and inspected the upstream localization, torsion-base-change and
   injective-approximation interfaces. No exact replacement exists: translating
   the scheme matching construction into their module data remains necessary.
   Verdict: both statements are true, needed and strictly parts of the argument;
   neither can be closed in a few minutes from the existing interface.
4. The item uses the two steps directly via the zero-kernel criterion; all its
   imports are needed. The split modules' sole public import supplies their
   signatures. The old proof_deps are def-sbc-completed-matching-ring-map,
   def-sbc-punctured-completion-matching-sections, def-weil-pbc-noetherian-ring and
   def-weil-finite-integral-morphism. They no longer directly prove the item;
   all remain statement/construction dependencies and occur in the split proof
   plans, so no corresponding modules can be pruned. Read the unit's realized
   fields (currently empty) and its spreading route: this decomposition stays
   below the formal-gluing input and bypasses no unit step. Verdict: pass.
5. Checked all node IDs, modules, declarations, verbatim Lean statements,
   statement dependencies, sources, proof plans, dependency unions, origin,
   creation fields, chapter/unit and blueprint ancestry. The original node
   records the two-step proof as written. The new nodes record the localization
   and torsion arguments separately and have all three required search kinds.
   Verdict: pass.

Second reading changed only the new lemmas' proof docstrings and matching node
proof text: made the finite affine-chart construction, matching-ring/H0 and
pushout/tensor identifications, scalar action, and kernel map formula explicit.
Clarified the monomial exponent and empty-generator case, and that the torsion
preimage may have a different annihilating exponent. Added explicit dependency
citations to the new node statements and recorded the independent searches.
The original signature, proof and all imports remain as submitted. One original
hole is closed, two new named holes remain; net holes closed minus added is -1.
