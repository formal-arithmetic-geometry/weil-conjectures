## What changed

Proved `AlgebraicGeometry.coherentFormalModules_restriction_kernel_factorization`
in its original module, with the signature and public imports unchanged.
The proof obtains the stabilized kernel presentation, restricts its images and
ideal-power quotients with their projection equations, and applies the already
proved `coherentFormalModule_kernel_factorization` on U. The given kernel fork
then supplies the map from the constructed K to its own point.

Added proof-only imports for the formal factorization theorem, coherence versus
quasi-coherence, quasi-coherent kernel/cokernel results, Mathlib's abelian-image
comparison, and the proved private quotient/restriction comparison helpers in
`Sheaf.AlgebraicGeometry.TorsionControlledFormalRestriction` (`import all`).
One proved private helper implements the restricted image of a levelwise kernel
composite. No public statement or definition changed.

Updated the existing node's proof and dependencies to record the explicit
quasi-coherence arguments and transport by the given fork's lift. The route of
the unit is preserved. The source was read at
https://stacks.math.columbia.edu/tag/087X, construction (a)--(d) and final sentence;
the local literature checkout does not contain coherent.tex.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.coherentFormalModules_restriction_kernel_factorization`
(node `lem-weil-pbc-formal-restriction-kernel-factorization`).
One hole closed, zero added, zero split off. No `sorry` remains in the delivered
module or its private kernel-image helper. This is a proof from existing library
declarations, not a decomposition into new holed statements. The existing
kernel-construction and restriction-object dependencies retain their own holes;
this delivery makes no claim that the theorem's entire axiom closure is closed.

The module compiles cleanly with lcompile.py. The argument does not divide by an
ideal element or require positive stabilization bounds; it includes empty U,
zero alpha, zero or unit ideals, and stabilization bound zero.

## No longer needed

No original imports were removed. The planned direct dependency
`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections` is replaced by
`lem-weil-pbc-torsion-controlled-formal-restriction`: only its already proved
private quotient/restriction comparisons are used. The ideal-product formula
remains a dependency of those helpers, so no library module is pruned.
Second reading removed the first worker's added direct imports of
`ModulePullbackIdealPowerProductImage` and `Modules.IdealTimesQuasiCoherentAffineSections`
after removing three duplicate helpers. The global
uniqueness clause returned by `coherentFormalModule_kernel` is unused, and no
kernel-fork isomorphism needs to be constructed: the given fork's lift suffices.
This does not remove that module, which supplies the kernel presentation.
The imported torsion-controlled module supplies generic quotient comparisons;
no torsion-bound or completion comparison theorem is applied.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The DAG omitted the explicit
coherence-to-quasi-coherence and quasi-coherent kernel/cokernel facts needed to
apply the ideal-product restriction formula to S; these dependencies are now
recorded. Its proposed transport through a kernel-fork isomorphism can be reduced
to the lift into the given limiting fork, with the same conclusion.
No forced adaptations and no new nodes.

## Second reading by Y3

1. PASS: compared the delivered module with the repository by diff. The existing
   theorem signature and docstring are byte-for-byte unchanged, as are both public
   imports. Only proof-only imports, private helpers, and the theorem proof changed.
   The node differs only in proof, proof_deps, and proof_origin.
2. PASS: the first version compiled without warnings. Scratch `#print axioms`
   checks found only propext, Classical.choice, and Quot.sound for its three
   private theorems and constructed quotient isomorphism. The main theorem also
   has sorryAx from existing dependencies, with no new local hole. There is no
   forbidden declaration or hollow definition. The quotient isomorphism is
   constructed by cokernel/subobject universal properties, not an arbitrary
   witness of an unproved existence theorem. Final compilation and the delivery
   probe recheck the repaired version.
3. PASS: no statements were split off and no holes were added. The remaining
   private kernel/image comparison is a generic preserved-image calculation.
   Zero morphisms, zero and unit ideals, empty opens, power zero, and bound zero
   require no additional hypotheses or exceptional argument.
4. REPAIRED: searched both library roots for quotient/restriction comparisons,
   kernel comparisons, and formal quotient isomorphisms; msearch grep for
   PreservesCokernel.iso, cokernelImageι, and image.preComp confirmed the Mathlib
   universal-property tools already used. Found three identical proved helpers
   in TorsionControlledFormalRestriction. Removed their duplicates and reused
   the existing quotient isomorphism and projection theorem with import all.
   Removed the two now-unused direct proof imports. Other imports supply named
   facts used in the proof or its preserved-kernel/image instances. All old
   proof dependencies remain used except the direct ideal-product dependency
   now supplied through the reused helper module. No module is pruned. Read
   dag/units/sk-thm-p1.json, including realized: the higher unit route stays.
5. REPAIRED: the DAG now names the helper module's node and records that only
   its generic quotient/restriction comparisons are used. Its other steps match
   the code: quasi-coherence of S, restriction of stabilized images and quotient
   equations, factorization on U, then the lift into the given limiting fork.
   The source [Stacks Tag 087X](https://stacks.math.columbia.edu/tag/087X) was read:
   the argument retains its stabilized-kernel construction and factorization
   route. No new node or change record is needed.

Changed: removed three duplicate private helpers and two direct proof imports,
added one proof-only import all for their existing module, corrected the DAG
helper dependency and this report. The main proof and public interface are retained.
