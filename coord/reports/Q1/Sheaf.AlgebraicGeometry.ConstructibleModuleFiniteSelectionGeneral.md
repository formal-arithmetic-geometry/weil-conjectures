## What changed

Proved the original theorem in `Sheaf.AlgebraicGeometry.ConstructibleModuleFiniteSelectionGeneral`
with its signature unchanged. Added private, proved helpers `jointMap` and
`failure_locus_constructible`. Added proof-only imports of
`ConstructibleModuleSubobjectNoetherian`, `ConstructibleModuleSupportGeneral`,
`SpectralConstructibleFiniteIntersection`, and the source-library `Sites.StalkwiseCokernel`.
Updated the existing DAG node to record the proof actually used.

For every finite family its kernel is constructible, and its support is the failure locus
of stalk injectivity. Compactness of the constructible topology supplies finitely many
such loci with empty intersection. The union of their families is monomorphic, by
projection and cancellation on geometric stalks, and is reindexed by `Fin n`.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.exists_mono_biproduct_of_constructible_module_stalk_injective_general`.
Both private helpers are proved. No `sorry` remains in the delivered module, and no hole or
new module is added. This is a proof from existing named dependencies, not a decomposition.
The existing subobject constructibility theorem still depends on its previously named
unproved generic-constancy input; this delivery does not claim to eliminate inherited holes.

The module compiles cleanly through `lcompile.py` in about three seconds.

## No longer needed

No original import or original explicit proof dependency was removed (the original node
had no proof dependencies). The descending-kernel stabilization route is unnecessary.
The finite-coefficient selection modules `ConstructibleModuleFiniteSelection` and
`ConstructibleFiniteSelection`, and their finite-stalk/generic-point selection route, are
not imported or used by this proof. They may still be needed by other parents; no global
unreachability claim is made.

## Where the brief, the DAG or earlier work was wrong

The original node claimed that Noetherianity forces a descending chain of joint kernels
to stabilize. Noetherianity provides ascending-chain termination, so that reasoning does
not justify the statement. The proof instead uses constructibility of kernels as
subobjects of F and compactness of constructible failure loci. The targets G need not be
constructible, so the kernel-of-a-map-between-constructibles theorem would not suffice;
the existing subobject theorem is essential. The finite-coefficient selection theorem
also cannot be applied with only `[IsNoetherianRing Λ]`.

## Second reading by Q1

1. Compared the delivered module with the repository version. The theorem declaration and
   all existing declaration signatures are unchanged byte for byte; only proof-only imports,
   private helpers, documentation, and the theorem proof changed. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds with no errors and contains no `sorry`,
   `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The proof uses only named
   imported declarations and its helper definitions contain no holes. Verdict: pass.
3. Checked the private helper route and the existing DAG statement against the stalk-kernel
   argument. The failure-locus theorem is a genuine intermediate reduction, not a restatement
   of the target, and the target statement remains unchanged and appropriately strong. Verdict:
   pass.
4. Read the proof from the target downward. It uses constructible kernel subobjects, support
   constructibility, constructible-topology finite intersection, and stalk conservativity;
   the obsolete descending-kernel route and finite-coefficient selection route are not needed.
   The imports retained are required by the proof. Verdict: pass.
5. Compared the changed proof with the node's recorded steps and dependencies. The node records
   the constructible failure loci, compactness, projection/cancellation, and stalk
   conservativity route, with the same source and unit. Verdict: pass.

I changed only this report by adding the present review section. No Lean declarations or DAG
files required repair.
