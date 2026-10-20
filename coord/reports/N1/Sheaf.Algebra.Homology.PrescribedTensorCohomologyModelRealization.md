## What changed

Restored Sheaf.Algebra.Homology.PrescribedTensorCohomologyModelRealization from
its quarantine archive and proved
RingTensorCohomology.prescribedTensorCohomology_model_realization without changing
its signature. The public model import now selects the adopted WeilConjectures
provider, resolving the duplicate-structure import error.

The proof constructs natural source and target identifications on the chosen
K-flat replacement, upgrades them to tensor-algebra-linear isomorphisms using
the prescribed scalar actions, and uses the canonical flat homology adjunct for
gamma. It proves gamma naturality, the counit-compatible model-map equation, and
the final localized comparison equation. All helper lemmas are private and fully
proved. The node proof and dependencies now describe this Lean argument.

Change record: coord/changes/N1-prescribed-tensor-cohomology-realization.md.

## Proved and sorry left

Closed 1 original hole:
RingTensorCohomology.prescribedTensorCohomology_model_realization
(node lem-pc-prescribed-tensor-cohomology-model-realization).

Zero sorry left in the item, zero holes added elsewhere, and zero results split
off. This is a proof, not a decomposition. No definitions contain sorry.
The final axiom probe reports exactly propext, Classical.choice, and Quot.sound.
Single-file compilation succeeds without warnings (25.2 seconds including the probe).
The unchanged quarantined consumer AffineTensorCohomologyLocalizationSquare also
compiles against this restoration (11.8 seconds), after compiling unchanged
copies of its restored dependencies. Those temporary test copies are not delivered.

## No longer needed

Removed the public Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel import
in favor of its adopted upstream provider. Removed direct proof imports of
WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit and
WeilConjectures.Algebra.Homology.MixedTensorKFlatQuasiIso. Instead use the existing
public ExtensionKFlatQuasiIso theorem and the source-library characterization of
left derived functors on K-flat complexes. Thus lem-pc-kflat-scalar-extension-counit
and lem-pc-mixed-tensor-kflat-quasi-iso are no longer direct proof dependencies of
this node. The latter remains a transitive dependency of ExtensionKFlatQuasiIso;
no declaration or module is withdrawn or claimed globally unnecessary.

Removed the redundant direct LeftDerivedFunctor.Defs import because the public
ExtensionKFlatQuasiIso import already supplies it. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The item is absent from lean because of quarantine, not withdrawal. Its archive
and its node attachment were preserved. The quarantine was caused by importing
two providers of the same model structure. The old Sheaf provider is now withdrawn;
the restored file explicitly imports the adopted upstream provider.

The original proof plan is valid, but invoking the existing scalar-extension
preservation theorem is shorter than repeating the mixed-tensor specialization,
and the general derived-functor API applies directly to the supplied K-flat
predicate. The implemented proof records these dependencies. No mathematical
statement repair, target change, consumer adaptation, or new node is required.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
