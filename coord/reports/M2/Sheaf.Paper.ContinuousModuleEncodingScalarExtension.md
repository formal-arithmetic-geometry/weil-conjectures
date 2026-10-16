## What changed

Repaired `Sheaf.Paper.ContinuousModuleEncodingScalarExtension` after the upstream sync.
Constructed the private `SheafOfModules.tensorToRestrict` and
`SheafOfModules.tensorHomEquiv` explicitly, restored the private inverse
`SheafOfModules.tensorFromRestrict`, and proved
`SheafOfModules.exists_siteChangeOfRingsAdjunction`.
The sectionwise inverse laws use Mathlib's scalar-extension Hom equivalence; naturality
uses the pure-tensor formula, recovered from the public `exists_changeOfRingsMap` theorem.
Sheafification and `Adjunction.leftAdjointOfEquiv` give the specified object function.
The continuous coefficient comparison and final uniqueness-of-left-adjoints proof are
unchanged. Public signatures and the unit route are preserved.
Updated the existing node's first proof step and proof origin to describe the repaired API.
Change record: `coord/changes/M2-continuous-module-scalar-extension-repair.md`.

## Proved and sorry left

Closed all three original holes:

- `SheafOfModules.tensorToRestrict` (a private data definition, now constructed).
- `SheafOfModules.tensorHomEquiv` (a private equivalence, now constructed).
- `SheafOfModules.exists_siteChangeOfRingsAdjunction`.

All belong to `lem-weil-pbc-continuous-module-encoding-scalar-extension`.
No holes added, no split-offs, and no `sorry` remains in the delivered module.
`continuousLisse_comap_compatibility` and `continuousModuleEncoding_scalar_extension`
retain their complete proofs. Single-file compilation passes; the dry run checks all
constants for axioms and performs the final static checks.

## No longer needed

Removed the redundant direct `import all
Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`. Its retired re-export module
supplies no declaration needed beyond those already available from the public coefficient
encoding import. The proof no longer accesses any private tensor-map theorem.
No mathematical proof-dependency node is removed: the sectionwise tensor/sheafification,
continuous encoding, and lisse coefficient notions remain necessary.
No claim is made that the wrapper becomes unreachable elsewhere in the target closure.

## Where the brief, the DAG or earlier work was wrong

The sync left two hollow private definitions and commented out their inverse, although
the public `exists_changeOfRingsMap` specification is sufficient to recover the generator
formula. The old `import all` of a retired wrapper does not expose private declarations
of the upstream module it re-exports. Using the public specification repairs this.
The existing mathematical statements and the three-step DAG route are correct.
The two downstream-use checks found no external user of either private helper; the public
consumer uses an unchanged theorem, so no forced adaptation is required.

## Second reading by M2

1. **Signatures and accidental changes — pass.** I compared the delivered module with
the repository version. The existing public theorem signatures and their statements are
byte-for-byte unchanged. The repair only fills private definitions, restores the private
inverse construction, proves the existing adjunction theorem, and removes one proof-only
import. The node and change record declare that repair.

2. **Proof and axioms — pass.** The delivered module compiles with
`python3 /home/ubuntu/weil-launcher/lcompile.py`. An axiom scan of
`SheafOfModules.exists_siteChangeOfRingsAdjunction`,
`continuousLisse_comap_compatibility`, and
`continuousModuleEncoding_scalar_extension` reports only `propext`, `Classical.choice`,
and `Quot.sound`. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
`implemented_by` declarations, and no definition contains `sorry`.

3. **Split-off statements — pass.** No new statement or split-off theorem was added.
The local pure-tensor helper is a private proved theorem derived from the public
`exists_changeOfRingsMap` specification, so it adds no DAG obligation. The repaired
definitions use explicit constructions rather than data selected from an undetermined
existence theorem.

4. **Shortest route and pruning — pass.** The proof uses the public scalar-extension
Hom equivalence, the public pure-tensor specification, sheafification's Hom equivalence,
and the adjunction constructors. The retired direct TensorProduct wrapper import is no
longer needed and was removed. The three proof steps and the unit route remain intact;
the node's proof text and origin record the repaired route and its existing dependencies.

5. **DAG agreement — pass.** The node's proof text describes the actual
`Classical.choose_spec`, sectionwise inverse, sheafification, and adjunction steps. Its
`proof_deps` are exactly the modules used by the proof, and its updated `proof_origin`
records M2's repair. No new nodes were required, and the unit's `realized` route is
unchanged.

I changed only the delivered module's proof and private constructions, the corresponding
existing node proof metadata, the repair change record, and this report. No statement was
weakened or strengthened, no holes were added, and all three original holes were closed.
