## What changed

Restored the quarantined zero-hole module
Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel with its
original public signature and public imports. Replaced the call to the retired
strictHenselization_structural_ringHom_flat with a proved private helper,
finiteEtaleModel_small_strictHenselization_flat. The helper uses the direct
filtered-colimit argument already present in repaired StrictHenselRootPurityData.
Its private import is WeilConjectures.RingTheory.ProEtale.FaithfullyFlat.

Updated proof, proof_deps, and proof_origin of
lem-sbc-strict-hensel-root-finite-etale-model to record that direct argument.
The Lean attachment, statement, all other node fields, and unit route remain.
Change record: coord/changes/E2-strict-hensel-root-finite-etale-model-restoration.md.

The archive fails in 2.5 seconds at the missing identifier; the repaired module
compiles in 4.9 seconds with axiom probes. Both the public theorem and private
flatness helper depend only on propext, Classical.choice, and Quot.sound.
The public signature was compared verbatim with the archive. Its quarantined
consumer's existing call still has exactly the same interface.

## Proved and sorry left

This is a repair of an already proved, quarantined module. Both the archive and
the restored module have zero local holes. Holes closed: none (0 of 0).
Holes added: none. Holes split off: none. Sorries left: none.

AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_finite_etale_model
(lem-sbc-strict-hensel-root-finite-etale-model) retains a complete proof.
The new private finiteEtaleModel_small_strictHenselization_flat is fully proved.

## No longer needed

Removed the private import
Sheaf.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat, an empty
retired module whose flatness declaration is no longer available.
Removed the redundant direct import Mathlib.RingTheory.Flat.Basic; the required
flatness API is supplied by the replacement proof import.

This proof no longer calls the upstream strictHenselization structural-flatness
theorem and no longer has lem-sbc-affine-strict-henselization-structural-flat as
a direct proof dependency. The underlying colimit and etale-flatness tools are
recorded directly instead. This does not withdraw that node or its upstream
module, which other consumers still use. No Lean module is withdrawn.
All other declared proof dependencies are used. The original incoming dependency
from lem-sbc-regular-divisor-strict-hensel-root-section is preserved.

## Where the brief, the DAG or earlier work was wrong

The rework row correctly identifies a missing declaration after upstream sync.
The upstream replacement has strictHenselization/strictLocalizationToBase in its
signature; it is not a direct substitute for the original small coordinate-ring
colimit interface strictHenselizationRing/strictHenselizationStructuralMap.
The neighboring repaired purity-data module provides the correct direct proof.
The general expectation of proving a sorry does not apply: this assigned repair
starts and ends with zero holes. No statement is disputed or changed.

Searches with msearch.py (loogle, leanfinder, and grep) and rg found the existing
colimit-flatness tools and that local repair. A possible Cartier-complement
shortcut would depend on a theorem that still contains sorry, so it was not used.
No second reader or other agent was started, as required by the dispatcher brief.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
