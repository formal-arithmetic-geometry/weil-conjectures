## What changed

Retire Sheaf.AlgebraicGeometry.Modules.ExteriorTensorKernelLocallySpanned under
retire-items.tsv row 750 and the human-approved retirement hand-off. Withdraw
the duplicate with deleted.txt and attach its node to the existing proved
WeilConjectures twin, preserving the mathematical statement and unit route.

Adapt the sole direct consumer ExteriorTensorKernelRelations: replace the proof
import, conjugate q through tensors of the canonical exteriorSheafPowerIso,
apply the upstream local-span theorem, and transport generator vanishing back.
The consumer's existing public signature and public imports are unchanged.
Its private comparison helper is fully proved from the existing comparison API.
Update the parent node to describe this proof.

Change record: coord/changes/G2-retire-exterior-tensor-kernel-locally-spanned.md.

## Proved and sorry left

Zero holes in the assigned module before retirement; zero holes closed, zero
holes added, zero split off. No sorry remains in the adapted consumer.
The existing exteriorTensor_kernel_locally_mem_span is retained upstream;
exteriorTensor_kernel_eq_zero_of_relations compiles with its unchanged type.
All new transport steps and the private exteriorTensor_comparison are proved.
The adapted consumer compiled cleanly on the server in 2.9 seconds.
A further import-order compile checked the adapted consumer (3.1 seconds) and
the unchanged immediate downstream DeterminantWedgeQuotientFactor (2.1 seconds).
Its temporary source copy was removed from the packet after validation.

## No longer needed

Withdraw lean/Sheaf/AlgebraicGeometry/Modules/ExteriorTensorKernelLocallySpanned.lean.
Replace its sole import in ExteriorTensorKernelRelations by
WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorKernelLocallySpanned.
The duplicate local_span_realization, locally_mem_of_germ_mem_span and
relationSpan_map proofs are supplied by the official twin. The duplicate
exteriorSheaf_comparison construction is unnecessary because the library already
provides exteriorSheafPowerIso. No mathematical dependency node is pruned: the
local-span node is retained with its upstream attachment, and the parent still
uses it. No other upstream declaration or proof is removed.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief does not identify this as a retirement assignment and
the assigned source already has a complete proof (D2/Q4). The authoritative
retire-items.tsv row 750 supplies the actual required repair. The APIs differ
only by two canonically isomorphic exterior-sheaf constructions; direct import
replacement alone would fail. The explicit comparison transport fixes this.
The edge cases r=0, s=0, zero rings and empty schemes introduce no new condition.

Searches ran through msearch.py: LeanFinder found general sheaf presentation
infrastructure; Loogle found Submodule.span_le; grep found no Mathlib match.
Direct source search found the exact upstream local-span theorem and the
existing exteriorSheafPowerIso comparison. These provide the shortest route.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
