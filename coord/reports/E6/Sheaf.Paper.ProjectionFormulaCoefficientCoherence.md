## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.compactificationProjection_coefficient_coherence` by a proof from the existing proper/open right projection-action components and their canonical compactification pasting. Private categorical calculations derive its unit law, conjugate the right action by tensor symmetry, and cancel exactly the assumed invertible components. Fixed-coefficient constructibility and Tor-amplitude transport provide all displayed domains. The public theorem signature is preserved. The coefficient-coherence predicate is represented by a Prop structure whose single `laws` field is precisely its former quantified body; no hypothesis, canonical map, equation or domain changes.

Updated `lem-pur-projection-formula-coefficient-coherence` to record this route. No other module is adapted.

The Prop-structure representation prevents expensive conversion between automatically abstracted nested monoidal instance proofs and the canonical instances used by the private theorems. The change record is `coord/changes/E6-projection-coherence-prop-structure.md`. The downstream tool lists eight modules; none uses this predicate or the theorem, and none requires adaptation. All other public definitions and the theorem signature remain verbatim. No module in the adopted source library is edited.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.compactificationProjection_coefficient_coherence`.
No `sorry` remains in the item module. Holes closed: 1; holes added: 0;
split statements: 0. All new private helpers are proved.

The complete file compiled through `lcompile.py` in 50.0 seconds, including kernel
checking of the structure interface, the categorical calculations, domain transport
and final assembly. Profiling and diagnostic heartbeat settings were then removed.
The required delivery tool performs the final compile and preflight checks.

## No longer needed

The proof does not use `lem-pur-adjoint-left-projection-action`, `lem-pur-open-left-projection-action`, or `lem-pur-composite-left-projection-action`: the existing proper/open right-action components and their pasting already supply the required associativity. The unit equation follows from that law and invertibility of its unit component. It does not use the intrinsic derived-pullback tensor comparison or the general ringed derived closed structure to identify the fixed-coefficient maps. Direct fixed-coefficient theorems supply tensor and pullback stability.

Removed proof imports:

- `Mathlib.CategoryTheory.Adjunction.Basic`
- `Sheaf.Paper.DerivedPullbackTensorIso`
- `Sheaf.Paper.PullbackTorAmplitude`
- `Sheaf.Paper.FiniteCoefficientTensorCtf`
- `Sheaf.Algebra.Homology.DerivedTensor`
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`
- `Sheaf.SixFunctors.OpenTensorNormalization`

The obsolete top-level tool approvals removed are `lem-pur-derived-pullback-tensor-iso`,
`lem-sf-open-tensor-normalization`, `lem-sf-pullback-tor-amplitude`,
`lem-sf-ringed-derived-closed-symmetric-monoidal`, and `lem-sf-tensor-ctf`.
Their statement dependencies and public imports remain where required by the original interface.
No module is withdrawn; these are dependencies pruned from this argument only.

## Where the brief, the DAG or earlier work was wrong

The original plan repeated the separate proper/open projection-action calculations already available in `FiniteProjectionActionLaws`. The fixed-coefficient formulation permits reusing its proved categorical pasting calculation and native proper/open inputs, without assuming absolute separatedness. The public theorem signature and mathematical assertion are unchanged. The original Prop-valued definition required a representation repair for kernel performance; the same quantified assertion is now its sole structure field, with the old/new declarations and consumer analysis in the change record.

The two newly used dependencies are generic tools: the already proved proper/open pasting calculations inside `FiniteProjectionActionLaws` are categorical identities, and `intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn` is the canonical fixed-ring realization comparison. They replace no step at the blueprint UNIT level. No maintainer approval is added to `tool_uses`.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
