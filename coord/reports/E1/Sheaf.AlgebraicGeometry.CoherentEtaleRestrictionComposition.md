## What changed

Filled `AlgebraicGeometry.Scheme.Modules.coherentEtaleRestrictionIso_composition`
in `Sheaf.AlgebraicGeometry.CoherentEtaleRestrictionComposition`, preserving its
statement and all four public imports. Added the proof-only import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.InternalHom`, using its proved
formula for the unit of localization restriction and direct image. The other
proof-only import, `Mathlib.Lean.Meta.CongrTheorems`, supplies the congruence
proof generator used for the final chart specialization.

Private proved helpers establish associativity of the unit-normalized tensor
composition maps, read the normalization of `coherentEtaleRestrictionIso`, and
identify the given section formula with the localization adjunct. Cancellation
then gives the required equality. An explicit congruence for the site counit's
scheme map avoids unfolding the tensor construction during kernel conversion.
The chart specialization uses a private congruence helper that caches repeated
pullback-object equality proofs; its generated proof is checked by the kernel.
No existing definition, public declaration, or other module is changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.coherentEtaleRestrictionIso_composition`
(node `lem-weil-pbc-coherent-etale-restriction-composition`).
There are zero remaining holes in the item module, zero holes added elsewhere,
and zero split-off statements. Every private helper has a complete proof.
The complete module compiled without errors or warnings in 43.5 seconds.
`#print axioms` for the public theorem and the private congruence helper lists
only `propext`, `Classical.choice`, and `Quot.sound`. The public theorem has no
transitive `sorry` dependency. Temporary probes and instrumentation were removed.

## No longer needed

None. No existing imports, modules, nodes, or unit steps are removed. All stated
proof dependencies remain used through their definitions and comparison maps.
The proof does not withdraw any source-library declaration or DAG obligation.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The proof follows the existing adjunction,
normalization, and tensor-composition route. No affine or nonempty hypothesis is
used. Localization coherence is proved by mates and the site pullback
composition equation.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
