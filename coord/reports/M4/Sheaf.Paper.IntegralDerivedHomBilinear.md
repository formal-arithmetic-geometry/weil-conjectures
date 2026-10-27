## What changed

Filled `WeilConjectures.integralDerivedHom_bilinear` in the assigned module without
changing its signature or either public import. Added only proof imports and a
proved private helper, `closedHom_bilinear`. The helper derives both separate
linear maps from the tensor-Hom adjunction, then uses linear composition and
functoriality to construct the requested nested linear map.

The specialization proves equality of the published constant-section linear
structure with the standard Mathlib derived linear structure. This ensures the
proof uses exactly the scalar action in the original statement. The native tensor
is linear by the existing general module-sheaf tensor helper, restriction of
scalars, braiding, and `DerivedCategory.monoidalLinear`.

Updated the item's DAG proof, proof dependencies and proof origin to this route.
No other existing module, signature, definition, attribute or public import changed.

Validation: the complete assigned module compiled through `lcompile.py` in 6.7 s,
with exit code 0 and no warnings. Its original public theorem signature is unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.integralDerivedHom_bilinear`
(`lem-sf-integral-derived-hom-bilinear`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivered module. The private helper is fully proved.

## No longer needed

No existing imports removed and no whole module pruned. The planned direct
chain-level Hom calculation and roof argument are replaced by the existing
closed tensor-Hom adjunction. Removed the direct proof-dependency edges to
`def-pur-derived-internal-hom` and `lem-pur-rhom-well-defined`; these remain
transitively needed by the existing construction and adjunction, so this delivery
does not claim that their modules can be withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The shorter route is the already-proved
`RingedDerivedNative.closedAdjunction`, together with the adopted source library's
`DerivedCategory.monoidalLinear`. The generic private `tensor_linear` helper of
`LineEvaluationInversePair` applies to every module sheaf, despite the surrounding
module's line-bundle topic. Its proof uses only pure-tensor extensionality and
scalar balancing, and introduces no line-bundle hypothesis here.

The cross-unit nodes `lem-sf-ringed-derived-tensor-hom-adjunction`,
`lem-sf-ringed-derived-native-tensor`, `lem-sfb-derived-monoidal`, and
`lem-pur-sheaf-line-evaluation-inverse-pair` are used as generic categorical tools.
No step of the owning unit is bypassed; its `realized` record has no designated
steps. No `tool_uses` approval field was added or edited.

Searches were run through `msearch.py` with LeanFinder (linear internal Hom),
Loogle (`CategoryTheory.Functor.Linear`), and grep (derived/Hom-complex linearity).
No direct bilinearity match was returned. Repository searches located the tensor
linearity, closed adjunction, and constant-section uniqueness declarations used.

Edge cases: the proof is categorical and assumes no nonzero object, torsion-free
input, boundedness, constructibility, or completeness of the four derived objects.
Zero objects and zero morphisms obey the same linear-map laws.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
