# Lisse local instance caches

## Reason

The completed tensor, quotient and rational scalar-extension proofs repeatedly ask
for the inherited additive and linear structures of sheaf and integral-system Hom
spaces. Four named caches keep those instance expressions shared. Without these
caches the full module repeatedly exceeded its 60-second compile limit. The
revised module compiled, including the delivery axiom probe.

All four instances are local: importing this module does not activate them. Their
values are the existing inherited instances, obtained by `inferInstance` before
the cache itself is registered. The names are public because they occur in the
elaborated bodies and types of public constructions. No existing public signature,
definition body, public import, mathematical structure, or target meaning changes.

## Old

None of the following four declaration names existed. Lean inferred the inherited
structures directly each time; the existing integral Hom caches remain unchanged.

## New

In `namespace AlgebraicGeometry.Scheme`, with the module's existing section variables:

```lean
local instance (priority := 10000) lisseIntegralPreadditive :
    Preadditive (LisseIntegralSheaf l E Y) := inferInstance

local instance (priority := 10000) lisseIntegralLinear :
    Linear (Padic.coefficientExtensionIntegers l E) (LisseIntegralSheaf l E Y) :=
  inferInstance

local instance (priority := 10000) lisseSheafHomAddCommGroup
    {R : Type (u + 1)} [Ring R]
    (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    AddCommGroup (F ⟶ G) := inferInstance

local instance (priority := 10000) lisseSheafHomModule
    {R : Type (u + 1)} [CommRing R]
    (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    Module R (F ⟶ G) := inferInstance
```

## Users

Running `tools/downstream.py Sheaf.Paper.LisseAdicSheaves --uses <name>`
for each of these four names reports zero existing module users of each name.
The module has 59 transitive import consumers, but the local instances do not
enter any consumer's instance search. No consumer needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LisseAdicSheaves | F7 | adds the four local caches and uses them internally |

No module held by another group is modified. The unchanged direct consumer
`Sheaf.Paper.LisseIntegralSmallCoefficients` is checked against the delivered module
in a separate scratch compilation overlay. Both compiled without warnings:
38.9 seconds for the delivered module and 2.9 seconds for that unchanged consumer.

## Status

landed 20261020T135405-L-1818283 2026-10-20 (merge of deliver/F7/Sheaf.Paper.LisseAdicSheaves)
