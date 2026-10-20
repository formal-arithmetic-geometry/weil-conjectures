# AlgebraicGeometry.FiniteSplitEtaleHypercover.injective_module_row_quasiIso

## Reason

The upstream sync quarantined this module because its arbitrary-ring proof called
the adopted constant-module equivalence with only `Ring R`, whereas that source
interface now requires `CommRing R`. The source declaration is correct and remains
verbatim. Restore the quarantined module with an explicit private arbitrary-ring
version of the scalar-extension construction. This changes only the proof and
adds proved private helpers; its public theorem and public import are identical.

The returned delivery `d585699ab6` was based on `e0d550965`; the landing tool
reported a concurrent write. After that return the current repository still
has no live copy under `lean/`. Re-read its rework entry and quarantined source,
confirmed that the current source matches the saved baseline byte for byte,
and reconstructed the module from that source with the retained repair
reapplied. The complete matching-lift and row proofs are preserved. The
matching-lift helper remains private as its `import all` consumer expects.

## Old

```lean
  let A := Scheme.etaleConstantModuleRing X R
  let G := Scheme.etaleConstantModuleFunctor X R
  have : G.IsEquivalence := Scheme.etaleConstantModuleFunctor_isEquivalence X R
```

These lines fail to synthesize `CommRing R`. The original module had zero holes.

## New

```lean
  let A := rowConstantModuleRing X R
  let G := rowConstantModuleFunctor X R
  have : G.IsEquivalence := rowConstantModuleFunctor_isEquivalence X R
```

The private construction uses the same `RingCat` module-sheafification and scalar
restriction argument as the adopted equivalence. Every private helper assumes
only `Ring`. Its unit and counit act identically on the underlying abelian
sections. The equivalence therefore preserves injectivity and supplies exactly
the module sheaf needed by the existing ringed-hypercover argument. All objects
are constructed explicitly; no existence witness or new proof hole is used.

The public theorem remains verbatim:

```lean
theorem injective_module_row_quasiIso (U : FiniteSplitEtaleHypercover X)
    (R : Type (u + 1)) [Ring R]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) [Injective F] :
    QuasiIso (sectionAugmentation R U F)
```

## Users

Searching both the live and quarantined Lean sources finds three direct importers,
including the `import all` consumer of the private matching-lift helper.
Two apply the unchanged public theorem; the third reuses the unchanged private
`matching_local_lifting` theorem. No consumer adapts, and no public
definition, target statement, or upstream source declaration changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.HypercoverInjectiveModuleRow | C9 | Restored proof with private scalar-equivalence helpers. |
| Sheaf.Paper.HypercoverCohomologyModule | unclaimed (quarantined) | Its call with `U R F` has the identical type. |
| Sheaf.AlgebraicGeometry.GrothendieckInjectiveHypercoverRow | unclaimed (quarantined) | Its endomorphism-ring specialization has the identical type. |
| Sheaf.AlgebraicGeometry.GrothendieckHypercoverZero | unclaimed (quarantined) | Its `import all` sees the unchanged private matching-lift theorem. |

## Status

landed 20261020T145458-L-2399959 2026-10-20 (merge of deliver/C9/Sheaf.Paper.HypercoverInjectiveModuleRow)
