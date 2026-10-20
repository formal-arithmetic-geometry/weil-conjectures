# AlgebraicGeometry.rhom_supported_quasiCoherent_pseudo_part_bound

## Reason

Retire the duplicate `Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPartBound`
in favor of `WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPartBound`,
as requested by its `coord/retire-items.tsv` row and the human's retirement instruction
in `coord/changes/retire-sheaf-twins-20261020.md`.
Both modules already contain complete proofs. The upstream statement's explicit
`SheafOfModules.overFunctor.{u}` universe annotation is the only statement difference;
it is definitionally the same functor inferred in the old statement.
No upstream declaration, public import, definition, or target statement is changed.

## Old

The statement in the duplicate module:

```lean
theorem rhom_supported_quasiCoherent_pseudo_part_bound
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K L : schemeDerivedCategory X)
    (hL : schemeDerivedQCohProperty X L)
    (hK : Scheme.IsPseudoCoherent X K) (hGE : ∃ a : ℤ, L.IsGE a) :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ a : ℤ, ∀ n : ℤ, n < a →
      IsZero ((SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
            ((derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
              X.toRingedSpace.sheaf).obj (op K, L))))
```

Consumer proof import:

```lean
import Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPartBound
```

## New

The existing, proved upstream declaration:

```lean
theorem rhom_supported_quasiCoherent_pseudo_part_bound
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K L : schemeDerivedCategory X)
    (hL : schemeDerivedQCohProperty X L)
    (hK : Scheme.IsPseudoCoherent X K) (hGE : ∃ a : ℤ, L.IsGE a) :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ a : ℤ, ∀ n : ℤ, n < a →
      IsZero ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
            ((derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
              X.toRingedSpace.sheaf).obj (op K, L))))
```

Consumer proof import:

```lean
import WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPartBound
```

Withdraw the duplicate module using `deleted.txt`; redirect its existing DAG attachment
to the upstream declaration. The parent's proof, statement, and DAG dependencies stay
valid: the same lower-bound component node is still used.

## Users

`tools/downstream.py` lists the two downstream modules below. Its `--uses` result
also includes the retired module itself, whose declaration is replaced by its upstream twin.
Neither consumer is currently claimed in `coord/claims/`.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPartBound | P7 | Withdraw duplicate; attach node upstream. |
| Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPart | unclaimed | Replace the proof import; theorem and proof unchanged. |
| Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherent | unclaimed | No text changes; uses the same parent theorem. |

## Status

landed 20261020T221305-L-4169557 2026-10-20 (merge of deliver/P7/Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPartBound)
