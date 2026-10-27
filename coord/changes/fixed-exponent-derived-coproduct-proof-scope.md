# AlgebraicGeometry.Etale.isIso_sigmaComparison_rightDerivedLowerStar_of_fixedExponent

## Reason

The completed proof adds a file-scoped backward elaboration option and a private
local right-adjoint instance for coinduction. The static interface check requires
this record for the changed command stream. These commands guide elaboration in
this file; no public declaration signature, definition, or public import changes.
All added private helpers are proved.

## Old

```lean
set_option autoImplicit false
```

There was no local coinduction instance. The public theorem signature was:

```lean
theorem isIso_sigmaComparison_rightDerivedLowerStar_of_fixedExponent
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (hf : f.torsionEtaleCohomologicalDimension < ⊤) (n : ℕ) (hn : 1 ≤ n)
    (I : Type (u + 1)) (K : I → DerivedCategoryModule Λ X)
    (hK : ∀ i : I, n • 𝟙 (K i) = 0) :
    IsIso (@sigmaComparison _ _ _ _ _
      (rightDerivedLowerStar (ModuleCat.{u + 1} Λ) f) K
      ((derived_hasCoproducts
        (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) I).has_colimit _)
      ((derived_hasCoproducts
        (C := Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) I).has_colimit _))
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private noncomputable local instance coind_rightAdjoint (n : ℕ) :
    (coindZMod.{u + 1} n).IsRightAdjoint :=
  (forget₂CoindZModAdj n).isRightAdjoint
```

The public theorem signature remains verbatim the signature in Old; its proof
now constructs the Z/n retract and transports coproduct preservation. Every new
import is a private proof import. The local instance does not become a public
instance, and the option does not modify the elaborated statement.

## Users

The declaration search in `tools/downstream.py --uses` reports exactly the
following two modules. Its separate import-closure list has 2344 modules; none
needs adaptation because the elaborated public interface is unchanged. The only
direct importing module is the projection-formula consumer listed below.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FixedExponentDerivedCoproducts | U3 | Proof completed; signature unchanged. |
| Sheaf.AlgebraicGeometry.TorsionObjectConstantProjection | unclaimed | Existing application at line 125 has exactly the same type; no adaptation. |

The target meanings and all consumer hypotheses and conclusions remain identical.
No forced adaptation is included.

## Status

landed 20261024T020704-L-2645657 2026-10-24 (merge of deliver/U3/Sheaf.AlgebraicGeometry.FixedExponentDerivedCoproducts)
