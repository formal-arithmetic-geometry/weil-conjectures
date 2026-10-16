# AlgebraicGeometry.ProEtale.exists_finiteCoefficient_gluing_of_local_models

## Reason

The static preflight classifies added proof-local commands as an interface change
and requires this record. The public theorem signature and all existing
definitions are unchanged. The commands support the new private scalar-adjoint
proof and keep its comparison isomorphism from unfolding during subsequent
proof elaboration. No target statement or definition is repaired or changed.

## Old

The original public signature, verbatim:

```lean
theorem exists_finiteCoefficient_gluing_of_local_models
    (T X : Scheme.{u}) [QuasiSeparatedSpace X]
    (f : X ⟶ T) (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)))
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (hfinite : Finite U.I₀) (haffine : ∀ i, IsAffine (U.X i))
    (N : ∀ i, Mod (Sheaf (Scheme.ProEt.topology (U.X i)) Ab.{u + 1})
      ((upperStar Ab.{u + 1} (U.f i)).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))))
    (hN : ∀ i, Mod.IsFinitelyPresented
      ((upperStar Ab.{u + 1} (U.f i)).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))) (N i))
    (e : ∀ i, Nonempty ((Mod.extendScalars
      ((upperStar Ab.{u + 1} (U.f i)).map
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).obj
          (N i) ≅
      ((upperStar Ab.{u + 1} (U.f i)).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))).obj M)) :
    ∃ (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (hEF : E ≤ F)
      (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F))),
      (∀ i, Nonempty (
        ((upperStar Ab.{u + 1} (U.f i)).mapMod
          ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F))).obj P ≅
        (Mod.extendScalars ((upperStar Ab.{u + 1} (U.f i)).map
          ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjMap T ℓ hEF)))).obj (N i))) ∧
      Nonempty ((Mod.extendScalars
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ F))).obj P ≅ M)
```

The original open commands, verbatim:

```lean
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
```

There was no ScalarComparison section and no local irreducibility attribute.

## New

The public signature remains verbatim identical:

```lean
theorem exists_finiteCoefficient_gluing_of_local_models
    (T X : Scheme.{u}) [QuasiSeparatedSpace X]
    (f : X ⟶ T) (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)))
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (hfinite : Finite U.I₀) (haffine : ∀ i, IsAffine (U.X i))
    (N : ∀ i, Mod (Sheaf (Scheme.ProEt.topology (U.X i)) Ab.{u + 1})
      ((upperStar Ab.{u + 1} (U.f i)).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))))
    (hN : ∀ i, Mod.IsFinitelyPresented
      ((upperStar Ab.{u + 1} (U.f i)).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))) (N i))
    (e : ∀ i, Nonempty ((Mod.extendScalars
      ((upperStar Ab.{u + 1} (U.f i)).map
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).obj
          (N i) ≅
      ((upperStar Ab.{u + 1} (U.f i)).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))).obj M)) :
    ∃ (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (hEF : E ≤ F)
      (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F))),
      (∀ i, Nonempty (
        ((upperStar Ab.{u + 1} (U.f i)).mapMod
          ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F))).obj P ≅
        (Mod.extendScalars ((upperStar Ab.{u + 1} (U.f i)).map
          ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjMap T ℓ hEF)))).obj (N i))) ∧
      Nonempty ((Mod.extendScalars
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ F))).obj P ≅ M)
```

The proof opens are now:

```lean
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonObj
open scoped CategoryTheory.Obj
```

The new private-helper section begins with these exact commands and variables:

```lean
section ScalarComparison

set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}} (g : Y ⟶ X)
  (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]
```

After `end ScalarComparison`, the proof-local attribute is:

```lean
attribute [local irreducible] pullbackExtendScalarsIso
```

All added helper declarations in the item module are private. The original three
public imports remain identical; the new proof imports are non-public. The
section option and local attribute affect proof elaboration in this module.
They change no existing declaration's signature or mathematical meaning.

## Users

`tools/downstream.py Sheaf.Paper.CondensedLocalModelGluing --uses
exists_finiteCoefficient_gluing_of_local_models` lists twelve downstream modules.
Only `Sheaf.Paper.CondensedLfpCoefficientModel` directly mentions the theorem;
the item module itself is also a textual hit. All downstream modules are listed
below. There are no forced adaptations.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | Not adapted; all existing signatures and definitions unchanged. |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | unclaimed | Not adapted; all existing signatures and definitions unchanged. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | unclaimed | Not adapted; all existing signatures and definitions unchanged. |
| `Sheaf.Paper.CondensedLfpCoefficientModel` | unclaimed | Not adapted; all existing signatures and definitions unchanged. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | Not adapted; all existing signatures and definitions unchanged. |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | Not adapted; all existing signatures and definitions unchanged. |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | A3 | Not adapted; all existing signatures and definitions unchanged. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | unclaimed | Not adapted; all existing signatures and definitions unchanged. |
| `TargetsCheck` | unclaimed | Not adapted; all existing signatures and definitions unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | Not adapted; all existing signatures and definitions unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | Not adapted; all existing signatures and definitions unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | unclaimed | Not adapted; all existing signatures and definitions unchanged. |
| `Sheaf.Paper.CondensedLocalModelGluing` | A3 | Proof changed; signature identical. |

The unchanged direct consumer `Sheaf.Paper.CondensedLfpCoefficientModel` was
compiled through `lcompile.py` against the delivered sandbox overlay (passed).

## Status

landed 20261016T103837-L-2369142 2026-10-16 (merge of deliver/A3/Sheaf.Paper.CondensedLocalModelGluing)
