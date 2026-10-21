# AlgebraicGeometry.affineTildeDerivedTensorToPushforward_homology

## Reason

Restore the quarantined item using the complete adopted source proof. The archived
and adopted theorem signatures are byte-identical. Reintroducing the old copied
implementation would duplicate a declaration already provided by the source tree;
the restored compatibility module instead publicly imports its canonical owner.
This repairs the absent module path without adding an open homology leaf.

The archive remains untouched. The node stays attached to the same declaration,
now at its actual source module, and all statement/proof dependencies and proof
steps are retained. No target statement or mathematical definition changes.

## Old

The quarantined module imported:

```lean
public import Sheaf.Algebra.Homology.AffineTildeDerivedTensorMate
import Sheaf.Algebra.Homology.AffineTildePushforwardHomologyFactorization
import Sheaf.Algebra.Homology.AffineTildeCoefficientPushforwardHomologyCoordinates
```

It locally redeclared the following already-adopted theorem with a complete proof:

```lean
theorem affineTildeDerivedTensorToPushforward_homology
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} B)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (m : ModuleCat.BaseDerivedTensorCohomologyModel R A B M D)
    (φ : A →+* D) (ψ : B →+* D)
    (hφ : (algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B)) = φ)
    (hψ : (algebraMap (A ⊗[R] B) D).comp
      Algebra.TensorProduct.includeRight.toRingHom = ψ) (i : ℤ) :
    let α := algebraMap (A ⊗[R] B) D
    let j : B →+* A ⊗[R] B := Algebra.TensorProduct.includeRight.toRingHom
    let T := tilde.functor (.of B)
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i
    let C := (((ModuleCat.extendScalars (α.comp
      (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj M)
    let Cg := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
    let cE := m.comparison i ≫ HomologicalComplex.homologyMap m.ordinaryToLocalized i ≫
      ((C.sc i).mapHomologyIso (ModuleCat.restrictScalars α)).hom
    let ρ := ModuleCat.restrictScalarsComp' j α ψ hψ.symm
    let s := (ModuleCat.restrictScalars j).map cE ≫ ρ.inv.app (C.homology i)
    let z₀ := (HomologicalComplex.homologyFunctor (ModuleCat.{u} D) (.up ℤ) i).map
      (eqToHom (by dsimp only [C, α]; rw [hφ] : C = Cg))
    (affineTildeDerivedTensorSourceIso R A B D M m i).hom ≫
        H.map (affineTildeDerivedTensorToPushforward R A B D M m φ ψ hφ hψ) =
      T.map s ≫ T.map ((ModuleCat.restrictScalars ψ).map z₀) ≫
        affineTildePushforwardCohomologyMap D B ψ Cg i
```

## New

```lean
public import WeilConjectures.Algebra.Homology.AffineTildeDerivedTensorHomologyCoordinates
```

The identical theorem is publicly available from its adopted implementation.
Its source proof retains exact-derived homology naturality, coefficient homology,
and the two proved pushforward-coordinate supporting results. Source-library
signatures, attributes, imports, definitions and proofs are untouched.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffineTildeDerivedTensorHomologyCoordinates | J3 | Restored compatibility interface; identical theorem re-exported. |
| Sheaf.Algebra.Homology.AffineBaseChangeTildeMateIdentityFactorization | unclaimed | Sole direct live importer from downstream.py; Forced import adaptation: use the adopted representative and retain the legacy tilde abbreviation; theorem signature and proof unchanged. |
| WeilConjectures.Algebra.Homology.AffineTildeDerivedTensorHomologyCoordinates | unclaimed | Canonical implementation reused without edits. |

A separate scan includes the quarantined parent at the same Sheaf path; its
existing import and use of the theorem are preserved. The original consumer fails against the restored interface with:

```text
import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeRepresentative failed,
environment already contains 'AlgebraicGeometry.affineBaseChangeTildeComplexIso._proof_18'
from Sheaf.Algebra.Homology.AffineBaseChangeTildeRepresentative
```

Its old representative import is replaced by these two public imports:

```lean
public import Sheaf.Algebra.Homology.AffineTildePushforwardCohomologyNormalization
public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeRepresentative
```

The normalization import preserves the `affineTildeFunctor` abbreviation used by
the unchanged public theorem signature. The adopted representative provides the
same public comparison definitions without loading their duplicate Sheaf bodies.
No theorem statement, visibility, attribute, proof or other line is changed.
`downstream.py` finds zero live modules importing this adapted parent; DAG parent
references remain intact.
The unit's realized statement and steps, and every DAG parent dependency, remain.
The adapted parent compiles (21.5 s); a fresh probe of its complete original
signature compiles (17.5 s). The original target-signature probe also compiles,
and its axiom audit contains only the permitted three axioms.

## Status

landed 20261021T203622-L-3844398 2026-10-21 (merge of deliver/J3/Sheaf.Algebra.Homology.AffineTildeDerivedTensorHomologyCoordinates)
