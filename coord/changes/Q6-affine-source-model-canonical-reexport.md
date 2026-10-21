# AlgebraicGeometry.exists_affineBaseChangeSourceModel

## Reason

Retire the quarantined Sheaf twin under the human's retirement hand-off of
2026-10-20. The archive has zero proof holes and duplicates the theorem already
proved under the same name in the official library. The previous attempt's
compatibility re-export did not satisfy the explicit retirement assignment.

The quarantine archive remains untouched. The original Lean path is listed in
deleted.txt; the delivery tool installs its standard empty withdrawn module.
The DAG attachment moves to the official provider, preserving the statement,
proof dependencies, proof steps and unit route. No upstream or target file changes.

## Old

The archived imports are, verbatim:

```lean
public import WeilConjectures.AlgebraicGeometry.AffineDerivedCohomologyPresentation
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.Algebra.Homology.AffineBaseChangeIntoPullback
import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeSourceModel
import Sheaf.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso
import WeilConjectures.Algebra.Homology.RingTensorCohomology
import Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde
import all Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore
```

The archived proved theorem's signature is, verbatim:

```lean
theorem exists_affineBaseChangeSourceModel
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    (φf : R →+* A) (φg : R →+* R') (φg' : A →+* A') (φf' : R' →+* A')
    (sq : IsPullback (Spec.map (CommRingCat.ofHom φg')) (Spec.map (CommRingCat.ofHom φf'))
      (Spec.map (CommRingCat.ofHom φf)) (Spec.map (CommRingCat.ofHom φg)))
    (K : schemeDerivedCategory (Spec (.of A)))
    (hK : schemeDerivedQCohProperty (Spec (.of A)) K)
    (hL : schemeDerivedQCohProperty (Spec (.of A'))
      ((derivedPullback (Spec.map (CommRingCat.ofHom φg'))).obj K))
    (P : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hP : P.IsAcyclicTensorKFlat) (e : DerivedCategory.Q.obj P ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φg'))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) (i : ℤ) :
    ∃ d : affineDerivedCohomologyModules A' i ⋙
          (ModuleCat.restrictScalars φf' ⋙ tilde.functor (.of R')) ≅
        (schemeDerivedQCohProperty (Spec (.of A'))).ι ⋙
          schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φf')) ⋙
          DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of R')).toRingedSpace)) i,
    let L : schemeDerivedQCohCategory (Spec (.of A')) := ⟨_, hL⟩
    let V := (affineDerivedCohomologyModules A' i).obj L
    let F := ModuleCat.restrictScalars φf' ⋙ tilde.functor (.of R')
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of R')).toRingedSpace)) i
    ∃ (U : ModuleCat.{u} A') (a : U ⟶ V)
      (eU : F.obj U ≅ H.obj ((derivedPullback (Spec.map (CommRingCat.ofHom φg))).obj
        ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φf))).obj K))),
      eU.hom ≫ H.map (schemeDerivedBaseChangeMap (Spec.map (CommRingCat.ofHom φf))
        (Spec.map (CommRingCat.ofHom φf')) (Spec.map (CommRingCat.ofHom φg))
        (Spec.map (CommRingCat.ofHom φg')) sq.w K) = F.map a ≫ d.hom.app L ∧
      ∀ p : PrimeSpectrum A',
        let r := affineBaseChangeIntoPullback
          (Spec.map (CommRingCat.ofHom φf)) (Spec.map (CommRingCat.ofHom φf'))
          (Spec.map (CommRingCat.ofHom φg)) (Spec.map (CommRingCat.ofHom φg'))
          sq K P e hc p i
        ∃ lU : LocalizedModule p.asIdeal.primeCompl U ≃+ (Arrow.mk r).left,
          ∀ x, affineDerivedCohomologyStalkIso A' i p L
            (LocalizedModule.map p.asIdeal.primeCompl a.hom x) = r (lU x)
```

The proof constructs a module K-flat resolution using the affine derived
quasi-coherent equivalence, applies the tilde source model, and transports the
localized equation through representative independence.

## New

The sole provider is the existing theorem in
`WeilConjectures.Algebra.Homology.AffineBaseChangeSourceModel`.
Its signature is the old signature above with precisely the binder
`(hP : P.IsAcyclicTensorKFlat)` replaced by `(hP : P.IsKFlatTensor)`.
The two predicates are definitionally equal, as the compatibility probe checks.
The complete official signature is recorded verbatim in the node's lean.statement.
No declaration is added and no proof is replaced by sorry.

The Sheaf copy is retired, not restored as a public re-export. Its node points to
the existing official declaration. The same node remains a dependency of its
cohomology-model parent, whose Lean attachment already points to the official twin.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.AffineBaseChangeSourceModel | Q6 | Retire quarantined copy; preserve theorem at official provider. |
| Sheaf.Algebra.Homology.AffineBaseChangeCohomologyModel | already retired; absent | Listed historical consumer has no current source or quarantine file. |
| WeilConjectures.Algebra.Homology.AffineBaseChangeCohomologyModel | unchanged source library | Already imports the official source model and uses IsKFlatTensor; compile unchanged. |

No live Lean module imports the historical Sheaf path. A scan of current source
and quarantine finds no remaining consumer to adapt. Only the archived item itself
and the official provider declare the theorem. The actual DAG parent is
lem-pc-affine-base-change-cohomology-model and continues to use the same source-model
node, now attached to the official theorem. Thus the mathematical dependency is
preserved, rather than inferred unnecessary from zero current importers.

## Status

landed 20261021T203719-L-3858263 2026-10-21 (merge of deliver/Q6/Sheaf.Algebra.Homology.AffineBaseChangeSourceModel)
