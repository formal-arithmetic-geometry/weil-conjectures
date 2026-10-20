# AlgebraicGeometry.Scheme.exists_affine_perfect_tensor_roof

## Reason

Restore the quarantined import path assigned in coord/rework.tsv. The archived
module fails because its public signature mentions IsAcyclicTensorKFlat while
that declaration is imported only privately. The upstream synchronization also
adopted a complete proof of the same roof theorem. Loading both declarations
would recreate a duplicate theorem and mixed tensor/K-flat environments.
Restore the Sheaf module as a public re-export of the canonical upstream module,
as already done for AffineKoszulSectionRoof. This restores the theorem and its
import path; it is not a withdrawal. The quarantine archive is untouched.
No source-library file, public declaration, or proof is edited.

## Old

The quarantined Sheaf module publicly imported
WeilConjectures.AlgebraicGeometry.PerfectComplex,
Sheaf.AlgebraicGeometry.DerivedTensorAugmentation, and
Mathlib.AlgebraicGeometry.AffineScheme. Its private proof imports were
WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPerfectPart,
Sheaf.AlgebraicGeometry.AffineKoszulSectionRoof, and
Sheaf.AlgebraicGeometry.TensorRoofTransposition. Its public signature was:

```lean
theorem exists_affine_perfect_tensor_roof
    (X : Scheme.{uX}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))]
    (E' : schemeDerivedQCohCategory X) (A : schemeDerivedCategory X) (hA : IsPerfect X A)
    (α : ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj A ⟶
        ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj E'.obj)
    (P : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) P)
    (eA : DerivedCategory.Q.obj P ≅ A) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := (SheafOfModules.tensorClosed X.sheaf).1.some
    ∃ J : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ,
      CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) J ∧ IsPerfect X (DerivedCategory.Q.obj J) ∧
      ∃ u : J ⟶ HomologicalComplex.tensorUnit
          (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ),
        let B := DerivedCategory.Q.obj (CochainComplex.mapBifunctor P J (curriedTensor _))
        let β : B ⟶ A := DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor _) (ComplexShape.up ℤ)) ≫
          DerivedCategory.Q.map (HomologicalComplex.rightUnitor P).hom ≫ eA.hom
        let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory
        ∃ (γ : B ⟶ E'.obj) (bU : R.obj B ≅ R.obj A),
          bU.hom = R.map β ∧ α = bU.inv ≫ R.map γ
```

## New

The restored module publicly imports
WeilConjectures.AlgebraicGeometry.AffinePerfectTensorRoof. It introduces no new
or duplicate declaration. The upstream module exposes the following existing
proved theorem:

```lean
theorem exists_affine_perfect_tensor_roof
    (X : Scheme.{uX}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))]
    (E' : schemeDerivedQCohCategory X) (A : schemeDerivedCategory X) (hA : IsPerfect X A)
    (α : ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj A ⟶
        ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj E'.obj)
    (P : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
    (eA : DerivedCategory.Q.obj P ≅ A) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := (SheafOfModules.tensorClosed X.sheaf).1.some
    ∃ J : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ,
      CochainComplex.IsKFlatTensor (R := X.sheaf) J ∧ IsPerfect X (DerivedCategory.Q.obj J) ∧
      ∃ u : J ⟶ HomologicalComplex.tensorUnit
          (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ),
        let B := DerivedCategory.Q.obj (CochainComplex.mapBifunctor P J (curriedTensor _))
        let β : B ⟶ A := DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor _) (ComplexShape.up ℤ)) ≫
          DerivedCategory.Q.map (HomologicalComplex.rightUnitor P).hom ≫ eA.hom
        let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory
        ∃ (γ : B ⟶ E'.obj) (bU : R.obj B ≅ R.obj A),
          bU.hom = R.map β ∧ α = bU.inv ≫ R.map γ
```

The two signatures are textually identical after replacing the archived name
IsAcyclicTensorKFlat by IsKFlatTensor. Their definition bodies, universes and
binders are identical: for every acyclic F the total tensor of F with K is
acyclic, using the same SheafOfModules.monoidalCategory. A consumer check
reconstructs the archived predicate under a fresh private name, copies the
complete archived signature, and applies the upstream theorem. This checks the
hypothesis and the existential witness property, including their tensor data.
No bound, nonempty-open hypothesis, perfectness of the total tensor, or support
condition is introduced. Empty U, zero complexes and the zero ring still fall
under the same theorem.

The node's Lean attachment now points to the existing upstream declaration,
with its current signature. Its mathematical statement, proof steps,
proof dependencies, proof origin, chapter and unit are preserved. The upstream
proof follows those steps: perfect-source RHom quasi-coherence; section-roof
representation; transposition; and inverse-isomorphism cancellation.
No target statement or target-used definition changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffinePerfectTensorRoof | A3 | Restore as public upstream re-export; retain the import path and theorem without a duplicate. |
| WeilConjectures.AlgebraicGeometry.AffinePerfectTensorRoof | unclaimed upstream; unchanged | Canonical proved theorem; its signature, imports and proof stay verbatim. |
| WeilConjectures.AlgebraicGeometry.AffinePerfectMapLift | unclaimed upstream; unchanged | Already imports and applies the canonical theorem; no adaptation. A scratch copy redirects only its private roof import to the restored Sheaf path to check the complete parent proof. |
| WeilConjectures | unclaimed upstream; unchanged | Publicly imports the canonical upstream module; no adaptation. |

An explicit scan of lean/Sheaf, lean/WeilConjectures, quarantine/Sheaf and
quarantine/WeilConjectures finds no source importing the Sheaf path. The sole
application is the upstream AffinePerfectMapLift. The archived item contains
the only other declaration of this name. The parent DAG node
lem-sc-affine-perfect-map-lift retains its dependency on
lem-sc-affine-perfect-tensor-roof. Other DAG references in created.item and
blueprint.from.via are provenance, not reverse mathematical dependencies.
The unit route is preserved. There are no forced adaptations.

## Status

landed 20261020T163937-L-3832571 2026-10-20 (merge of deliver/A3/Sheaf.AlgebraicGeometry.AffinePerfectTensorRoof)
