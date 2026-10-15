# AlgebraicGeometry.qcoh_ordinary_tensor_resolution_coordinates_witness

## Reason

The assigned family theorem was concurrently decomposed before this review. Its only
user, the parent coordinate theorem, can construct the already-existing normalized
coordinates and apply the already-existing fixed-coordinate naturality theorem to the
supplied maps. The existential comparison family is therefore redundant. This is
stage-3 pruning, with no new theorem hole and no claim that its existing downstream
naturality hole has been proved.

## Old

```lean
theorem qcoh_ordinary_tensor_resolution_coordinates_witness
    (Y : Scheme.{u}) (M N : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (MA NA : ∀ U : Y.affineOpens, ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : ∀ U : Y.affineOpens, MA U ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (sN : ∀ U : Y.affineOpens, NA U ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (P : ∀ U : Y.affineOpens, ProjectiveResolution (MA U))
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M)
    (hK : CochainComplex.IsKFlat (R := Y.sheaf) K) (hq : QuasiIso q) (n : ℕ) :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    let S := CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q := (CochainComplex.mapBifunctor K (S.obj N)
      (curriedTensor (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))).homology
        (-(n : ℤ))
    ∃ c : ∀ U : Y.affineOpens,
        ((((tensorRight (NA U)).mapHomologicalComplex (.down ℕ)).obj
          (P U).complex).homology n) ≃ₗ[Γ(Y, U.1)] Q.val.obj (op U.1),
      ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
        (_hbasic : ∃ f : Γ(Y, U.1), Y.basicOpen f = V.1),
        let φ := (Y.presheaf.map (homOfLE h).op).hom
        let TA := (tensorRight (NA U)).mapHomologicalComplex (.down ℕ)
        let TC := (tensorRight (NA V)).mapHomologicalComplex (.down ℕ)
        ∃ (b : NA U →ₛₗ[φ] NA V)
          (a : (P U).complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
            (.down ℕ)).obj (P V).complex)
          (k : TA.obj (P U).complex ⟶
            ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.down ℕ)).obj
              (TC.obj (P V).complex)),
          (∀ x : (P U).complex.X 0,
            sM V ((P V).π.f 0 (a.f 0 x)) =
              M.val.map (homOfLE h).op (sM U ((P U).π.f 0 x))) ∧
          (∀ y : NA U, sN V (b y) = N.val.map (homOfLE h).op (sN U y)) ∧
          (∀ (j : ℕ) (x : (P U).complex.X j) (y : NA U),
            k.f j (x ⊗ₜ[Γ(Y, U.1)] y) =
              (show (P V).complex.X j from a.f j x) ⊗ₜ[Γ(Y, V.1)] (b y)) ∧
          let e := ((TC.obj (P V).complex).sc n).mapHomologyIso
            (ModuleCat.restrictScalars φ)
          ∀ x, Q.val.map (homOfLE h).op (c U x) =
            c V (e.hom (HomologicalComplex.homologyMap k n x))
```

The parent imported the family module and used its existential comparison witnesses,
then proved comparison independence with private tensor-homotopy helpers.

## New

The family module is empty, as recorded in deleted.txt. No replacement declaration
with this name is introduced. The parent's existing public signature and visibility
are unchanged. Its proof chooses a K-flat resolution of N[0] inside the theorem proof,
constructs each coordinate with tensorResolutionCoordinateSections, and applies
tensorResolutionCoordinateSections_naturality to every supplied b,a,k. Both are
existing library declarations. Proof imports are QCohTensorResolutionCoordinateSectionsNaturality
and KFlatResolution. The unused private homotopy helpers and their
QuotientTensorResolutionLiftHomotopy import are removed. No target signature or
existing data definition changes. The existing naturality theorem remains open.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.QCohOrdinaryTensorResolutionCoordinates` | unclaimed at 12:12, 2026-10-15 | Replace the obsolete family import and witness proof with the direct fixed-coordinate proof; public signature unchanged. |

The source search found no other importer or user of the withdrawn declaration.
The original parent fails against the empty family module with
`Unknown identifier qcoh_ordinary_tensor_resolution_coordinates_witness` at line 212.
The adapted parent compiles. The witness node's lean attachment is removed with null;
its statement is preserved. The parent node records the direct construction and square.

## Status

landed 20261015T052200-L-1265930 2026-10-15 (merge of deliver/G2/Sheaf.AlgebraicGeometry.QCohOrdinaryTensorResolutionCoordinatesFamily)
