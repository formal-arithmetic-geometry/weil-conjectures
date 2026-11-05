# Relative exceptional base change

Status: proof drafted; remote validation is running at snapshot `cacdd5c338` in
`/home/ubuntu/u9/logs/K4c-20261106T010205.log`. The generic adjunction helper has passed.
The concrete chain and transitive axiom audit have not yet completed.

The target is
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_smoothUnitBaseChange_geometricFiberLowerShriekBaseChangeRelative`.
It quantifies over any morphism `f : X ⟶ Y` of separated finite-type schemes over a finite
field. It does not require `Y` to be a point, or `f` to be smooth or proper. Its exchange is
specified by the open and proper factors of `compactificationOverField f`.

The proper input exported for the actual descended-trace route is
`purity_isIso_upperShriekBaseChangeOfMap_unit_geometricFiber`. Its conclusion is invertibility
of the library's `upperShriekBaseChangeOfMap` at the unit for an arbitrary proper `f : X ⟶ Y`.
The new construction introduces no extra base-change hypothesis.

## Proof

1. The exceptional projection formula identifies the left adjoints of
   `f^! RHom(K, -)` and `RHom(f^* K, f^! -)`. Right-adjoint uniqueness gives their isomorphism.
2. Absolute Verdier biduality at the unit gives `1 ≅ RHom(omega_Y, omega_Y)`. Thus
   `f^! 1 ≅ RHom(f^* omega_Y, omega_X)`, including for singular `Y`.
3. PR #2144's point theorem transports the absolute dualizing objects of both `X` and `Y`.
   Weakly étale pullback commutes with internal Hom, so the relative exceptional units on
   the two sides of the field extension are isomorphic.
4. For proper `f`, relative Verdier duality proves that the proper pushforward of the
   specified base-change map is invertible. The library's endomorphism criterion, supplied
   with the isomorphism from step 3, proves that this specified map itself is invertible.
5. Paste that proper comparison with the invertible mate of the specified open exchange,
   and transport along the chosen compactification's factorization equalities.

The isomorphism built in step 3 need not equal the specified base-change map. Step 4 proves
invertibility of the specified map by the existing proper criterion; it does not assert
that an arbitrary isomorphism is the desired comparison. The remaining trace-identification
and Tate-encoding consumer work belongs to K4/C9 and is not claimed by this report.

## Existing inputs

- `isIso_verdierBiduality`: `PoincareDuality/Biduality/Constructible.lean`.
- `isIso_nearbyDualityMap_upperStarOfMap_id_of_weaklyEtale`:
  `SixFunctors/ProEtale/ModuleObject/DualizingFieldChange/SmoothProjection.lean`.
- `isIso_lowerStar_map_upperShriekBaseChangeOfMap_app` and
  `isIso_upperShriekBaseChangeOfMap_app_of_iso`: the same file.
- `isIso_smoothUnitBaseChange_geometricFiberLowerShriekBaseChangePoint`: adopted PR #2144.
- `isIso_smoothUnitBaseChange_paste`: the existing abstract pasting theorem.

Six new files under `WeilConjectures/WeilSheaf` contain the proof and audit:
`SmoothPurityRelativeDualityIso`, `SmoothPurityRelativeUnitDual`,
`SmoothPurityPointDualizingIso`, `SmoothPurityRelativeUnitIso`,
`SmoothPurityUnitBaseChangeRelative`, and `SmoothPurityK4cRelativeAudit`.
