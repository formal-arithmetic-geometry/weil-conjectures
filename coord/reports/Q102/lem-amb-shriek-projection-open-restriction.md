## Worker report

The module `lean/Sheaf/AlgebraicGeometry/CompactSupportProjectionOpenRestriction.lean` states the open-base specialization of the canonical compact-support projection/base-change square. The main declaration is `AlgebraicGeometry.Etale.compactSupportProjection_open_restriction`; the auxiliary declaration `compactSupportProjection_open_restriction_inverse` records the categorical cancellation step for inverse maps.

The main statement renders the node as follows. `A : Type (u + 1)` with `[CommRing A] [Finite A]` is the finite commutative coefficient ring. `X`, `S`, and `U` are Noetherian schemes. `f : X ⟶ S` is separated, locally of finite type, quasi-compact, and compactifiable through `[IsSeparated f]`, `[LocallyOfFiniteType f]`, `[QuasiCompact f]`, and `[HasCompactification f]`. `u : U ⟶ S` has `[IsOpenImmersion u]`. The pullback is the chosen categorical pullback `pullback f u`; its map to `U` is `pullback.snd f u`, with compactification and quasi-compactness assumptions. `K` is the base object in `D(X_et,A)` in the published projection-map convention, and `M` is the coefficient object in `D(S_et,A)`.

The displayed equality is the exact derived tensor-transport square from `projectionMap_rightDerivedLowerShriekBaseChangeMap`: the left side applies the derived pullback along `u` to the compactified projection map, then the normalized compact-support exchange, then the pullback tensor comparison and the inverse square identification; the right side first applies the pullback tensor comparison, then tensors the exchange map with the pulled-back coefficient, and finally applies the projection map for `pullback.snd f u`. The source convention has `Rf_! M ⊗ K`; the paper writes `K ⊗ Rf_! M`. The canonical braiding `β_` identifies these conventions, as documented on the declaration.

The inverse clause is represented by `compactSupportProjection_open_restriction_inverse`, the general categorical fact that an equality of isomorphisms remains an equality after taking inverses. It is the cancellation operation applied to the displayed square when both projection maps are isomorphisms.

Dependencies used by the statement are the recorded declarations:

- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories` / `AlgebraicGeometry.Etale.DerivedCategoryModule` and `DerivedCategory`.
- `prop-weil-pbc-inverse-image-modules-exact`: `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact` / `AlgebraicGeometry.etaleInverseImageModulesExact`.
- `def-kun-derived-tensor`: `WeilConjectures.SixFunctors.Etale.Derived.Tensor` / `AlgebraicGeometry.Etale.derivedTensor`.
- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme`.
- `def-amb-etale-compact-support`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek` / `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`.
- `lem-amb-unbounded-compact-support-comparisons`: `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons` / `AlgebraicGeometry.Etale.unboundedEtaleCompactSupport_baseChange`.
- `def-weil-scheme-morphism-properties`: the project convention record for scheme and morphism properties.
- `def-pc-fibre-product`: Mathlib `CategoryTheory.Limits.pullback` and its projections.
- `def-weil-open-immersion`: Mathlib `AlgebraicGeometry.IsOpenImmersion`.
- `def-kun-projection-formula-map`: `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection` / `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`.
- `lem-weil-pbc-ringed-slice-extension-tensor`: `Sheaf.CategoryTheory.RingedSliceExtensionTensor` / `SheafOfModules.ringedSlice_extension_tensor`.
- `def-kun-unbounded-exchange`: `Sheaf.AlgebraicGeometry.ExactUnboundedExchange` / `AlgebraicGeometry.Etale.exactDerivedBaseChangeMap`.
- `def-weil-pbc-etale-shriek-base-change-map`: `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap` / `AlgebraicGeometry.Etale.etaleLowerShriekBaseChangeMap`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` / `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
- `lem-pur-etale-open-derived-tensor`: `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection` / `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso`.

Edge cases checked: `u = 𝟙 S` (the exchange and tensor transports reduce to identity normalizations), `X = ∅`, `K = 0`, `M = 0`, the identity morphism `f`, and the case where the projection maps are isomorphisms (inverse cancellation). No boundedness, constructibility, finite Tor-amplitude, or invertibility assumption was added.

Searches made:

- `msearch.py ... leanfinder "ordinary etale compact support projection formula commutes with restriction to an open base"`: only generic scheme restriction and presheaf hits; no compact-support projection statement.
- `msearch.py ... loogle "projectionMap rightDerivedLowerShriekBaseChangeMap"`: no direct Loogle hit (the names are project declarations rather than Mathlib names).
- `msearch.py ... grep "compactSupport|projectionMap|baseChange" CategoryTheory`: generic categorical base-change results only.
- `rg -n "projectionMap|unboundedEtaleCompactSupport|compactSupport"` in the source and group Lean trees: found `projectionMap_rightDerivedLowerShriekBaseChangeMap` and `unboundedEtaleCompactSupport_baseChange`; no existing declaration with this open-restriction item.

## Second reading by Q102

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix

The independent maintainer review replaced the module by a corrected version with the same
main statement. (1) `compactSupportProjection_open_restriction_inverse` stated only
`inv (eqToHom h) = eqToHom h.symm` in an arbitrary category, which is not the node's inverse
clause; it now states, under `IsIso` of the two projection maps, that
`Ex_! ≫ transports ≫ P_{f_U}⁻¹ = Lu^*(P_f⁻¹) ≫ tensor comparison ≫ (Ex_! ⊗ 1)`, i.e.
`P_{f_U}⁻¹ ∘ C = (1 ⊗ C) ∘ u^*P_f⁻¹` after the canonical identifications. (2) The module
docstring was missing and the declaration docstrings lacked the source places and the node's
proof steps (H8); they were added. The main declaration's signature is unchanged.
