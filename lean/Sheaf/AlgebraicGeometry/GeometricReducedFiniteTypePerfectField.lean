/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.FieldTheory.Perfect

import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Geometric reducedness over a perfect field

Source: blueprint node `lem-kun-geometric-reduced-perfect` in
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/`.
(blueprint: lem-kun-geometric-reduced-perfect)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A reduced finite type scheme over a perfect field remains reduced after every field
extension; its structure morphism is flat and of finite presentation with geometrically
reduced fibres.

Source: Stacks Project, Tag 01J1, and Tag 00I4 for the perfect-field tensor argument
(blueprint: lem-kun-geometric-reduced-perfect).

Proof, following the eight steps of the node:
1. By `def-weil-finite-type-morphism`, choose a finite affine cover `Spec A_i` of `X`.
   The rings `A_i` are reduced by `def-pc-reduced-scheme` (Stacks 01J1). The cover may be empty.
2. For an arbitrary field extension `L/K`, both `A_i` and `L` are reduced. Apply
   `lem-weil-pbc-perfect-reduced-tensor` (Stacks 00I4), namely
   `isReduced_tensorProduct_of_perfectField`, to obtain reducedness of `A_i ⊗[K] L`.
3. By `lem-weil-pbc-open-fibre-product` and `lem-weil-pbc-fibre-product-affine-spectra`,
   the inverse images of the affine charts cover `X_L` and are `Spec (A_i ⊗[K] L)`.
   They are reduced by `lem-weil-pbc-affine-scheme-reduced-iff` (Stacks 01J2).
4. A nilpotent section on any open of `X_L` restricts to zero on these charts, hence is
   zero by sheaf uniqueness. The section-wise criterion gives reducedness of `X_L`.
   This is the reducedness clause of `def-pc-geometrically-irreducible`. The unique
   point of `Spec K` has residue field canonically `K`; its fibre is isomorphic over `K`
   to `X` by the universal property of `def-pc-fibre-product` and `def-pc-scheme-fibre`.
   Base-changing this isomorphism identifies its field-extension fibres with `X_L`,
   giving geometrically reduced fibres.
5. Apply `lem-pc-flat-field`: every morphism to the spectrum of a field is flat.
6. A field is Noetherian, since its only ideals are zero and the whole ring. Apply
   `lem-weil-pbc-finite-type-noetherian-finite-presentation` (Stacks 00FP(3)) on the charts
   to get local finite presentation as in `def-sbc-locally-finite-presentation`.
7. The one affine chart of `Spec K` is Noetherian. By `pqf-def-locnoeth` and
   `lem-weil-pbc-finite-type-over-noetherian`, `X` is Noetherian, hence locally Noetherian.
   Apply `lem-weil-pbc-locally-noetherian-quasi-separated` and then clause (1) of
   `lem-weil-pbc-qcqs-morphism-permanence` to obtain quasi-separatedness of the morphism.
8. Finite type already includes quasi-compactness. Together with steps 6 and 7 this is
   finite presentation in `def-sbc-locally-finite-presentation` (Stacks 01TP). Combine
   this with steps 4 and 5 to obtain all the conclusions.
-/
theorem geometricallyReduced_finiteType_of_perfectField
    (K : Type u) [Field K] [PerfectField K] (X : Scheme.{u})
    [X.Over (Spec (.of K))] [IsReduced X]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))] :
    (∀ (L : Type u) [Field L] [Algebra K L],
      IsReduced (pullback (X ↘ Spec (.of K))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))))) ∧
      Flat (X ↘ Spec (.of K)) ∧
      LocallyOfFinitePresentation (X ↘ Spec (.of K)) ∧
      QuasiCompact (X ↘ Spec (.of K)) ∧
      QuasiSeparated (X ↘ Spec (.of K)) ∧
      GeometricallyReduced (X ↘ Spec (.of K)) := by
  let : GeometricallyReduced (X ↘ Spec (.of K)) :=
    GeometricallyReduced.of_perfectField (X ↘ Spec (.of K))
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  refine ⟨?_, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
  intro L _ _
  exact pullback_of_geometrically
    (GeometricallyReduced.geometrically_isReduced (f := X ↘ Spec (.of K))) L
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))

end AlgebraicGeometry
