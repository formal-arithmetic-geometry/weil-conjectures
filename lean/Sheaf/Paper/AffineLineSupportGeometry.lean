/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q108
-/
module

public import Sheaf.Paper.PurityAffineLineDatum
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite-type and Noetherian geometry of the affine-line support pair

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
lem-pur-gysin-structure.proof.md, first paragraph; Stacks Tags 01T6, 01OW, 01OX
(blueprint: lem-pur-affine-line-support-geometry).

The line, zero section and coordinate basic open are the published affine-line datum.
No coefficient datum or separatedness assumption is needed for this geometric statement.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The affine line and its zero-section complement over a finite-type scheme over a field
are finite type over that field and Noetherian, and the complementary open immersion is
quasi-compact. Here `Punctured Y` is the coordinate basic open `D(t)`, which is precisely
`Line Y` minus the image of `zeroSection Y` by `AffineSpace.range_zeroSection` for the
singleton coordinate type. On an affine base its ring is the localization of `R[t]` at `t`.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
lem-pur-gysin-structure.proof.md, first paragraph; Stacks Tags 01T6, 01OW, 01OX
(blueprint: lem-pur-affine-line-support-geometry).

Proof plan:
1. The spectrum of the field is Noetherian. Apply
   lem-weil-pbc-finite-type-over-noetherian to the structure map of Y to obtain Noetherianity.
2. The affine charts of the line are Spec R[t], finitely generated over R by t. Thus its
   projection is finite type. Compose with the structure map of Y using
   lem-sfb-finite-type-composition-base-change to obtain finite type over the field.
3. The coordinate t is global (pulled back from the integral affine-line model), and the
   image of the zero section is its vanishing locus. On every affine open Spec B of the
   line, the complement is D(t|_B), homeomorphic to Spec B_t by
   lem-weil-pbc-spec-localization-away-basic-open. That spectrum is quasi-compact by
   lem-weil-pbc-affine-scheme-qcqs. Therefore the complementary immersion is quasi-compact.
4. By lem-weil-pbc-qc-open-immersion-finite-type the complementary open immersion is finite
   type. Compose with the line's structure map using
   lem-sfb-finite-type-composition-base-change to obtain finite type for the punctured line.
5. Apply lem-weil-pbc-finite-type-over-noetherian to these two finite-type structure maps.
   Together with step 1, this gives Noetherianity of all three schemes. -/
theorem affineLine_support_geometry (k : Type u) [Field k] (Y : Scheme.{u})
    [Y.Over (Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] :
    (LocallyOfFiniteType (lineProjection Y ≫ Y ↘ Spec (.of k)) ∧
      QuasiCompact (lineProjection Y ≫ Y ↘ Spec (.of k))) ∧
    (LocallyOfFiniteType (puncturedProjection Y ≫ Y ↘ Spec (.of k)) ∧
      QuasiCompact (puncturedProjection Y ≫ Y ↘ Spec (.of k))) ∧
    IsNoetherian Y ∧ IsNoetherian (Line Y) ∧ IsNoetherian (Punctured Y) ∧
    QuasiCompact (openImmersion Y) := by
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian Y := ⟨⟩
  have : LocallyOfFiniteType (lineProjection Y) := by
    dsimp only [lineProjection]
    infer_instance
  have : QuasiCompact (lineProjection Y) := by
    dsimp only [lineProjection]
    infer_instance
  have : IsLocallyNoetherian (Line Y) :=
    LocallyOfFiniteType.isLocallyNoetherian (lineProjection Y)
  have : CompactSpace (Line Y) :=
    QuasiCompact.compactSpace_of_compactSpace (lineProjection Y)
  have : IsNoetherian (Line Y) := ⟨⟩
  have : IsOpenImmersion (openImmersion Y) := by
    dsimp only [openImmersion]
    infer_instance
  have : QuasiCompact (openImmersion Y) := inferInstance
  have : LocallyOfFiniteType (puncturedProjection Y) := by
    dsimp only [puncturedProjection]
    infer_instance
  have : QuasiCompact (puncturedProjection Y) := by
    dsimp only [puncturedProjection]
    infer_instance
  have : IsLocallyNoetherian (Punctured Y) :=
    LocallyOfFiniteType.isLocallyNoetherian (puncturedProjection Y)
  have : CompactSpace (Punctured Y) :=
    QuasiCompact.compactSpace_of_compactSpace (puncturedProjection Y)
  have : IsNoetherian (Punctured Y) := ⟨⟩
  exact ⟨⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance⟩,
    inferInstance, inferInstance, inferInstance, inferInstance⟩

end WeilConjectures.PurityFiniteSetting
