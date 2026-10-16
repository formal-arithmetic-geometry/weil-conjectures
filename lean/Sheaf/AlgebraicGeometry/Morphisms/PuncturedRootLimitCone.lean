/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Auxiliary limit statements for punctured root charts
Source: Stacks Project, Tags 0BSK, 05N9 and 01YW. -/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The pointed etale neighbourhoods give a ring-colimit presentation over the base.

Source: Stacks Project, Tag 0BSK; canonical structural map, Tag 03Q9.
(blueprint: lem-sbc-pointed-etale-ring-colimit)

Proof: Take the small representative category of affine pointed etale neighbourhoods.
Its opposite-indexed global-section diagram is strictHenselizationDiagram barY, and its
canonical colimit is strictHenselizationRing barY. Cofilteredness follows from
strictHenselization_properties. The structure maps from R are obtained by applying global
sections to the neighbourhood structure morphisms and using GammaSpecIso. Their naturality
follows from the over-category equations. The colimit legs composed with these maps equal b:
apply Spec, use exists_strictHenselizationStructuralMap and hb, and use faithfulness of Spec.
Each neighbourhood is etale by its AffineEtale structure. Its lift of barY supplies a point
above y: choose the zero prime of the field Omega, map it by the lift, and apply hy to the
over-category equality. Transfer these points through the affine-spectrum isomorphisms. -/
theorem pointed_etale_ring_colimit
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (y : Spec R) (hy : ∀ x : Spec (.of Ω), barY x = y)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    ∃ (I : Type u) (cat : Category.{u} I), letI := cat
      ∃ (_ : IsCofiltered I) (F : Iᵒᵖ ⥤ CommRingCat.{u}) (c : Cocone F)
        (a : (Functor.const Iᵒᵖ).obj R ⟶ F)
        (e : c.pt ≅ strictHenselizationRing barY),
        Nonempty (IsColimit c) ∧
        (∀ j, a.app j ≫ c.ι.app j ≫ e.hom = b) ∧
        ∀ j, Etale (Spec.map (a.app j)) ∧
          ∃ z : Spec (F.obj j), (Spec.map (a.app j)) z = y := by
  sorry

end AlgebraicGeometry.Scheme
