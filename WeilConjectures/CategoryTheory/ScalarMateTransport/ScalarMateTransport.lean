/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Transport of canonical scalar mates through uniqueness of adjoints

The explicit composite avoids repeatedly expanding the inverse mates construction
when derived coefficient categories are specialized.
(blueprint: lem-sf-scalar-mate-adjoint-transport).
-/

@[expose] public section
set_option autoImplicit false
namespace CategoryTheory.ScalarMateTransport

universe u₀ u₁ v₀ v₁
/-- The natural transformation underlying Mathlib's inverse mates correspondence.
This wrapper keeps category data abstract when specializing the mate.
Source: Mathlib `CategoryTheory.Adjunction.Mates`, `mateEquiv`.
(blueprint: lem-sf-scalar-mate-adjoint-transport). -/
noncomputable def scalarMate
    {C₀ : Type u₀} {C₁ : Type u₁} {D₀ : Type v₀} {D₁ : Type v₁}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    {QX : C₀ ⥤ C₁} {RX : C₁ ⥤ C₀} {QY : D₀ ⥤ D₁} {RY : D₁ ⥤ D₀}
    (ax : QX ⊣ RX) (ay : QY ⊣ RY)
    (F : C₀ ⥤ D₀) (G : C₁ ⥤ D₁) (σ : RX ⋙ F ⟶ G ⋙ RY) :
    F ⋙ QY ⟶ QX ⋙ G :=
  ((mateEquiv ax ay).symm (TwoSquare.mk _ _ _ _ σ)).natTrans

private theorem mate_change_leftAdjoint
    {C₀ : Type u₀} {C₁ : Type u₁} {D₀ : Type v₀} {D₁ : Type v₁}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    {QX PX : C₀ ⥤ C₁} {RX : C₁ ⥤ C₀}
    {QY PY : D₀ ⥤ D₁} {RY : D₁ ⥤ D₀}
    (ax : QX ⊣ RX) (bx : PX ⊣ RX) (ay : QY ⊣ RY) (by' : PY ⊣ RY)
    (F : C₀ ⥤ D₀) (G : C₁ ⥤ D₁) (σ : RX ⋙ F ⟶ G ⋙ RY) (K : C₀) :
    (ay.homEquiv _ _).symm (F.map (ax.unit.app K) ≫ σ.app (QX.obj K)) =
      (Adjunction.leftAdjointUniq ay by').hom.app (F.obj K) ≫
        (by'.homEquiv _ _).symm (F.map (bx.unit.app K) ≫ σ.app (PX.obj K)) ≫
        G.map ((Adjunction.leftAdjointUniq ax bx).inv.app K) := by
  let ex := Adjunction.leftAdjointUniq ax bx
  apply (ay.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.id_obj, Functor.comp_obj]
  rw [← Category.assoc, ← Category.assoc,
    Adjunction.unit_leftAdjointUniq_hom_app ay by']
  rw [← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]
  have hn := σ.naturality (ex.inv.app K)
  change F.map (RX.map (ex.inv.app K)) ≫ σ.app (QX.obj K) =
    σ.app (PX.obj K) ≫ RY.map (G.map (ex.inv.app K)) at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← F.map_comp]
  have hu : bx.unit.app K ≫ RX.map (ex.inv.app K) = ax.unit.app K := by
    simpa only [ex, Adjunction.leftAdjointUniq_inv_app] using
      Adjunction.unit_leftAdjointUniq_hom_app bx ax K
  rw [hu]

private theorem mate_app
    {C₀ : Type u₀} {C₁ : Type u₁} {D₀ : Type v₀} {D₁ : Type v₁}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    {QX : C₀ ⥤ C₁} {RX : C₁ ⥤ C₀} {QY : D₀ ⥤ D₁} {RY : D₁ ⥤ D₀}
    (ax : QX ⊣ RX) (ay : QY ⊣ RY)
    (F : C₀ ⥤ D₀) (G : C₁ ⥤ D₁) (σ : RX ⋙ F ⟶ G ⋙ RY) (K : C₀) :
    (((mateEquiv ax ay).symm (TwoSquare.mk _ _ _ _ σ)).natTrans).app K =
      (ay.homEquiv _ _).symm (F.map (ax.unit.app K) ≫ σ.app (QX.obj K)) := by
  apply (ay.homEquiv _ _).injective
  change (ay.homEquiv (F.obj K) (G.obj (QX.obj K))) _ =
    (ay.homEquiv (F.obj K) (G.obj (QX.obj K)))
      ((ay.homEquiv (F.obj K) (G.obj (QX.obj K))).symm _)
  rw [Equiv.apply_symm_apply]
  exact (unit_mateEquiv_symm ax ay (TwoSquare.mk _ _ _ _ σ) K).symm

private theorem mate_isIso
    {C₀ : Type u₀} {C₁ : Type u₁} {D₀ : Type v₀} {D₁ : Type v₁}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    {QX : C₀ ⥤ C₁} {RX : C₁ ⥤ C₀} {QY : D₀ ⥤ D₁} {RY : D₁ ⥤ D₀}
    (ax : QX ⊣ RX) (ay : QY ⊣ RY)
    (F : C₀ ⥤ D₀) (G : C₁ ⥤ D₁) (σ : RX ⋙ F ⟶ G ⋙ RY) (K : C₀)
    (hi : IsIso ((ay.homEquiv _ _).symm
      (F.map (ax.unit.app K) ≫ σ.app (QX.obj K)))) :
    IsIso ((scalarMate ax ay F G σ).app K) := by
  rw [scalarMate, mate_app]
  exact hi

/-- Transport a scalar mate between two choices of left adjoints after specified
identifications of their right adjoints. The outside factors are the uniqueness
isomorphisms for left adjoints, so the construction fixes the canonical mate.
Source: Mathlib `Adjunction.leftAdjointUniq` and `unit_leftAdjointUniq_hom_app`.
(blueprint: lem-sf-scalar-mate-adjoint-transport). -/
noncomputable def transport
    {C₀ : Type u₀} {C₁ : Type u₁} {D₀ : Type v₀} {D₁ : Type v₁}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    {QX PX : C₀ ⥤ C₁} {RX RX' : C₁ ⥤ C₀}
    {QY PY : D₀ ⥤ D₁} {RY RY' : D₁ ⥤ D₀}
    (ax : QX ⊣ RX) (bx : PX ⊣ RX') (ay : QY ⊣ RY) (by' : PY ⊣ RY')
    (hx : RX = RX') (hy : RY = RY')
    (F : C₀ ⥤ D₀) (G : C₁ ⥤ D₁) (σ : RX' ⋙ F ⟶ G ⋙ RY') :
    F ⋙ QY ⟶ QX ⋙ G :=
  (Functor.isoWhiskerLeft F (Adjunction.leftAdjointUniq (hy ▸ ay) by')).hom ≫
    scalarMate bx by' F G σ ≫
    (Functor.isoWhiskerRight (Adjunction.leftAdjointUniq (hx ▸ ax) bx).symm G).hom

/-- Transport preserves invertibility of a component of the specified scalar mate.
Source: uniqueness of adjoints and Mathlib's mates correspondence.
(blueprint: lem-sf-scalar-mate-adjoint-transport).

Proof: the component is the canonical scalar mate between two components of natural
isomorphisms. Whiskering an isomorphism is an isomorphism, and their composite with
the assumed invertible scalar mate is invertible. -/
theorem isIso_transport
    {C₀ : Type u₀} {C₁ : Type u₁} {D₀ : Type v₀} {D₁ : Type v₁}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    {QX PX : C₀ ⥤ C₁} {RX RX' : C₁ ⥤ C₀}
    {QY PY : D₀ ⥤ D₁} {RY RY' : D₁ ⥤ D₀}
    (ax : QX ⊣ RX) (bx : PX ⊣ RX') (ay : QY ⊣ RY) (by' : PY ⊣ RY')
    (hx : RX = RX') (hy : RY = RY')
    (F : C₀ ⥤ D₀) (G : C₁ ⥤ D₁) (σ : RX' ⋙ F ⟶ G ⋙ RY') (K : C₀)
    (hi : IsIso ((by'.homEquiv _ _).symm (F.map (bx.unit.app K) ≫ σ.app (PX.obj K)))) :
    IsIso ((transport ax bx ay by' hx hy F G σ).app K) := by
  have := mate_isIso bx by' F G σ K hi
  dsimp only [transport, NatTrans.comp_app]
  infer_instance

/-- The transported map together with its componentwise invertibility criterion.
Keeping these together lets specializations reuse exactly the same category data.
Source: the preceding transport construction and invertibility proof.
(blueprint: lem-sf-scalar-mate-adjoint-transport). -/
noncomputable def certifiedTransport
    {C₀ : Type u₀} {C₁ : Type u₁} {D₀ : Type v₀} {D₁ : Type v₁}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    {QX PX : C₀ ⥤ C₁} {RX RX' : C₁ ⥤ C₀}
    {QY PY : D₀ ⥤ D₁} {RY RY' : D₁ ⥤ D₀}
    (ax : QX ⊣ RX) (bx : PX ⊣ RX') (ay : QY ⊣ RY) (by' : PY ⊣ RY')
    (hx : RX = RX') (hy : RY = RY')
    (F : C₀ ⥤ D₀) (G : C₁ ⥤ D₁) (σ : RX' ⋙ F ⟶ G ⋙ RY') :
    {t : F ⋙ QY ⟶ QX ⋙ G // ∀ K : C₀,
      IsIso ((by'.homEquiv _ _).symm
        (F.map (bx.unit.app K) ≫ σ.app (PX.obj K))) → IsIso (t.app K)} :=
  ⟨transport ax bx ay by' hx hy F G σ,
    isIso_transport ax bx ay by' hx hy F G σ⟩

/-- The transported map is exactly the inverse mate of the identified restriction
square, including its specified units and counits.
Source: Mathlib `unit_mateEquiv_symm`, `unit_leftAdjointUniq_hom_app`.
(blueprint: lem-sf-scalar-mate-adjoint-transport).

Proof: eliminate the two right-adjoint equalities. The normalization square becomes
the given square. Apply the target adjunction's Hom equivalence to the proposed
identity. The unit equation for uniqueness of left adjoints removes the target
uniqueness factor. Naturality of the square moves the source uniqueness factor
past the square, and the source unit equation removes it. Injectivity of the Hom
equivalence proves equality of components, hence of natural transformations. -/
theorem mate_eq_transport
    {C₀ : Type u₀} {C₁ : Type u₁} {D₀ : Type v₀} {D₁ : Type v₁}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    {QX PX : C₀ ⥤ C₁} {RX RX' : C₁ ⥤ C₀}
    {QY PY : D₀ ⥤ D₁} {RY RY' : D₁ ⥤ D₀}
    (ax : QX ⊣ RX) (bx : PX ⊣ RX') (ay : QY ⊣ RY) (by' : PY ⊣ RY')
    (hx : RX = RX') (hy : RY = RY')
    (F : C₀ ⥤ D₀) (G : C₁ ⥤ D₁) (σ : RX' ⋙ F ⟶ G ⋙ RY') :
    scalarMate ax ay F G
      ((Functor.isoWhiskerRight (eqToIso hx) F).hom ≫ σ ≫
        (Functor.isoWhiskerLeft G (eqToIso hy).symm).hom) =
      transport ax bx ay by' hx hy F G σ := by
  subst RX' RY'
  simp only [eqToIso_refl, Iso.refl_symm, Functor.isoWhiskerRight_refl,
    Functor.isoWhiskerLeft_refl, Iso.refl_hom, Category.id_comp, Category.comp_id]
  ext K
  rw [scalarMate, mate_app, mate_change_leftAdjoint ax bx ay by' F G σ K]
  change _ = (Adjunction.leftAdjointUniq ay by').hom.app (F.obj K) ≫
    (scalarMate bx by' F G σ).app K ≫
    G.map ((Adjunction.leftAdjointUniq ax bx).inv.app K)
  rw [scalarMate, mate_app]
  rfl

end CategoryTheory.ScalarMateTransport
