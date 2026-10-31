/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteProperProductMaps
import WeilConjectures.AlgebraicGeometry.FiniteProperCompositorMate

/-! # Transposition of the specified ordinary direct-image transport

Source: Stacks Tags 07A6 and 0D6E; step 6 of finite proper product transposition.
(blueprint: lem-pur-finite-proper-transport-transpose).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteProperProduct

private theorem conjugate_transpose
    {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {M : C} {N : D} (u : M ⟶ R₁.obj N) :
    (a₂.homEquiv M N).symm (u ≫ (conjugateEquiv a₁ a₂ α).app N) =
      α.app M ≫ (a₁.homEquiv M N).symm u := by
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [conjugateEquiv_counit, α.naturality_assoc]

private theorem unit_transpose
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : C ⥤ D} {R : D ⥤ C} {L' : D ⥤ E} {R' : E ⥤ D}
    (a : L ⊣ R) (b : L' ⊣ R') {M : C} {Q : D}
    (u : M ⟶ R.obj Q) :
    ((a.comp b).homEquiv M (L'.obj Q)).symm (u ≫ R.map (b.unit.app Q)) =
      L'.map ((a.homEquiv _ _).symm u) := by
  rw [Adjunction.comp_homEquiv]
  change (b.homEquiv _ _).symm ((a.homEquiv _ _).symm (u ≫ R.map _)) = _
  rw [Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_naturality_left_symm]
  simp only [Adjunction.homEquiv_counit, b.left_triangle_components, Category.comp_id]

private theorem transport_general
    {I : Type*} [Category* I] (D : I → Type*) [∀ X, Category (D X)]
    (L : ∀ {X Y : I}, (X ⟶ Y) → D Y ⥤ D X)
    (R : ∀ {X Y : I}, (X ⟶ Y) → D X ⥤ D Y)
    (adj : ∀ {X Y : I} (f : X ⟶ Y), L f ⊣ R f)
    (α : ∀ {X Y Z : I} (f : X ⟶ Y) (g : Y ⟶ Z), L (f ≫ g) ≅ L g ⋙ L f)
    (β : ∀ {X Y Z : I} (f : X ⟶ Y) (g : Y ⟶ Z), R f ⋙ R g ≅ R (f ≫ g))
    (mate : ∀ {X Y Z : I} (f : X ⟶ Y) (g : Y ⟶ Z),
      (β f g).hom = conjugateEquiv ((adj g).comp (adj f)) (adj (f ≫ g)) (α f g).hom)
    {B X X' : I} (s : X ⟶ X') (q : X' ⟶ B) (c : X ⟶ B) (hc : s ≫ q = c)
    {M : D B} {K' : D X'} {K : D X}
    (d : (L s).obj K' ⟶ K) (u : M ⟶ (R q).obj K') :
    ((adj c).homEquiv _ _).symm
      (u ≫ (R q).map ((adj s).unit.app K') ≫
        (β s q).hom.app ((L s).obj K') ≫
        (eqToIso (congrArg (fun f ↦ (R f).obj ((L s).obj K')) hc)).hom ≫
        (R c).map d) =
      (eqToIso (congrArg (fun f ↦ (L f).obj M) hc.symm)).hom ≫
        (α s q).hom.app M ≫ (L s).map (((adj q).homEquiv _ _).symm u) ≫ d := by
  subst c
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]
  rw [← Category.assoc, ← Category.assoc,
    Adjunction.homEquiv_naturality_right_symm]
  rw [mate]
  have h := conjugate_transpose ((adj q).comp (adj s)) (adj (s ≫ q))
    (α s q).hom (u ≫ (R q).map ((adj s).unit.app K'))
  rw [unit_transpose] at h
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ d) h

/-- The ordinary unit/compositor transport transposes to pullback followed by d.
Source: Stacks Tags 07A6 and 0D6E, step 6 of
lem-pur-finite-proper-product-transpose.
(blueprint: lem-pur-finite-proper-transport-transpose).

Proof: substitute the equality hc so the structure map is s followed by q.
Inverse-Hom naturality moves d outside the transpose. The compositor-mate identity
identifies the remaining transpose with the composite adjunction transpose after
the pullback compositor. The composite Hom bijection first transposes through q,
then s. Naturality moves the q-pushforward of the s-unit through the q-transpose.
The result is the pullback of the old q-transpose, then the pullback of the s-unit,
then the s-counit. The left triangle identity cancels the last two factors.
Reinsert the equality transports, giving exactly the displayed formula. This is
valid for any morphism s and any arrow d; neither is required to be invertible. -/
theorem finiteProperTransportTranspose (P : PurityFiniteSetting.{u})
    {B X X' : Scheme.{u}} (s : X ⟶ X') (q : X' ⟶ B) (c : X ⟶ B)
    (hc : s ≫ q = c) {M : D P B} {K' : D P X'} {K : D P X}
    (d : (pull P s).obj K' ⟶ K) (u : M ⟶ (push P q).obj K') :
    ((adj P c).homEquiv _ _).symm
      (u ≫ (push P q).map ((adj P s).unit.app K') ≫
        (kappa P s q).inv.app ((pull P s).obj K') ≫
        (eqToIso (congrArg (fun f ↦ (push P f).obj ((pull P s).obj K')) hc)).hom ≫
        (push P c).map d) =
      (eqToIso (congrArg (fun f ↦ (pull P f).obj M) hc.symm)).hom ≫
        (comp P s q).hom.app M ≫
        (pull P s).map (((adj P q).homEquiv _ _).symm u) ≫ d := by
  exact transport_general (D P) (fun f ↦ pull P f) (fun f ↦ push P f)
    (fun f ↦ adj P f) (fun f g ↦ comp P f g) (fun f g ↦ (kappa P f g).symm)
    (fun f g ↦ finiteProperCompositorMate P f g) s q c hc d u

end WeilConjectures.FiniteProperProduct
