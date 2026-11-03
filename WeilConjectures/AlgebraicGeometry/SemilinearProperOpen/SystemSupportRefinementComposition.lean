/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SystemSupportRefinement
import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SystemDirectImageLeftUnit
/-! # Composition of whole-system compact-support refinements

Source: Stacks Tags 0F7C and 07A7; latest blueprint,
`sk-prop-sf-comp-coherence`, composition of refinement comparisons.
(blueprint: lem-pur-system-support-refinement-composition). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.proofsInPublic true
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  HasDerivedCategory.ofHasKInjectiveResolutions _root_.instCategoryDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
attribute [local instance 2000] WeilConjectures.SemilinearSections.moduleAbelian derived
attribute [local irreducible] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] J R gamma sComp sId derived

end AlgebraicGeometry.ProEtale.SemilinearProperOpen

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen

private theorem map_id_comp_eq
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) {X : A} {Y : B}
    (f : F.obj X ⟶ Y) : f = F.map (𝟙 X) ≫ f :=
  ((congrArg (fun h ↦ h ≫ f) (F.map_id X)).trans (Category.id_comp f)).symm

private theorem map_comp_map_id
    {A B D : Type*} [Category A] [Category B] [Category D]
    (F : A ⥤ B) (J : B ⥤ D) {X : A} {Y : B} {Z : D}
    (f : Y ⟶ F.obj X) (g : J.obj (F.obj X) ⟶ Z) :
    J.map (f ≫ F.map (𝟙 X)) ≫ g = J.map f ≫ g := by
  rw [F.map_id, Category.comp_id]

private theorem normalized_pasting
    {A B D S : Type*} [Category A] [Category B] [Category D] [Category S]
    (F : A ⥤ A) (Jj : A ⥤ B) (Ji : A ⥤ D) (Ja : A ⥤ S)
    (P : B ⥤ D) (Q : D ⥤ S) (T : B ⥤ S) (e : F ≅ 𝟭 A)
    (a₁ : F ⋙ Ji ⟶ Jj ⋙ P) (a₂ : F ⋙ Ja ⟶ Ji ⋙ Q)
    (a₁₂ : F ⋙ Ja ⟶ Jj ⋙ T) (c : P ⋙ Q ≅ T) (M : A)
    (hv : Ja.map (F.map (e.hom.app M)) ≫ a₁₂.app M ≫ c.inv.app (Jj.obj M) =
      a₂.app (F.obj M) ≫ Q.map (a₁.app M)) :
    Ja.map (e.inv.app M) ≫ a₁₂.app M =
      (Ja.map (e.inv.app M) ≫ a₂.app M) ≫
        Q.map (Ji.map (e.inv.app M) ≫ a₁.app M) ≫ c.hom.app (Jj.obj M) := by
  have hn := a₂.naturality (e.inv.app M)
  dsimp only [Functor.comp_map] at hn
  symm
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn, ← reassoc_of% hv]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Category.comp_id]
  exact map_comp_map_id F Ja (e.inv.app M) (a₁₂.app M)

private theorem source_transport_of_heq
    {A B D : Type*} [Category A] [Category B] [Category D]
    (J : B ⥤ D) (H : A ⥤ D) {F F' : A ⥤ B} (h : F = F')
    (a : F ⋙ J ⟶ H) (a' : F' ⋙ J ⟶ H) (ha : HEq a a') (M : A) :
    a.app M = J.map ((eqToIso h).hom.app M) ≫ a'.app M := by
  subst F'
  cases ha
  exact map_id_comp_eq J (a.app M)

private theorem gamma_heq {X Z W : Scheme.{u}}
    (j : X ⟶ Z) (a : X ⟶ W) (p : Z ⟶ W) (r r' : X ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion a] [QuasiCompact j] [QuasiCompact a]
    [IsProper p] [IsProper r] [IsProper r']
    (hr : r = r') (hj : j ≫ p = r ≫ a) (hj' : j ≫ p = r' ≫ a) :
    HEq (gamma C τ j r p a hj) (gamma C τ j r' p a hj') := by
  cases hr
  exact HEq.rfl

/-- Equality transport of the proper map on the source of the mate. -/
private theorem gamma_source_transport {X Z W : Scheme.{u}}
    (j : X ⟶ Z) (a : X ⟶ W) (p : Z ⟶ W) (r r' : X ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion a] [QuasiCompact j] [QuasiCompact a]
    [IsProper p] [IsProper r] [IsProper r']
    (hr : r = r') (hj : j ≫ p = r ≫ a) (hj' : j ≫ p = r' ≫ a)
    (M : Derived C τ X) :
    (gamma C τ j r p a hj).app M =
      (J C τ a).map ((eqToIso (congrArg (R C τ) hr)).hom.app M) ≫
        (gamma C τ j r' p a hj').app M := by
  exact source_transport_of_heq (J C τ a) (J C τ j ⋙ R C τ p)
    (congrArg (R C τ) hr) (gamma C τ j r p a hj) (gamma C τ j r' p a hj')
    (gamma_heq C τ j a p r r' hr hj hj') M

/-- Remove the two identity direct-image factors from the vertical mate equation. -/
private theorem normalized_gamma_comp {X Z W V : Scheme.{u}}
    (j : X ⟶ Z) (i : X ⟶ W) (a : X ⟶ V) (p : Z ⟶ W) (q : W ⟶ V)
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion a]
    [QuasiCompact j] [QuasiCompact i] [QuasiCompact a] [IsProper p] [IsProper q]
    (hj : j ≫ p = (𝟙 X) ≫ i) (hi : i ≫ q = (𝟙 X) ≫ a)
    (ha : j ≫ (p ≫ q) = (𝟙 X) ≫ a) (M : Derived C τ X) :
    (J C τ a).map ((sId C τ X).inv.app M) ≫
        (gamma C τ j (𝟙 X) (p ≫ q) a ha).app M =
      ((J C τ a).map ((sId C τ X).inv.app M) ≫
        (gamma C τ i (𝟙 X) q a hi).app M) ≫
      (R C τ q).map ((J C τ i).map ((sId C τ X).inv.app M) ≫
        (gamma C τ j (𝟙 X) p i hj).app M) ≫
      (sComp C τ p q).hom.app ((J C τ j).obj M) := by
  have hv := (semilinearProperOpenMatePasting C τ).1 j i a
    (𝟙 X) (𝟙 X) p q hj hi (by simpa only [Category.id_comp] using ha) M
  have hu := sComp_left_unit C τ (𝟙 X) M
  rw [gamma_source_transport C τ j a (p ≫ q) _ _ (Category.id_comp _) _ ha M] at hv
  simp only [Category.assoc] at hv
  rw [← Functor.map_comp_assoc, hu] at hv
  exact normalized_pasting (R C τ (𝟙 X)) (J C τ j) (J C τ i) (J C τ a)
    (R C τ p) (R C τ q) (R C τ (p ≫ q)) (sId C τ X)
    (gamma C τ j (𝟙 X) p i hj) (gamma C τ i (𝟙 X) q a hi)
    (gamma C τ j (𝟙 X) (p ≫ q) a ha) (sComp C τ p q) M hv

/-- Composition of the specified system refinement, before evaluation or total limit.
Source: Stacks Tags 0F7C and 07A7; the refinement cocycle in the current blueprint.
(blueprint: lem-pur-system-support-refinement-composition).
Proof: replace each refinement by its canonical normalized mate paste. Vertical mate
pasting, naturality at the inverse identity comparison, and the direct-image left
unit give composition of the normalized open mates. Naturality of the proper-image
compositor moves the first mate through the second compositor. Associativity of the
proper-image compositors then gives the outer paste, including equality transport
along the two triangles. No evaluation functor is used. The calculation allows empty
opens and arbitrary unbounded derived system objects. -/
theorem supportRefinement_comp_app {X Y Z W V : Scheme.{u}}
    (j : X ⟶ Z) (g : Z ⟶ Y) (i : X ⟶ W) (h : W ⟶ Y)
    (a : X ⟶ V) (t : V ⟶ Y) (p : Z ⟶ W) (q : W ⟶ V)
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion a]
    [QuasiCompact j] [QuasiCompact i] [QuasiCompact a] [IsProper p] [IsProper q]
    (hj : j ≫ p = (𝟙 X) ≫ i) (hi : i ≫ q = (𝟙 X) ≫ a)
    (ha : j ≫ (p ≫ q) = (𝟙 X) ≫ a)
    (hp : p ≫ h = g) (hq : q ≫ t = h)
    (hpq : (p ≫ q) ≫ t = g) (M : Derived C τ X) :
    (supportRefinement C τ j g a t (p ≫ q) ha (congrArg (R C τ) hpq)).app M =
      (supportRefinement C τ i h a t q hi (congrArg (R C τ) hq)).app M ≫
      (supportRefinement C τ j g i h p hj (congrArg (R C τ) hp)).app M := by
  subst g
  subst h
  rw [supportRefinement_eq_canonical, supportRefinement_eq_canonical,
    supportRefinement_eq_canonical]
  delta canonicalSupportRefinement
  simp only [normalizedSupportPaste_app, Iso.trans_hom, NatTrans.comp_app,
    eqToIso_refl, Iso.refl_hom, Category.comp_id]
  have hn := (sComp C τ q t).hom.naturality
    ((J C τ i).map ((sId C τ X).inv.app M) ≫
      (gamma C τ j (𝟙 X) p i hj).app M)
  dsimp only [Functor.comp_map] at hn
  have hc := (compositor_associativity C τ).2.1 p q t ((J C τ j).obj M)
  have hc' := congrArg (fun z ↦ z ≫
    (eqToIso (congrArg (R C τ) (Category.assoc p q t))).hom.app ((J C τ j).obj M)) hc
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at hc'
  rw [normalized_gamma_comp C τ j i a p q hj hi ha M]
  simp only [Functor.map_comp, Category.assoc]
  rw [hc']
  simp only [Functor.map_comp, Category.assoc] at hn
  rw [reassoc_of% hn]

end AlgebraicGeometry.ProEtale.SemilinearProperOpen
