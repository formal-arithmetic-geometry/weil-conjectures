/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraColimit
import Sheaf.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections
import Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections

/-! # Affine pushforward and tensor modules commute with directed limits

Source: Stacks Project, Limits, Tags 01Z0 and 01YX
(blueprint: lem-sc-valuation-limit-affine-pushforward-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

set_option hygiene false in
local notation "𝒪⁎" f:max => Under.mk (⟨(f).c⟩ : Scheme.sheaf _ ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} (f).base).obj (Scheme.sheaf _))

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The algebra colimit describes the relative spectrum of the limit, the affine projection
formula is canonical, and tensoring its underlying cocone with a fixed module is a colimit.
All algebra and module diagram maps are specified on sections, including the colimit legs.
Source: Stacks Project, Limits, Tags 01Z0 and 01YX
(blueprint: lem-sc-valuation-limit-affine-pushforward-colimit).

Proof: (1) Restrict to the cofinal tail above `i₀`. On an affine open of the base, the
inverse images are affine (lem-weil-pbc-limit-affine-transition). Their section rings have
colimit the sections of the algebra colimit (lem-weil-pbc-quasi-coherent-algebra-colimit).
Spec converts this colimit into a limit (lem-weil-pbc-spec-colimit-limit). Glue these charts
using lem-weil-pbc-affine-morphism-relative-spec, identifying the pushforward algebra.
(2) The canonical affine pullback comparison sends `s ⊗ a` to `a • η(s)`
(lem-weil-pbc-module-pullback-affine-sections). The tensor section comparison
(lem-weil-pbc-quasi-coherent-tensor-product-affine-sections) identifies its source with the
sections of the sheaf tensor. Glue on the affine basis. Naturality gives compatibility with
the transition maps and the limit legs.
(3) The module colimit is quasi-coherent and has the expected affine sections
(lem-weil-pbc-quasi-coherent-module-colimit-affine-sections). Tensoring those sections
commutes with the directed ring colimit (lem-weil-pbc-tensor-commutes-with-colimits).
The comparison is therefore bijective on the affine basis, hence an isomorphism.
(4) Substitute the projection-formula isomorphisms into this tensor colimit. -/
theorem affine_pushforward_colimit
    (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] (i₀ : I)
    (D : Iᵒᵖ ⥤ Scheme.{u}) (s : Cone D) (hs : IsLimit s)
    [∀ i : I, CompactSpace (D.obj (op i))]
    [∀ i : I, QuasiSeparatedSpace (D.obj (op i))]
    (haff : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f.op))
    (gᵢ : ∀ i : {i : I // i₀ ≤ i}, D.obj (op i.val) ⟶ D.obj (op i₀))
    (hgᵢ : ∀ i, gᵢ i = D.map (homOfLE i.property).op)
    (F : (D.obj (op i₀)).Modules) [F.IsQuasicoherent]
    (A : {i : I // i₀ ≤ i} ⥤ (D.obj (op i₀)).CommAlgebraSheaf)
    (hA : ∀ i, A.obj i = 𝒪⁎ (gᵢ i))
    (hAm : ∀ {i j : {i : I // i₀ ≤ i}} (f : i ⟶ j) (U : (D.obj (op i₀)).Opens),
      (A.map f).right.hom.app (op U) =
        eqToHom (by rw [hA i]; rfl) ≫
          (D.map (homOfLE (x := i.val) (y := j.val) (leOfHom f)).op).appLE
            ((gᵢ i) ⁻¹ᵁ U) ((gᵢ j) ⁻¹ᵁ U)
            (by rw [hgᵢ i, hgᵢ j, ← Scheme.Hom.comp_preimage, ← D.map_comp]; rfl) ≫
          eqToHom (by rw [hA j]; rfl))
    (c : Cocone A) (hc : IsColimit c)
    (B : {i : I // i₀ ≤ i} ⥤ (D.obj (op i₀)).Modules)
    (hB : ∀ i, B.obj i = (A.obj i).toModule)
    (hBm : ∀ {i j : {i : I // i₀ ≤ i}} (f : i ⟶ j) (U : (D.obj (op i₀)).Opens)
        (a : (A.obj i).right.obj.obj (op U)),
      ((eqToHom (hB i).symm ≫ B.map f ≫ eqToHom (hB j)).val.app (op U)) a =
        (A.map f).right.hom.app (op U) a)
    (b : Cocone B) (hbp : b.pt = c.pt.toModule)
    (hbm : ∀ (i) (U : (D.obj (op i₀)).Opens)
        (a : (A.obj i).right.obj.obj (op U)),
      ((eqToHom (hB i).symm ≫ b.ι.app i ≫ eqToHom hbp).val.app (op U)) a =
        (c.ι.app i).right.hom.app (op U) a) :
    c.pt.toModule.IsQuasicoherent ∧
    (∀ i, (A.obj i).toModule.IsQuasicoherent) ∧
    IsAffineHom (s.π.app (op i₀)) ∧
    ∃ α : c.pt ≅ 𝒪⁎ (s.π.app (op i₀)),
      (∀ (i) (U : (D.obj (op i₀)).Opens),
        (c.ι.app i ≫ α.hom).right.hom.app (op U) =
          eqToHom (by rw [hA i]; rfl) ≫
            (s.π.app (op i.val)).appLE ((gᵢ i) ⁻¹ᵁ U)
              ((s.π.app (op i₀)) ⁻¹ᵁ U)
              (by rw [hgᵢ i, ← Scheme.Hom.comp_preimage,
                s.w (homOfLE i.property).op])) ∧
      (∀ (U : (D.obj (op i₀)).Opens), IsAffineOpen U →
        IsIso (((s.π.app (op i₀)) ⁻¹ᵁ U).toSpecΓ ≫
          Spec.map (α.hom.right.hom.app (op U)))) ∧
      ∃ (eᵢ : ∀ i, F ⊗ (A.obj i).toModule ≅
          (pushforward (gᵢ i)).obj ((tensorPullback (gᵢ i)).obj F))
        (e : F ⊗ c.pt.toModule ≅
          (pushforward (s.π.app (op i₀))).obj
            ((tensorPullback (s.π.app (op i₀))).obj F)),
        (∀ (i) (U : (D.obj (op i₀)).Opens) (t : Γ(F, U))
            (a : (A.obj i).right.obj.obj (op U)),
          (eᵢ i).hom.app U (tmulSection t a) =
            ((eqToHom (by rw [hA i]; rfl : (A.obj i).right.obj.obj (op U) =
              Γ(D.obj (op i.val), (gᵢ i) ⁻¹ᵁ U))) a) •
              (@id Γ((tensorPullback (gᵢ i)).obj F, (gᵢ i) ⁻¹ᵁ U)
                (((Classical.choose (exists_tensorPullbackAdjunction (gᵢ i))).unit.app F).app
                  U t))) ∧
        (∀ (U : (D.obj (op i₀)).Opens) (t : Γ(F, U))
            (a : c.pt.right.obj.obj (op U)),
          e.hom.app U (tmulSection t a) =
            (@id Γ(s.pt, (s.π.app (op i₀)) ⁻¹ᵁ U) (α.hom.right.hom.app (op U) a)) •
              (@id Γ((tensorPullback (s.π.app (op i₀))).obj F, (s.π.app (op i₀)) ⁻¹ᵁ U)
                (((Classical.choose
                  (exists_tensorPullbackAdjunction (s.π.app (op i₀)))).unit.app F).app U t))) ∧
        (∀ {i j : {i : I // i₀ ≤ i}} (f : i ⟶ j)
            (U : (D.obj (op i₀)).Opens) (t : Γ(F, U))
            (a : (A.obj i).right.obj.obj (op U)),
          ((eᵢ i).inv ≫
            (F ◁ (eqToHom (hB i).symm ≫ B.map f ≫ eqToHom (hB j))) ≫
            (eᵢ j).hom).app U ((eᵢ i).hom.app U (tmulSection t a)) =
              ((eqToHom (by rw [hA j]; rfl : (A.obj j).right.obj.obj (op U) =
                  Γ(D.obj (op j.val), (gᵢ j) ⁻¹ᵁ U)))
                ((A.map f).right.hom.app (op U) a)) •
                (@id Γ((tensorPullback (gᵢ j)).obj F, (gᵢ j) ⁻¹ᵁ U)
                  (((Classical.choose (exists_tensorPullbackAdjunction (gᵢ j))).unit.app F).app
                    U t))) ∧
        (∀ (i) (U : (D.obj (op i₀)).Opens) (t : Γ(F, U))
            (a : (A.obj i).right.obj.obj (op U)),
          ((eᵢ i).inv ≫
            (F ◁ (eqToHom (hB i).symm ≫ b.ι.app i ≫ eqToHom hbp)) ≫
            e.hom).app U ((eᵢ i).hom.app U (tmulSection t a)) =
              (@id Γ(s.pt, (s.π.app (op i₀)) ⁻¹ᵁ U)
                  ((c.ι.app i ≫ α.hom).right.hom.app (op U) a)) •
                (@id Γ((tensorPullback (s.π.app (op i₀))).obj F, (s.π.app (op i₀)) ⁻¹ᵁ U)
                  (((Classical.choose
                    (exists_tensorPullbackAdjunction (s.π.app (op i₀)))).unit.app F).app U t))) ∧
        Nonempty (IsColimit b) ∧
        Nonempty (IsColimit ((tensorLeft F).mapCocone b)) := by
  sorry

end AlgebraicGeometry
