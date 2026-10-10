/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.FinitePresentationModel
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.SeparatingPair
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Closed subschemes as limits of closed subschemes of finite presentation

A closed subscheme of a quasi-compact quasi-separated scheme `Y` is the cofiltered limit of the
closed subschemes of `Y` cut out by the subideal sheaves of finite type of its ideal sheaf
(`AlgebraicGeometry.Scheme.IdealSheafData.isLimitFgSubCone`, Stacks Project Tag 09ZP).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section ClosedSubschemeLimit

/-!
## A closed subscheme as the limit of its closed neighbours of finite presentation

Let `I` be a quasi-coherent ideal sheaf on a quasi-compact quasi-separated scheme `Y`. Every
section of `I` over an affine open lies in a subideal sheaf of `I` of finite type
(`AlgebraicGeometry.Scheme.IdealSheafData.exists_finiteType_le_of_mem`). This is proved by
absolute Noetherian approximation of the ambient scheme rather than by the quasi-coherent
extension theorem of Stacks Project Tag 01PF: the section descends to an affine open of a
Noetherian stage `Yⱼ`, and there the scheme-theoretic image `I.map (π j)` of `V(I)` has
finitely generated ideals of sections, because a closed immersion into a Noetherian scheme is
locally of finite presentation. Its inverse image on `Y` is then a subideal sheaf of `I` of
finite type containing the given section.

Consequently `V(I)` is the cofiltered limit of the closed subschemes `V(J)`, for `J` running
over the subideal sheaves of `I` of finite type
(`AlgebraicGeometry.Scheme.IdealSheafData.isLimitFgSubCone`, Stacks Project Tag 09ZP). The
index category is the directed poset
`AlgebraicGeometry.Scheme.IdealSheafData.FGSub`, the diagram is
`AlgebraicGeometry.Scheme.IdealSheafData.fgSubDiagram`, its transition morphisms are the
subscheme inclusions, hence closed immersions, and each `V(J) ⟶ Y` is locally of finite
presentation.
-/

set_option backward.defeqAttrib.useBackward true

namespace Scheme.IdealSheafData

variable {X Y Z : Scheme.{u}}

/-- (Implementation) A section over an affine open `V` of `Y` lies in the pushforward `I.map f`
as soon as its pullback to `f ⁻¹ᵁ V` lies in `I`. -/
private lemma mem_ideal_map_of_preimage_eq (I : X.IdealSheafData)
    (f : X ⟶ Y) [QuasiCompact f] (V : Y.affineOpens) (U : X.affineOpens)
    (hUV : f ⁻¹ᵁ V.1 = U.1) (t : Γ(Y, V.1)) (h : U.1 ≤ f ⁻¹ᵁ V.1)
    (hmem : f.appLE V.1 U.1 h t ∈ I.ideal U) : t ∈ (I.map f).ideal V := by
  obtain ⟨U, hU⟩ := U
  dsimp only at hUV h hmem
  subst hUV
  rw [ideal_map I f V hU, Ideal.mem_comap, Scheme.Hom.app_eq_appLE]
  exact hmem

/-- (Implementation) The inverse image along `π : Y ⟶ Z` of the scheme-theoretic image of
`V(I)` in a locally Noetherian scheme `Z` is a subideal sheaf of `I` of finite type, and it
contains every section of `I` that comes from `Z`. -/
private lemma exists_finiteType_le_of_appLE_eq [IsLocallyNoetherian Z]
    (I : Y.IdealSheafData) (π : Y ⟶ Z) [QuasiCompact π] (V : Z.affineOpens) (U : Y.affineOpens)
    (hUV : π ⁻¹ᵁ V.1 = U.1) (h : U.1 ≤ π ⁻¹ᵁ V.1) (t : Γ(Z, V.1)) {s : Γ(Y, U.1)}
    (hts : π.appLE V.1 U.1 h t = s) (hs : s ∈ I.ideal U) :
    ∃ J : Y.IdealSheafData, J ≤ I ∧ (∀ W : Y.affineOpens, (J.ideal W).FG) ∧ s ∈ J.ideal U := by
  refine ⟨(I.map π).comap π, le_map_iff_comap_le.mp le_rfl, ?_, ?_⟩
  · have : LocallyOfFinitePresentation ((I.map π).comap π).subschemeι := by
      rw [← comapIso_hom_fst (I.map π) π]
      exact MorphismProperty.comp_mem _ _ _ inferInstance
        (MorphismProperty.pullback_fst _ _ inferInstance)
    intro W
    have hfg := Scheme.Hom.fg_ideal_ker ((I.map π).comap π).subschemeι W
    rwa [ker_subschemeι] at hfg
  · have htV : t ∈ (I.map π).ideal V :=
      mem_ideal_map_of_preimage_eq I π V U hUV t h (by rw [hts]; exact hs)
    have hmem := ideal_map_appLE_le_ideal_comap (I.map π) π V U h (Ideal.mem_map_of_mem _ htV)
    rwa [hts] at hmem

/-- **Every section of an ideal sheaf on a quasi-compact quasi-separated scheme lies in a
subideal sheaf of finite type.** (Blueprint: `lemma:nagata-closed-subscheme-fp-system`.) -/
theorem exists_finiteType_le_of_mem [CompactSpace Y] [QuasiSeparatedSpace Y]
    (I : Y.IdealSheafData) (U : Y.affineOpens) {s : Γ(Y, U.1)} (hs : s ∈ I.ideal U) :
    ∃ J : Y.IdealSheafData, J ≤ I ∧ (∀ V : Y.affineOpens, (J.ideal V).FG) ∧ s ∈ J.ideal U := by
  obtain ⟨N⟩ := Y.nonempty_noetherianApproximation
  obtain ⟨U, hU⟩ := U
  dsimp only at s hs ⊢
  obtain ⟨k, V, hV, hkV⟩ : ∃ (k : N.I) (V : (N.D.obj k).Opens), IsAffineOpen V ∧
      N.π.app k ⁻¹ᵁ V = U := by
    obtain ⟨i, W, hWc, hWU⟩ := exists_preimage_eq N.D (Cone.mk Y N.π) N.isLimit U hU.isCompact
    obtain ⟨j, hVj⟩ := exists_isAffineOpen_preimage (D := N.D) (c := Cone.mk Y N.π) N.isLimit hWc
      (hWU ▸ hU)
    have hWU' : N.π.app i ⁻¹ᵁ W = U := hWU
    have hwj : N.π.app j.left ≫ N.D.map j.hom = N.π.app i := (Cone.mk Y N.π).w j.hom
    refine ⟨j.left, _, hVj, ?_⟩
    rw [← Scheme.Hom.comp_preimage, hwj]
    exact hWU'
  subst hkV
  obtain ⟨m, g, t, ht⟩ :=
    exists_appLE_π_app_eq (D := N.D) (c := Cone.mk Y N.π) N.isLimit k hV s
  have ht' : ∀ e : N.π.app k ⁻¹ᵁ V ≤ N.π.app m ⁻¹ᵁ (N.D.map g ⁻¹ᵁ V),
      (N.π.app m).appLE (N.D.map g ⁻¹ᵁ V) (N.π.app k ⁻¹ᵁ V) e t = s := ht
  have hwm : N.π.app m ≫ N.D.map g = N.π.app k := (Cone.mk Y N.π).w g
  have hmk : N.π.app m ⁻¹ᵁ (N.D.map g ⁻¹ᵁ V) = N.π.app k ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, hwm]
  have : IsAffineHom (N.π.app m) := isAffineHom_π_app N.D (Cone.mk Y N.π) N.isLimit m
  exact exists_finiteType_le_of_appLE_eq I (N.π.app m) ⟨N.D.map g ⁻¹ᵁ V, hV.preimage _⟩
    ⟨N.π.app k ⁻¹ᵁ V, hU⟩ hmk hmk.ge t (ht' hmk.ge) hs

/-- The subideal sheaves of finite type of an ideal sheaf `I`, ordered by inclusion.
(Blueprint: `def:nagata-closed-subscheme-fp-system`.) -/
protected abbrev FGSub (I : Y.IdealSheafData) : Type u :=
  {J : Y.IdealSheafData // J ≤ I ∧ ∀ U : Y.affineOpens, (J.ideal U).FG}

variable (I : Y.IdealSheafData)

instance : OrderBot I.FGSub where
  bot := ⟨⊥, bot_le, fun _ ↦ Submodule.fg_bot⟩
  bot_le _ := Subtype.coe_le_coe.mp bot_le

instance : Inhabited I.FGSub := ⟨⊥⟩

@[simp]
lemma FGSub.coe_bot : ((⊥ : I.FGSub) : Y.IdealSheafData) = ⊥ := rfl

/-- The subideal sheaves of finite type of `I` are directed: the sum of two of them is one. -/
instance : IsDirectedOrder I.FGSub :=
  ⟨fun J J' ↦ ⟨⟨J.1 ⊔ J'.1, sup_le J.2.1 J'.2.1, fun U ↦ Submodule.FG.sup (J.2.2 U) (J'.2.2 U)⟩,
    Subtype.coe_le_coe.mp le_sup_left, Subtype.coe_le_coe.mp le_sup_right⟩⟩

/-- The cofiltered diagram of the closed subschemes cut out by the subideal sheaves of finite
type of `I`, with the subscheme inclusions as transition morphisms.
(Blueprint: `def:nagata-closed-subscheme-fp-system`.) -/
@[simps]
noncomputable def fgSubDiagram : (I.FGSub)ᵒᵖ ⥤ Scheme.{u} where
  obj J := J.unop.1.subscheme
  map f := inclusion (Subtype.coe_le_coe.mpr f.unop.le)
  map_id _ := inclusion_id _
  map_comp _ _ := (inclusion_comp _ _).symm

set_option backward.isDefEq.respectTransparency false in
instance isClosedImmersion_fgSubDiagram_map {J J' : (I.FGSub)ᵒᵖ} (f : J ⟶ J') :
    IsClosedImmersion (I.fgSubDiagram.map f) := by
  have h : I.fgSubDiagram.map f ≫ (J'.unop : Y.IdealSheafData).subschemeι =
      (J.unop : Y.IdealSheafData).subschemeι := inclusion_subschemeι _
  have : IsClosedImmersion
      (I.fgSubDiagram.map f ≫ (J'.unop : Y.IdealSheafData).subschemeι) := by
    rw [h]; infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (J'.unop : Y.IdealSheafData).subschemeι

instance compactSpace_fgSubDiagram_obj [CompactSpace Y] (J : (I.FGSub)ᵒᵖ) :
    CompactSpace (I.fgSubDiagram.obj J) :=
  inferInstanceAs (CompactSpace (J.unop : Y.IdealSheafData).subscheme)

instance quasiSeparatedSpace_fgSubDiagram_obj [QuasiSeparatedSpace Y] (J : (I.FGSub)ᵒᵖ) :
    QuasiSeparatedSpace (I.fgSubDiagram.obj J) :=
  inferInstanceAs (QuasiSeparatedSpace (J.unop : Y.IdealSheafData).subscheme)

instance locallyOfFinitePresentation_fgSub_subschemeι (J : I.FGSub) :
    LocallyOfFinitePresentation (J.1).subschemeι :=
  locallyOfFinitePresentation_subschemeι J.2.2

/-- The cone with point the closed subscheme cut out by `I` over the diagram of the closed
subschemes cut out by the subideal sheaves of finite type of `I`. -/
@[simps]
noncomputable def fgSubCone : Cone I.fgSubDiagram where
  pt := I.subscheme
  π := { app J := inclusion J.unop.2.1 }

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) All the legs of a cone over `I.fgSubDiagram` induce the same morphism
to the ambient scheme. -/
lemma π_app_comp_subschemeι (s : Cone I.fgSubDiagram) (J : (I.FGSub)ᵒᵖ) :
    s.π.app J ≫ J.unop.1.subschemeι =
      s.π.app (Opposite.op ⊥) ≫ (⊥ : Y.IdealSheafData).subschemeι := by
  rw [← s.w (Quiver.Hom.op (homOfLE (bot_le : (⊥ : I.FGSub) ≤ J.unop)))]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) The ideal sheaf `I` is contained in the kernel of the morphism to the
ambient scheme induced by any cone over `I.fgSubDiagram`. -/
lemma le_ker_π_app_bot_comp_subschemeι [CompactSpace Y] [QuasiSeparatedSpace Y]
    (s : Cone I.fgSubDiagram) :
    I.subschemeι.ker ≤
      (s.π.app (Opposite.op ⊥) ≫ (⊥ : Y.IdealSheafData).subschemeι).ker := by
  rw [ker_subschemeι]
  intro U x hx
  obtain ⟨J, hJI, hJfg, hxJ⟩ := I.exists_finiteType_le_of_mem U hx
  have hle : J ≤ (s.π.app (Opposite.op ⟨J, hJI, hJfg⟩) ≫ J.subschemeι).ker := by
    simpa using Scheme.Hom.le_ker_comp (s.π.app (Opposite.op ⟨J, hJI, hJfg⟩)) J.subschemeι
  rw [← π_app_comp_subschemeι I s (Opposite.op ⟨J, hJI, hJfg⟩)]
  exact hle U hxJ

set_option backward.isDefEq.respectTransparency false in
/-- **A closed subscheme of a quasi-compact quasi-separated scheme is the cofiltered limit of
the closed subschemes cut out by the subideal sheaves of finite type of its ideal sheaf.**
(Blueprint: `lemma:nagata-closed-subscheme-fp-system`.) -/
@[stacks 09ZP]
noncomputable def isLimitFgSubCone [CompactSpace Y] [QuasiSeparatedSpace Y] :
    IsLimit I.fgSubCone where
  lift s := IsClosedImmersion.lift I.subschemeι
    (s.π.app (Opposite.op ⊥) ≫ (⊥ : Y.IdealSheafData).subschemeι)
    (le_ker_π_app_bot_comp_subschemeι I s)
  fac s J := by
    rw [← cancel_mono J.unop.1.subschemeι, Category.assoc, fgSubCone_π_app,
      inclusion_subschemeι, IsClosedImmersion.lift_fac, π_app_comp_subschemeι I s J]
  uniq s m hm := by
    rw [← cancel_mono I.subschemeι, IsClosedImmersion.lift_fac,
      ← inclusion_subschemeι (⊥ : I.FGSub).2.1, ← fgSubCone_π_app, ← Category.assoc,
      hm (Opposite.op ⊥)]
    rfl

end Scheme.IdealSheafData

end ClosedSubschemeLimit

end AlgebraicGeometry
