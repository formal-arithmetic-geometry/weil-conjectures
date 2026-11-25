/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.AbsoluteFrobeniusIterate
public import WeilConjectures.SixFunctors.Etale.Derived.LocalOperatorUnit

/-!
# The transport of derived global sections along a Frobenius automorphism of a point

Let `k` be a separably closed field of characteristic `p` and `h` an automorphism of
`s = Spec k` inverse to the absolute `p ^ n`-power Frobenius `F_s`. The transport
`RΓ(s, M) ≅ RΓ(s, Lh^* M)` of derived global sections along `h`
(`AlgebraicGeometry.Etale.globalSectionsTransport`) is compatible with the identification
`L(F_s)^* ≅ L(𝟙 s)^*` of `AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso`
(`AlgebraicGeometry.Etale.globalSectionsTransport_hom_app_leftDerivedUpperStarComp_inv_app`).

## Implementation details

On sheaves, both the transport and the identification are compared with the pullback maps on
sections over the terminal object `Γ(Y, G) ⟶ Γ(X, f^* G)`, which are compatible with
composition; all the identifications of sections over the terminal objects involved are
restriction maps between terminal objects of the small étale sites.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section Sheaf

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- The components of `AlgebraicGeometry.Etale.lowerStarCompSheafSectionsTerminalIso` are the
restriction maps along `(g^{-1} ⊤ ≅ ⊤)⁻¹`. -/
lemma lowerStarCompSheafSectionsTerminalIso_hom_app {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (H : Sheaf Z.smallEtaleTopology A) :
    (lowerStarCompSheafSectionsTerminalIso A g).hom.app H =
      H.obj.map (PreservesTerminal.iso g.Etale).inv.op :=
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- The identifications `(g_* H)(⊤) ≅ H(⊤)` of sections over the terminal objects are compatible
with the composition isomorphisms of the pushforwards. -/
lemma lowerStarComp_inv_app_hom_app_comp_lowerStarCompSheafSectionsTerminalIso
    {X Y Z : Scheme.{u}} (g₁ : X ⟶ Y) (g₂ : Y ⟶ Z) (g₁₂ : X ⟶ Z) (h : g₁₂ = g₁ ≫ g₂)
    (W : Sheaf X.smallEtaleTopology A) :
    ((lowerStarComp A g₁ g₂ g₁₂ h).inv.app W).hom.app (op (⊤_ Z.Etale)) ≫
        (lowerStarCompSheafSectionsTerminalIso A g₂).hom.app ((g₁)_*[A].obj W) ≫
        (lowerStarCompSheafSectionsTerminalIso A g₁).hom.app W =
      (lowerStarCompSheafSectionsTerminalIso A g₁₂).hom.app W := by
  have hl := Etale.lowerStar_obj_val_map A g₁ W (PreservesTerminal.iso g₂.Etale).inv
  simp only [lowerStarComp_inv_app_hom_app', lowerStarCompSheafSectionsTerminalIso_hom_app, hl,
    ← Functor.map_comp, ← op_comp]
  exact congrArg (fun φ ↦ W.obj.map φ.op)
    ((terminalIsTerminal.ofIso (PreservesTerminal.iso g₁₂.Etale).symm).hom_ext _ _)

set_option backward.isDefEq.respectTransparency false in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- The identification `((𝟙 X)_* H)(⊤) ≅ H(⊤)` of sections over the terminal object is the
identity isomorphism `(𝟙 X)_* ≅ 𝟭`. -/
lemma lowerStarCompSheafSectionsTerminalIso_id_hom_app {X : Scheme.{u}}
    (N : Sheaf X.smallEtaleTopology A) :
    (lowerStarCompSheafSectionsTerminalIso A (𝟙 X)).hom.app N =
      ((lowerStarId A X).hom.app N).hom.app (op (⊤_ X.Etale)) := by
  dsimp only [lowerStarId, GrothendieckTopology.lowerStarId]
  simp only [lowerStarCompSheafSectionsTerminalIso_hom_app,
    Functor.sheafPushforwardContinuousId'_hom_app_hom_app]
  exact congrArg (fun φ ↦ N.obj.map φ.op)
    ((terminalIsTerminal.ofIso (PreservesTerminal.iso (Scheme.Hom.Etale (𝟙 X))).symm).hom_ext _ _)

variable {p : ℕ} (hp : p.Prime)

set_option backward.isDefEq.respectTransparency false in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- The identification `((F_X)_* H)(⊤) ≅ H(⊤)` of sections over the terminal object is
compatible with the isomorphism `(F_X)_* ≅ (𝟙 X)_*` of
`AlgebraicGeometry.Etale.lowerStarIterateFrobeniusIso`. -/
lemma lowerStarIterateFrobeniusIso_inv_app_hom_app_comp_lowerStarCompSheafSectionsTerminalIso
    {X : Scheme.{u}} (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ) (H : Sheaf X.smallEtaleTopology A) :
    ((lowerStarIterateFrobeniusIso A hp hX n).inv.app H).hom.app (op (⊤_ X.Etale)) ≫
        (lowerStarCompSheafSectionsTerminalIso A (X.iterateFrobenius hp hX n)).hom.app H =
      (lowerStarCompSheafSectionsTerminalIso A (𝟙 X)).hom.app H := by
  have hi : ((lowerStarIterateFrobeniusIso A hp hX n).inv.app H).hom.app (op (⊤_ X.Etale)) =
      H.obj.map ((overPullbackIterateFrobeniusIso hp hX n).inv.app (⊤_ X.Etale)).op :=
    rfl
  simp only [hi, lowerStarCompSheafSectionsTerminalIso_hom_app, ← Functor.map_comp, ← op_comp]
  exact congrArg (fun φ ↦ H.obj.map φ.op)
    ((terminalIsTerminal.ofIso (PreservesTerminal.iso (Scheme.Hom.Etale (𝟙 X))).symm).hom_ext _ _)

end Sheaf


section Pullback

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

/-- The pullback map `G(⊤) ⟶ (g^* G)(⊤)` on sections over the terminal objects along
`g : X ⟶ Y`: the unit `G ⟶ g_* g^* G` followed by `(g_* g^* G)(⊤) ≅ (g^* G)(⊤)`. -/
noncomputable def terminalSectionsUpperStarMap {X Y : Scheme.{u}} (g : X ⟶ Y)
    (G : Sheaf Y.smallEtaleTopology A) :
    ((sheafSections Y.smallEtaleTopology A).obj (op (⊤_ Y.Etale))).obj G ⟶
      ((sheafSections X.smallEtaleTopology A).obj (op (⊤_ X.Etale))).obj ((g)^*[A].obj G) :=
  ((sheafSections Y.smallEtaleTopology A).obj (op (⊤_ Y.Etale))).map
      ((upperStarLowerStarAdjunction A g).unit.app G) ≫
    (lowerStarCompSheafSectionsTerminalIso A g).hom.app ((g)^*[A].obj G)

/-- The pullback maps on sections over the terminal objects are compatible with composition:
`G(⊤) ⟶ (F^* G)(⊤) ⟶ (h^* F^* G)(⊤) ≅ ((h ≫ F)^* G)(⊤)` is the pullback map along `h ≫ F`. -/
lemma terminalSectionsUpperStarMap_comp {X Y Z : Scheme.{u}} (h : X ⟶ Y) (F : Y ⟶ Z)
    (g : X ⟶ Z) (hg : g = h ≫ F) (G : Sheaf Z.smallEtaleTopology A) :
    terminalSectionsUpperStarMap A F G ≫ terminalSectionsUpperStarMap A h ((F)^*[A].obj G) ≫
        ((sheafSections X.smallEtaleTopology A).obj (op (⊤_ X.Etale))).map
          ((upperStarComp A h F g hg).inv.app G) =
      terminalSectionsUpperStarMap A g G := by
  have n₁ := (lowerStarCompSheafSectionsTerminalIso A F).hom.naturality
    ((upperStarLowerStarAdjunction A h).unit.app ((F)^*[A].obj G))
  have n₂ := (lowerStarCompSheafSectionsTerminalIso A g).hom.naturality
    ((upperStarComp A h F g hg).hom.app G)
  simp only [Functor.comp_map] at n₁ n₂
  have hu := upperStarComp_hom_app_unit_app A h F G g hg
  simp only [Adjunction.comp_unit_app] at hu
  have hu' : (upperStarLowerStarAdjunction A F).unit.app G ≫
      (F)_*[A].map ((upperStarLowerStarAdjunction A h).unit.app ((F)^*[A].obj G)) =
      (upperStarLowerStarAdjunction A g).unit.app G ≫
        (g)_*[A].map ((upperStarComp A h F g hg).hom.app G) ≫
        (lowerStarComp A h F g hg).inv.app ((h)^*[A].obj ((F)^*[A].obj G)) := by
    rw [reassoc_of% hu, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  have s₁ := lowerStarComp_inv_app_hom_app_comp_lowerStarCompSheafSectionsTerminalIso A h F g hg
    ((h)^*[A].obj ((F)^*[A].obj G))
  simp only [terminalSectionsUpperStarMap, Category.assoc]
  rw [← reassoc_of% n₁, ← Functor.map_comp_assoc, hu', Functor.map_comp, Functor.map_comp,
    Category.assoc, Category.assoc]
  erw [reassoc_of% s₁]
  rw [reassoc_of% n₂, ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.comp_id]

variable {p : ℕ} (hp : p.Prime)

omit [HasSmallSiteSheafify A] in
/-- The pullback map on sections over the terminal object along the absolute Frobenius `F_X`,
followed by the isomorphism `F_X^* ≅ (𝟙 X)^*`, is the pullback map along `𝟙 X`. -/
lemma terminalSectionsUpperStarMap_comp_upperStarIterateFrobeniusIso {X : Scheme.{u}}
    (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ) (G : Sheaf X.smallEtaleTopology A) :
    terminalSectionsUpperStarMap A (X.iterateFrobenius hp hX n) G ≫
        ((sheafSections X.smallEtaleTopology A).obj (op (⊤_ X.Etale))).map
          ((upperStarIterateFrobeniusIso A hp hX n).hom.app G) =
      terminalSectionsUpperStarMap A (𝟙 X) G := by
  have n₁ := (lowerStarCompSheafSectionsTerminalIso A (X.iterateFrobenius hp hX n)).hom.naturality
    ((upperStarIterateFrobeniusIso A hp hX n).hom.app G)
  simp only [Functor.comp_map] at n₁
  have hc : conjugateEquiv (upperStarLowerStarAdjunction A (𝟙 X))
      (upperStarLowerStarAdjunction A (X.iterateFrobenius hp hX n))
      (upperStarIterateFrobeniusIso A hp hX n).hom =
      (lowerStarIterateFrobeniusIso A hp hX n).inv :=
    congrArg Iso.hom (conjugateIsoEquiv_upperStarIterateFrobeniusIso A hp hX n)
  have hu := unit_conjugateEquiv (upperStarLowerStarAdjunction A (𝟙 X))
    (upperStarLowerStarAdjunction A (X.iterateFrobenius hp hX n))
    (upperStarIterateFrobeniusIso A hp hX n).hom G
  rw [hc] at hu
  have s := lowerStarIterateFrobeniusIso_inv_app_hom_app_comp_lowerStarCompSheafSectionsTerminalIso
    A hp hX n ((𝟙 X)^*[A].obj G)
  simp only [terminalSectionsUpperStarMap, Category.assoc]
  rw [← n₁, ← Functor.map_comp_assoc, ← hu, Functor.map_comp, Category.assoc]
  erw [s]

omit [HasSmallSiteSheafify A] in
/-- For an isomorphism `h`, the transport `G(⊤) ≅ ((h⁻¹)_* G)(⊤) ≅ (h^* G)(⊤)` through
`h^* ≅ (h⁻¹)_*` (`AlgebraicGeometry.Etale.upperStarInvIsoLowerStarHom`) is the pullback map
along `h` on sections over the terminal objects. -/
lemma lowerStarCompSheafSectionsTerminalIso_inv_app_comp_upperStarInvIsoLowerStarHom_inv_app
    {X Y : Scheme.{u}} (h : X ⟶ Y) [IsIso h] (N : Sheaf Y.smallEtaleTopology A) :
    (lowerStarCompSheafSectionsTerminalIso A (asIso h).symm.hom).inv.app N ≫
        ((sheafSections X.smallEtaleTopology A).obj (op (⊤_ X.Etale))).map
          ((upperStarInvIsoLowerStarHom A (asIso h).symm).inv.app N) =
      terminalSectionsUpperStarMap A h N := by
  have c := Adjunction.leftAdjointUniq_hom_app_counit (upperStarLowerStarAdjunction A h)
    (lowerStarEquivalenceOfIso A (asIso h).symm).toAdjunction ((h)^*[A].obj N)
  have nat := (upperStarInvIsoLowerStarHom A (asIso h).symm).hom.naturality
    ((upperStarLowerStarAdjunction A h).unit.app N)
  have tri := (upperStarLowerStarAdjunction A h).left_triangle_components N
  have hι : (upperStarInvIsoLowerStarHom A (asIso h).symm).inv.app N =
      ((asIso h).symm.hom)_*[A].map ((upperStarLowerStarAdjunction A h).unit.app N) ≫
        (lowerStarEquivalenceOfIso A (asIso h).symm).counit.app ((h)^*[A].obj N) := by
    rw [← cancel_epi ((upperStarInvIsoLowerStarHom A (asIso h).symm).hom.app N),
      Iso.hom_inv_id_app]
    erw [← reassoc_of% nat]
    erw [c]
    exact tri.symm
  have n := (lowerStarCompSheafSectionsTerminalIso A (asIso h).symm.hom).inv.naturality
    ((upperStarLowerStarAdjunction A h).unit.app N)
  simp only [Functor.comp_map] at n
  have s₁ := lowerStarComp_inv_app_hom_app_comp_lowerStarCompSheafSectionsTerminalIso A
    (asIso h).symm.inv (asIso h).symm.hom (𝟙 X) (by simp) ((h)^*[A].obj N)
  have s₂ := lowerStarCompSheafSectionsTerminalIso_id_hom_app A ((h)^*[A].obj N)
  have e₂ : ((lowerStarComp A (asIso h).symm.inv (asIso h).symm.hom (𝟙 X) (by simp)).inv.app
        ((h)^*[A].obj N)).hom.app (op (⊤_ X.Etale)) ≫
      ((lowerStarComp A (asIso h).symm.inv (asIso h).symm.hom (𝟙 X) (by simp)).hom.app
        ((h)^*[A].obj N)).hom.app (op (⊤_ X.Etale)) = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id_app]
    rfl
  have hε : (((sheafSections X.smallEtaleTopology A).obj (op (⊤_ X.Etale))).map
      ((lowerStarEquivalenceOfIso A (asIso h).symm).counit.app ((h)^*[A].obj N))) =
      ((lowerStarComp A (asIso h).symm.inv (asIso h).symm.hom (𝟙 X) (by simp)).hom.app
        ((h)^*[A].obj N)).hom.app (op (⊤_ X.Etale)) ≫
      ((lowerStarId A X).hom.app ((h)^*[A].obj N)).hom.app (op (⊤_ X.Etale)) :=
    rfl
  have key : (lowerStarCompSheafSectionsTerminalIso A (asIso h).symm.hom).inv.app
        ((h)_*[A].obj ((h)^*[A].obj N)) ≫
      ((sheafSections X.smallEtaleTopology A).obj (op (⊤_ X.Etale))).map
        ((lowerStarEquivalenceOfIso A (asIso h).symm).counit.app ((h)^*[A].obj N)) =
      (lowerStarCompSheafSectionsTerminalIso A h).hom.app ((h)^*[A].obj N) := by
    rw [← cancel_epi ((lowerStarCompSheafSectionsTerminalIso A (asIso h).symm.hom).hom.app _)]
    erw [Iso.hom_inv_id_app_assoc]
    rw [hε,
      ← cancel_epi (((lowerStarComp A (asIso h).symm.inv (asIso h).symm.hom (𝟙 X)
        (by simp)).inv.app ((h)^*[A].obj N)).hom.app (op (⊤_ X.Etale))), reassoc_of% e₂, ← s₂]
    exact s₁.symm
  rw [hι]
  erw [Functor.map_comp, ← reassoc_of% n, key]
  rfl

end Pullback


section Frobenius

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] {p : ℕ} (hp : p.Prime)

/-- For an automorphism `h` inverse to the absolute Frobenius `F_X`, the transport
`(F_X^* G)(⊤) ≅ (h^* F_X^* G)(⊤)` along `h`, followed by `h^* F_X^* ≅ (𝟙 X)^*`, is induced by the
isomorphism `F_X^* ≅ (𝟙 X)^*` of `AlgebraicGeometry.Etale.upperStarIterateFrobeniusIso`. -/
lemma terminalSections_transport_upperStarComp_inv_app {X : Scheme.{u}}
    (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ) (h : X ⟶ X) [IsIso h]
    (hh : h ≫ X.iterateFrobenius hp hX n = 𝟙 X) (G : Sheaf X.smallEtaleTopology A) :
    (lowerStarCompSheafSectionsTerminalIso A (asIso h).symm.hom).inv.app
          ((X.iterateFrobenius hp hX n)^*[A].obj G) ≫
        ((sheafSections X.smallEtaleTopology A).obj (op (⊤_ X.Etale))).map
          ((upperStarInvIsoLowerStarHom A (asIso h).symm).inv.app
            ((X.iterateFrobenius hp hX n)^*[A].obj G)) ≫
        ((sheafSections X.smallEtaleTopology A).obj (op (⊤_ X.Etale))).map
          ((upperStarComp A h (X.iterateFrobenius hp hX n) (𝟙 X) hh.symm).inv.app G) =
      ((sheafSections X.smallEtaleTopology A).obj (op (⊤_ X.Etale))).map
        ((upperStarIterateFrobeniusIso A hp hX n).hom.app G) := by
  have hF : X.iterateFrobenius hp hX n = inv h := by
    rw [← cancel_epi h, hh, IsIso.hom_inv_id]
  have : IsIso (X.iterateFrobenius hp hX n) := by
    rw [hF]
    infer_instance
  have : IsIso (upperStarLowerStarAdjunction A (X.iterateFrobenius hp hX n)).unit :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  have : IsIso (terminalSectionsUpperStarMap A (X.iterateFrobenius hp hX n) G) := by
    unfold terminalSectionsUpperStarMap
    infer_instance
  rw [← Category.assoc,
    lowerStarCompSheafSectionsTerminalIso_inv_app_comp_upperStarInvIsoLowerStarHom_inv_app,
    ← cancel_epi (terminalSectionsUpperStarMap A (X.iterateFrobenius hp hX n) G),
    terminalSectionsUpperStarMap_comp A h (X.iterateFrobenius hp hX n) (𝟙 X) hh.symm G,
    terminalSectionsUpperStarMap_comp_upperStarIterateFrobeniusIso]

end Frobenius


section Derived

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C E : Type*} [Category* C] [Category* E] [Abelian C] [Abelian E] [HasDerivedCategory C]
  [HasDerivedCategory E] {P Q H : C ⥤ C} {S : C ⥤ E}
  [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]

/-- Let `e : S ≅ H ⋙ S`, `u : Q ≅ P ⋙ H` and `t : P ≅ Q` be isomorphisms of exact functors such
that `e_{P G} ≫ S(u⁻¹_G) = S(t_G)` for all `G`. Then the same holds for the induced isomorphisms
on derived categories. -/
lemma mapDerivedCategoryTriangleIso_hom_app_comp_map_of_comp (e : S ≅ H ⋙ S) (u : Q ≅ P ⋙ H)
    (t : P ≅ Q) (hyp : ∀ G, e.hom.app (P.obj G) ≫ S.map (u.inv.app G) = S.map (t.hom.app G))
    (M : DerivedCategory C) :
    (Functor.mapDerivedCategoryTriangleIso e).hom.app (P.mapDerivedCategory.obj M) ≫
        S.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso P H).hom.app M ≫
          (Functor.mapDerivedCategoryNatIso u).inv.app M) =
      S.mapDerivedCategory.map ((Functor.mapDerivedCategoryNatIso t).hom.app M) := by
  have J : Functor.isoWhiskerLeft P e ≪≫ Functor.isoWhiskerRight u.symm S =
      Functor.isoWhiskerRight t S := by
    ext G
    simpa using hyp G
  have key := NatTrans.congr_app (congrArg (fun i ↦ (Functor.mapDerivedCategoryNatIso i).hom ≫
    (Functor.mapDerivedCategoryCompIso Q S).inv) J) M
  simp only [Functor.mapDerivedCategoryNatIso_trans, Category.assoc, NatTrans.comp_app] at key
  have hWL := NatTrans.congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft P e) M
  have hWRu := NatTrans.congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight u.symm S) M
  have hWRt := NatTrans.congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight t S) M
  have hA := NatTrans.congr_app (Functor.mapDerivedCategoryCompIso_assoc P H S) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hWL hWRu
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hWRt hA
  rw [hWRu, hWRt, Functor.mapDerivedCategoryNatIso_symm] at key
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso P S).inv.app M), ← reassoc_of% hWL,
    reassoc_of% hA, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact key

end Derived

section PointDerived

variable (Λ : Type (u + 1)) [CommRing Λ] {k : Type u} [Field k] [IsSepClosed k] {p : ℕ}
  (hp : p.Prime)

/-- Over a separably closed field `k`, for an automorphism `h` of `Spec k` inverse to the absolute
Frobenius `F`, the sections over the point of the transport along `h`, followed by
`h^* F^* ≅ (𝟙)^*`, are induced by `F^* ≅ (𝟙)^*`. -/
lemma sectionsPointTransportIso_hom_app_comp_upperStarComp_inv_app
    (hk : (p : Γ(Spec (.of k), ⊤)) = 0) (n : ℕ) (h : Spec (.of k) ⟶ Spec (.of k)) [IsIso h]
    (hh : h ≫ (Spec (.of k)).iterateFrobenius hp hk n = 𝟙 _)
    (G : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (sectionsPointTransportIso Λ h).hom.app
        (((Spec (.of k)).iterateFrobenius hp hk n)^*[ModuleCat.{u + 1} Λ].obj G) ≫
      ((sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (op (etalePoint k))).map ((upperStarComp (ModuleCat.{u + 1} Λ) h
          ((Spec (.of k)).iterateFrobenius hp hk n) (𝟙 _) hh.symm).inv.app G) =
      ((sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (op (etalePoint k))).map
        ((upperStarIterateFrobeniusIso (ModuleCat.{u + 1} Λ) hp hk n).hom.app G) := by
  have h₁ := ΓNatIsoSheafSections_inv_app_comp_lowerStarCompGlobalSectionsIso_inv_app (Λ := Λ)
    (asIso h).symm.hom (((Spec (.of k)).iterateFrobenius hp hk n)^*[ModuleCat.{u + 1} Λ].obj G)
  have key := terminalSections_transport_upperStarComp_inv_app (ModuleCat.{u + 1} Λ) hp hk n h
    hh G
  have n₂ := ((upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ) (asIso h).symm).inv.app
    (((Spec (.of k)).iterateFrobenius hp hk n)^*[ModuleCat.{u + 1} Λ].obj G) ≫
      (upperStarComp (ModuleCat.{u + 1} Λ) h ((Spec (.of k)).iterateFrobenius hp hk n) (𝟙 _)
        hh.symm).inv.app G).hom.naturality (terminalIsTerminal.from (etalePoint k)).op
  have n₁ := ((upperStarIterateFrobeniusIso (ModuleCat.{u + 1} Λ) hp hk n).hom.app G).hom.naturality
    (isTerminalEtalePoint.from (⊤_ _)).op
  have hr : terminalIsTerminal.from (etalePoint k) ≫ isTerminalEtalePoint.from (⊤_ _) = 𝟙 _ :=
    isTerminalEtalePoint.hom_ext _ _
  simp only [sectionsPointTransportIso, sectionsTransportIso_hom_app, Category.assoc]
  rw [reassoc_of% h₁, ← Functor.map_comp]
  erw [n₂]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Category.assoc]
  erw [reassoc_of% key]
  erw [reassoc_of% n₁]
  rw [← Functor.map_comp, ← op_comp, hr, op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- **The transport along a Frobenius automorphism of a separably closed point.** Over a
separably closed field `k` of characteristic `p`, let `h` be an automorphism of `s = Spec k`
inverse to the absolute `p ^ n`-power Frobenius `F_s`. Then the transport
`RΓ(s, LF_s^* M) ≅ RΓ(s, Lh^* LF_s^* M)` of derived global sections along `h`
(`AlgebraicGeometry.Etale.globalSectionsTransport`), followed by
`Lh^* LF_s^* ≅ L(h ≫ F_s)^* = L(𝟙 s)^*`, is induced by the identification `LF_s^* ≅ L(𝟙 s)^*` of
`AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso`. -/
theorem globalSectionsTransport_hom_app_leftDerivedUpperStarComp_inv_app
    (hk : (p : Γ(Spec (.of k), ⊤)) = 0) (n : ℕ) (h : Spec (.of k) ⟶ Spec (.of k)) [IsIso h]
    (hh : h ≫ (Spec (.of k)).iterateFrobenius hp hk n = 𝟙 _)
    (M : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (globalSectionsTransport Λ h).hom.app
        (L(((Spec (.of k)).iterateFrobenius hp hk n)^*[ModuleCat.{u + 1} Λ]).obj M) ≫
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) _).map
        ((leftDerivedUpperStarComp _ h ((Spec (.of k)).iterateFrobenius hp hk n) (𝟙 _)
          hh.symm).inv.app M) =
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) _).map
        ((leftDerivedUpperStarIterateFrobeniusIso _ hp hk n).hom.app M) := by
  have T := globalSectionsTransport_hom_app_comp_rightDerivedGlobalSectionsIsoOfIsSepClosed
    (Λ := Λ) h (L(((Spec (.of k)).iterateFrobenius hp hk n)^*[ModuleCat.{u + 1} Λ]).obj M)
  have A₀ := mapDerivedCategoryTriangleIso_hom_app_comp_map_of_comp
    (sectionsPointTransportIso Λ h)
    (upperStarComp (ModuleCat.{u + 1} Λ) h ((Spec (.of k)).iterateFrobenius hp hk n) (𝟙 _)
      hh.symm)
    (upperStarIterateFrobeniusIso (ModuleCat.{u + 1} Λ) hp hk n)
    (sectionsPointTransportIso_hom_app_comp_upperStarComp_inv_app Λ hp hk n h hh) M
  have hc : (leftDerivedUpperStarComp _ h ((Spec (.of k)).iterateFrobenius hp hk n) (𝟙 _)
      hh.symm).inv.app M =
      ((h)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctorIsoMapDerivedCategory.hom.app
          (L(((Spec (.of k)).iterateFrobenius hp hk n)^*[ModuleCat.{u + 1} Λ]).obj M) ≫
        ((h)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.map
          ((Functor.leftDerivedFunctorIsoMapDerivedCategory
            ((Spec (.of k)).iterateFrobenius hp hk n)^*[ModuleCat.{u + 1} Λ]).hom.app M) ≫
        (Functor.mapDerivedCategoryCompIso
          ((Spec (.of k)).iterateFrobenius hp hk n)^*[ModuleCat.{u + 1} Λ]
          (h)^*[ModuleCat.{u + 1} Λ]).hom.app M ≫
        (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} Λ) h
          ((Spec (.of k)).iterateFrobenius hp hk n) (𝟙 _) hh.symm)).inv.app M ≫
        ((𝟙 (Spec (.of k)))^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctorIsoMapDerivedCategory.inv.app
          M := by
    simp [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
      Functor.leftDerivedFunctorCompIso]
  have hθ : (leftDerivedUpperStarIterateFrobeniusIso (ModuleCat.{u + 1} Λ) hp hk n).hom.app M =
      (Functor.leftDerivedFunctorIsoMapDerivedCategory
            ((Spec (.of k)).iterateFrobenius hp hk n)^*[ModuleCat.{u + 1} Λ]).hom.app M ≫
        (Functor.mapDerivedCategoryNatIso
          (upperStarIterateFrobeniusIso (ModuleCat.{u + 1} Λ) hp hk n)).hom.app M ≫
        ((𝟙 (Spec (.of k)))^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctorIsoMapDerivedCategory.inv.app
          M :=
    rfl
  have hD := (Functor.mapDerivedCategoryTriangleIso (sectionsPointTransportIso Λ h)).hom.naturality
    ((Functor.leftDerivedFunctorIsoMapDerivedCategory
            ((Spec (.of k)).iterateFrobenius hp hk n)^*[ModuleCat.{u + 1} Λ]).hom.app M)
  simp only [Functor.comp_map] at hD
  simp only [leftDerivedUpperStarIsoMapDerivedCategory] at T
  rw [← cancel_mono ((rightDerivedGlobalSectionsIsoOfIsSepClosed Λ).hom.app _), Category.assoc,
    (rightDerivedGlobalSectionsIsoOfIsSepClosed Λ).hom.naturality, reassoc_of% T,
    (rightDerivedGlobalSectionsIsoOfIsSepClosed Λ).hom.naturality, cancel_epi, hc, hθ]
  simp only [Functor.map_comp]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← reassoc_of% hD]
  simp only [Functor.map_comp] at A₀
  rw [reassoc_of% A₀]

end PointDerived

end AlgebraicGeometry.Etale
