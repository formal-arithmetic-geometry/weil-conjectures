/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSectionArrows
import WeilConjectures.AlgebraicGeometry.AffineSpacePurity.AffineSpacePurityComparison

/-! # Transposition of the specified compact-support compositor

Source: coordinate section recursion, expanded pasted-counit step.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

attribute [local irreducible] originCompositionAmbient rightDerivedUpperShriekHomEquiv
  rightDerivedUpperShriekCounit

end AlgebraicGeometry.ProEtale.AffineZeroPurity

namespace AlgebraicGeometry.ProEtale.AffineZeroPurity

private theorem iso_naturality_paste {C D E : Type*} [Category* C]
    [Category* D] [Category* E] (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    (Q : ObjectProperty C) (e : Q.ι ⋙ F ⋙ G ≅ Q.ι ⋙ H)
    {T M : C} (hT : Q T) (hM : Q M) (v : T ⟶ M)
    {V : D} {K : E} (a : F.obj M ⟶ V) (b : G.obj V ⟶ K) :
    e.inv.app ⟨T, hT⟩ ≫ G.map (F.map v ≫ a) ≫ b =
      H.map v ≫ (e.inv.app ⟨M, hM⟩ ≫ G.map a ≫ b) := by
  have hn := e.inv.naturality (ObjectProperty.homMk v : ⟨T, hT⟩ ⟶ ⟨M, hM⟩)
  change H.map v ≫ e.inv.app ⟨M, hM⟩ =
    e.inv.app ⟨T, hT⟩ ≫ G.map (F.map v) at hn
  rw [Functor.map_comp, ← Category.assoc, ← Category.assoc, ← hn,
    Category.assoc, Category.assoc]

private theorem transpose_paste {C D E : Type v} [Category.{w} C]
    [Category.{w} D] [Category.{w} E] (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    (Q : ObjectProperty C) (e : Q.ι ⋙ F ⋙ G ≅ Q.ι ⋙ H)
    {T U M N : C} (hT : Q T) (hM : Q M) {V V' : D} {K : E}
    (ehT : (H.obj T ⟶ K) ≃ (T ⟶ N))
    (ehM : (H.obj M ⟶ K) ≃ (M ⟶ N))
    (hn : ∀ (v : T ⟶ M) (b : H.obj M ⟶ K),
      ehT (H.map v ≫ b) = v ≫ ehM b)
    (v₁ : T ⟶ U) (v₂ : U ⟶ M) (t : V ⟶ V')
    (alpha : F.obj T ⟶ V) (beta : G.obj V ⟶ K)
    (a : F.obj M ⟶ V') (b : G.obj V' ⟶ K)
    (hv : F.map (v₁ ≫ v₂) ≫ a = alpha ≫ t)
    (ht : G.map t ≫ b = beta) :
    ehT (e.inv.app ⟨T, hT⟩ ≫ G.map alpha ≫ beta) =
      v₁ ≫ v₂ ≫ transposeComposition F G H Q hM ehM a b e := by
  unfold transposeComposition
  have hp := iso_naturality_paste F G H Q e hT hM (v₁ ≫ v₂) a b
  rw [hv, Functor.map_comp, Category.assoc, ht] at hp
  rw [hp, hn, Category.assoc]

private theorem homEquiv_congr (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g)
    [HasCompactification f] [HasCompactification g] [CompactSpace Y]
    {K : C A X} (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K)
    {L : C A Y} (hL : DerivedCategory.TStructure.t.plus L)
    (a : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K ⟶ L) :
    rightDerivedUpperShriekHomEquiv g hK hL
      ((rightDerivedLowerShriekCongr (ModuleCat.{u + 1} A) e.symm).hom.app K ≫ a) =
      rightDerivedUpperShriekHomEquiv f hK hL a ≫
        (rightDerivedUpperShriekCongr A e).hom.app L := by
  subst g
  simp only [rightDerivedLowerShriekCongr_rfl, rightDerivedUpperShriekCongr_rfl,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp, Category.comp_id]

private theorem composition_transpose (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace Y] [CompactSpace Z]
    {T : C A X} (hT : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X T)
    {V : C A Y} (hV : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y V)
    {L : C A Z} (hL : DerivedCategory.TStructure.t.plus L)
    (alpha : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj T ⟶ V)
    (beta : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).obj V ⟶ L) :
    rightDerivedUpperShriekHomEquiv (f ≫ g) hT hL
      ((originCompositionAmbient A f g).inv.app ⟨T, hT⟩ ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map alpha ≫ beta) =
      rightDerivedUpperShriekHomEquiv f hT hV.plus alpha ≫
        (rightDerivedUpperShriek A f).map
          (rightDerivedUpperShriekHomEquiv g hV hL beta) ≫
        compositionInverse A f g ⟨L, hL⟩ := by
  let t := rightDerivedUpperShriekHomEquiv g hV hL beta
  let v := rightDerivedUpperShriekHomEquiv f hT hV.plus alpha ≫
    (rightDerivedUpperShriek A f).map t
  have hv : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map v ≫
      rightDerivedUpperShriekCounit f _ (plus_rightDerivedUpperShriek_obj g hL) =
      alpha ≫ t := by
    rw [← rightDerivedUpperShriekHomEquiv_symm_apply f hT]
    change (rightDerivedUpperShriekHomEquiv f hT
      (plus_rightDerivedUpperShriek_obj g hL)).symm
        (rightDerivedUpperShriekHomEquiv f hT hV.plus alpha ≫
          (rightDerivedUpperShriek A f).map t) = _
    rw [rightDerivedUpperShriekHomEquiv_naturality_right_symm f hT hV.plus,
      Equiv.symm_apply_apply]
  have ht : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map t ≫
      rightDerivedUpperShriekCounit g L hL = beta := by
    simpa only [rightDerivedUpperShriekHomEquiv_symm_apply] using
      (rightDerivedUpperShriekHomEquiv g hV hL).symm_apply_apply beta
  unfold compositionInverse
  exact transpose_paste
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X)
    (originCompositionAmbient A f g) hT
    (plusEtaleOrigin_rightDerivedUpperShriek_obj f
      (plus_rightDerivedUpperShriek_obj g hL))
    (rightDerivedUpperShriekHomEquiv (f ≫ g) hT hL)
    (rightDerivedUpperShriekHomEquiv (f ≫ g)
      (plusEtaleOrigin_rightDerivedUpperShriek_obj f
        (plus_rightDerivedUpperShriek_obj g hL)) hL)
    (fun w c ↦ rightDerivedUpperShriekHomEquiv_naturality_left (f ≫ g) hT
      (plusEtaleOrigin_rightDerivedUpperShriek_obj f
        (plus_rightDerivedUpperShriek_obj g hL)) hL w c)
    (rightDerivedUpperShriekHomEquiv f hT hV.plus alpha)
    ((rightDerivedUpperShriek A f).map t) t alpha beta
    (rightDerivedUpperShriekCounit f _ (plus_rightDerivedUpperShriek_obj g hL))
    (rightDerivedUpperShriekCounit g L hL) hv ht

private theorem composition_transpose_congr
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (e : f ≫ g = h)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [HasCompactification h] [QuasiCompact f] [QuasiCompact g]
    [CompactSpace Y] [CompactSpace Z]
    {T : C A X} (hT : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X T)
    {V : C A Y} (hV : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y V)
    {L : C A Z} (hL : DerivedCategory.TStructure.t.plus L)
    (alpha : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj T ⟶ V)
    (beta : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).obj V ⟶ L) :
    rightDerivedUpperShriekHomEquiv h hT hL
      (((rightDerivedLowerShriekCongr (ModuleCat.{u + 1} A) e.symm).app T ≪≫
          (originCompositionAmbient A f g).symm.app ⟨T, hT⟩).hom ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map alpha ≫ beta) =
      rightDerivedUpperShriekHomEquiv f hT hV.plus alpha ≫
        (rightDerivedUpperShriek A f).map
          (rightDerivedUpperShriekHomEquiv g hV hL beta) ≫
        (compositionInverse A f g ⟨L, hL⟩ ≫
          (rightDerivedUpperShriekCongr A e).hom.app L) := by
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Category.assoc]
  rw [homEquiv_congr A (f := f ≫ g) (g := h) e]
  rw [composition_transpose A f g hT hV]
  simp only [Category.assoc]

/-- The specified coordinate exceptional compositor transposes the specified
compact-support compositor for an arbitrary earlier compact-support arrow.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, iterated affine-line adjunctions;
expanded parent proof Step 6
(blueprint: lem-pur-coordinate-adjunction-composition).

Proof: First eliminate e, so the terminal morphism is literally f followed by g.
Here f is zero B r, g is lastSection B r, h is zero B (r+1), and beta is
sectionArrow. Let t be the g-adjunct of beta and v the f-adjunct of alpha followed by f^!t.
The inverse-Hom-bijection formula and its naturality give
f_!v followed by the f-counit equal to alpha followed by t, and g_!t followed by
the g-counit equal to beta. Naturality of originCompositionAmbient at v now
identifies its inverse component followed by g_!alpha and beta with the composite
of (fg)_!v, the inverse component at f^!g^!L, and the two pasted counits.
Transpose through the composite Hom bijection. Its source naturality extracts v;
the remaining transpose is compositionInverse by its defining pasted-counit
formula. Restore e using the two congruence natural isomorphisms. This proof
uses only the recorded bounded-origin Hom bijections, never an unbounded
adjunction. Zero objects and empty schemes satisfy the same equations. -/
theorem coordinateAdjunction_composition (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ)
    (alpha : (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
      (zero B r)).obj (unit P n B) ⟶ target P n _ r) :
    let := tower_noetherian (setting P n) B aB r
    let := tower_noetherian (setting P n) B aB (r + 1)
    rightDerivedUpperShriekHomEquiv (zero B (r + 1)) (unit_origin P n B)
      (target_plus P n _ (towerBase aB (r + 1)) (r + 1))
      ((coordinateComposition P n B r).hom ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
          (lastSection B r)).map alpha ≫ sectionArrow P n B aB r) =
      rightDerivedUpperShriekHomEquiv (zero B r) (unit_origin P n B)
        (target_plus P n _ (towerBase aB r) r) alpha ≫
        (rightDerivedUpperShriek (setting P n).Coefficient
          (zero B r)).map (sectionAdjunct P n B aB r) ≫
        coordinateExceptionalComposition P n B aB r := by
  let := tower_noetherian (setting P n) B aB r
  let := tower_noetherian (setting P n) B aB (r + 1)
  unfold coordinateComposition coordinateExceptionalComposition sectionAdjunct
  exact composition_transpose_congr (setting P n).Coefficient
    (zero B r) (lastSection B r) (zero B (r + 1))
    (CoordinateTowerNormalization.zero_successor B r)
    (unit_origin P n B) (target_origin P n _ (towerBase aB r) r)
    (target_plus P n _ (towerBase aB (r + 1)) (r + 1)) alpha (sectionArrow P n B aB r)

end AlgebraicGeometry.ProEtale.AffineZeroPurity
