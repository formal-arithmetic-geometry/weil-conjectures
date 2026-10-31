/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineDifferenceTowerFactorization
public import WeilConjectures.SecSmoothPurity.FiniteEtaleDualizingNormalization
import WeilConjectures.AlgebraicGeometry.DualizingSigmaCocycleLocality
import all WeilConjectures.AlgebraicGeometry.SectionExceptionalFibreCoherence

/-! # Difference-coordinate first input restriction

Source: composition coherence Step 1
(blueprint: lem-pur-difference-first-input-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.DifferenceCoordinateSection
open WeilConjectures.PurityFiniteSetting.DiagonalPasting
open AlgebraicGeometry.AffineDifferenceTower
open FiniteEtaleNormalization

/-- Insert equality of structure maps into the specified normalized etale comparison.
Source: composition coherence Step 1, the comparisons E for the difference charts
(blueprint: lem-pur-difference-coordinate-section-identifications). -/
def normalizedE (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y B : Scheme.{u}} (v : X ⟶ Y) (h : Y ⟶ B) (h' : X ⟶ B)
    [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated h'] [LocallyOfFiniteType h'] [QuasiCompact h']
    [HasCompactification h] [HasCompactification h']
    (hv : h' = v ≫ h) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] :
    Etale.dualizingComplex P.Coefficient h' ≅
      (pull P v).obj (Etale.dualizingComplex P.Coefficient h) :=
  letI : B.Over (Spec (.of P.field.k)) := ⟨aB⟩
  letI : Y.Over (Spec (.of P.field.k)) := ⟨h ≫ aB⟩
  letI : X.Over (Spec (.of P.field.k)) := ⟨h' ≫ aB⟩
  letI : h.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : h'.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : v.IsOver (Spec (.of P.field.k)) :=
    ⟨(Category.assoc v h aB).symm.trans (congrArg (fun t ↦ t ≫ aB) hv.symm)⟩
  letI : LocallyOfFiniteType (B ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aB)
  letI : QuasiCompact (B ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aB)
  letI : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (h ≫ aB))
  letI : QuasiCompact (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (h ≫ aB))
  letI : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (h' ≫ aB))
  letI : QuasiCompact (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (h' ≫ aB))
  (FiniteEtaleNormalization.congr P h' (v ≫ h) hv).app
      (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) B) ≪≫
    sourceEtale P v h


/-- Normalized source-etale base change, with named equal structure maps. The source-base-change
clause of the existing locality theorem gives the equality after equality substitution.
Source: composition coherence Step 1 (blueprint: lem-pur-difference-first-input-restriction). -/
private theorem normalized_base_change
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y X₀ Y₀ U U₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [U₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (U₀ ↘ Spec (.of P.field.k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dh : ℕ) [SmoothOfRelativeDimension dh h]
    (h₀ : X₀ ⟶ Y₀) [h₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₀] [LocallyOfFiniteType h₀] [QuasiCompact h₀]
    (dh₀ : ℕ) [SmoothOfRelativeDimension dh₀ h₀]
    (v : Y₀ ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (u : X₀ ⟶ X) [u.IsOver (Spec (.of P.field.k))]
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    (e₀ : U₀ ⟶ X₀) [e₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated e₀] [LocallyOfFiniteType e₀] [QuasiCompact e₀]
    [Etale e₀]
    (u₁ : U₀ ⟶ U) [u₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated u₁] [LocallyOfFiniteType u₁] [QuasiCompact u₁]
    (sqh : IsPullback u h₀ h v) (sqe : IsPullback u₁ e₀ e u)
    (p : U ⟶ Y) [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (p₀ : U₀ ⟶ Y₀) [IsSeparated p₀] [LocallyOfFiniteType p₀] [QuasiCompact p₀]
    [HasCompactification h] [HasCompactification h₀]
    [HasCompactification p] [HasCompactification p₀]
    (hp : p = e ≫ h) (hp₀ : p₀ = e₀ ≫ h₀)
    (sqp : IsPullback u₁ p₀ p v) :
    Etale.dualizingComplexBaseChangeMap P.Coefficient sqp ≫
        (normalizedE P e₀ h₀ p₀ hp₀ (Y₀ ↘ Spec (.of P.field.k))).hom =
      (pull P u₁).map (normalizedE P e h p hp (Y ↘ Spec (.of P.field.k))).hom ≫
        (DualizingLocality.pullSquare P u₁ e₀ e u sqe.toCommSq).hom.app (omega P h) ≫
        (pull P e₀).map (Etale.dualizingComplexBaseChangeMap P.Coefficient sqh) := by
  subst p
  subst p₀
  have hb := (DualizingLocality.dualizing_sigma_cocycle_locality P).2.2.2.1
    h dh h₀ dh₀ v u e e₀ u₁ sqh sqe
  simp only [normalizedE, Iso.trans_hom, Iso.app_hom, FiniteEtaleNormalization.congr,
    Etale.unboundedEtaleLowerShriekCongr, conjugateIsoEquiv_apply_hom, Iso.refl_hom,
    conjugateEquiv_id, NatTrans.id_app, FiniteEtaleNormalization.beta, baseChange,
    Etale.dualizingComplexBaseChangeMap, exceptional, coefficientUnit, omega,
    Category.assoc] at hb ⊢
  erw [Category.id_comp, Category.id_comp]
  exact hb

/-- The raw dualizing base-change composition law with named composite arrows. Substitute those
names and apply the existing mate-pasting calculation.
Source: composition coherence Step 1 (blueprint: lem-pur-difference-first-input-restriction). -/
private theorem dualizing_base_comp_named
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (a : X'' ⟶ X) (b : Y'' ⟶ Y) (ha : a = w' ≫ v') (hb : b = w ≫ v)
    (sq : IsPullback a f'' f b) :
    Etale.dualizingComplexBaseChangeMap A sq =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v' a ha).hom.app
        (Etale.dualizingComplex A f) ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctor.map
        (Etale.dualizingComplexBaseChangeMap A sq₁) ≫
      Etale.dualizingComplexBaseChangeMap A sq₂ := by
  subst a
  subst b
  exact Etale.dualizing_base_comp A sq₁ sq₂

/-- The identity-square base-change map is the inverse-image unit comparison. Apply pasting to
two identity squares, cancel their invertible base-change map, and use unit naturality.
Source: composition coherence Step 1 (blueprint: lem-pur-difference-first-input-restriction). -/
private theorem dualizing_base_id
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f]
    [IsIso (Etale.dualizingComplexBaseChangeMap A (IsPullback.id_horiz f))] :
    Etale.dualizingComplexBaseChangeMap A (IsPullback.id_horiz f) =
      (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app
        (Etale.dualizingComplex A f) := by
  let b := Etale.dualizingComplexBaseChangeMap A (IsPullback.id_horiz f)
  let C := Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (𝟙 X) (𝟙 X) (𝟙 X) (Category.id_comp _).symm
  let I := Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) X
  have hp : b = C.hom.app _ ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) (𝟙 X)).leftDerivedFunctor.map b ≫ b := by
    exact dualizing_base_comp_named A (IsPullback.id_horiz f)
      (IsPullback.id_horiz f) (𝟙 X) (𝟙 Y)
      (Category.id_comp _).symm (Category.id_comp _).symm (IsPullback.id_horiz f)
  have he : 𝟙 _ = C.hom.app _ ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) (𝟙 X)).leftDerivedFunctor.map b := by
    apply (cancel_mono b).1
    simpa only [Category.id_comp, Category.assoc] using hp
  have hn := I.hom.naturality b
  have hu := Etale.leftDerivedUpperStarComp_id_left_hom_app
    (ModuleCat.{u + 1} A) (𝟙 X) (Etale.dualizingComplex A f)
  have hh : C.hom.app _ ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) (𝟙 X)).leftDerivedFunctor.map b ≫
      I.hom.app _ = b := by
    rw [hn, ← Category.assoc, hu, Category.id_comp, Functor.id_map]
  change b = I.hom.app _
  rw [← hh, ← Category.assoc, ← he, Category.id_comp]

/-- Pullback of the projection square along a section gives inverse base change. Paste the two
squares to the identity square and use the preceding unit normalization. Restrict once more
and apply compositor naturality, associativity, and the right unit law.
Source: composition coherence Step 1 (blueprint: lem-pur-difference-first-input-restriction). -/
private theorem projection_retraction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {D B E S : Scheme.{u}}
    [IsNoetherian D] [IsNoetherian B] [IsNoetherian E] [IsNoetherian S]
    (p : D ⟶ B) (q : D ⟶ E) (r : B ⟶ S) (v : E ⟶ S)
    (k : B ⟶ D) (z : S ⟶ E)
    [IsSeparated r] [LocallyOfFiniteType r] [QuasiCompact r]
    [HasCompactification r] [HasCompactification q] [QuasiCompact q]
    (sq : IsPullback p q r v) (sqk : IsPullback k r q z)
    (hkp : k ≫ p = 𝟙 B) (hzv : z ≫ v = 𝟙 S)
    [IsIso (Etale.dualizingComplexBaseChangeMap A sq)]
    [IsIso (Etale.dualizingComplexBaseChangeMap A (IsPullback.id_horiz r))]
    (a : S ⟶ B) (b : S ⟶ D) (hak : a ≫ k = b) (hbp : b ≫ p = a) :
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a k b hak.symm).hom.app
        (Etale.dualizingComplex A q) ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) a).leftDerivedFunctor.map
        (Etale.dualizingComplexBaseChangeMap A sqk) =
    (Etale.upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.map
        (inv (Etale.dualizingComplexBaseChangeMap A sq)) ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b p a hbp.symm).inv.app
        (Etale.dualizingComplex A r) := by
  let L := fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦
    (Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
  have hp := dualizing_base_comp_named A sq sqk (𝟙 B) (𝟙 S)
    hkp.symm hzv.symm (IsPullback.id_horiz r)
  rw [dualizing_base_id] at hp
  have hb : Etale.dualizingComplexBaseChangeMap A sqk =
      (L k).map (inv (Etale.dualizingComplexBaseChangeMap A sq)) ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) k p (𝟙 B) hkp.symm).inv.app _ ≫
        (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) B).hom.app _ := by
    rw [hp]
    simp only [Functor.map_inv, Iso.inv_hom_id_app_assoc]
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [hb]
  simp only [Functor.map_comp]
  have hn := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a k b hak.symm).hom.naturality
    (inv (Etale.dualizingComplexBaseChangeMap A sq))
  have hc := Etale.leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarComp_inv_app
    (ModuleCat.{u + 1} A) a k p b (𝟙 B) a hak.symm hkp.symm hbp.symm
    (Etale.dualizingComplex A r)
  change (L b).map _ ≫ _ = _ ≫ (L a).map ((L k).map _) at hn
  rw [← reassoc_of% hn, reassoc_of% hc]
  rw [Etale.leftDerivedUpperStarComp_id_right_hom_app, Category.comp_id]

/-- Restrict a normalized base-change square along a compatible section. Expand the square
comparison, use two compositor associativity equations, and cancel the invertible base map.
Source: composition coherence Step 1 (blueprint: lem-pur-difference-first-input-restriction). -/
private theorem restrict_source_square
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {W R W₀ A U : Scheme.{u}}
    (i : W₀ ⟶ W) (H : W ⟶ R) (E : W₀ ⟶ A) (l : A ⟶ R)
    (D : U ⟶ W₀) (t : U ⟶ W) (z : U ⟶ A)
    (ht : D ≫ i = t) (hz : D ≫ E = z) (sq : CommSq i E H l)
    {M : Etale.DerivedCategoryModule P.Coefficient W}
    {N : Etale.DerivedCategoryModule P.Coefficient R}
    {M₀ : Etale.DerivedCategoryModule P.Coefficient W₀}
    {N₀ : Etale.DerivedCategoryModule P.Coefficient A}
    (α : M ⟶ (pull P H).obj N) (α₀ : M₀ ⟶ (pull P E).obj N₀)
    (b : (pull P i).obj M ⟶ M₀) [IsIso b]
    (c : (pull P l).obj N ⟶ N₀)
    (hb : b ≫ α₀ = (pull P i).map α ≫
      (DualizingLocality.pullSquare P i E H l sq).hom.app N ≫ (pull P E).map c) :
    (pull P D).map α₀ ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          D E z hz.symm).inv.app N₀ =
      (pull P D).map (inv b) ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          D i t ht.symm).inv.app M ≫
        (pull P t).map α ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          t H (z ≫ l) (by rw [← ht, Category.assoc, sq.w, ← Category.assoc, hz])).inv.app N ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) z l).hom.app N ≫
        (pull P z).map c := by
  have hcomp : z ≫ l = t ≫ H := by
    rw [← ht, Category.assoc, sq.w, ← Category.assoc, hz]
  have h₁ := Etale.leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarComp_inv_app
    (ModuleCat.{u + 1} P.Coefficient) D i H t (E ≫ l) (z ≫ l)
    ht.symm sq.w.symm hcomp N
  have h₂ := Etale.map_leftDerivedUpperStarComp_hom_app_leftDerivedUpperStarComp_inv_app
    (ModuleCat.{u + 1} P.Coefficient) D E l z (E ≫ l) (z ≫ l)
    hz.symm rfl rfl N
  have hs : (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) D i t ht.symm).hom.app
        ((pull P H).obj N) ≫
      (pull P D).map ((DualizingLocality.pullSquare P i E H l sq).hom.app N) ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) D E z hz.symm).inv.app
        ((pull P l).obj N) =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        t H (z ≫ l) hcomp).inv.app N ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) z l).hom.app N := by
    simp only [DualizingLocality.pullSquare, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.map_comp, Category.assoc]
    rw [reassoc_of% h₁, h₂]
    simp only [Iso.hom_inv_id_app_assoc]
  have hn₂ := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    D E z hz.symm).inv.naturality
     c
  change (pull P D).map ((pull P E).map c) ≫ _ =
    _ ≫ (pull P z).map c at hn₂
  rw [← cancel_epi ((pull P D).map b)]
  simp only [← Functor.map_comp_assoc, IsIso.hom_inv_id]
  erw [(pull P D).map_id, Category.id_comp]
  rw [hb]
  simp only [Functor.map_comp, Category.assoc]
  rw [hn₂]
  rw [← cancel_epi ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    D i t ht.symm).hom.app M)]
  simp only [Iso.hom_inv_id_app_assoc]
  have hn₃ := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    D i t ht.symm).hom.naturality
     α
  change (pull P t).map α ≫ _ = _ ≫ (pull P D).map ((pull P i).map α) at hn₃
  rw [← reassoc_of% hn₃, reassoc_of% hs]

/-- Substitute a pasted base-change calculation into the section transport. Two compositor
associativity equations and naturality cancel the base-change isomorphism with its inverse.
Source: composition coherence Step 1 (blueprint: lem-pur-difference-first-input-restriction). -/
private theorem tower_section_transport
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U W R B D : Scheme.{u}}
    (t : U ⟶ W) (H : W ⟶ R) (J : R ⟶ D) (F : W ⟶ D)
    (z : U ⟶ B) (l : B ⟶ R) (k : B ⟶ D)
    (b : U ⟶ D) (h : U ⟶ R)
    (hF : F = H ≫ J) (hk : k = l ≫ J)
    (ht : h = t ≫ H) (hz : h = z ≫ l)
    (htF : b = t ≫ F) (hzk : b = z ≫ k)
    {M : Etale.DerivedCategoryModule P.Coefficient R}
    {K : Etale.DerivedCategoryModule P.Coefficient D}
    {N : Etale.DerivedCategoryModule P.Coefficient B}
    (β : (pull P J).obj K ⟶ M) [IsIso β]
    (c : (pull P l).obj M ⟶ N)
    (δ : (pull P b).obj K ⟶ (pull P z).obj N)
    (hp : δ =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        z k b hzk).hom.app K ≫
      (pull P z).map ((Etale.leftDerivedUpperStarComp
        (ModuleCat.{u + 1} P.Coefficient) l J k hk).hom.app K) ≫
      (pull P z).map ((pull P l).map β) ≫ (pull P z).map c) :
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        t H h ht).inv.app M ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        z l h hz).hom.app M ≫ (pull P z).map c =
    (pull P t).map ((pull P H).map (inv β)) ≫
      (pull P t).map ((Etale.leftDerivedUpperStarComp
        (ModuleCat.{u + 1} P.Coefficient) H J F hF).inv.app K) ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        t F b htF).inv.app K ≫ δ := by
  have hfinal : b = h ≫ J := by rw [ht, Category.assoc, ← hF, htF]
  have h₁ := Etale.map_leftDerivedUpperStarComp_inv_app_leftDerivedUpperStarComp_inv_app
    (ModuleCat.{u + 1} P.Coefficient) t H J h F b ht hF hfinal K
  have h₂ := Etale.leftDerivedUpperStarComp_assoc'_app
    (ModuleCat.{u + 1} P.Coefficient) z l J h k b hz hk hfinal K
  have hn₁ := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    t H h ht).inv.naturality
     (inv β)
  have hn₂ := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    z l h hz).hom.naturality
     (inv β)
  change (pull P t).map ((pull P H).map (inv β)) ≫ _ =
    _ ≫ (pull P h).map (inv β) at hn₁
  change (pull P h).map (inv β) ≫ _ =
    _ ≫ (pull P z).map ((pull P l).map (inv β)) at hn₂
  rw [hp]
  rw [reassoc_of% h₁, reassoc_of% h₂]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% hn₁, reassoc_of% hn₂]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, IsIso.inv_hom_id]
  erw [(pull P l).map_id, Category.id_comp]

set_option linter.unusedVariables false in
set_option maxHeartbeats 1000000 in
-- The factorization conjunction and explicit compositor terms need additional elaboration.
/-- The first diagonal input in etale-origin coordinates.
Source: composition coherence Step 1, refined input calculation, Steps 2--4 of
lem-pur-difference-coordinate-section-identifications
(blueprint: lem-pur-difference-first-input-restriction).

Proof: paste the Cartesian squares for q along G and s. Horizontal compact-support
exchange and mate pasting identify beta(q_Q,s) after l-pullback of beta(q,G) with
beta(q,z_e). Paste the projection square with the zero section; P_e z_e = id makes
beta(q,z_e) inverse to k-pullback of beta(P_d,P_e). These particular maps are
invertible by smooth base change. Restrict along z_d to obtain the displayed delta.
Next apply normalized source-etale base change to (q_Q,H,s). Its base-changed
etale arrow is H_f, since H i = l H_f. Pull along Delta_f, use i Delta_f = t and
H_f Delta_f = z_d, and precompose with the inverse of the specified beta(a,s).
Substitute the projection calculation and use H t = l z_d. Pullback associativity
and naturality put every compositor in exactly the displayed firstRoute order.
The actual translated coordinates prove the scheme equalities; this also covers
empty schemes and either zero block, using P_e z_e = id in that direction. -/
theorem difference_first_input_restriction
    (P : WeilConjectures.PurityFiniteSetting.{u}) {U V T : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))] [V.Over (Spec (.of P.field.k))]
    [T.Over (Spec (.of P.field.k))]
    [IsAffine U] [IsAffine V] [IsAffine T]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of P.field.k))]
    [QuasiCompact (V ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (f : U ⟶ V) (g : V ⟶ T)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (x : U ⟶ A d V) (y : V ⟶ A e T) [Etale x] [Etale y]
    (hx : x ≫ pr d V = f) (hy : y ≫ pr e T = g) :
    (by
      letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
      letI := LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of P.field.k))
      letI := LocallyOfFiniteType.isLocallyNoetherian (V ↘ Spec (.of P.field.k))
      letI := LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of P.field.k))
      letI : IsNoetherian U := ⟨⟩
      letI : IsNoetherian V := ⟨⟩
      letI : IsNoetherian T := ⟨⟩
      let fac := factorization (k := P.field.k) f g d e x y hx hy
      let hHJ := fac.1
      let hHa := fac.2.1
      let hGpr := fac.2.2.1
      let hJq := fac.2.2.2.1
      let hGs := fac.2.2.2.2.1
      let hFt := fac.2.2.2.2.2.1
      let fac1 := fac.2.2.2.2.2.2.2.2
      let hFpr := fac1.1
      let hGe := fac1.2.1
      let hGsep := fac1.2.2.1
      let hGlft := fac1.2.2.2.1
      let hGqc := fac1.2.2.2.2.1
      let hHe := fac1.2.2.2.2.2.1
      let hHsep := fac1.2.2.2.2.2.2.1
      let hHlft := fac1.2.2.2.2.2.2.2.1
      let fac2 := fac1.2.2.2.2.2.2.2.2
      let hHqc := fac2.1
      let hJe := fac2.2.1
      let hJsep := fac2.2.2.1
      let hJlft := fac2.2.2.2.1
      let hJqc := fac2.2.2.2.2.1
      let hFe := fac2.2.2.2.2.2.1
      let hFsep := fac2.2.2.2.2.2.2.1
      let hFlft := fac2.2.2.2.2.2.2.2.1
      let fac3 := fac2.2.2.2.2.2.2.2.2
      let hFqc := fac3.1
      let hQa := fac3.2.1
      let hWa := fac3.2.2.1
      let hRa := fac3.2.2.2.1
      let hWfa := fac3.2.2.2.2.1
      let hWga := fac3.2.2.2.2.2.1
      let hAda := fac3.2.2.2.2.2.2.1
      let hAea := fac3.2.2.2.2.2.2.2.1
      let fac4 := fac3.2.2.2.2.2.2.2.2
      let hAdea := fac4.1
      let hAdVa := fac4.2.1
      let hAeTa := fac4.2.2.1
      let hAeVa := fac4.2.2.2.1
      let fac5 := fac4.2.2.2.2.2.2.2.2
      let hRsq := fac5.1
      let hAffsq := fac5.2.1
      let hsq := fac5.2.2.1
      let hPe := fac5.2.2.2.1
      let hPde := fac5.2.2.2.2.1
      let hqQ := fac5.2.2.2.2.2.1
      let hHsq := fac5.2.2.2.2.2.2.1
      let hGsq := fac5.2.2.2.2.2.2.2.1
      let fac6 := fac5.2.2.2.2.2.2.2.2
      let hHfe := fac6.1
      let hGge := fac6.2.1
      let hHfz := fac6.2.2.1
      let hGgz := fac6.2.2.2
      letI := hGe
      letI := hGsep
      letI := hGlft
      letI := hGqc
      letI := hHe
      letI := hHsep
      letI := hHlft
      letI := hHqc
      letI := hJe
      letI := hJsep
      letI := hJlft
      letI := hJqc
      letI := hFe
      letI := hFsep
      letI := hFlft
      letI := hFqc
      letI := hQa
      letI := hWa
      letI := hRa
      letI := hWfa
      letI := hWga
      letI := hAda
      letI := hAea
      letI := hAdea
      letI := hAdVa
      letI := hAeTa
      letI := hAeVa
      letI := hsq
      letI := hPe
      letI := hPde
      letI := hqQ
      letI := hHfe
      letI := hGge
      letI := (geometryProperties d e f g).1
      letI := (geometryProperties d e f g).2.1
      letI := (geometryProperties d e f g).2.2.1
      letI := (geometryProperties d e f g).2.2.2.1
      letI := (geometryProperties d e f g).2.2.2.2
      letI := affineDimension d U
      letI := affineDimension e V
      letI := affineDimension (d + e) U
      let aU := U ↘ Spec (.of P.field.k)
      let aV := V ↘ Spec (.of P.field.k)
      let aT := T ↘ Spec (.of P.field.k)
      let aQ := pullback.fst (f ≫ g) g ≫ aU
      let t := pullback.diagonal (f ≫ g)
      let G := differenceSecond e f g y
      let HH := H f g x
      let JJ := J d f g y
      let FF := differenceTotal d e f g x y
      let qQ := R d f g ↘ Q f g
      let hHfpr : pullback.fst f f = differenceFirst d f x ≫ pr d U :=
        (AffineSpace.homOfVector_over _ _).symm
      let hGgpr : pullback.fst g g = differenceFirst e g y ≫ pr e V :=
        (AffineSpace.homOfVector_over _ _).symm
      let chiF := (pull P (pullback.diagonal f)).map
        (normalizedE P (differenceFirst d f x) (pr d U) (pullback.fst f f)
          hHfpr aU).hom ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          (pullback.diagonal f) (differenceFirst d f x) (zero d U) hHfz.symm).inv.app _
      letI := (affineGeometry d e U).2.2.2.2.2.1
      letI := (affineGeometry d e U).2.2.2.2.2.2.1
      letI := (affineGeometry d e U).2.2.2.2.2.2.2.1
      let delta :=
        (pull P (zero (d + e) U)).map
          (WeilConjectures.PurityFiniteSetting.DiagonalPasting.beta P.Coefficient P d
            hAffsq (pr d U ≫ aU)).inv ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          (zero (d + e) U) (first d e U) (zero d U)
          (affineGeometry d e U).2.1.symm).inv.app _
      let firstRoute := (gammaF P.Coefficient P d f g aT).hom ≫
        (pull P t).map
          ((normalizedE P HH qQ (a f g) hHa.symm aQ).hom ≫
            (pull P HH).map
              (WeilConjectures.PurityFiniteSetting.DiagonalPasting.beta P.Coefficient P d
                hRsq (pr (d + e) U ≫ aU)).inv ≫
            (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
              HH JJ FF hHJ.symm).inv.app _) ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          t FF (zero (d + e) U) hFt.symm).inv.app _ ≫ delta
      exact chiF = firstRoute
      : Prop) := by
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  let := LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of P.field.k))
  let := LocallyOfFiniteType.isLocallyNoetherian (V ↘ Spec (.of P.field.k))
  let := LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of P.field.k))
  let : IsNoetherian U := ⟨⟩
  let : IsNoetherian V := ⟨⟩
  let : IsNoetherian T := ⟨⟩
  let fac := factorization (k := P.field.k) f g d e x y hx hy
  let hHJ := fac.1
  let hHa := fac.2.1
  let hGpr := fac.2.2.1
  let hJq := fac.2.2.2.1
  let hGs := fac.2.2.2.2.1
  let hFt := fac.2.2.2.2.2.1
  let fac1 := fac.2.2.2.2.2.2.2.2
  let hFpr := fac1.1
  let hGe := fac1.2.1
  let hGsep := fac1.2.2.1
  let hGlft := fac1.2.2.2.1
  let hGqc := fac1.2.2.2.2.1
  let hHe := fac1.2.2.2.2.2.1
  let hHsep := fac1.2.2.2.2.2.2.1
  let hHlft := fac1.2.2.2.2.2.2.2.1
  let fac2 := fac1.2.2.2.2.2.2.2.2
  let hHqc := fac2.1
  let hJe := fac2.2.1
  let hJsep := fac2.2.2.1
  let hJlft := fac2.2.2.2.1
  let hJqc := fac2.2.2.2.2.1
  let hFe := fac2.2.2.2.2.2.1
  let hFsep := fac2.2.2.2.2.2.2.1
  let hFlft := fac2.2.2.2.2.2.2.2.1
  let fac3 := fac2.2.2.2.2.2.2.2.2
  let hFqc := fac3.1
  let hQa := fac3.2.1
  let hWa := fac3.2.2.1
  let hRa := fac3.2.2.2.1
  let hWfa := fac3.2.2.2.2.1
  let hWga := fac3.2.2.2.2.2.1
  let hAda := fac3.2.2.2.2.2.2.1
  let hAea := fac3.2.2.2.2.2.2.2.1
  let fac4 := fac3.2.2.2.2.2.2.2.2
  let hAdea := fac4.1
  let hAdVa := fac4.2.1
  let hAeTa := fac4.2.2.1
  let hAeVa := fac4.2.2.2.1
  let fac5 := fac4.2.2.2.2.2.2.2.2
  let hRsq := fac5.1
  let hAffsq := fac5.2.1
  let hsq := fac5.2.2.1
  let hPe := fac5.2.2.2.1
  let hPde := fac5.2.2.2.2.1
  let hqQ := fac5.2.2.2.2.2.1
  let hHsq := fac5.2.2.2.2.2.2.1
  let hGsq := fac5.2.2.2.2.2.2.2.1
  let fac6 := fac5.2.2.2.2.2.2.2.2
  let hHfe := fac6.1
  let hGge := fac6.2.1
  let hHfz := fac6.2.2.1
  let hGgz := fac6.2.2.2
  let := hGe
  let := hGsep
  let := hGlft
  let := hGqc
  let := hHe
  let := hHsep
  let := hHlft
  let := hHqc
  let := hJe
  let := hJsep
  let := hJlft
  let := hJqc
  let := hFe
  let := hFsep
  let := hFlft
  let := hFqc
  let := hQa
  let := hWa
  let := hRa
  let := hWfa
  let := hWga
  let := hAda
  let := hAea
  let := hAdea
  let := hAdVa
  let := hAeTa
  let := hAeVa
  let := hsq
  let := hPe
  let := hPde
  let := hqQ
  let := hHfe
  let := hGge
  let := (geometryProperties d e f g).1
  let := (geometryProperties d e f g).2.1
  let := (geometryProperties d e f g).2.2.1
  let := (geometryProperties d e f g).2.2.2.1
  let := (geometryProperties d e f g).2.2.2.2
  let := affineDimension d U
  let := affineDimension e V
  let := affineDimension (d + e) U
  let aU := U ↘ Spec (.of P.field.k)
  let aV := V ↘ Spec (.of P.field.k)
  let aT := T ↘ Spec (.of P.field.k)
  let aQ := pullback.fst (f ≫ g) g ≫ aU
  let t := pullback.diagonal (f ≫ g)
  let G := differenceSecond e f g y
  let HH := H f g x
  let JJ := J d f g y
  let FF := differenceTotal d e f g x y
  let qQ := R d f g ↘ Q f g
  let hHfpr : pullback.fst f f = differenceFirst d f x ≫ pr d U :=
    (AffineSpace.homOfVector_over _ _).symm
  let hGgpr : pullback.fst g g = differenceFirst e g y ≫ pr e V :=
    (AffineSpace.homOfVector_over _ _).symm
  let chiF := (pull P (pullback.diagonal f)).map
    (normalizedE P (differenceFirst d f x) (pr d U) (pullback.fst f f)
      hHfpr aU).hom ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      (pullback.diagonal f) (differenceFirst d f x) (zero d U) hHfz.symm).inv.app _
  let := (affineGeometry d e U).2.2.2.2.2.1
  let := (affineGeometry d e U).2.2.2.2.2.2.1
  let := (affineGeometry d e U).2.2.2.2.2.2.2.1
  let delta :=
    (pull P (zero (d + e) U)).map
      (WeilConjectures.PurityFiniteSetting.DiagonalPasting.beta P.Coefficient P d
        hAffsq (pr d U ≫ aU)).inv ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      (zero (d + e) U) (first d e U) (zero d U)
      (affineGeometry d e U).2.1.symm).inv.app _
  let firstRoute := (gammaF P.Coefficient P d f g aT).hom ≫
    (pull P t).map
      ((normalizedE P HH qQ (a f g) hHa.symm aQ).hom ≫
        (pull P HH).map
          (WeilConjectures.PurityFiniteSetting.DiagonalPasting.beta P.Coefficient P d
            hRsq (pr (d + e) U ≫ aU)).inv ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          HH JJ FF hHJ.symm).inv.app _) ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      t FF (zero (d + e) U) hFt.symm).inv.app _ ≫ delta
  change chiF = firstRoute
  let l := includeR d f g
  let k := l ≫ JJ
  let sqr : IsPullback l (pr d U) qQ (s f g) := AffineSpace.isPullback_map (s f g)
  let sqk : IsPullback k (pr d U) (q d e U) (zero e U) := by
    simpa only [← hGs] using sqr.paste_horiz hRsq
  have hkp : k ≫ first d e U = 𝟙 (A d U) := by
    apply AffineSpace.hom_ext
    · simp [k, l, JJ, includeR, J, first, s]
    · rintro ⟨j⟩
      simp [k, l, JJ, includeR, J, first]
  have hzk : zero d U ≫ k = zero (d + e) U := by
    have hi : zero d U ≫ l = t ≫ HH := by
      change AffineSpace.zeroSection (Coords d) U ≫ l = t ≫ HH
      rw [← hHfz, Category.assoc, hHsq.w, ← Category.assoc,
        (geometry f g).2.2.2.2.1]
    change zero d U ≫ (l ≫ JJ) = _
    rw [← Category.assoc, hi, Category.assoc, hHJ, hFt]
  let : (Q f g).Over (Spec (.of P.field.k)) := ⟨aQ⟩
  let : (R d f g).Over (Spec (.of P.field.k)) := ⟨qQ ≫ aQ⟩
  let : (W f g).Over (Spec (.of P.field.k)) := ⟨a f g ≫ aQ⟩
  let : (pullback f f).Over (Spec (.of P.field.k)) := ⟨pullback.fst f f ≫ aU⟩
  let : (A d U).Over (Spec (.of P.field.k)) := ⟨pr d U ≫ aU⟩
  let : LocallyOfFiniteType (Q f g ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aQ)
  let : QuasiCompact (Q f g ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact aQ)
  let : LocallyOfFiniteType (R d f g ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (qQ ≫ aQ))
  let : QuasiCompact (R d f g ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (qQ ≫ aQ))
  let : LocallyOfFiniteType (W f g ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (a f g ≫ aQ))
  let : QuasiCompact (W f g ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (a f g ≫ aQ))
  let : LocallyOfFiniteType (pullback f f ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst f f ≫ aU))
  let : QuasiCompact (pullback f f ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (pullback.fst f f ≫ aU))
  let : LocallyOfFiniteType (A d U ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pr d U ≫ aU))
  let : QuasiCompact (A d U ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (pr d U ≫ aU))
  let : qQ.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : (pr d U).IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  have hsQ : s f g ≫ aQ = aU := by
    change s f g ≫ (pullback.fst (f ≫ g) g ≫ aU) = aU
    rw [← Category.assoc, show s f g ≫ pullback.fst (f ≫ g) g = 𝟙 U by
      simp only [s, pullback.lift_fst]]
    exact Category.id_comp aU
  let : (s f g).IsOver (Spec (.of P.field.k)) := ⟨hsQ⟩
  let : l.IsOver (Spec (.of P.field.k)) := ⟨by
    change l ≫ (qQ ≫ aQ) = pr d U ≫ aU
    rw [← Category.assoc, sqr.w, Category.assoc, hsQ]⟩
  let : HH.IsOver (Spec (.of P.field.k)) := ⟨by
    change HH ≫ (qQ ≫ aQ) = a f g ≫ aQ
    rw [← Category.assoc, hHa]⟩
  let : (differenceFirst d f x).IsOver (Spec (.of P.field.k)) := ⟨by
    change differenceFirst d f x ≫ (pr d U ≫ aU) = pullback.fst f f ≫ aU
    rw [← Category.assoc, ← hHfpr]⟩
  let : (i f g).IsOver (Spec (.of P.field.k)) := ⟨by
    change i f g ≫ (a f g ≫ aQ) = pullback.fst f f ≫ aU
    rw [← Category.assoc, (geometry f g).1.w, Category.assoc, hsQ]⟩
  let : IsSeparated (s f g) := inferInstance
  let : LocallyOfFiniteType (s f g ≫ aQ) := by
    rw [hsQ]
    infer_instance
  let : LocallyOfFiniteType (s f g) := locallyOfFiniteType_of_comp (s f g) aQ
  let : QuasiCompact (s f g) := inferInstance
  let : IsSeparated l := MorphismProperty.of_isPullback sqr.flip inferInstance
  let : LocallyOfFiniteType l := MorphismProperty.of_isPullback sqr.flip inferInstance
  let : QuasiCompact l := MorphismProperty.of_isPullback sqr.flip inferInstance
  let : IsSeparated (i f g) :=
    MorphismProperty.of_isPullback (geometry f g).1.flip inferInstance
  let : LocallyOfFiniteType (i f g) :=
    MorphismProperty.of_isPullback (geometry f g).1.flip inferInstance
  let : QuasiCompact (i f g) :=
    MorphismProperty.of_isPullback (geometry f g).1.flip inferInstance
  have hb := normalized_base_change P qQ d (pr d U) d (s f g) l HH
    (differenceFirst d f x) (i f g) sqr hHsq.flip (a f g)
    (pullback.fst f f) hHa.symm hHfpr (geometry f g).1
  let := betaIsIso P.Coefficient P d hAffsq (pr d U ≫ aU)
  let := betaIsIso P.Coefficient P d (IsPullback.id_horiz (pr d U)) (pr d U ≫ aU)
  let := betaIsIso P.Coefficient P d hRsq (pr (d + e) U ≫ aU)
  let := betaIsIso P.Coefficient P d (geometry f g).1
    (pullback.fst (f ≫ g) (f ≫ g) ≫ (f ≫ g) ≫ aT)
  have hproj := projection_retraction P.Coefficient (first d e U) (q d e U)
    (pr d U) (pr e U) k (zero e U) hAffsq sqk hkp
    (AffineSpace.zeroSection_comp_over (Coords e) U) (zero d U) (zero (d + e) U)
    hzk (affineGeometry d e U).2.1
  have hpaste := dualizing_base_comp_named P.Coefficient hRsq sqr k (zero e U)
    rfl hGs.symm sqk
  rw [hpaste] at hproj
  simp only [Functor.map_comp] at hproj
  have hp : delta =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        (zero d U) k (zero (d + e) U) hzk.symm).hom.app _ ≫
      (pull P (zero d U)).map ((Etale.leftDerivedUpperStarComp
        (ModuleCat.{u + 1} P.Coefficient) l JJ k rfl).hom.app _) ≫
      (pull P (zero d U)).map ((pull P l).map
        (Etale.dualizingComplexBaseChangeMap P.Coefficient hRsq)) ≫
      (pull P (zero d U)).map
        (Etale.dualizingComplexBaseChangeMap P.Coefficient sqr) := by
    simpa only [delta, WeilConjectures.PurityFiniteSetting.DiagonalPasting.beta,
      asIso_inv] using hproj.symm
  have hHt : zero d U ≫ l = t ≫ HH := by
    change AffineSpace.zeroSection (Coords d) U ≫ l = t ≫ HH
    rw [← hHfz, Category.assoc, hHsq.w, ← Category.assoc,
      (geometry f g).2.2.2.2.1]
  have hc := tower_section_transport P t HH JJ FF (zero d U) l k (zero (d + e) U)
    (zero d U ≫ l) hHJ.symm rfl hHt rfl hFt.symm hzk.symm
    (Etale.dualizingComplexBaseChangeMap P.Coefficient hRsq)
    (Etale.dualizingComplexBaseChangeMap P.Coefficient sqr) delta hp
  have hr := restrict_source_square P (i f g) HH (differenceFirst d f x) l
    (pullback.diagonal f) t (zero d U) (geometry f g).2.2.2.2.1 hHfz
    hHsq.flip.toCommSq
    (normalizedE P HH qQ (a f g) hHa.symm aQ).hom
    (normalizedE P (differenceFirst d f x) (pr d U) (pullback.fst f f) hHfpr aU).hom
    (Etale.dualizingComplexBaseChangeMap P.Coefficient (geometry f g).1)
    (Etale.dualizingComplexBaseChangeMap P.Coefficient sqr) hb
  rw [hc] at hr
  simpa only [chiF, firstRoute, gammaF, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    WeilConjectures.PurityFiniteSetting.DiagonalPasting.beta, asIso_inv] using hr


end AlgebraicGeometry.ProEtale.DifferenceCoordinateSection
