/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Sheaf.Paper.FiniteSpanModuleComparisonData
import Sheaf.Paper.FiniteSpanScalarTransport
import Sheaf.CategoryTheory.DerivedExactSquareComposition
import Sheaf.CategoryTheory.ExchangeMateCube
import Sheaf.CategoryTheory.CompatibleSquareComponents

/-! # Finite-span comparison and compatibility with exchange

The unchanged comparison data live in FiniteSpanModuleComparisonData so the scalar
transport construction is independent of the final mate-cube argument.
Source: Bhatt--Scholze, Remark 6.8.15; Stacks Project, Tags 03D7, 09T5 and 07A7.
(blueprint: lem-sf-finite-span-module-derived-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option Elab.async false

universe u v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteSpanComparison

private theorem transpose_coefficient_square
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (a : F ⊣ G) {A B : C} {U V : D}
    (x : A ⟶ B) (y : U ⟶ V) (alpha : F.obj A ⟶ U) (delta : B ⟶ G.obj V)
    (h : a.homEquiv _ _ alpha ≫ G.map y = x ≫ delta) :
    F.map x ≫ (a.homEquiv _ _).symm delta = alpha ≫ y := by
  apply (a.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right]
  exact h.symm

private theorem coefficient_inverse_square (l : ℕ) [Fact l.Prime]
    (theta : ∀ X : Scheme.{u},
      condensedRingObj (Profinite.padicAlgClRingObj l) X ≅ nativeAb l X)
    (hcoeff : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      condensedPushforwardHom (Profinite.padicAlgClRingObj l) f ≫
        (lowerStar Ab.{u + 1} f).map (theta X).hom =
      (theta Y).hom ≫ (weilCoefficientsForgetAb l Y).map (adicConstantSheafToLowerStar l f))
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar Ab.{u + 1} f).map (theta Y).hom ≫ rho l f =
      condensedPullbackHom (Profinite.padicAlgClRingObj l) f ≫ (theta X).hom := by
  apply transpose_coefficient_square (upperStarLowerStarAdjunction Ab.{u + 1} f)
    (theta Y).hom (theta X).hom (condensedPullbackHom (Profinite.padicAlgClRingObj l) f)
    ((weilCoefficientsForgetAb l Y).map (adicConstantSheafToLowerStar l f))
  change condensedPushforwardHom (Profinite.padicAlgClRingObj l) f ≫
    (lowerStar Ab.{u + 1} f).map (theta X).hom = _
  exact hcoeff X Y f

private theorem coefficient_rho_isIso (l : ℕ) [Fact l.Prime]
    (theta : ∀ X : Scheme.{u},
      condensedRingObj (Profinite.padicAlgClRingObj l) X ≅ nativeAb l X)
    (hcoeff : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      condensedPushforwardHom (Profinite.padicAlgClRingObj l) f ≫
        (lowerStar Ab.{u + 1} f).map (theta X).hom =
      (theta Y).hom ≫ (weilCoefficientsForgetAb l Y).map (adicConstantSheafToLowerStar l f))
    {X Y : Scheme.{u}} (f : X ⟶ Y) : IsIso (rho l f) := by
  have hi : IsIso ((upperStar Ab.{u + 1} f).map (theta Y).hom ≫ rho l f) := by
    rw [coefficient_inverse_square l theta hcoeff f]
    infer_instance
  exact IsIso.of_isIso_comp_left ((upperStar Ab.{u + 1} f).map (theta Y).hom) (rho l f)

private theorem comparison_composition (l : ℕ) [Fact l.Prime] [d : Data.{u} l]
    (h : Properties l) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : DerivedCategory.{u + 1} (internal l Z)) :
    (derivedEquivalence l X).map ((internalPullComp l f g).hom.app M) ≫
      (derivedPullComparison l f).hom.app ((internalPull l g).obj M) ≫
      (nativePull l f).map ((derivedPullComparison l g).hom.app M) =
    (derivedPullComparison l (f ≫ g)).hom.app M ≫
      (nativePullComp l f g).hom.app ((derivedEquivalence l Z).obj M) := by
  have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.1 (X := X) (Y := Y) (Z := Z)
  have he := Functor.mapDerivedCategorySquareIso_comp
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (f ≫ g))
    (inverse l g (d.coefficientMap g)) (inverse l f (d.coefficientMap f))
    (inverse l (f ≫ g) (d.coefficientMap (f ≫ g)))
    (equivalence l Z (d.theta Z)).functor (equivalence l Y (d.theta Y)).functor
    (equivalence l X (d.theta X)).functor
    (d.pullComparison g) (d.pullComparison f) (d.pullComparison (f ≫ g))
    (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g)
    (d.pullComposition f g) (fun N ↦ (hc f g N).symm)
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using congrArg (fun e ↦ e.hom.app M) he


private theorem invert_compositor
    {C : Type*} [Category C] {A B C' D : C}
    (a : A ≅ B) (b : C' ≅ D) (x : A ⟶ C') (y : B ⟶ D)
    (h : a.hom ≫ y = x ≫ b.hom) : a.inv ≫ x = y ≫ b.inv := by
  apply (cancel_epi a.hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]


private theorem invert_square
    {C : Type*} [Category C] {A B C' D E F : C}
    (a : A ≅ B) (b : B ≅ C') (c : D ≅ E) (d : E ≅ F)
    (x : A ⟶ D) (y : C' ⟶ F)
    (h : a.hom ≫ b.hom ≫ y = x ≫ c.hom ≫ d.hom) :
    b.inv ≫ a.inv ≫ x = y ≫ d.inv ≫ c.inv := by
  have he := invert_compositor (a ≪≫ b) (c ≪≫ d) x y
    (by simpa only [Iso.trans_hom, Category.assoc] using h)
  simpa only [Iso.trans_inv, Category.assoc] using he

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryNatIso
  Functor.mapDerivedCategoryCompIso Functor.rightDerivedFunctor
  HasDerivedCategory.standard DerivedCategory


private theorem comparison_composition_inv (l : ℕ) [Fact l.Prime] [d : Data.{u} l]
    (h : Properties l) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : DerivedCategory.{u + 1} (internal l Z)) :
    (derivedEquivalence l X).map ((internalPullComp l f g).inv.app M) ≫
      (derivedPullComparison l (f ≫ g)).hom.app M =
    (derivedPullComparison l f).hom.app ((internalPull l g).obj M) ≫
      (nativePull l f).map ((derivedPullComparison l g).hom.app M) ≫
      (nativePullComp l f g).inv.app ((derivedEquivalence l Z).obj M) := by
  simpa only [Functor.mapIso_inv, Iso.app_inv, Category.assoc] using
    invert_compositor
      ((derivedEquivalence l X).mapIso ((internalPullComp l f g).app M))
      ((nativePullComp l f g).app ((derivedEquivalence l Z).obj M)) _ _
      (comparison_composition l h f g M)


set_option backward.defeqAttrib.useBackward true in
private theorem square_comparison
    {C : Scheme.{u} → Type v₁} {D : Scheme.{u} → Type v₂}
    [catC : ∀ X, Category.{w₁} (C X)] [catD : ∀ X, Category.{w₂} (D X)]
    (E : ∀ X, C X ⥤ D X)
    (P : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → C Y ⥤ C X)
    (Q : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → D Y ⥤ D X)
    (pc : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      P (f ≫ g) ≅ P g ⋙ P f)
    (qc : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      Q (f ≫ g) ≅ Q g ⋙ Q f)
    (e : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), P f ⋙ E X ≅ E Y ⋙ Q f)
    (hc : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : C Z),
      (E X).map ((pc f g).inv.app M) ≫ (e (f ≫ g)).hom.app M =
        (e f).hom.app ((P g).obj M) ≫ (Q f).map ((e g).hom.app M) ≫
          (qc f g).inv.app ((E Z).obj M))
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : CommSq g' f' f g) (M : C Y) :
    (e f').hom.app ((P g).obj M) ≫ (Q f').map ((e g).hom.app M) ≫
        (square (fun T ↦ D T) Q qc s).hom.app ((E Y).obj M) =
      (E X').map ((square (fun T ↦ C T) P pc s).hom.app M) ≫
        (e g').hom.app ((P f).obj M) ≫ (Q g').map ((e f).hom.app M) := by
  have he := square_pasting (E Y) (E X')
    (fun t : X' ⟶ Y ↦ P t) (fun t : X' ⟶ Y ↦ Q t)
    (fun t ↦ e t) s.w.symm
    (pc f' g).symm (qc f' g).symm
    (pc g' f) (qc g' f) M
    ((e f').hom.app ((P g).obj M))
    ((Q f').map ((e g).hom.app M))
    ((e g').hom.app ((P f).obj M))
    ((Q g').map ((e f).hom.app M))
    (hc f' g M) (hc g' f M)
  exact he


set_option backward.defeqAttrib.useBackward true in
private theorem inverse_square_comparison
    {C : Scheme.{u} → Type v₁} {D : Scheme.{u} → Type v₂}
    [catC : ∀ X, Category.{w₁} (C X)] [catD : ∀ X, Category.{w₂} (D X)]
    (E : ∀ X, C X ⥤ D X)
    (P : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → C Y ⥤ C X)
    (Q : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → D Y ⥤ D X)
    (pc : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      P (f ≫ g) ≅ P g ⋙ P f)
    (qc : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      Q (f ≫ g) ≅ Q g ⋙ Q f)
    (e : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), P f ⋙ E X ≅ E Y ⋙ Q f)
    (hc : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : C Z),
      (E X).map ((pc f g).inv.app M) ≫ (e (f ≫ g)).hom.app M =
        (e f).hom.app ((P g).obj M) ≫ (Q f).map ((e g).hom.app M) ≫
          (qc f g).inv.app ((E Z).obj M))
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : CommSq g' f' f g) (M : C Y) :
    (Q f').map ((e g).inv.app M) ≫ (e f').inv.app ((P g).obj M) ≫
        (E X').map ((square (fun T ↦ C T) P pc s).hom.app M) =
      (square (fun T ↦ D T) Q qc s).hom.app ((E Y).obj M) ≫
        (Q g').map ((e f).inv.app M) ≫ (e g').inv.app ((P f).obj M) := by
  exact invert_square ((e f').app ((P g).obj M)) ((Q f').mapIso ((e g).app M))
    ((e g').app ((P f).obj M)) ((Q g').mapIso ((e f).app M)) _ _
    (square_comparison E P Q pc qc e hc s M)


set_option backward.defeqAttrib.useBackward true in
private theorem normalized_exchange_cube
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {K' : C' ⥤ D'} {S' : D' ⥤ C'}
    (adj : F ⊣ R) (adjK : K ⊣ S) (adj' : F' ⊣ R') (adjK' : K' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    (pF : F ⋙ b ≅ a ⋙ F') (pG : G ⋙ c ≅ a ⋙ G')
    (pH : H ⋙ d ≅ b ⋙ H') (pK : K ⋙ d ≅ c ⋙ K')
    (θ : G ⋙ K ⟶ F ⋙ H) (θ' : G' ⋙ K' ⟶ F' ⋙ H')
    (hc : ∀ X : A,
      K'.map (pG.inv.app X) ≫ pK.inv.app (G.obj X) ≫ d.map (θ.app X) =
        θ'.app (a.obj X) ≫ H'.map (pF.inv.app X) ≫ pH.inv.app (F.obj X))
    (E : B)
    (mF : a.obj (R.obj E) ⟶ R'.obj (b.obj E))
    (mK : c.obj (S.obj (H.obj E)) ⟶ S'.obj (d.obj (H.obj E)))
    (hF : (mateEquiv (G := a) (H := b) adj adj' (TwoSquare.mk a F F' b pF.inv)).app E = mF)
    (hK : (mateEquiv (G := c) (H := d) adjK adjK'
      (TwoSquare.mk c K K' d pK.inv)).app (H.obj E) = mK) :
    c.map ((mateEquiv (G := G) (H := H) adj adjK (TwoSquare.mk G F K H θ)).app E) ≫ mK ≫
        S'.map (pH.hom.app E) =
      pG.hom.app (R.obj E) ≫ G'.map mF ≫
        (mateEquiv (G := G') (H := H') adj' adjK' (TwoSquare.mk G' F' K' H' θ')).app (b.obj E) := by
  have h := exchangeMate_cube (F := F) (R := R) (G := G) (H := H) (K := K) (S := S)
    (F' := F') (R' := R') (G' := G') (H' := H') (K' := K') (S' := S')
    adj adjK adj' adjK' a b c d pF pG pH pK θ θ' hc E
  rw [hF, hK] at h
  exact h

set_option backward.defeqAttrib.useBackward true in
private theorem exchange_from_composition
    {C : Scheme.{u} → Type v₁} {D : Scheme.{u} → Type v₂}
    [catC : ∀ X, Category.{w₁} (C X)] [catD : ∀ X, Category.{w₂} (D X)]
    (E : ∀ X, C X ⥤ D X)
    (P : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → C Y ⥤ C X)
    (Q : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → D Y ⥤ D X)
    (R : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → C X ⥤ C Y)
    (S : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → D X ⥤ D Y)
    (adjP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), P f ⊣ R f)
    (adjQ : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), Q f ⊣ S f)
    (pc : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      P (f ≫ g) ≅ P g ⋙ P f)
    (qc : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      Q (f ≫ g) ≅ Q g ⋙ Q f)
    (e : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), P f ⋙ E X ≅ E Y ⋙ Q f)
    (m : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), R f ⋙ E Y ⟶ E X ⋙ S f)
    (hc : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : C Z),
      (E X).map ((pc f g).inv.app M) ≫ (e (f ≫ g)).hom.app M =
        (e f).hom.app ((P g).obj M) ≫ (Q f).map ((e g).hom.app M) ≫
          (qc f g).inv.app ((E Z).obj M))
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : CommSq g' f' f g)
    (hf : (mateEquiv (adjP f) (adjQ f) (e f).inv).natTrans = m f)
    (hf' : (mateEquiv (adjP f') (adjQ f') (e f').inv).natTrans = m f') (M : C X) :
    (E Y').map ((mateEquiv (adjP f) (adjP f')
      (square (fun T ↦ C T) P pc s).hom).app M) ≫
        (m f').app ((P g').obj M) ≫ (S f').map ((e g').hom.app M) =
      (e g).hom.app ((R f).obj M) ≫ (Q g).map ((m f).app M) ≫
        (mateEquiv (adjQ f) (adjQ f') (square (fun T ↦ D T) Q qc s).hom).app ((E X).obj M) := by
  exact normalized_exchange_cube (adjP f) (adjP f') (adjQ f) (adjQ f')
    (E Y) (E X) (E Y') (E X') (e f) (e g) (e g') (e f')
    (square (fun T ↦ C T) P pc s).hom (square (fun T ↦ D T) Q qc s).hom
    (inverse_square_comparison E P Q pc qc e hc s) M
    ((m f).app M) ((m f').app ((P g').obj M))
    (NatTrans.congr_app hf M) (NatTrans.congr_app hf' ((P g').obj M))

attribute [local instance] DerivedComparisonFrame.catC DerivedComparisonFrame.catD

private theorem normalization_mate (l : ℕ) [Fact l.Prime] [d : Data.{u} l]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (h : DerivedNormalization l f) :
    (derivedComparisonFrame l).MateCondition f := h.1

private theorem DerivedComparisonFrame.exchange (a : DerivedComparisonFrame.{u})
    (hc : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : a.C Z),
      (a.E X).map ((a.pc f g).inv.app M) ≫ (a.e (f ≫ g)).hom.app M =
        (a.e f).hom.app ((a.P g).obj M) ≫ (a.Q f).map ((a.e g).hom.app M) ≫
          (a.qc f g).inv.app ((a.E Z).obj M))
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : CommSq g' f' f g)
    (hf : a.MateCondition f) (hf' : a.MateCondition f')
    (M : a.C X) : a.ExchangeCondition s M := by
  exact exchange_from_composition a.E a.P a.Q a.R a.S a.adjP a.adjQ a.pc a.qc a.e a.m
    hc s hf hf' M

private theorem DerivedComparisonFrame.exchange_pullback
    (a : DerivedComparisonFrame.{u})
    (hc : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : a.C Z),
      (a.E X).map ((a.pc f g).inv.app M) ≫ (a.e (f ≫ g)).hom.app M =
        (a.e f).hom.app ((a.P g).obj M) ≫ (a.Q f).map ((a.e g).hom.app M) ≫
          (a.qc f g).inv.app ((a.E Z).obj M))
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : IsPullback g' f' f g)
    (hf : a.MateCondition f) (hf' : a.MateCondition f')
    (M : a.C X) : a.PullbackExchangeCondition s M := by
  exact a.exchange hc s.toCommSq hf hf' M

attribute [local irreducible] mateEquiv


set_option backward.defeqAttrib.useBackward true in
private theorem exchange_of_properties (l : ℕ) [Fact l.Prime] [d : Data.{u} l]
    (h : Properties l) : ExchangeProperty l := by
  intro k _ p _ _ hpl X' X Y' Y _ _ _ _ _ _ _ _ _ _ _ _ g' f' f g s K
  exact DerivedComparisonFrame.exchange_pullback (derivedComparisonFrame l)
    (comparison_composition_inv l h) s
    (normalization_mate l f.left (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 k p hpl X Y f))
    (normalization_mate l f'.left (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 k p hpl X' Y' f')) K

/-- The finite-span coefficient transport and its normalized ordinary and derived comparisons.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Lemma 6.8.2, Remark 6.8.15;
Stacks Project, Tags 03D6, 03D7, 070I, 070Y and 09T5.
(blueprint: lem-sf-finite-span-module-derived-comparison).

Proof:
1. Apply lem-sf-locally-finite-coefficient-ring-realization. Its finite-field charts fix
   theta. Take adjuncts of its coefficient square to obtain theta alpha = rho f^-1(theta).
   Since alpha and theta are invertible, rho is invertible. Repeated precomposition proves
   rho_composition, including identity morphisms.
2. Reconstruct section modules by def-weil-pbc-internal-abelian-sheaf-module-equivalence.
   Restrict the action along theta inverse. The inverse restricts along theta, and both
   composites are identities on actions. Underlying abelian sheaves, arrows and restrictions
   are unchanged. The equivalence is additive and exact; a finite free chart uses the same
   basis vectors, including the rank-zero chart.
3. Apply lem-sfb-internal-module-operations-transport. The coefficient square identifies
   the two direct-image scalar actions, giving the identity pushComparison. Inverting that
   square identifies the inverse-image actions transported along alpha inverse and rho
   inverse. The tensor presentation sends r tensor m to rho inverse(r)m and m to 1 tensor m.
4. Ordinary transposition evaluates at 1 tensor m, which these comparisons preserve.
   Hence the Hom bijections, units and counits agree. The geometric direct-image compositor
   has unchanged section maps, so its inverse-image mate agrees too.
5. Localize the exact equivalence and its inverse by
   lem-weil-pbc-exact-functor-derived-factorization. For acyclic N, the homotopy Hom from
   N to E(I) equals that from E inverse(N) to I. This proves K-injectivity preservation
   in both directions, using def-pur-kinjective-complex.
6. Use prop-pur-kinjective-resolutions-exist on the small sites. On a resolution K to I,
   compare the ordinary pushforwards of I and E(I). The normalization equation fixes this
   comparison relative to the right-derived units. Naturality and independence follow from
   lem-sf-kinjective-derived-map-computation. This compares total unbounded derived functors.
7. In the stated field setting, apply lem-pd-section-derived-pushpull-normalization.
   Relabel the section-ring actions by theta. Exact pullback sends acyclic complexes to
   acyclic complexes, so its right adjoint preserves K-injectives. By
   lem-weil-pbc-kinjective-hom-derived every morphism into I is a homotopy class of chain
   maps. The derived adjunction of lem-sc-derived-adjunction-from-underived sends this
   class to the class of the ordinary transpose. Relabelling preserves that transpose;
   identity transposes identify units and counits. Localizing step 4 identifies compositors.
8. The exchange assertion expands the unit--square--counit mate. Steps 6--7 identify
   each factor, its whiskerings, and composition. This holds for every complex and uses
   neither properness nor constructibility. -/
theorem finiteSpanModuleDerivedComparison (l : ℕ) [Fact l.Prime] :
    ∃ d : Data.{u} l, @Properties.{u} l _ d ∧ @ExchangeProperty.{u} l _ d := by
  obtain ⟨theta, hmon, hchart, hcoeff⟩ := locallyFiniteCoefficientRing_realization l
  let : ∀ X : Scheme.{u}, IsMonHom (theta X).hom := hmon
  obtain ⟨d, hd, hsections, hrcomp, hmate, hpush, hunder, hbasis,
    hpc, hpcm, hc, hkf, hki, hnorm, hfield⟩ := finiteSpanScalarTransport l theta hcoeff
  let : Data.{u} l := d
  subst theta
  have hp : Properties l := by
    refine ⟨?_, hsections, ?_, ?_, ?_, hrcomp, hmate, hpush, hunder, hbasis,
      hpc, hpcm, hc, hkf, hki, hnorm, hfield⟩
    · intro X E V s x
      exact hchart X E V s x
    · intro X Y f
      exact hcoeff X Y f
    · intro X Y f
      exact coefficient_inverse_square l d.theta hcoeff f
    · intro X Y f
      exact coefficient_rho_isIso l d.theta hcoeff f
  exact ⟨d, hp, exchange_of_properties l hp⟩

end AlgebraicGeometry.ProEtale.FiniteSpanComparison
