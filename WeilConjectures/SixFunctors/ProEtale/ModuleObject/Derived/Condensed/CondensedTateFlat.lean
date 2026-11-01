/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.Tate.TateTwistOneLocalLine
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable
import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
import all WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian

/-! # Flatness of signed condensed Tate twists -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] Mod.monoidalClosed

private noncomputable def concreteHomIso
    {Y : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R) :
    ihom M ≅ Mod.ihom' R M :=
  (ihom.adjunction M).rightAdjointUniq
    ((Mod.ihom'Adjunction R M).ofNatIsoLeft
      (Mod.relativeTensorRightIso M ≪≫
        (BraidedCategory.tensorLeftIsoTensorRight M).symm))

private theorem nonempty_pullback_ihom
    {X Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    Nonempty (((ProEtale.upperStar Ab.{u + 1} f).mapMod R).obj ((ihom M).obj N) ≅
      (ihom (((ProEtale.upperStar Ab.{u + 1} f).mapMod R).obj M)).obj
        (((ProEtale.upperStar Ab.{u + 1} f).mapMod R).obj N)) := by
  let G := ProEtale.upperStar Ab.{u + 1} f
  let F := G.mapMod R
  let : G.Braided := {}
  let e : F ⋙ Mod.comap (𝟙 (G.obj R)) ≅ F :=
    Functor.isoWhiskerLeft F (Mod.comapId _) ≪≫ Functor.rightUnitor F
  have : ∀ Z, IsIso (Functor.LaxMonoidal.ihomComparison G Z).natTrans :=
    ProEtale.isIso_ihomComparison_upperStar Ab.{u + 1} f
  have := Mod.isIso_mapIhom'Hom G (𝟙 (G.obj R)) M N
  exact ⟨F.mapIso ((concreteHomIso R M).app N) ≪≫
    (e.app ((Mod.ihom' R M).obj N)).symm ≪≫
    asIso (Mod.mapIhom'Hom G (𝟙 (G.obj R)) M N) ≪≫
    ((concreteHomIso _ _).app _).symm ≪≫
    asIso ((pre (e.app M).inv).app _) ≪≫ (ihom _).mapIso (e.app N)⟩

private theorem powers_image_regular
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
    {Z : Scheme.{u}} (g : Z ⟶ Y) [WeaklyEtale g]
    (e : (((ProEtale.upperStar Ab.{u + 1} g).mapMod
      ((ProEtale.upperStar Ab.{u + 1} f).obj
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))).obj
      (((ProEtale.upperStar Ab.{u + 1} f).mapMod
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).obj
          (tateTwistOne X ℓ))) ≅ 𝟙_ _) (d : ℤ) :
    Nonempty ((((ProEtale.upperStar Ab.{u + 1} g).mapMod
      ((ProEtale.upperStar Ab.{u + 1} f).obj
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))).obj
      (((ProEtale.upperStar Ab.{u + 1} f).mapMod
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).obj
          (tateTwist X ℓ d))) ≅ 𝟙_ _) := by
  let R := condensedRingObj (Profinite.padicAlgClRingObj ℓ) X
  let F := ProEtale.upperStar Ab.{u + 1} f
  let G := ProEtale.upperStar Ab.{u + 1} g
  let : F.Braided := {}
  let : G.Braided := {}
  let H := F.mapMod R ⋙ G.mapMod (F.obj R)
  have hn (n : ℕ) : Nonempty (H.obj (tateTwistNat X ℓ n) ≅ 𝟙_ _) := by
    induction n with
    | zero => exact ⟨Functor.Monoidal.εIso H |>.symm⟩
    | succ n hn =>
      exact ⟨(Functor.Monoidal.μIso H _ _).symm ≪≫
        tensorIso hn.some e ≪≫ λ_ _⟩
  cases d with
  | ofNat n => exact hn n
  | negSucc n =>
    obtain ⟨hf⟩ := nonempty_pullback_ihom f R (tateTwistNat X ℓ (n + 1)) (𝟙_ _)
    obtain ⟨hg⟩ := nonempty_pullback_ihom g (F.obj R)
      ((F.mapMod R).obj (tateTwistNat X ℓ (n + 1))) ((F.mapMod R).obj (𝟙_ _))
    exact ⟨(G.mapMod (F.obj R)).mapIso hf ≪≫ hg ≪≫
      asIso ((pre (hn (n + 1)).some.inv).app _) ≪≫
      (ihom _).mapIso (Functor.Monoidal.εIso H).symm ≪≫
      MonoidalClosed.unitIsoSelf _⟩

/-- Every signed condensed Tate twist is flat when ell is invertible on the scheme.
Source: current blueprint, `sk-def-sp-tate-twist`, the common-root-cover argument.
(blueprint: lem-pur-condensed-tate-flat).

Proof: pull back along the identity, then along the compatible-root cover. The first
Tate twist becomes the unit. Tensor powers and preservation of internal Hom by weakly
etale pullback show that every signed twist becomes the unit on the same cover.
Thus its identity pullback is locally free and dualizable. The identity pullback on
modules is conservative, strong monoidal and commutes with internal Hom, so it detects
dualizability. A dualizable object is flat. This also covers zero twist and empty schemes.
-/
theorem flat_tateTwist (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : Γ(X, ⊤))) (d : ℤ) :
    ObjectProperty.flat (tateTwist X ℓ d) := by
  classical
  let R := condensedRingObj (Profinite.padicAlgClRingObj ℓ) X
  let G := ProEtale.upperStar Ab.{u + 1} (𝟙 X)
  let F := G.mapMod R
  let : G.Braided := {}
  obtain ⟨U, hU⟩ := tateTwistOne_pullback_locally_trivial X ℓ hℓ (𝟙 X)
  have hfree : ProEtale.IsLocallyFree (G.obj R) (F.obj (tateTwist X ℓ d)) := by
    refine ⟨U, fun i ↦ ?_⟩
    have : WeaklyEtale (U.f i) :=
      Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ U.mem₀ ⟨i⟩
    exact ⟨1, ⟨(powers_image_regular X ℓ (𝟙 X) (U.f i) (hU i).some d).some ≪≫
      (biproductUniqueIso (fun _ : Fin 1 ↦ Mod.regular _)).symm⟩⟩
  have hdual : IsDualizable (tateTwist X ℓ d) := by
    have : ∀ Z, IsIso (Functor.LaxMonoidal.ihomComparison G Z).natTrans :=
      ProEtale.isIso_ihomComparison_upperStar Ab.{u + 1} (𝟙 X)
    refine isDualizable_of_isDualizable_map (fun _ : Unit ↦ F) ?_
      (fun _ ↦ hfree.isDualizable)
    intro Y Z f hf
    have : IsIso (F.map f) := hf ()
    suffices IsIso ((Mod.forget R).map f) from isIso_of_reflects_iso f (Mod.forget R)
    have h : IsIso (G.map f.hom) :=
      inferInstanceAs (IsIso ((Mod.forget (G.obj R)).map (F.map f)))
    exact (NatIso.isIso_map_iff (ProEtale.upperStarId Ab.{u + 1} X) f.hom).mp h
  exact hdual.flat

end AlgebraicGeometry.ProEtale.CondensedRing
