/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityConventions.PurityConventions
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameKummer
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# Exchange detected by the affine-line unit and punctured-line generator

Source: det-prop-a1-kummer.proof.md, paragraph "Base change on Y".
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The direct-image exchange followed by the canonical coefficient identification.
Source: det-prop-a1-kummer, base change (blueprint: new-pur-a1-kummer-exchange-criterion). -/
def a1KummerExchange (P : PurityFiniteSetting.{u}) {X' X Y' Y : Scheme.{u}}
    {q : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq q p' p g) (a : Y ⟶ Spec (.of P.field.k)) (b : Bool) :=
  (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient) sq).app
      (P.a1KummerComplex X b) ≫
    (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) p').rightDerivedFunctor.map
      (P.a1KummerPullback q (p ≫ a) b)

/-- The cohomology exchange with pullback of coefficients on its source.
Source: det-prop-a1-kummer, base change (blueprint: new-pur-a1-kummer-exchange-criterion). -/
def a1KummerCohomologyExchange (P : PurityFiniteSetting.{u})
    {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) (a : Y ⟶ Spec (.of P.field.k)) (n : ℤ) :=
  (ProEtale.leftDerivedUpperStarHomologyFunctorIso
    (ModuleCat.{u + 1} P.Coefficient) g n).hom.app
      ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
        (puncturedProjection Y)).rightDerivedFunctor.obj
          (P.a1KummerComplex (Punctured Y) true)) ≫
    (DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y') (ModuleCat.{u + 1} P.Coefficient)) n).map
        (P.a1KummerExchange (puncturedSquare g) a true)

/-- The degree-zero unit, with its source identified with the coefficient sheaf.
Source: det-prop-a1-kummer (b) (blueprint: new-pur-a1-kummer-exchange-criterion). -/
def a1KummerZeroUnit (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (a : Y ⟶ Spec (.of P.field.k)) :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).inv.app
      (P.a1KummerCoefficient Y true) ≫
    (DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).map
        (P.a1KummerUnit (puncturedProjection Y) a true)

/-- Coherence of the four actual derived coefficient pullback identifications.
Source: det-prop-a1-kummer.proof.md, Base change on Y
(blueprint: new-pur-a1-kummer-exchange-criterion). -/
def A1KummerCoefficientSquare (P : PurityFiniteSetting.{u})
    {X' X Y' Y : Scheme.{u}} {q : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq q p' p g)
    (a : Y ⟶ Spec (.of P.field.k)) (b : Bool) : Prop :=
  (ProEtale.leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} P.Coefficient) sq).hom.app
      (P.a1KummerComplex Y b) ≫
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) q).leftDerivedFunctor.map
      (P.a1KummerPullback p a b) ≫
    P.a1KummerPullback q (p ≫ a) b =
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) p').leftDerivedFunctor.map
      (P.a1KummerPullback g a b) ≫
    P.a1KummerPullback p' (g ≫ a) b

/-- The four canonical normalization identities needed in the base-change argument.
They assert preservation of the class, coefficient coherence for both squares, and the
punctured-line degree-one generator. Source: det-prop-a1-kummer.proof.md, "Base change on Y"
(blueprint: new-pur-a1-kummer-exchange-criterion). -/
def A1KummerExchangeNormalization (P : PurityFiniteSetting.{u})
    {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) (a : Y ⟶ Spec (.of P.field.k)) : Prop :=
  ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (puncturedMap g)).leftDerivedFunctor.map (P.a1KummerClass Y a).hom ≫
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (puncturedMap g)).leftDerivedFunctor.commShiftIso (1 : ℤ)).hom.app
        (P.a1KummerComplex (Punctured Y) true) ≫
    (P.a1KummerPullback (puncturedMap g) (puncturedProjection Y ≫ a) true)⟦(1 : ℤ)⟧' =
      P.a1KummerPullback (puncturedMap g) (puncturedProjection Y ≫ a) false ≫
        (P.a1KummerClass Y' (g ≫ a)).hom) ∧
  (P.A1KummerCoefficientSquare
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq a false) ∧
  (P.A1KummerCoefficientSquare (puncturedSquare g) a true) ∧
  ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).map
      (P.a1KummerGenerator Y a) ≫ P.a1KummerCohomologyExchange g a 1 =
    (P.a1KummerCoefficientPullback g a false).hom ≫
      P.a1KummerGenerator Y' (g ≫ a))

private theorem unit_exchange_of_coefficient_square
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : C ⥤ C') (H : D ⥤ D')
    (σ : G ⋙ L' ⟶ L ⋙ H) {A : C} {B : D} {A' : C'} {B' : D'}
    (cp : L.obj A ⟶ B) (cg : G.obj A ⟶ A') (cq : H.obj B ⟶ B')
    (cp' : L'.obj A' ⟶ B')
    (h : σ.app A ≫ H.map cp ≫ cq = L'.map cg ≫ cp') :
    G.map (adj.unit.app A ≫ R.map cp) ≫
        (mateEquiv adj adj' σ).app B ≫ R'.map cq =
      cg ≫ adj'.unit.app A' ≫ R'.map cp' := by
  let b := mateEquiv adj adj' σ
  calc
    G.map (adj.unit.app A ≫ R.map cp) ≫ b.app B ≫ R'.map cq =
        G.map (adj.unit.app A) ≫ b.app (L.obj A) ≫
          R'.map (H.map cp) ≫ R'.map cq := by
      have hn := b.naturality cp
      simpa only [Functor.map_comp, Functor.comp_map, Category.assoc] using
        congrArg (fun t ↦ G.map (adj.unit.app A) ≫ t ≫ R'.map cq) hn
    _ = (G.map (adj.unit.app A) ≫ b.app (L.obj A)) ≫
        R'.map (H.map cp ≫ cq) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = adj'.unit.app (G.obj A) ≫ R'.map (σ.app A ≫ H.map cp ≫ cq) := by
      rw [unit_mateEquiv adj adj' σ A]
      simp only [Functor.map_comp, Category.assoc, Functor.id_obj]
    _ = adj'.unit.app (G.obj A) ≫ R'.map (L'.map cg ≫ cp') := by rw [h]
    _ = cg ≫ adj'.unit.app A' ≫ R'.map cp' := by
      rw [Functor.map_comp, ← Category.assoc, adj'.unit_naturality cg, Category.assoc]

private theorem a1KummerPullback_isIso (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a : Y ⟶ Spec (.of P.field.k)) (b : Bool) :
    IsIso (P.a1KummerPullback f a b) := by
  unfold a1KummerPullback
  infer_instance

private theorem a1KummerImage_negative (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (n : ℤ) (hn : n < 0) : IsZero
    ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) n).obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (puncturedProjection Y)).rightDerivedFunctor.obj
            (P.a1KummerComplex (Punctured Y) true))) := by
  have := (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
    (puncturedProjection Y)).isGE_rightDerivedFunctor_obj_singleFunctor
      (P.a1KummerCoefficient (Punctured Y) true)
  exact ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
    (puncturedProjection Y)).rightDerivedFunctor.obj
      (P.a1KummerComplex (Punctured Y) true)).isZero_of_isGE 0 n hn

/-- Cohomology and the four normalization identities imply the specified derived exchanges
are invertible. Source: det-prop-a1-kummer.proof.md, "Base change on Y"
(blueprint: new-pur-a1-kummer-exchange-criterion).

Proof: the mate-unit identity and the two coefficient squares imply both unit
squares. Cancel its invertible unit. For the punctured
line cancel the invertible degree-zero unit and degree-one Kummer generator from their
normalization squares. Exact pullback commutes with cohomology. In every other degree
both source and target vanish: negative degrees by right derivation of a single sheaf,
and degrees at least two by the computed cohomology. The cohomology criterion detects
isomorphisms in the derived category. Finally cancel the coefficient identifications. -/
theorem a1KummerBaseChange_of_normalization (P : PurityFiniteSetting.{u})
    {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) (a : Y ⟶ Spec (.of P.field.k))
    (hY : P.A1KummerConclusions Y a) (hY' : P.A1KummerConclusions Y' (g ≫ a))
    (hn : P.A1KummerExchangeNormalization g a) : P.A1KummerBaseChange g a := by
  obtain ⟨hline, hzero, hgen, hhigh⟩ := hY
  obtain ⟨hline', hzero', hgen', hhigh'⟩ := hY'
  obtain ⟨hclass, hcline, hcgm, hugen⟩ := hn
  have huline :
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor.map
          (P.a1KummerUnit (lineProjection Y) a false) ≫
        P.a1KummerExchange
          (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq a false =
      P.a1KummerPullback g a false ≫
        P.a1KummerUnit (lineProjection Y') (g ≫ a) false := by
    exact unit_exchange_of_coefficient_square
      (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
        (lineProjection Y))
      (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
        (lineProjection Y'))
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.map (n := ULift.{u} (Fin 1)) g)).leftDerivedFunctor
      (ProEtale.leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq).hom
      (P.a1KummerPullback (lineProjection Y) a false) (P.a1KummerPullback g a false)
      (P.a1KummerPullback (AffineSpace.map (n := ULift.{u} (Fin 1)) g)
        (lineProjection Y ≫ a) false)
      (P.a1KummerPullback (lineProjection Y') (g ≫ a) false) hcline
  have hugm :
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor.map
          (P.a1KummerUnit (puncturedProjection Y) a true) ≫
        P.a1KummerExchange (puncturedSquare g) a true =
      P.a1KummerPullback g a true ≫
        P.a1KummerUnit (puncturedProjection Y') (g ≫ a) true := by
    exact unit_exchange_of_coefficient_square
      (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
        (puncturedProjection Y))
      (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
        (puncturedProjection Y'))
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (puncturedMap g)).leftDerivedFunctor
      (ProEtale.leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} P.Coefficient)
        (puncturedSquare g)).hom
      (P.a1KummerPullback (puncturedProjection Y) a true)
      (P.a1KummerPullback g a true)
      (P.a1KummerPullback (puncturedMap g) (puncturedProjection Y ≫ a) true)
      (P.a1KummerPullback (puncturedProjection Y') (g ≫ a) true) hcgm
  have := hline
  have := hline'
  have := hzero
  have := hzero'
  have := hgen
  have := hgen'
  have hpull : ∀ {X Z : Scheme.{u}} (f : X ⟶ Z)
      (aZ : Z ⟶ Spec (.of P.field.k)) (b : Bool),
      IsIso (P.a1KummerPullback f aZ b) := a1KummerPullback_isIso P
  refine ⟨hclass, ?_, ?_⟩
  · have hc : IsIso
        ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor.map
          (P.a1KummerUnit (lineProjection Y) a false) ≫
            P.a1KummerExchange
              (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq a false) := by
      rw [huline]
      infer_instance
    have he : IsIso (P.a1KummerExchange
        (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq a false) :=
      IsIso.of_isIso_comp_left
        ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor.map
          (P.a1KummerUnit (lineProjection Y) a false)) _
    have : IsIso
        ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient)
          (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq).app
            (P.a1KummerComplex (Line Y) false) ≫
          (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
            (lineProjection Y')).rightDerivedFunctor.map
              (P.a1KummerPullback (AffineSpace.map (n := ULift.{u} (Fin 1)) g)
                (lineProjection Y ≫ a) false)) := he
    exact IsIso.of_isIso_comp_right _
      ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
        (lineProjection Y')).rightDerivedFunctor.map
          (P.a1KummerPullback (AffineSpace.map (n := ULift.{u} (Fin 1)) g)
            (lineProjection Y ≫ a) false))
  · let A := ModuleCat.{u + 1} P.Coefficient
    let H := fun (B : Scheme.{u}) (n : ℤ) =>
      DerivedCategory.homologyFunctor (Sheaf (Scheme.ProEt.topology B) A) n
    let R := fun (B : Scheme.{u}) =>
      (ProEtale.lowerStar A (puncturedProjection B)).rightDerivedFunctor
    let T := P.a1KummerExchange (puncturedSquare g) a true
    have he : IsIso T := by
      rw [DerivedCategory.isIso_iff]
      intro n
      by_cases hn0 : n = 0
      · subst n
        have hu : IsIso ((H Y' 0).map
            ((ProEtale.upperStar A g).leftDerivedFunctor.map
              (P.a1KummerUnit (puncturedProjection Y) a true))) :=
          (NatIso.isIso_map_iff (ProEtale.leftDerivedUpperStarHomologyFunctorIso A g 0)
            (P.a1KummerUnit (puncturedProjection Y) a true)).mp
              (inferInstanceAs (IsIso ((ProEtale.upperStar A g).map
                ((H Y 0).map (P.a1KummerUnit (puncturedProjection Y) a true)))))
        have hc : IsIso ((H Y' 0).map
            ((ProEtale.upperStar A g).leftDerivedFunctor.map
                (P.a1KummerUnit (puncturedProjection Y) a true) ≫ T)) := by
          change IsIso ((H Y' 0).map
            ((ProEtale.upperStar A g).leftDerivedFunctor.map
                (P.a1KummerUnit (puncturedProjection Y) a true) ≫
              P.a1KummerExchange (puncturedSquare g) a true))
          rw [hugm, Functor.map_comp]
          infer_instance
        have : IsIso
            ((H Y' 0).map ((ProEtale.upperStar A g).leftDerivedFunctor.map
                (P.a1KummerUnit (puncturedProjection Y) a true)) ≫ (H Y' 0).map T) := by
          simpa only [Functor.map_comp] using hc
        exact IsIso.of_isIso_comp_left
          ((H Y' 0).map ((ProEtale.upperStar A g).leftDerivedFunctor.map
            (P.a1KummerUnit (puncturedProjection Y) a true))) ((H Y' 0).map T)
      by_cases hn1 : n = 1
      · subst n
        have hc : IsIso
            ((ProEtale.upperStar A g).map (P.a1KummerGenerator Y a) ≫
              P.a1KummerCohomologyExchange g a 1) := by
          rw [hugen]
          infer_instance
        have hcx : IsIso (P.a1KummerCohomologyExchange g a 1) :=
          IsIso.of_isIso_comp_left
            ((ProEtale.upperStar A g).map (P.a1KummerGenerator Y a)) _
        have : IsIso
            ((ProEtale.leftDerivedUpperStarHomologyFunctorIso A g 1).hom.app
              ((R Y).obj (P.a1KummerComplex (Punctured Y) true)) ≫ (H Y' 1).map T) := hcx
        exact IsIso.of_isIso_comp_left
          ((ProEtale.leftDerivedUpperStarHomologyFunctorIso A g 1).hom.app
            ((R Y).obj (P.a1KummerComplex (Punctured Y) true))) ((H Y' 1).map T)
      have hz (B : Scheme.{u})
          (hB : ∀ m : ℕ, 2 ≤ m → IsZero
            ((H B (m : ℤ)).obj ((R B).obj
              (P.a1KummerComplex (Punctured B) true)))) :
          IsZero ((H B n).obj ((R B).obj
            (P.a1KummerComplex (Punctured B) true))) := by
        by_cases hneg : n < 0
        · exact a1KummerImage_negative P B n hneg
        · have hn : 2 ≤ n := by omega
          have hnat : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
          exact hnat ▸ hB n.toNat (by omega)
      have hs := (Functor.map_isZero (ProEtale.upperStar A g) (hz Y hhigh)).of_iso
        ((ProEtale.leftDerivedUpperStarHomologyFunctorIso A g n).app
          ((R Y).obj (P.a1KummerComplex (Punctured Y) true))).symm
      exact isIso_of_source_target_iso_zero _ hs.isoZero (hz Y' hhigh').isoZero
    have : IsIso
        ((ProEtale.derivedBaseChangeMap A (puncturedSquare g)).app
            (P.a1KummerComplex (Punctured Y) true) ≫
          (R Y').map (P.a1KummerPullback (puncturedMap g)
            (puncturedProjection Y ≫ a) true)) := he
    exact IsIso.of_isIso_comp_right _
      ((ProEtale.lowerStar A (puncturedProjection Y')).rightDerivedFunctor.map
        (P.a1KummerPullback (puncturedMap g) (puncturedProjection Y ≫ a) true))

end WeilConjectures.PurityFiniteSetting
