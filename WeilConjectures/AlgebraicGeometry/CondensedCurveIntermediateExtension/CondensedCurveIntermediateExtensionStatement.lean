/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import WeilConjectures.AlgebraicGeometry.CurveMiddleExtension
public import WeilConjectures.AlgebraicGeometry.CurvePerverseHeartStatement.CurvePerverseHeartStatement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ModuleOpenPasting.ModuleDirectImageOpenPasting
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleInverseImageStalk
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.CategoryTheory.ProperBaseChange.ExtOneExtensionClassification
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-! # Condensed curve perverse intermediate extension

Source: `literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-fourier-transform/sec-wft-perverse/sk-lem-wft-curve-heart/rem-dl-a1-conventions.md`,
ordinary direct-image paragraph.
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedCurveIntermediateExtension

open WeilConjectures
open WeilConjectures.NativeL2
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed
open AlgebraicGeometry.ProEtale.CurvePerverseHeartStatement

variable (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
  (c : Scheme.MiddleExtensionCurve D)

/-- The condensed coefficient ring of $\overline{\mathbf Q}_\ell$.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev coeff (ell : ℕ) [Fact ell.Prime] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  Profinite.padicAlgClRingObj ell
/-- The geometric open $U=U_0\otimes_{k_0}k$.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev geomU (D : FiniteFieldDatum.{u}) (c : Scheme.MiddleExtensionCurve D) :=
  (D.geometricFiber c.U).left
/-- The geometric curve $C=C_0\otimes_{k_0}k$.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev geomC (D : FiniteFieldDatum.{u}) (c : Scheme.MiddleExtensionCurve D) :=
  (D.geometricFiber c.C).left
/-- The geometric open immersion $j:U\to C$, base change of $j_0$.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev geomJ (D : FiniteFieldDatum.{u}) (c : Scheme.MiddleExtensionCurve D) :=
  NativeL2.geometricMap D c.j
/-- The geometric Frobenius automorphism $g_U$ of $U$ defining Weil structures.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev frobU (D : FiniteFieldDatum.{u}) (c : Scheme.MiddleExtensionCurve D) :=
  StrictWeilCondensed.modelFrobenius D c.U
/-- The geometric Frobenius automorphism $g_C$ of $C$ defining Weil structures.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev frobC (D : FiniteFieldDatum.{u}) (c : Scheme.MiddleExtensionCurve D) :=
  StrictWeilCondensed.modelFrobenius D c.C
/-- Module sheaves over the condensed coefficient ring on the pro-étale site
(the ambient category of thm-a1-curve-perverse-heart).
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev Modules (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (X : Scheme.{u}) :=
  CurvePerverseHeartStatement.Modules ell X
/-- The perverse heart ${}^pD^{\le0}(C)\cap{}^pD^{\ge0}(C)$ of thm-a1-curve-perverse-heart
inside the bounded constructible derived category of the geometric curve.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev perverseHeart (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (c : Scheme.MiddleExtensionCurve D) (hEll : ell ≠ D.p) :
    ObjectProperty (DerivedCategory (Modules D ell (geomC D c))) :=
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  letI : Fact (ringChar D.k).Prime := ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
  letI : Fact (ringChar D.k ≠ ell) := ⟨(ringChar.eq D.k D.p).symm ▸ hEll.symm⟩
  letI : Invertible (ell : D.k) := invertibleOfNonzero
    (by
      intro h
      have hd : D.p ∣ ell := by
        exact (CharP.cast_eq_zero_iff D.k D.p ell).mp h
      exact hEll ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : ell.Prime)).mp hd).symm)
  letI : LocallyOfFiniteType (D.geometricFiber c.C).hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd c.C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : QuasiCompact (D.geometricFiber c.C).hom := inferInstanceAs
    (QuasiCompact (pullback.snd c.C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : IsSeparated (D.geometricFiber c.C).hom := inferInstanceAs
    (IsSeparated (pullback.snd c.C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  fun K => CurvePerverseHeartStatement.InHeart
    (AlgebraicGeometry.ProEtale.boundedConstructible
      (condensedRingObj (coeff ell) (geomC D c)))
    (fun K : (AlgebraicGeometry.ProEtale.boundedConstructible
        (condensedRingObj (coeff ell) (geomC D c))).FullSubcategory ↦
      CondensedRing.CondensedPerverseLEZero ell
        (CurvePerverseHeartStatement.closure_baseField D) (D.geometricFiber c.C)
        ⟨K.obj, K.property⟩)
    (fun K : (AlgebraicGeometry.ProEtale.boundedConstructible
        (condensedRingObj (coeff ell) (geomC D c))).FullSubcategory ↦
      CondensedRing.CondensedPerverseGEZero ell
        (CurvePerverseHeartStatement.closure_baseField D) (D.geometricFiber c.C)
        ⟨K.obj, K.property⟩)
    K

/-- The ordinary module direct image $A=j_*F$ (def-wf-middle-extension).
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev image (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (c : Scheme.MiddleExtensionCurve D)
    (F : StrictWeilCondensed.WeilModule (coeff ell) (frobU D c)) : Modules D ell (geomC D c) :=
  (NativeL2.middleImage D ell c.j).obj F.carrier
/-- The shifted ordinary direct image $(j_*F)[1]$.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev shiftedImage (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (c : Scheme.MiddleExtensionCurve D)
    (F : StrictWeilCondensed.WeilModule (coeff ell) (frobU D c)) :
    DerivedCategory (Modules D ell (geomC D c)) :=
  (NativeL2.shiftedMiddleImage D ell c.j).obj F.carrier
/-- The derived restriction $j^*$ to the geometric open.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev restriction (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (c : Scheme.MiddleExtensionCurve D) :
    DerivedCategory (Modules D ell (geomC D c)) ⥤
      DerivedCategory (Modules D ell (geomU D c)) :=
  (CondensedRing.upperStar (coeff ell) (geomJ D c)).mapDerivedCategory
/-- A sheaf on $U$ placed in degree zero and shifted by one: $F\mapsto F[1]$.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev shiftedSheaf (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (c : Scheme.MiddleExtensionCurve D) :
    Modules D ell (geomU D c) ⥤ DerivedCategory (Modules D ell (geomU D c)) :=
  DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ (1 : ℤ)

/-- The canonical identification $j^*((j_*F)[1])\to F[1]$: shift and single-complex
commutation of $j^*$ followed by the shifted counit $j^*j_*F\to F$.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
def openIdentificationMap (F : StrictWeilCondensed.WeilModule (coeff ell) (frobU D c)) :
    (restriction D ell c).obj (shiftedImage D ell c F) ⟶
      (shiftedSheaf D ell c).obj F.carrier :=
  ((restriction D ell c).commShiftIso (1 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj (image D ell c F)) ≫
    (shiftFunctor _ (1 : ℤ)).map
      (((CondensedRing.upperStar (coeff ell) (geomJ D c)).mapDerivedCategorySingleFunctor 0).hom.app
        (image D ell c F)) ≫
    (shiftedSheaf D ell c).map
      ((CondensedRing.upperStarLowerStarAdjunction (coeff ell) (geomJ D c)).counit.app F.carrier)

/-- Both boundary Hom vanishings: $\operatorname{Hom}(Q,P)=0=\operatorname{Hom}(P,Q)$ for every
heart object $Q$ with $j^*Q=0$.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
def BoundaryMinimal (_F : StrictWeilCondensed.WeilModule (coeff ell) (frobU D c)) (P :
    DerivedCategory (Modules D ell (geomC D c))) (hEll : ell ≠ D.p) : Prop :=
  ∀ Q : DerivedCategory (Modules D ell (geomC D c)),
    perverseHeart D ell c hEll Q →
    IsZero ((restriction D ell c).obj Q) →
      (∀ f : Q ⟶ P, f = 0) ∧ (∀ f : P ⟶ Q, f = 0)

/-- The pullback composition comparison $\rho:g_U^*j^*\simeq j^*g_C^*$, from the
canonical square $j g_U=g_C j$.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
def restrictionFrobeniusComparison :
    restriction D ell c ⋙ StrictWeilCondensed.action (coeff ell) (frobU D c) ≅
      StrictWeilCondensed.action (coeff ell) (frobC D c) ⋙ restriction D ell c :=
  (Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar (coeff ell) (geomJ D c))
      (CondensedRing.upperStar (coeff ell) (frobU D c).hom)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (CondensedRing.upperStarSquareComparison (coeff ell)
        (CommSq.mk (NativeL2.frobeniusSquare D c.j).w)).symm ≪≫
    Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar (coeff ell) (frobC D c).hom)
      (CondensedRing.upperStar (coeff ell) (geomJ D c))

/-- The Weil structure of $F[1]$ induced by that of $F$.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
def shiftedWeilMap (F : StrictWeilCondensed.WeilModule (coeff ell) (frobU D c)) :
    (StrictWeilCondensed.action (coeff ell) (frobU D c)).obj
        ((shiftedSheaf D ell c).obj F.carrier) ⟶
      (shiftedSheaf D ell c).obj F.carrier :=
  ((StrictWeilCondensed.action (coeff ell) (frobU D c)).commShiftIso (1 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj F.carrier) ≫
    (shiftFunctor _ (1 : ℤ)).map
      (((CondensedRing.upperStar (coeff ell) (frobU D c).hom).mapDerivedCategorySingleFunctor
        0).hom.app F.carrier) ≫
    (shiftedSheaf D ell c).map F.str.hom

/-- All clauses of the node: heart membership, the canonical open identification,
the boundary-Hom characterization with unique normalized comparison, and Weil compatibility.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
def IntermediateExtensionAssertion
    (hEll : ell ≠ D.p)
    (F : StrictWeilCondensed.WeilModule (coeff ell) (frobU D c)) : Prop :=
  perverseHeart D ell c hEll (shiftedImage D ell c F) ∧
    ∃ β : (restriction D ell c).obj (shiftedImage D ell c F) ≅
        (shiftedSheaf D ell c).obj F.carrier,
      β.hom = openIdentificationMap D ell c F ∧
      BoundaryMinimal D ell c F (shiftedImage D ell c F) hEll ∧
      (∀ P : DerivedCategory (Modules D ell (geomC D c)),
        perverseHeart D ell c hEll P →
        ∀ α : (restriction D ell c).obj P ≅
          (shiftedSheaf D ell c).obj F.carrier,
          BoundaryMinimal D ell c F P hEll ↔
            ∃! e : P ≅ shiftedImage D ell c F,
              (restriction D ell c).map e.hom ≫ β.hom = α.hom) ∧
      ∃ θA : (StrictWeilCondensed.action (coeff ell) (frobC D c)).obj
          (shiftedImage D ell c F) ≅ shiftedImage D ell c F,
        (restrictionFrobeniusComparison D ell c).hom.app _ ≫
            (restriction D ell c).map θA.hom ≫ β.hom =
          (StrictWeilCondensed.action (coeff ell) (frobU D c)).map β.hom ≫
            shiftedWeilMap D ell c F ∧
        ∀ P : DerivedCategory (Modules D ell (geomC D c)),
          perverseHeart D ell c hEll P →
          BoundaryMinimal D ell c F P hEll →
          ∀ (α : (restriction D ell c).obj P ≅
            (shiftedSheaf D ell c).obj F.carrier)
            (θP : (StrictWeilCondensed.action (coeff ell) (frobC D c)).obj P ≅ P)
            (e : P ≅ shiftedImage D ell c F),
            (restriction D ell c).map e.hom ≫ β.hom = α.hom →
            (restrictionFrobeniusComparison D ell c).hom.app P ≫
                (restriction D ell c).map θP.hom ≫ α.hom =
              (StrictWeilCondensed.action (coeff ell) (frobU D c)).map α.hom ≫
                shiftedWeilMap D ell c F →
            θP.hom ≫ e.hom = (StrictWeilCondensed.action (coeff ell) (frobC D c)).map e.hom ≫ θA.hom

private theorem lift_aut
    (h : Function.Bijective (fun f : A ⟶ A ↦ R.map f)) (a : R.obj A ≅ R.obj A) :
    ∃ b : A ≅ A, R.map b.hom = a.hom := by
  obtain ⟨b, hb⟩ := h.2 a.hom
  obtain ⟨c, hc⟩ := h.2 a.inv
  have hbc : b ≫ c = 𝟙 A := h.1 (by simp [hb, hc])
  have hcb : c ≫ b = 𝟙 A := h.1 (by simp [hb, hc])
  exact ⟨⟨b, c, hbc, hcb⟩, hb⟩

private theorem lift_iso
    (h : Function.Bijective (fun f : A ⟶ A ↦ R.map f))
    {P : C} (e₀ : P ≅ A) (α : R.obj P ≅ R.obj A) :
    ∃! e : P ≅ A, R.map e.hom = α.hom := by
  obtain ⟨b, hb⟩ := lift_aut R h ((R.mapIso e₀).symm ≪≫ α)
  refine ⟨e₀ ≪≫ b, ?_, ?_⟩
  · simp only [Iso.trans_hom, Functor.map_comp, hb, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_inv]
    simp
  · intro e he
    apply Iso.ext
    have hh : e₀.inv ≫ e.hom = b.hom := h.1 (by
      simp only [Functor.map_comp, he, hb, Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_inv])
    calc
      e.hom = e₀.hom ≫ (e₀.inv ≫ e.hom) := by simp
      _ = e₀.hom ≫ b.hom := by rw [hh]

private theorem map_injective_of_iso
    (h : Function.Injective (fun f : A ⟶ A ↦ R.map f))
    {P : C} (e : P ≅ A) {f g : P ⟶ A} (hh : R.map f = R.map g) : f = g := by
  have hx : e.inv ≫ f = e.inv ≫ g := h (by simp only [Functor.map_comp, hh])
  calc
    f = e.hom ≫ (e.inv ≫ f) := by simp
    _ = e.hom ≫ (e.inv ≫ g) := by rw [hx]
    _ = g := by simp

private theorem normalize_weil
    (h : Function.Bijective (fun f : A ⟶ A ↦ R.map f))
    (T : C ⥤ C) (S : E ⥤ E) (ρ : R ⋙ S ≅ T ⋙ R)
    {B : E} (β : R.obj A ≅ B) (w : S.obj B ≅ B) (θ₀ : T.obj A ≅ A) :
    ∃ θ : T.obj A ≅ A,
      ρ.hom.app A ≫ R.map θ.hom ≫ β.hom = S.map β.hom ≫ w.hom ∧
      ∀ {P : C} (α : R.obj P ≅ B) (θP : T.obj P ≅ P) (e : P ≅ A),
        R.map e.hom ≫ β.hom = α.hom →
        ρ.hom.app P ≫ R.map θP.hom ≫ α.hom = S.map α.hom ≫ w.hom →
        θP.hom ≫ e.hom = T.map e.hom ≫ θ.hom := by
  let d : R.obj (T.obj A) ≅ R.obj A :=
    (ρ.app A).symm ≪≫ S.mapIso β ≪≫ w ≪≫ β.symm
  obtain ⟨θ, hθ, _⟩ := lift_iso R h θ₀ d
  have hn : ρ.hom.app A ≫ R.map θ.hom ≫ β.hom = S.map β.hom ≫ w.hom := by
    rw [hθ]
    simp [d, Category.assoc]
  refine ⟨θ, hn, ?_⟩
  intro P α θP e he hP
  apply map_injective_of_iso R h.1 (θP ≪≫ e)
  apply (cancel_epi (ρ.hom.app P)).1
  apply (cancel_mono β.hom).1
  calc
    (ρ.hom.app P ≫ R.map (θP.hom ≫ e.hom)) ≫ β.hom =
        ρ.hom.app P ≫ R.map θP.hom ≫ α.hom := by
      simp only [Functor.map_comp, Category.assoc, he]
    _ = S.map α.hom ≫ w.hom := hP
    _ = S.map (R.map e.hom) ≫ (S.map β.hom ≫ w.hom) := by
      rw [← he, Functor.map_comp, Category.assoc]
    _ = S.map (R.map e.hom) ≫ (ρ.hom.app A ≫ R.map θ.hom ≫ β.hom) := by rw [hn]
    _ = (ρ.hom.app P ≫ R.map (T.map e.hom ≫ θ.hom)) ≫ β.hom := by
      rw [Functor.map_comp]
      simp only [← Category.assoc]
      have hnat := ρ.hom.naturality e.hom
      change S.map (R.map e.hom) ≫ ρ.hom.app A =
        ρ.hom.app P ≫ R.map (T.map e.hom) at hnat
      rw [hnat]

private theorem normalized_hom_bijective (M : C) (F : D) :
    Function.Bijective (fun f : I.obj M ⟶ I.obj (R.obj F) ↦
      L'.map f ≫ γ.hom.app (R.obj F) ≫ J.map (adj.counit.app F)) := by
  let e : (I.obj M ⟶ I.obj (R.obj F)) ≃ (L'.obj (I.obj M) ⟶ J.obj F) :=
    (Functor.FullyFaithful.ofFullyFaithful I).homEquiv.symm |>.trans
      ((adj.homEquiv M F).symm.trans
        ((Functor.FullyFaithful.ofFullyFaithful J).homEquiv.trans
          (γ.app M).symm.homFromEquiv))
  have he (f : I.obj M ⟶ I.obj (R.obj F)) :
      e f = L'.map f ≫ γ.hom.app (R.obj F) ≫ J.map (adj.counit.app F) := by
    change γ.hom.app M ≫ J.map ((adj.homEquiv M F).symm (I.preimage f)) = _
    rw [Adjunction.homEquiv_counit, Functor.map_comp]
    have hn := γ.hom.naturality (I.preimage f)
    change L'.map (I.map (I.preimage f)) ≫ γ.hom.app (R.obj F) =
      γ.hom.app M ≫ J.map (L.map (I.preimage f)) at hn
    rw [Functor.map_preimage] at hn
    rw [← Category.assoc, ← hn, Category.assoc]
  exact (show (fun f ↦ L'.map f ≫ γ.hom.app (R.obj F) ≫
    J.map (adj.counit.app F)) = e from funext fun f ↦ (he f).symm) ▸ e.bijective

private theorem endomorphism_map_bijective (F : D) [IsIso (adj.counit.app F)] :
    Function.Bijective (fun f : I.obj (R.obj F) ⟶ I.obj (R.obj F) ↦ L'.map f) := by
  have hb := normalized_hom_bijective L R adj I J L' γ (R.obj F) F
  have : IsIso (γ.hom.app (R.obj F) ≫ J.map (adj.counit.app F)) := inferInstance
  constructor
  · intro f g hfg
    exact hb.1 (congrArg
      (fun k ↦ k ≫ γ.hom.app (R.obj F) ≫ J.map (adj.counit.app F)) hfg)
  · intro g
    obtain ⟨f, hf⟩ := hb.2 (g ≫ γ.hom.app (R.obj F) ≫ J.map (adj.counit.app F))
    exact ⟨f, (cancel_mono (γ.hom.app (R.obj F) ≫ J.map (adj.counit.app F))).1 hf⟩

private theorem boundary_ext_zero (adj : L ⊣ R) (F : B) (T : A)
    (hT : IsZero (L.obj T))
    (δ : (DerivedCategory.singleFunctor A 0).obj T ⟶
      ((DerivedCategory.singleFunctor A 0).obj (R.obj F))⟦(1 : ℤ)⟧) : δ = 0 := by
  let : HasExt A := HasExt.standard A
  let ξ : Abelian.Ext T (R.obj F) 1 := Abelian.Ext.homAddEquiv.symm δ
  have hξ : ξ.hom = δ := Abelian.Ext.homAddEquiv.apply_symm_apply δ
  obtain ⟨M, a, b, hab, h, he⟩ :=
    (ext_one_extension_classification.{max u v, max u v, t, t, v, v, u, u} (R.obj F) T).1 ξ
  have ha : IsIso (L.map a) := (h.map_of_exact L).isIso_f_iff.mpr hT
  let r : M ⟶ R.obj F :=
    (adj.homEquiv M F) (inv (L.map a) ≫ adj.counit.app F)
  have har : a ≫ r = 𝟙 _ := by
    apply (adj.homEquiv (R.obj F) F).symm.injective
    rw [adj.homEquiv_naturality_left_symm, adj.homEquiv_symm_id]
    simp [r]
  have hδ : h.singleδ = δ := by
    rw [← ShortComplex.ShortExact.extClass_hom, he]
    exact hξ
  have hz : δ ≫ ((DerivedCategory.singleFunctor A 0).map a)⟦(1 : ℤ)⟧' = 0 := by
    rw [← hδ]
    exact comp_distTriang_mor_zero₃₁ _ h.singleTriangle_distinguished
  calc
    δ = (δ ≫ ((DerivedCategory.singleFunctor A 0).map a)⟦(1 : ℤ)⟧') ≫
        ((DerivedCategory.singleFunctor A 0).map r)⟦(1 : ℤ)⟧' := by
      simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, har,
        CategoryTheory.Functor.map_id, Category.comp_id]
    _ = 0 := by rw [hz, zero_comp]

private theorem shifted_single_to_single_zero (M T : A)
    (f : ((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧ ⟶
      (DerivedCategory.singleFunctor A 0).obj T) : f = 0 := by
  have ht : DerivedCategory.TStructure.t.IsLE
      (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) (-1) :=
    DerivedCategory.TStructure.t.isLE_shift
      ((DerivedCategory.singleFunctor A 0).obj M) 0 1 (-1) (by lia)
  exact DerivedCategory.TStructure.t.zero_of_isLE_of_isGE f (-1) 0 (by lia) ht
    (inferInstanceAs (DerivedCategory.TStructure.t.IsGE
      ((DerivedCategory.singleFunctor A 0).obj T) 0))

private def shifted_iso
    (T : A ⥤ A) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (M : A) (b : T.obj M ≅ M) :
    T.mapDerivedCategory.obj (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧ :=
  (T.mapDerivedCategory.commShiftIso (1 : ℤ)).app
      ((DerivedCategory.singleFunctor A 0).obj M) ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso
      ((T.mapDerivedCategorySingleFunctor 0).app M ≪≫
        (DerivedCategory.singleFunctor A 0).mapIso b)

private theorem open_counit_isIso : IsIso (upperStarLowerStarAdjunction Λ j).counit := by
  let aj := ProEtale.openImmersionRestrictionLowerStarAdjunction Ab.{u + 1} j
  let : (ProEtale.lowerStar Ab.{u + 1} j).Full := aj.fullyFaithfulROfIsIsoCounit.full
  let : (ProEtale.lowerStar Ab.{u + 1} j).Faithful := aj.fullyFaithfulROfIsIsoCounit.faithful
  have : IsIso (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} j).counit :=
    Adjunction.counit_isIso_of_R_fully_faithful _
  let adj := (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} j).mapModAdjunction
    (condensedRingObj Λ C)
  have : IsIso adj.counit := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun N ↦ ?_
    have : IsIso ((Mod.forget _).map (adj.counit.app N)) := by
      rw [Mod.forget_map, Adjunction.mapModAdjunction_counit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have hf : (lowerStar Λ j).FullyFaithful :=
    ((Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ j)).fullyFaithfulFunctor.comp
      adj.fullyFaithfulROfIsIsoCounit).ofIso (comapPullbackHomCompIso Λ j)
  let := hf.full
  let := hf.faithful
  exact Adjunction.counit_isIso_of_R_fully_faithful _

private theorem geometric_open : IsOpenImmersion (geomJ D c) :=
  MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) c.j inferInstance

private def shiftedRestrictionComparison :
    (DerivedCategory.singleFunctor (Modules D ell (geomC D c)) 0 ⋙
      shiftFunctor _ (1 : ℤ)) ⋙ restriction D ell c ≅
    CondensedRing.upperStar (coeff ell) (geomJ D c) ⋙ shiftedSheaf D ell c :=
  (Functor.associator _ _ _ ) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor _ 0)
      ((restriction D ell c).commShiftIso (1 : ℤ)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((CondensedRing.upperStar (coeff ell) (geomJ D c)).mapDerivedCategorySingleFunctor 0)
      (shiftFunctor _ (1 : ℤ)) ≪≫
    Functor.associator _ _ _

private theorem shifted_weil_isIso
    (F : StrictWeilCondensed.WeilModule (coeff ell) (frobU D c)) :
    IsIso (shiftedWeilMap D ell c F) := by
  unfold shiftedWeilMap
  infer_instance

private theorem boundary_minimal_of_iso (hEll : ell ≠ D.p)
    (F : StrictWeilCondensed.WeilModule (coeff ell) (frobU D c))
    {P : DerivedCategory (Modules D ell (geomC D c))}
    (e : P ≅ shiftedImage D ell c F)
    (hA : BoundaryMinimal D ell c F (shiftedImage D ell c F) hEll) :
    BoundaryMinimal D ell c F P hEll := by
  intro Q hQ hZero
  obtain ⟨hi, ho⟩ := hA Q hQ hZero
  constructor
  · intro f
    exact (cancel_mono e.hom).1 (by simpa using hi (f ≫ e.hom))
  · intro f
    exact (cancel_epi e.inv).1 (by simpa using ho (e.inv ≫ f))

/-- The ordinary direct image shifted by one is the perverse intermediate extension.
Proof (deferred at stage 2), following the nine DAG steps.  (1) Base change preserves
separatedness, finite type, smoothness, geometric connectedness and dimension one; the
open remains dense and has finite closed complement.  (2) Apply the current definition
of the ordinary degree-zero direct image and the curve-heart basic-object clause; the
open counit is the canonical identification.  (3) A heart object restricting to zero
has only degree-zero punctual cohomology by the curve-heart description.  (4) The
Ext-one classification and ordinary adjunction retract the first map of an extension,
forcing the boundary-to-image Hom to vanish; standard t-structure orthogonality gives
the reverse vanishing.  (5) The truncation exact sequence and minimality kill degree
zero, so every minimal extension is a shifted sheaf.  (6) The adjoint to the ordinary
direct image has punctual kernel and cokernel; the kernel-free and boundary-minimal
arguments make it an isomorphism.  (7) Full faithfulness of shifted single complexes
and ordinary adjunction give the unique comparison with the prescribed open map.
(8) The canonical Frobenius square and degree-zero comparison give the induced Weil
isomorphism, normalized on the open.  (9) Uniqueness of the normalized comparison
proves Weil equivariance.  The assertion is stated in the geometric derived category,
with the Weil convention supplied by the current curve-heart interface.
Source: `literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-fourier-transform/sec-wft-perverse/sk-lem-wft-curve-heart/rem-dl-a1-conventions.md`;
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension).
-/
theorem condensed_curve_intermediate_extension
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (c : Scheme.MiddleExtensionCurve D)
    (_hEll : ell ≠ D.p) [GeometricallyConnected c.C.hom]
    (F : StrictWeilCondensed.WeilModule (coeff ell) (frobU D c))
    (_hCons : IsConstantModelConstructible (coeff ell) (geomU D c) F.carrier)
    (_hLisse : IsLisseCoefficientModule (coeff ell) F.carrier) :
    IntermediateExtensionAssertion D ell c _hEll F := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedCurveIntermediateExtension
