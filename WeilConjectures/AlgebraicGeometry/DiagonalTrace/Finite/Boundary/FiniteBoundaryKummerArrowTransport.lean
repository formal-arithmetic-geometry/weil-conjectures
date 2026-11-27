/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Boundary.FiniteBoundarySourceEndpointTransport
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Boundary.FiniteBoundaryTargetEndpointTransport
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralKummer
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralEndpoints
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryExactTransport

/-! The finite boundary square assembled after its two endpoint transports.

## Implementation details

The finite Chern normalization is stated in the standard model of the derived category of
abelian sheaves, while the assembled square uses the model supplied by
`DiagonalTraceLocalizations`. The square is therefore first proved as an equality of `Ext`
classes, which does not depend on the model, by checking it in the standard model.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses
attribute [local implicit_reducible] spCoefficientCommRings SpTowerShriek.tau Functor.ofOpSequence
  Functor.ofSequence WeilConjectures.SemilinearSections.evaluation

abbrev source_endpoint_statement
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r) (n : ℕ) : Prop :=
  let S := DerivedCategory.singleFunctor (DiagonalAb T) 0
  let e := finiteBoundaryRestrictionUnderlying l T r n
  S.map (finiteQuotient l (ULift (Padic l)) T n) ≫
      S.map (e.inv.app (coefficient T (Arings l (ULift (Padic l)) T))) =
    S.map (diagonalCoefficientIntegerMap T (Scheme.purTwistFiniteRing T l n) ≫
      k.coefficientForget.inv.app (op n))

abbrev target_endpoint_statement
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hN : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))) : Prop :=
  let S := DerivedCategory.singleFunctor (DiagonalAb T) 0
  let e := finiteBoundaryRestrictionUnderlying l T r n
  S.map (finiteRootMap l (ULift (Padic l)) T n) ≫
      S.map ((finiteForget l (ULift (Padic l)) T n).mapIso
        (lineEvaluation l (ULift (Padic l)) c n)).inv ≫
      S.map (e.inv.app (lineModule l (ULift (Padic l)) c)) ≫
      S.map (k.lineForget.hom.app (op n)) ≫
      S.map (cartierProRootMap A (l ^ (n + 1)) hA T
        (pow_pos (Fact.out : l.Prime).pos _) hN) =
    S.map (cartierProRootMap A (l ^ (n + 1)) hA T
      (pow_pos (Fact.out : l.Prime).pos _) hN)

/-- Pasting a source endpoint square, a naturality square, a normalization square and a target
endpoint square in a category with a shift. -/
private theorem finiteBoundary_paste {D : Type*} [Category D] [HasShift D ℤ]
    {S₀ S₁ S₂ L₁ L₁' L₂ R R' : D} (x : S₀ ⟶ S₂) (q : S₀ ⟶ S₁) (ei : S₁ ⟶ S₂)
    (mF : S₂ ⟶ L₂⟦(2 : ℤ)⟧) (mG : S₁ ⟶ L₁⟦(2 : ℤ)⟧) (eiL : L₁ ⟶ L₂) (h : L₁ ⟶ L₁')
    (hi : L₁' ⟶ L₁) (ρ : R ⟶ L₁') (lf : L₂ ⟶ R) (root : R ⟶ R') (lr : L₂ ⟶ R')
    (β : S₀ ⟶ R⟦(2 : ℤ)⟧) (hs : q ≫ ei = x) (hnat : ei ≫ mF = mG ≫ eiL⟦(2 : ℤ)⟧')
    (hN : q ≫ mG ≫ h⟦(2 : ℤ)⟧' = β ≫ ρ⟦(2 : ℤ)⟧') (hhi : h ≫ hi = 𝟙 _)
    (ht : ρ ≫ hi ≫ eiL ≫ lf ≫ root = root) (hlr : lf ≫ root = lr) :
    x ≫ mF ≫ lr⟦(2 : ℤ)⟧' = β ≫ root⟦(2 : ℤ)⟧' := by
  rw [← hs, Category.assoc, reassoc_of% hnat, ← hlr]
  conv_rhs => rw [← ht]
  simp only [Functor.map_comp]
  rw [← reassoc_of% hN, ← Functor.map_comp_assoc (shiftFunctor D (2 : ℤ)) h hi, hhi,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The derived arrow of an `Ext` class pre- and postcomposed with ordinary maps after an exact
functor. -/
private theorem ext_mk₀_comp_mapExactFunctor_comp_hom {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [HasExt C] [HasExt D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y : C} {X' Y' : D} (a : X' ⟶ F.obj X) (x : Ext X Y 2) (b : F.obj Y ⟶ Y') :
    ((Ext.mk₀ a).comp ((x.mapExactFunctor F).comp (Ext.mk₀ b) (add_zero 2))
        (zero_add 2)).hom =
      (DerivedCategory.singleFunctor D 0).map a ≫ mapSingleArrow F (2 : ℤ) x.hom ≫
        ((DerivedCategory.singleFunctor D 0).map b)⟦(2 : ℤ)⟧' := by
  rw [Ext.comp_hom, Ext.comp_hom, Ext.mk₀_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp,
    ShiftedHom.comp_mk₀, ← FiniteExactArrow.mapSingleArrow_ext]
  rfl

/-- `Ext` groups of abelian sheaves, stated with the abelian structure `diagonalAbSheafAbelian`. -/
private theorem diagonalAbHasExt (T : Scheme.{u}) : HasExt.{u + 1} (DiagonalAb T) :=
  inferInstance

attribute [local instance 100000] diagonalAbHasExt

section Assembly

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 100000] integralAbDerived
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The finite boundary square in the standard model of the derived category of abelian sheaves,
where the finite Chern normalization is stated. -/
private theorem finiteBoundary_transport_square
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hN : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (hc : FiniteChernNormalization l (ULift.{u} (Padic l)) c) (P : T.Pic)
    (hs : finiteQuotient l (ULift.{u} (Padic l)) T n ≫
        (finiteBoundaryRestrictionUnderlying l T r n).inv.app
          (coefficient T (Arings l (ULift.{u} (Padic l)) T)) =
      diagonalCoefficientIntegerMap T (Scheme.purTwistFiniteRing T l n) ≫
        k.coefficientForget.inv.app (op n))
    (ht : finiteRootMap l (ULift.{u} (Padic l)) T n ≫
        ((finiteForget l (ULift.{u} (Padic l)) T n).mapIso
          (lineEvaluation l (ULift.{u} (Padic l)) c n)).inv ≫
        (finiteBoundaryRestrictionUnderlying l T r n).inv.app
          (lineModule l (ULift.{u} (Padic l)) c) ≫
        k.lineForget.hom.app (op n) ≫
        cartierProRootMap A (l ^ (n + 1)) hA T (pow_pos (Fact.out : l.Prime).pos _) hN =
      cartierProRootMap A (l ^ (n + 1)) hA T (pow_pos (Fact.out : l.Prime).pos _) hN) :
    (DerivedCategory.singleFunctor (DiagonalAb T) 0).map
        (diagonalCoefficientIntegerMap T (Scheme.purTwistFiniteRing T l n) ≫
          k.coefficientForget.inv.app (op n)) ≫
      mapSingleArrow (C := Systems T (Arings l (ULift.{u} (Padic l)) T)) (D := DiagonalAb T)
        (r.F ⋙ (evaluation ℕᵒᵖ (DiagonalMod l T)).obj (op n) ⋙ diagonalForget l T) (2 : ℤ)
        (firstChern l (ULift.{u} (Padic l)) c P) ≫
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map (k.lineForget.hom.app (op n) ≫
        cartierProRootMap A (l ^ (n + 1)) hA T (pow_pos (Fact.out : l.Prime).pos _) hN))⟦(2 : ℤ)⟧' =
      evaluatedTowerBoundary l T n c.kummer P ≫
        ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          (cartierProRootMap A (l ^ (n + 1)) hA T
            (pow_pos (Fact.out : l.Prime).pos _) hN))⟦(2 : ℤ)⟧' := by
  let S := DerivedCategory.singleFunctor (DiagonalAb T) 0
  have hb : finiteBoundaryEquality
      (S.map (finiteQuotient l (ULift.{u} (Padic l)) T n))
      ((S.map (finiteRootMap l (ULift.{u} (Padic l)) T n))⟦(2 : ℤ)⟧')
      (mapSingleArrow (finiteForget l (ULift.{u} (Padic l)) T n) (2 : ℤ)
        (evaluatedChern l (ULift.{u} (Padic l)) c P n))
      (evaluatedTowerBoundary l T n c.kummer P) := hc P n
  obtain ⟨α, β, hα, hβ, hb⟩ := hb
  obtain rfl := eq_of_heq hα
  obtain rfl := eq_of_heq hβ
  simp only [evaluatedChern, mapSingleArrow_postcompose] at hb
  erw [mapSingleArrow_composite] at hb
  exact finiteBoundary_paste _ _ _ _ _ _ _
    (S.map ((finiteForget l (ULift.{u} (Padic l)) T n).mapIso
      (lineEvaluation l (ULift.{u} (Padic l)) c n)).inv) _ _ _ _ _
    ((S.map_comp _ _).symm.trans (congrArg S.map hs))
    (mapSingleArrow_natIso _ _ (finiteBoundaryRestrictionUnderlying l T r n).symm (2 : ℤ)
      (firstChern l (ULift.{u} (Padic l)) c P)) hb
    (by rw [← S.map_comp]; simp) (by
      refine Eq.trans ?_ (congrArg S.map ht)
      simp only [Functor.map_comp]
      rfl)
    (S.map_comp _ _).symm

/-- The finite boundary square as an equality of `Ext` classes, checked in the standard model
of the derived category of abelian sheaves. -/
private theorem finiteBoundary_transport_assembly_ext
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hN : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    [HasExt.{w} (Systems T (Arings l (ULift.{u} (Padic l)) T))]
    (P : T.Pic)
    (x : Ext (coefficient T (Arings l (ULift.{u} (Padic l)) T))
      (lineModule l (ULift.{u} (Padic l)) c) 2)
    (hx : x.hom = firstChern l (ULift.{u} (Padic l)) c P)
    (h : (DerivedCategory.singleFunctor (DiagonalAb T) 0).map
        (diagonalCoefficientIntegerMap T (Scheme.purTwistFiniteRing T l n) ≫
          k.coefficientForget.inv.app (op n)) ≫
      mapSingleArrow (C := Systems T (Arings l (ULift.{u} (Padic l)) T)) (D := DiagonalAb T)
        (r.F ⋙ (evaluation ℕᵒᵖ (DiagonalMod l T)).obj (op n) ⋙ diagonalForget l T) (2 : ℤ)
        (firstChern l (ULift.{u} (Padic l)) c P) ≫
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map (k.lineForget.hom.app (op n) ≫
        cartierProRootMap A (l ^ (n + 1)) hA T (pow_pos (Fact.out : l.Prime).pos _) hN))⟦(2 : ℤ)⟧' =
      evaluatedTowerBoundary l T n c.kummer P ≫
        ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          (cartierProRootMap A (l ^ (n + 1)) hA T
            (pow_pos (Fact.out : l.Prime).pos _) hN))⟦(2 : ℤ)⟧') :
    (Ext.mk₀ (diagonalCoefficientIntegerMap T (Scheme.purTwistFiniteRing T l n) ≫
        k.coefficientForget.inv.app (op n))).comp
      ((x.mapExactFunctor
          (r.F ⋙ (evaluation ℕᵒᵖ (DiagonalMod l T)).obj (op n) ⋙ diagonalForget l T)).comp
        (Ext.mk₀ (k.lineForget.hom.app (op n) ≫
          cartierProRootMap A (l ^ (n + 1)) hA T (pow_pos (Fact.out : l.Prime).pos _) hN))
        (add_zero 2)) (zero_add 2) =
      evaluatedIntegralKummerClass l T A n hA c.kummer hN P := by
  apply Ext.ext
  refine (ext_mk₀_comp_mapExactFunctor_comp_hom (C := Systems T (Arings l (ULift.{u} (Padic l)) T))
    (D := DiagonalAb T)
    (r.F ⋙ (evaluation ℕᵒᵖ (DiagonalMod l T)).obj (op n) ⋙ diagonalForget l T)
    (diagonalCoefficientIntegerMap T (Scheme.purTwistFiniteRing T l n) ≫
      k.coefficientForget.inv.app (op n)) x
    (k.lineForget.hom.app (op n) ≫
      cartierProRootMap A (l ^ (n + 1)) hA T (pow_pos (Fact.out : l.Prime).pos _) hN)).trans ?_
  rw [hx, evaluatedIntegralKummerClass_hom]
  exact h

end Assembly

/-- Assemble the finite boundary square once the source coefficient-one and
root endpoint equations have been supplied. -/
theorem finiteBoundary_transport_assembly
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hN : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (hc : FiniteChernNormalization l (ULift.{u} (Padic l)) c) (P : T.Pic)
    (hs : source_endpoint_statement l T c r k n)
    (ht : target_endpoint_statement l T c r k A n hA hN) :
    (finiteConeChernClass l T c r k A n hA hN
        (firstChern l (ULift.{u} (Padic l)) c P)).hom =
      (evaluatedIntegralKummerClass l T A n hA c.kummer hN P).hom := by
  let := HasExt.standard (Systems T (Arings l (ULift.{u} (Padic l)) T))
  let S := DerivedCategory.singleFunctor (DiagonalAb T) 0
  let x := Ext.homEquiv.symm (firstChern l (ULift.{u} (Padic l)) c P)
  have hx : x.hom = firstChern l (ULift.{u} (Padic l)) c P := Ext.homEquiv.apply_symm_apply _
  refine Eq.trans ?_ (congrArg Ext.hom (finiteBoundary_transport_assembly_ext l T c r k A n hA hN
    P x hx (finiteBoundary_transport_square l T c r k A n hA hN hc P
      (S.map_injective (by rw [S.map_comp]; exact hs))
      (S.map_injective (by
        refine Eq.trans ?_ ht
        simp only [Functor.map_comp]
        rfl)))))
  rw [finiteConeChernClass]
  change Ext.homEquiv (Ext.homEquiv.symm _) = _
  rw [Equiv.apply_symm_apply]
  refine Eq.trans ?_ (ext_mk₀_comp_mapExactFunctor_comp_hom
    (C := Systems T (Arings l (ULift.{u} (Padic l)) T)) (D := DiagonalAb T)
    (r.F ⋙ (evaluation ℕᵒᵖ (DiagonalMod l T)).obj (op n) ⋙ diagonalForget l T)
    (diagonalCoefficientIntegerMap T (Scheme.purTwistFiniteRing T l n) ≫
      k.coefficientForget.inv.app (op n)) x
    (k.lineForget.hom.app (op n) ≫
      cartierProRootMap A (l ^ (n + 1)) hA T (pow_pos (Fact.out : l.Prime).pos _) hN)).symm
  rw [hx]

end AlgebraicGeometry.ProEtale.DiagonalTrace
