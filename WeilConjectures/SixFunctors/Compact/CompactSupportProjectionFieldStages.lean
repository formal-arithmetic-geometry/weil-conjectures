/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates
import WeilConjectures.SixFunctors.Compact.CompactSupportProjectionIntegralStages
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Tactic.Convert
import all Mathlib.Logic.Small.Defs
import WeilConjectures.SixFunctors.Rational.RationalProjectionComparisonEquations
import WeilConjectures.SixFunctors.Common.CommonProjectionComparisonEquations

/-! # Field coefficient projection laws

The field part of the compact-support projection formula.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false

universe u v w v' w'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open CategoryTheory.SuppliedExchangeProjection

namespace WeilConjectures

section Transport
variable {D : FiniteFieldDatum.{u}}
  {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
  {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]
  {P : SixFunctorPushStage D B} {P' : SixFunctorPushStage D B'}
  {T : ∀ X, B X ⥤ B X ⥤ B X} {T' : ∀ X, B' X ⥤ B' X ⥤ B' X}
  {Q : SixFunctorCompactifiedSquare D}
  {A : SixFunctorExchangeData P T Q} {A' : SixFunctorExchangeData P' T' Q}
  {V : ∀ X, B X ⥤ B' X} {c : SixFunctorCoefficientComparison P P' V}

private theorem projection_natural (A : SixFunctorExchangeData P T Q)
    (K K' : B Q.X) (L L' : B Q.Y) (a : K ⟶ K') (b : L ⟶ L') :
    ((T Q.Y).map ((P.support Q.f Q.compactification).map a)).app L ≫
        ((T Q.Y).obj ((P.support Q.f Q.compactification).obj K')).map b ≫
        A.projectionComponent K' L' =
      A.projectionComponent K L ≫ (P.support Q.f Q.compactification).map
        (((T Q.X).map a).app ((P.pull Q.f).obj L) ≫
          ((T Q.X).obj K').map ((P.pull Q.f).map b)) := by
  let η := Functor.uncurry.map A.stage.projection
  have hs : (P.support Q.f Q.compactification).prod (𝟭 (B Q.Y)) ⋙
      Functor.uncurry.obj (T Q.Y) =
      Functor.uncurry.obj (A.stage.compactSupport ⋙ A.stage.tensorY) := by
    simp only [← A.tensorY, ← A.compactSupport]
    rfl
  have ht : ((𝟭 (B Q.X)).prod (P.pull Q.f) ⋙ Functor.uncurry.obj (T Q.X)) ⋙
      P.support Q.f Q.compactification = Functor.uncurry.obj
        ((Functor.postcompose₂.obj A.stage.compactSupport).obj
          ((((Functor.whiskeringLeft₂ (B Q.X)).obj (𝟭 (B Q.X))).obj
            A.stage.pull).obj A.stage.tensorX)) := by
    simp only [← A.tensorX, ← A.compactSupport, ← A.pull]
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro M
      rfl
    intro M M' f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    dsimp
    exact A.stage.compactSupport.map_comp _ _
  let η' := (eqToHom hs) ≫ η ≫ (eqToHom ht.symm)
  have hc : ∀ K L, η'.app (K, L) = A.projectionComponent K L := by
    intro K L
    simp only [η', NatTrans.comp_app, eqToHom_app, η, Functor.uncurry_map_app,
      SixFunctorExchangeData.projectionComponent]
  simpa only [hc, Functor.comp_map, Functor.prod_map, Functor.id_map,
    Functor.uncurry_obj_map, Functor.prod_obj, Functor.id_obj, Category.assoc]
    using η'.naturality (Prod.mkHom a b)

private theorem projection_isIso_of_iso (A : SixFunctorExchangeData P T Q)
    {K K' : B Q.X} {L L' : B Q.Y} (a : K ≅ K') (b : L ≅ L')
    [IsIso (A.projectionComponent K' L')] : IsIso (A.projectionComponent K L) := by
  have h := projection_natural A K K' L L' a.hom b.hom
  have hi : IsIso
      (((T Q.Y).map ((P.support Q.f Q.compactification).map a.hom)).app L ≫
        ((T Q.Y).obj ((P.support Q.f Q.compactification).obj K')).map b.hom ≫
        A.projectionComponent K' L') := inferInstance
  rw [h] at hi
  simpa only [isIso_comp_right_iff] using hi

end Transport

private theorem integral_finiteTor {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (X : SixFunctorSpace D)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    finiteTorConstructibleIntegral C.l E X.obj.left K.obj := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) := fun x ↦
    let φ := ((Scheme.ΓSpecIso (.of D.k)).inv ≫ X.obj.hom.appTop ≫
      X.obj.left.Γevaluation x).hom
    (Eq.mp (congrArg IsUnit (map_natCast φ C.l))
      ((isUnit_iff_ne_zero.mpr
        (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out : C.l.Prime)
          C.different.symm)).map φ)).invertible
  rw [← (integral_residue_tor D C.l C.different E X.obj.left).2]
  exact K.property

end WeilConjectures
