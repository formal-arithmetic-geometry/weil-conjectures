/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFiniteDiagonal
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryEndpointMaps
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.IntegralSitePullbackIntegerEndpointMate
import all WeilConjectures.AlgebraicGeometry.CartierReductionData

/-! # The transported supported integral unit is the constant direct-image map -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- The supported integral unit transported to the pro-etale site is the canonical
constant-sheaf direct-image map.

Proof: transpose through the comparison adjunction. The unit equation of the base-change
mate and naturality of the direct-image comparison reduce the claim to the integer
endpoint mate equation. -/
theorem supportedIntegralUnit_eq_constantDirectImageMap (S : Scheme.{u}) :
    supportedIntegralUnit S = proEtaleConstantDirectImageMap (diagonalImmersion S)
      AddCommGrpCat.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} ℤ)) := by
  let i := diagonalImmersion S
  let W := diagonalSurface S
  let D := ProjectiveLine S
  let adW := comparisonAdjunction AddCommGrpCat.{u + 1} W
  let adD := comparisonAdjunction AddCommGrpCat.{u + 1} D
  let F := Etale.supportedIntegralConstant D
  let α := (lowerStarCompComparisonLowerStarIso i AddCommGrpCat.{u + 1}).inv
  have hm := unit_mateEquiv_symm adD adW α F
  have hmate := integral_site_pullback_integer_endpoint_mate i
  have hp : (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).homEquiv _ _
      (proEtaleConstantInverseImageMap i AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) =
      proEtaleConstantDirectImageMap i AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
    Equiv.apply_symm_apply ((proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).homEquiv _ _) _
  dsimp only at hmate
  rw [hp] at hmate
  have hX : adW.homEquiv _ _ (cartierIntegralSourceIso i).hom =
      (Etale.lowerStar AddCommGrpCat.{u + 1} i).map
        (adD.homEquiv _ _ (integerComparison D).hom) ≫
        α.app ((constantSheaf (ProEt.topology D) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    erw [Functor.map_comp]
    rw [← Category.assoc]
    erw [← hm]
    rw [Category.assoc]
    have hn := α.naturality (cartierIntegralConstantComparisonIso D).hom
    erw [← hn]
    rw [Functor.map_comp, Category.assoc]
    rfl
  unfold SpTowerClasses.supportedIntegralUnit
  rw [Iso.inv_comp_eq]
  apply (adW.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right, hX]
  exact hmate

/-- The constant direct-image map sends a constant integer to the same constant integer
on the base-changed chart. -/
theorem proEtaleConstantDirectImageMap_toSheafify {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.ProEtᵒᵖ) (k : ULift.{u + 1} ℤ) :
    (proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom.app U
        ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U k) =
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app ((proEtaleBaseChange f).op.obj U) k := by
  have h := Equiv.apply_symm_apply ((sheafificationAdjunction (ProEt.topology Y)
    AddCommGrpCat.{u + 1}).homEquiv _ ((proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).obj
      ((constantSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))))) (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))))
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun a ↦ (a.app U).hom k) h

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- After the supported integral unit, the supported finite quotient is the finite integer
quotient followed by the ordinary adjunct of the coefficient pullback.

Proof: both maps leave the integral constant sheaf, so it suffices to compare them on
constant integers. The ordinary push evaluation is injective; there the left side is the
integer by the defining property of the supported quotient, and the right side is the
integer by the normalization of the coefficient pullback and the fact that ring maps
preserve integer casts. -/
theorem supportedIntegralUnit_comp_finiteSupportedQuotient {b : SpTowerShriek.Base l E}
    {S : Scheme.{u}} (g : SpTowerShriek.Geometry l E b (diagonalImmersion S))
    (p : CoefficientPullback l E b (diagonalImmersion S) g) (n : ℕ) :
    supportedIntegralUnit S ≫ finiteSupportedQuotient l E g n =
      finiteQuotient l E (diagonalSurface S) n ≫
        (finiteForget l E (diagonalSurface S) n).map
          ((SpTowerShriek.ev l E (diagonalSurface S) n).map
            ((g.ordinaryAdjunction.homEquiv _ _) p.iso.hom)) := by
  rw [supportedIntegralUnit_eq_constantDirectImageMap]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology (diagonalSurface S)) _ _
    (ObjectProperty.FullSubcategory.property _)
  ext U k
  let W := diagonalSurface S
  let i := diagonalImmersion S
  let e := (g.ordinaryPushEvaluation n).app
    (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
  have hi : Function.Injective (e.hom.val.app U) := by
    apply Function.LeftInverse.injective (g := e.inv.val.app U)
    intro z
    exact congrArg (fun a ↦ a.val.app U z) e.hom_inv_id
  apply hi
  have hL := (finiteSupportedQuotient_existsUnique l E g n).exists.choose_spec U k
  have hu := proEtaleConstantDirectImageMap_toSheafify i U k
  erw [← hu] at hL
  have hq := (finiteQuotient_existsUnique l E W n).exists.choose_spec U k
  have hN := p.normalization n U (k.down : (SpTowerShriek.B l E W n).obj.obj U) _ hq.symm
  have hc := map_intCast ((proEtaleConstantDirectImageMap i CommRingCat.{u + 1}
    (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n)))).hom.app U).hom k.down
  exact eq_of_heq (hL.trans ((hN.trans (heq_of_eq hc)).symm))

/-- A finite source map is determined by its precomposition with an epimorphism into the
constant source: if the ordinary tower equation holds after this epimorphism and the
candidate map is the finite integer quotient followed by the ordinary coefficient map
there, then the evaluated ordinary map is the candidate.

Proof: cancel the epimorphism, rewrite the integer quotient by the generator formula, and
use naturality of the finite forgetting comparison. -/
theorem finite_source_of_precompose {T : Scheme.{u}} (c : Chern l E T)
    {Z : Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}}
    (v : (constantSheaf (ProEt.topology T) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ Z) [Epi v]
    {M : Systems T (Rrings l T)} (η : (constant T).obj Z ⟶ c.reduction.forget.F.obj M)
    {N : Systems T (Arings l E T)}
    (q : M ⟶ (WeilConjectures.SemilinearSections.res (coefficientSystemMap l E T)).obj N)
    (t : coefficient T (Arings l E T) ⟶ N) (n : ℕ)
    (f : Z ⟶ (finiteForget l E T n).obj ((SpTowerShriek.ev l E T n).obj N))
    (h : (constant T).map v ≫ η ≫ c.reduction.forget.F.map q =
      integerGenerator T (Rrings l T) c.reduction.forget ≫
        c.reduction.forget.F.map (scalarGenerator l E T ≫
          (WeilConjectures.SemilinearSections.res (coefficientSystemMap l E T)).map t))
    (hf : v ≫ f = finiteQuotient l E T n ≫
      (finiteForget l E T n).map ((SpTowerShriek.ev l E T n).map t)) :
    (abEvaluation T n).map η ≫ (c.reduction.forget.F ⋙ abEvaluation T n).map q ≫
      (finiteScalarForgetIso l E c n).hom.app N = f := by
  rw [← cancel_epi v, hf, ← finiteBoundary_sourceMap l E c n]
  have h' := congrArg (fun φ ↦ (abEvaluation T n).map φ ≫
    (finiteScalarForgetIso l E c n).hom.app N) h
  simp only [Functor.map_comp, Category.assoc] at h'
  have hn := (finiteScalarForgetIso l E c n).hom.naturality t
  simp only [Category.assoc]
  erw [← hn]
  exact h'

end AlgebraicGeometry.ProEtale.SpTowerClasses
