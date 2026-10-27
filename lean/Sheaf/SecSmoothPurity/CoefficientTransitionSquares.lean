/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.NormalizedCoefficientDiagram
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.BifunctorShift
import all Sheaf.SecSmoothPurity.NormalizedKappaTransitions
import Sheaf.SecSmoothPurity.NormalizedScalarTensorTransitions
/-! # CoefficientTransitionSquares

Source: Stacks Project, Modules on Sites, Tags 03EK and 03EL, and
Cohomology on Sites, Tag 07A4.
(blueprint: lem-pur-normalized-coefficient-transition-squares).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] SheafOfModules.monoidalCategory
universe w uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open SheafOfModules
namespace CategoryTheory.CochainPullback.StrictCoefficient
variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

open KappaCalculation
attribute [local irreducible] scalarComp scalarUnit extensionAdjunction generator
attribute [local irreducible] extensionFunctor Comparisons.pullArrow squareArrow
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem kappaTransitionLaws (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (hn : e.Normalized c) : e.KappaTransitionLaws := by
  intro i j k l a b r s h P Q f
  ext p : 1
  apply ((extensionAdjunction (d.S.map s)).homEquiv _ _).injective
  apply ((extensionAdjunction (d.S.map a)).homEquiv _ _).injective
  apply pull_generator_hom_ext (d.ringed i) (c i) (P.X p)
  intro Z x
  apply Sheaf.hom_ext
  ext U v
  change (d.inverse.obj Z).obj.obj U at v
  change ((kappaTransitionForward e a b r s h P Q f).f p).val.app U
      (((extensionAdjunction (d.S.map s)).unit.app
        ((extensionFunctor (d.S.map a)).obj ((d.L i).obj (P.X p)))).val.app U
        (((extensionAdjunction (d.S.map a)).unit.app ((d.L i).obj (P.X p))).val.app U
          ((generator (d.ringed i) (c i) x).hom.app U v))) =
    ((e.kappa b).hom.app (Q.X p)).val.app U
      (((squareArrow d.S a b r s h ((pull (d.ringed i)).obj P)
        ((pull (d.ringed k)).obj Q) (e.pullArrow r P Q f)).f p).val.app U
        (((extensionAdjunction (d.S.map s)).unit.app
          ((extensionFunctor (d.S.map a)).obj ((d.L i).obj (P.X p)))).val.app U
          (((extensionAdjunction (d.S.map a)).unit.app ((d.L i).obj (P.X p))).val.app U
            ((generator (d.ringed i) (c i) x).hom.app U v))))
  erw [extension_unit, extension_unit]
  have ht := (kappaTransitionValues d c e hn a b r s h P Q f p U 1 1
    (((d.algebraic i).moduleUnderlying.inv.app (P.X p)).hom.app U
      ((d.inverse.map x).hom.app U v))).1
  have hq : (generator (d.ringed i) (c i) x).hom.app U v =
      diagramPullSection d i (P.X p) U 1
        (((d.algebraic i).moduleUnderlying.inv.app (P.X p)).hom.app U
          ((d.inverse.map x).hom.app U v)) := by
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    exact (show _ from by
      erw [diagramPullSection_eq d c, one_smul]
      unfold generator
      rfl)
  rw [hq]
  simp only [map_one, one_mul] at ht
  refine ht.trans ?_
  symm
  erw [squareArrow_value, map_one, mul_one, semilinear_pullArrow_section d c e hn,
    kappa_section d c e hn, map_one, mul_one]


/-- The independent transition calculation used in strict totalization.
Source: Stacks 03EK, 03EL and 07A4
(blueprint: lem-pur-normalized-coefficient-transition-squares).

Proof: Both routes are tested after scalar-extension adjunctions. Kappa normalization
identifies their unit insertions with the same inverse image of the semilinear
transition. For tensor transitions, test each coproduct summand and the two
scalar-extension units in each factor. Both pairings are the tensor of the two
semilinear maps. Multiplicativity and unitality of the coefficient maps identify
the coefficients. Adjunction injectivity, the tensor universal property and
coproduct extensionality give the whole chain-map equations. No transition is inverted.
-/
theorem normalizedCoefficientTransitionSquares
    (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (_normalized : e.Normalized c) :
  e.KappaTransitionLaws ∧ TensorTransitionLaws d.R e.sigmaR ∧
    TensorTransitionLaws d.S e.sigmaS := by
  exact ⟨kappaTransitionLaws d c e _normalized,
    (ScalarCalculation.normalizedScalarTensorTransitions d.R e.sigmaR).1,
    (ScalarCalculation.normalizedScalarTensorTransitions d.S e.sigmaS).1⟩

end CategoryTheory.CochainPullback.StrictCoefficient
