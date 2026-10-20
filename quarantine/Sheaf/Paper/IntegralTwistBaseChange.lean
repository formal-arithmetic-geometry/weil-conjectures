/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q138
-/
module

public import Sheaf.Paper.CoefficientTwistsDetailed
public import Sheaf.Paper.PurIntegralTwistLineInverseImage
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeDualPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.Paper.PurTwistSheafLocallyFree
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-! # Completed integral twist base change

Source: main-20261015 blueprint, sec-six-functors-basics/sk-prop-sf-existence,
`prop-weil-twist-preserves.proof.md`, first and final sentences
(blueprint: lem-weil-integral-twist-base-change).

The line, coefficient inclusion and scalar-extension isomorphism are the published
constructions of `def-coefficient-twists-detailed`. Scheme naturality is expressed
on their underlying semilinear maps, using the actual inverse-image adjunction.
The helper predicates specify the pullback identifications by roots, powers and evaluation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Forget only the module structure of the published signed integral twist line.
Source: twist-power and internal-Hom clauses of the coefficient-twist blueprint
(blueprint: lem-weil-integral-twist-base-change). -/
abbrev integralTwistUnderlying (S : Scheme.{u}) (m : ℤ) :=
  (SheafOfModules.toSheaf _).obj (integralTwistLine l E S m)

/-- The underlying additive sheaf map of the canonical signed scalar map.
Source: first and final sentences of `prop-weil-twist-preserves.proof.md`
(blueprint: lem-weil-integral-twist-base-change). -/
def integralTwistScalarUnderlying (S : Scheme.{u})
    [∀ x : S, Invertible (l : S.residueField x)]
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F) (m : ℤ) :
    integralTwistUnderlying l E S m ⟶ integralTwistUnderlying l F S m :=
  ⟨(PresheafOfModules.toPresheaf _).map (twistScalarMaps l E S F ι m).val⟩

/-- A local section transported along an inverse-image comparison, via its adjunct.
This uses source sections only at source objects and target sections at their base changes.
Source: scheme naturality in the final sentence of `prop-weil-twist-preserves.proof.md`
(blueprint: lem-weil-integral-twist-base-change). -/
def integralTwistInverseSection {X Y : Scheme.{u}} (h : X ⟶ Y)
    (ρ : ∀ m : ℤ, (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
      (integralTwistUnderlying l E Y m) ≅ integralTwistUnderlying l E X m)
    (m : ℤ) (V : Y.ProEtᵒᵖ) (x : (integralTwistLine l E Y m).val.obj V) :
    (integralTwistLine l E X m).val.obj ((proEtaleBaseChange h).op.obj V) :=
  (((proEtaleSheafAdjunction h AddCommGrpCat.{u + 1}).homEquiv _ _)
    (ρ m).hom).hom.app V x

/-- Normalization of the signed inverse-image identifications: unit, root tensor,
completed scalar action, positive powers, and dual evaluation. These are the canonical
pullback comparisons, rather than arbitrary isomorphisms of rank-one sheaves.
Source: first and final sentences of `prop-weil-twist-preserves.proof.md`, and the
Integral twist paragraph of `sk-prop-sfb-cartesian-coefficients-twists.proof.md`
(blueprint: lem-weil-integral-twist-base-change). -/
def IsIntegralTwistInverseComparison {X Y : Scheme.{u}} (h : X ⟶ Y)
    (α : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (completedIntegralCommRingSheafUnrestricted l E Y) ⟶
        completedIntegralCommRingSheafUnrestricted l E X)
    (τ : (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
      (purTwistZlOne Y l) ⟶ purTwistZlOne X l)
    (ρ : ∀ m : ℤ, (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
      (integralTwistUnderlying l E Y m) ≅ integralTwistUnderlying l E X m) : Prop :=
  (∀ (V : Y.ProEtᵒᵖ) (a : (completedIntegralCommRingSheafUnrestricted l E Y).obj.obj V),
    integralTwistInverseSection l E h ρ 0 V a =
      (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _) α).hom.app V a) ∧
  IsPurIntegralTwistComparison h l E α τ (ρ 1).hom ∧
  (∀ (m : ℤ) (V : Y.ProEtᵒᵖ)
      (a : (completedIntegralCommRingSheafUnrestricted l E Y).obj.obj V)
      (x : (integralTwistLine l E Y m).val.obj V),
    integralTwistInverseSection l E h ρ m V (a • x) =
      @id ((completedIntegralCommRingSheafUnrestricted l E X).obj.obj
        ((proEtaleBaseChange h).op.obj V))
        ((((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _) α).hom.app V a) •
          integralTwistInverseSection l E h ρ m V x) ∧
  (∀ (n : ℕ) (V : Y.ProEtᵒᵖ)
      (x : (integralTwistLine l E Y (Int.ofNat (n + 1))).val.obj V)
      (y : (integralTwistLine l E Y 1).val.obj V),
    integralTwistInverseSection l E h ρ (Int.ofNat (n + 2)) V
        (SheafOfModules.siteSheafTensorTmul
          (A := completedIntegralCommRingSheafUnrestricted l E Y) _ _ V x y) =
      SheafOfModules.siteSheafTensorTmul
        (A := completedIntegralCommRingSheafUnrestricted l E X) _ _
        ((proEtaleBaseChange h).op.obj V)
        (integralTwistInverseSection l E h ρ (Int.ofNat (n + 1)) V x)
        (integralTwistInverseSection l E h ρ 1 V y)) ∧
  ∀ (n : ℕ) (V : Y.ProEtᵒᵖ)
      (f : (integralTwistLine l E Y (Int.negSucc n)).val.obj V)
      (x : (integralTwistLine l E Y (Int.ofNat (n + 1))).val.obj V),
    ((integralTwistInverseSection l E h ρ (Int.negSucc n) V f).app
        (op (Over.mk (𝟙 ((proEtaleBaseChange h).op.obj V).unop))))
        (integralTwistInverseSection l E h ρ (Int.ofNat (n + 1)) V x) =
      (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _) α).hom.app V
        ((f.app (op (Over.mk (𝟙 V.unop)))) x)

/-- Canonical scalar base change of all signed integral Tate lines, with evaluation,
tensor-power, tower and scheme compatibility.
Source: first and final sentences of `prop-weil-twist-preserves.proof.md`
(blueprint: lem-weil-integral-twist-base-change).

Proof:
1. Put A equal to the completed Z_l sheaf. The locally-free twist theorem gives
   T locally free of rank one and R_H = A tensor O_H. Rebracket the defining
   first line to identify it with T tensor_A R_H. The coefficient inclusion is
   the completed inclusion, since its composites with every finite quotient agree.
2. The first comparison sends (t tensor a) tensor b to t tensor iota(a)b; its
   inverse sends t tensor b to (t tensor 1) tensor b. Balanced relations verify
   both composites, independently of generators. Sheaf tensor sheafification
   makes these restriction-compatible formulas into sheaf maps.
3. At zero use multiplication R_E tensor R_F to R_F. For positive exponents
   iterate the canonical tensor/pullback comparison and the first-line map.
4. For -n use the dual base-change pairing
   (phi tensor b, x tensor c) to iota(phi(x))bc, then precompose with the inverse
   positive comparison. The sheaf-Hom tensor adjunction defines this map.
5. On a cover trivializing T the positive and dual lines are free rank one,
   and the dual comparison sends the dual generator tensor b to b times the
   target dual generator. Its local inverses agree and glue. The pairing formula
   proves compatibility with evaluation.
6. Positive products and all opposite-sign contractions agree on local powers
   of a generator. Changing the generator scales both routes equally, so the
   equalities are independent of the cover and descend by sheaf separatedness.
7. For E into F into G both scalar composites send a local generator with
   coefficient a to the generator with coefficient kappa(iota(a)). Balancing
   gives the same equality for the scalar-extension isomorphisms; the identity
   extension gives the unit map.
8. For h : X to S, use the coefficient and first-line comparisons of
   lem-pur-integral-twist-line-inverse-image, normalized by finite projections
   and root tensors. Tensor pullback gives the positive powers, and finite-free
   dual pullback gives the negative powers, with the displayed unit, action,
   tensor and evaluation normalizations. The first-line field-inclusion square
   extends to positive powers by induction and to duals by their evaluation
   characterization. Thus the displayed square commutes for every signed line.
-/
theorem integral_twist_base_change
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F) (S : Scheme.{u})
    [∀ x : S, Invertible (l : S.residueField x)] :
    IsCanonicalTwistScalarMaps l E S F ι (twistScalarMaps l E S F ι) ∧
    (∀ (m : ℤ) (U : S.ProEtᵒᵖ)
        (b : (completedIntegralCommRingSheafUnrestricted l F S).obj.obj U)
        (x : (integralTwistLine l E S m).val.obj U),
      (twistLineScalarIso l E S F ι m).hom.val.app U
          (integralOrdinaryTensorSection l E F ι S _ U b x) =
        b • (@id ((integralTwistLine l F S m).val.obj U)
          ((twistScalarMaps l E S F ι m).val.app U x))) ∧
    (∀ (G : Type u) [Field G] [Algebra (Padic l) G] [FiniteDimensional (Padic l) G]
        (κ : F →ₐ[Padic l] G) (m : ℤ) (U : S.ProEtᵒᵖ)
        (x : (integralTwistLine l E S m).val.obj U),
      (twistScalarMaps l E S G (κ.comp ι) m).val.app U x =
        (twistScalarMaps l F S G κ m).val.app U
          ((twistScalarMaps l E S F ι m).val.app U x)) ∧
    ∀ (X : Scheme.{u}) (h : X ⟶ S)
        [∀ x : X, Invertible (l : X.residueField x)],
      ∃ (αE : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
          (completedIntegralCommRingSheafUnrestricted l E S) ⟶
            completedIntegralCommRingSheafUnrestricted l E X)
        (αF : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
          (completedIntegralCommRingSheafUnrestricted l F S) ⟶
            completedIntegralCommRingSheafUnrestricted l F X)
        (τ : (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
          (purTwistZlOne S l) ⟶ purTwistZlOne X l)
        (ρE : ∀ m : ℤ, (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
          (integralTwistUnderlying l E S m) ≅ integralTwistUnderlying l E X m)
        (ρF : ∀ m : ℤ, (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
          (integralTwistUnderlying l F S m) ≅ integralTwistUnderlying l F X m),
        (IsIso αE ∧ IsPurIntegralCoefficientComparison h l E αE) ∧
        (IsIso αF ∧ IsPurIntegralCoefficientComparison h l F αF) ∧
        (IsIso τ ∧ IsPurRootLimitComparison h l τ) ∧
        IsIntegralTwistInverseComparison l E h αE τ ρE ∧
        IsIntegralTwistInverseComparison l F h αF τ ρF ∧
        (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
            (integralCompletedScalarMap l E F ι S) ≫ αF =
          αE ≫ integralCompletedScalarMap l E F ι X ∧
        ∀ m : ℤ,
          (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).map
              (integralTwistScalarUnderlying l E S F ι m) ≫ (ρF m).hom =
            (ρE m).hom ≫ integralTwistScalarUnderlying l E X F ι m := by
  sorry

end WeilConjectures
