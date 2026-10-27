/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.Paper.TowerChernPullbackData
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # Restriction of coefficients in the ordinary geometric adjunction

Source: blueprint classes proof (2); Stacks 03EL, ordinary coefficient extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- Direct image of whole abelian towers, taken componentwise.
Source: classes (2), ordinary system topos
(blueprint: lem-sp-tower-restricted-scalar-adjunction). -/
abbrev abPush {X Y : Scheme.{u}} (f : X ⟶ Y) : Ab X ⥤ Ab Y :=
  (Functor.whiskeringRight ℕᵒᵖ (DiagonalAb X) (DiagonalAb Y)).obj
    (lowerStar AddCommGrpCat.{u + 1} f)

/-- The componentwise ordinary abelian adjunction.
Source: classes (2), ordinary system topos
(blueprint: lem-sp-tower-restricted-scalar-adjunction). -/
def abAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) : abPull f ⊣ abPush f :=
  (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).whiskerRight ℕᵒᵖ

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The normalized restriction/direct-image square and its integral Hom adjunction.
This statement involves neither a coefficient-unit arrow nor a Tate-line comparison.

Source: blueprint latest, classes proof (2), balanced coefficient extension;
Stacks 03EL, ordinary module inverse image and scalar restriction.
(blueprint: lem-sp-tower-restricted-scalar-adjunction).

Proof: forget the scalar action on the given ordinary direct-image system. At
(n,U) it is the additive group of the original system at the base-changed chart.
The section, restriction and morphism equations of the two Forget records and
ordinaryPushEvaluation give identity-transport isomorphisms chi, natural in N.
These preserve every horizontal map, so assemble to an isomorphism of whole
abelian towers, with the displayed section formula. For an R-system M and an
A-system N, forget an R-linear map d.pull(M) -> res(N), precompose with the
specified forgetIso, transpose under the componentwise abelian adjunction, and
postcompose with chi inverse. The resulting additive tower map is R-linear:
locally every section of the constant Z/ell^(n+1) ring sheaf lifts to a constant
integer, and additive maps commute with integer multiples. The local lifts
cover, so separatedness proves linearity on every chart. Forget is fully
faithful by the same argument. Thus this construction is a bijection of Hom
sets, natural in both arguments. Compose with the target ordinary scalar
adjunction to obtain the asserted adjunction a. Its Hom equivalence satisfies
exactly the displayed equation by construction. The normalization of the
integral unit ensures the transported quotient action is the unital one.
No root object or Kummer map is used, and no coefficient flatness is required;
the local-lift argument also applies on empty charts and to zero rings. -/
theorem restrictedScalarAdjunction_exists
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : SpTowerShriek.Base l E) (g : SpTowerShriek.Geometry l E b f)
    (cY : Chern l E Y) (cX : Chern l E X)
    (d : IntegralCoefficientPullback l E f cY cX) :
    ∃ χ : (g.push ⋙ SemilinearSections.res.{u + 1, u, u + 1}
        (coefficientSystemMap l E Y)) ⋙ cY.reduction.forget.F ≅
      (SemilinearSections.res.{u + 1, u, u + 1}
        (coefficientSystemMap l E X) ⋙ cX.reduction.forget.F) ⋙ abPush f,
      (∀ (N : Systems X (Arings l E X)) (n : ℕ) (U : Y.ProEtᵒᵖ)
        (x : (((cY.reduction.forget.F.obj
          ((SemilinearSections.res.{u + 1, u, u + 1}
            (coefficientSystemMap l E Y)).obj (g.push.obj N))).obj (op n)).obj.obj U)),
        HEq ((((χ.hom.app N).app (op n)).hom.app U) x) x) ∧
      ∃ a : (d.pull ⋙ cX.scalar.model.E) ⊣
          (g.push ⋙ SemilinearSections.res.{u + 1, u, u + 1}
            (coefficientSystemMap l E Y)),
        ∀ (M : Systems Y (Rrings l Y)) (N : Systems X (Arings l E X))
          (t : cX.scalar.model.E.obj (d.pull.obj M) ⟶ N),
          cY.reduction.forget.F.map ((a.homEquiv M N) t) ≫ χ.hom.app N =
            ((abAdjunction f).homEquiv _ _)
              (d.forgetIso.hom.app M ≫ cX.reduction.forget.F.map
                ((cX.scalar.ordinaryAdjunction.homEquiv _ _) t)) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerClasses
