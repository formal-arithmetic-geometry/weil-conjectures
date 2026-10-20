/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T6
-/
module

public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower

/-! # Strict adic cone model for a normalized DVR Roos limit -/

@[expose] public noncomputable section
set_option autoImplicit false
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
/-- The canonical standard derived category, registered only in this file. -/
abbrev normalizedDVRAdicConeModelLocal1 :
    HasDerivedCategory (completedIntegralModuleSheaves l E X D hl) :=
  HasDerivedCategory.standard _
attribute [local instance] normalizedDVRAdicConeModelLocal1
/-- The canonical size witness, registered only in this file. -/
abbrev normalizedDVRAdicConeModelLocal2 :
    EssentiallySmall.{max u (t + 1)} X.ProEt :=
  essentiallySmallSelf.{u} X.ProEt
attribute [local instance 4000] normalizedDVRAdicConeModelLocal2
/-- Canonical abelian sheafification, registered only in this file. -/
abbrev normalizedDVRAdicConeModelLocal3 :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} X
attribute [local instance] normalizedDVRAdicConeModelLocal3
/-- The canonical locally bijective sheafification criterion, registered locally. -/
abbrev normalizedDVRAdicConeModelLocal4 :
    (AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} X
attribute [local instance] normalizedDVRAdicConeModelLocal4

/-- A strict normalized adic complex model and the bounded-free cone computation
of a finite scalar extension of a Roos limit.
Source: Bhatt--Scholze, Lemmas 3.5.4 and 3.5.5, regular-element case; Stacks 06YS,
05RT and 0941. (blueprint: lem-coef-normalized-dvr-adic-cone-model).

Proof: write the ring of integers as a DVR and choose a uniformizer. Its constant
action on the completed sheaf gives the indicated linear category. Successively use
right fractions and K-flat resolutions with flat terms to represent the finite
transitions by semilinear chain maps. After restriction to the completed sheaf these
give U; insert the zero complex at index zero. Flatness over each finite quotient
identifies the kernel of the b-th power with the image of the a-th power at level
a+b. The adjoint normalization gives quasi-isomorphisms from the termwise quotients
to the smaller levels. These are the three fields of IsNormalizedAdicTower.
The level identifications eU cover every positive level and intertwine every
successor map. Their products
transport the given Roos triangle to this strict model, retaining projections; no
fullness theorem for derived evaluation is needed. Remove the finite prefix n+1. Tensoring
with the two-term free resolution [R --uniformizer^(n+1)--> R] commutes with products
and the Roos cone, since only two terms and finite sums occur in every degree.
Consequently the restricted derived reduction of M is the homotopy limit c of the
cones, giving a. The augmentation of the multiplication cone to the quotient is
rho followed by desc followed by the normalized cokernel map. The ordinary tensor
adjunction on pure tensors and its derived normalization show that a, this cone
projection and the specified level identification compose to the restriction of the adjoint of
the original limit
projection. This proves the displayed equation, including all signs and projections.
No assertion that this map is invertible is used: invertibility follows separately
from the existing strict adic tower theorem. All exponents are n+1. -/
theorem normalizedDVR_adic_cone_model
    (T : NormalizedDVRTower l E X D hl)
    (M : completedIntegralDerivedCategory l E X D hl)
    [HasProduct (fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)]
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)
    (δ : (∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower) ⟶
      M⟦(1 : ℤ)⟧)
    (hc : IsDerivedLimitTriangle
      (fun n : ℕ ↦ (normalizedDVRTowerTransition l E X D hl n.le_succ).app T.tower)
      M p δ) (n : ℕ)
    (adj : scalarReductionDerivedExtension l E X n ⊣
      scalarReductionDerivedRestriction l E X n) :
    ∃ (S : Type (max u (t + 1))) (hS : CommRing S), letI := hS
      ∃ (hlin : Linear S (completedIntegralModuleSheaves l E X D hl)), letI := hlin
      ∃ (hprod : HasLimitsOfShape (Discrete ℕ)
          (completedIntegralDerivedCategory l E X D hl)), letI := hprod
      ∃ (ϖ : S)
        (U : ℕᵒᵖ ⥤ CochainComplex (completedIntegralModuleSheaves l E X D hl) ℤ)
        (hU : CochainComplex.IsNormalizedAdicTower ϖ U)
        (eU : ∀ j : ℕ, DerivedCategory.Q.obj (U.obj (op (j + 1))) ≅
          (normalizedDVRTowerEvaluation l E X D hl j).obj T.tower),
        (∀ j : ℕ,
          DerivedCategory.Q.map (U.map
              (homOfLE (Nat.succ_le_succ j.le_succ)).op) ≫ (eU j).hom =
            (eU (j + 1)).hom ≫
              (normalizedDVRTowerTransition l E X D hl j.le_succ).app T.tower) ∧
        ∃ (c : Cone (CochainComplex.IsNormalizedAdicTower.arrowTower
          (ϖ := ϖ) (T := U) (n + 1) ⋙ CochainComplex.ConeCoimage.cone ⋙ DerivedCategory.Q)),
        CategoryTheory.Pretriangulated.IsHomotopyLimit c ∧
        ∃ (a : (scalarReductionDerivedRestriction l E X n).obj
              ((scalarReductionDerivedExtension l E X n).obj M) ≅ c.pt),
          (scalarReductionDerivedRestriction l E X n).map
              ((adj.homEquiv M (T.M n)).symm
                (p ≫ Pi.π _ n ≫ (T.evaluationIso n).hom)) =
            a.hom ≫ c.π.app (op 0) ≫ DerivedCategory.Q.map
              (CochainComplex.ConeCoimage.ρ.app _ ≫ CochainComplex.ConeCoimage.desc.app _ ≫
                hU.cokerDesc (n + 1) (op 0)) ≫ (eU n).hom ≫
                (T.evaluationIso n).hom := by
  sorry

end WeilConjectures
