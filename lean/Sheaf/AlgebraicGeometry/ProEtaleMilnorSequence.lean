/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.IntegralOperationsWellDefined
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.ProEtaleProductsExact

/-!
# The Milnor sequence on the small pro-etale site

Source: Weil conjectures blueprint, main-20261015, sec-proetale-coefficients,
sk-prop-pe-milnor/det-pe-milnor-sequence.md (blueprint: det-pe-milnor-sequence).

The existing strict Roos construction `WeilConjectures.integralOperationsRoos` is
exactly Cone(1-T)[-1], including its diagonal map on strict tower morphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

section Cokernel

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

/-- The sheaf cokernel of 1-T on a tower product, using the existing transition map.
Source: blueprint main-20261015, det-pe-milnor-sequence, clause 1
(blueprint: det-pe-milnor-sequence). -/
abbrev milnorTowerCokernel (M : ℕᵒᵖ ⥤ A) : A :=
  cokernel (towerTransitionEndomorphism (K := fun n : ℕ ↦ M.obj (op n))
    (fun n : ℕ ↦ M.map (homOfLE (Nat.le_succ n)).op))

/-- The canonical map of these cokernels induced by a tower morphism.
Source: blueprint main-20261015, det-pe-milnor-sequence, naturality in clause 1
(blueprint: det-pe-milnor-sequence). -/
def milnorTowerCokernelMap {M N : ℕᵒᵖ ⥤ A} (f : M ⟶ N) :
    milnorTowerCokernel M ⟶ milnorTowerCokernel N :=
  cokernel.map
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ M.obj (op n))
      (fun n ↦ M.map (homOfLE (Nat.le_succ n)).op))
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ N.obj (op n))
      (fun n ↦ N.map (homOfLE (Nat.le_succ n)).op))
    (Limits.Pi.map (fun n : ℕ ↦ f.app (op n)))
    (Limits.Pi.map (fun n : ℕ ↦ f.app (op n)))
    (towerTransitionEndomorphism_natural_backward _ _ _
      (fun n ↦ (f.naturality (homOfLE (Nat.le_succ n)).op).symm)).symm

/-- The tower of q-th cohomology sheaves, with induced transition maps.
Source: blueprint main-20261015, det-pe-milnor-sequence, clause 1
(blueprint: det-pe-milnor-sequence). -/
abbrev milnorCohomologyTower (K : ℕᵒᵖ ⥤ CochainComplex A ℤ) (q : ℤ) : ℕᵒᵖ ⥤ A :=
  K ⋙ HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q

/-- Regard a module tower as complexes concentrated in degree zero.
Source: blueprint main-20261015, det-pe-milnor-sequence, clause 2
(blueprint: det-pe-milnor-sequence). -/
abbrev milnorSingleTower (M : ℕᵒᵖ ⥤ A) : ℕᵒᵖ ⥤ CochainComplex A ℤ :=
  M ⋙ HomologicalComplex.single A (ComplexShape.up ℤ) 0

end Cokernel

/-- All three clauses of the natural Milnor sequence, for arbitrary unbounded towers.
The chosen isomorphisms e₀ and e₁ compute the cohomology of the degree-zero Roos
complex. The final short exact complex is the first one with its left endpoint
rewritten by e₁; in particular it uses the same maps, not unrelated exact sequences.

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-pe-milnor/det-pe-milnor-sequence.md (blueprint: det-pe-milnor-sequence).

Proof:
1. In the abelian category of ringedSiteModules, apply the cone long exact
cohomology sequence (lem-sf-derived-homology-long-exact and
 def-weil-abstract-derived-category) to 1-T on the termwise product. Exactness
identifies the cokernel in degree q-1 with the kernel of the outgoing map, and
its image with the kernel in degree q. By det-pe-products-derived, using exact
products from det-pe-products-exact, the projection-induced product/cohomology
comparison is an isomorphism. Its coordinate formulas identify the induced map
with 1-T on cohomology. The kernel is the sheaf inverse limit by
 def-pur-sheaf-inverse-limit. The diagonal product map on cone summands commutes
with inclusion and negative projection; factoring through cokernels and kernels
gives both naturality squares below.
2. For modules concentrated in degree zero the shifted cone has only degrees
0 and 1, with differential -(1-T). Negating degree 1 identifies it with the
usual two-term complex. Its cohomology is the kernel in degree 0, the cokernel
in degree 1, and zero in every other integer degree. Identify the kernel with
the sectionwise inverse limit. The constructions commute with tower maps.
3. Apply the degree-1 calculation to the tower of H^(q-1)(K_n). Composing its
isomorphism with the first inclusion gives the last displayed short exact
complex, which is exactly the Milnor sequence in clause 3. -/
theorem milnor_sequence (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{max u (t + 1)}) :
    ∃ (e₀ : ∀ M : ℕᵒᵖ ⥤ (ringedSiteModules.{max u (t + 1)} R),
        (WeilConjectures.integralOperationsRoos (milnorSingleTower M)).homology 0 ≅ limit M)
      (e₁ : ∀ M : ℕᵒᵖ ⥤ (ringedSiteModules.{max u (t + 1)} R),
        (WeilConjectures.integralOperationsRoos (milnorSingleTower M)).homology 1 ≅
          milnorTowerCokernel M),
      (∀ (M : ℕᵒᵖ ⥤ (ringedSiteModules.{max u (t + 1)} R)) (p : ℤ), p ≠ 0 → p ≠ 1 →
        IsZero ((WeilConjectures.integralOperationsRoos (milnorSingleTower M)).homology p)) ∧
      (∀ (M N : ℕᵒᵖ ⥤ (ringedSiteModules.{max u (t + 1)} R)) (f : M ⟶ N),
        HomologicalComplex.homologyMap
            (WeilConjectures.integralOperationsRoosMap
              (Functor.whiskerRight f
                (HomologicalComplex.single
                  (ringedSiteModules.{max u (t + 1)} R) (ComplexShape.up ℤ) 0))) 0 ≫
            (e₀ N).hom = (e₀ M).hom ≫ limMap f ∧
        HomologicalComplex.homologyMap
            (WeilConjectures.integralOperationsRoosMap
              (Functor.whiskerRight f
                (HomologicalComplex.single
                  (ringedSiteModules.{max u (t + 1)} R) (ComplexShape.up ℤ) 0))) 1 ≫
            (e₁ N).hom = (e₁ M).hom ≫ milnorTowerCokernelMap f) ∧
      ∀ q : ℤ,
        ∃ (a : ∀ K : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ,
            milnorTowerCokernel (milnorCohomologyTower K (q - 1)) ⟶
              (WeilConjectures.integralOperationsRoos K).homology q)
          (b : ∀ K : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ,
            (WeilConjectures.integralOperationsRoos K).homology q ⟶
              limit (milnorCohomologyTower K q)),
          (∀ K : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ,
            ∃ h : a K ≫ b K = 0, (ShortComplex.mk (a K) (b K) h).ShortExact) ∧
          (∀ (K L : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ) (f : K ⟶ L),
            milnorTowerCokernelMap
                (Functor.whiskerRight f
                  (HomologicalComplex.homologyFunctor (ringedSiteModules.{max u (t + 1)} R)
                    (ComplexShape.up ℤ) (q - 1))) ≫ a L =
              a K ≫ HomologicalComplex.homologyMap
                (WeilConjectures.integralOperationsRoosMap f) q ∧
            HomologicalComplex.homologyMap
                (WeilConjectures.integralOperationsRoosMap f) q ≫ b L =
              b K ≫ limMap (Functor.whiskerRight f
                (HomologicalComplex.homologyFunctor
                  (ringedSiteModules.{max u (t + 1)} R) (ComplexShape.up ℤ) q))) ∧
          ∀ K : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ,
            ∃ h : (e₁ (milnorCohomologyTower K (q - 1))).hom ≫ a K ≫ b K = 0,
              (ShortComplex.mk
                ((e₁ (milnorCohomologyTower K (q - 1))).hom ≫ a K) (b K) h).ShortExact := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
