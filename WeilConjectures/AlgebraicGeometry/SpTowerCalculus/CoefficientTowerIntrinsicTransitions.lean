/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces

/-! # Strict transitions in intrinsic coefficient coordinates

Source: Zheng, Construction 4.1; Stacks 07A6; the first step of the
coefficient-tower transition compatibility argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SpTowerCalculus

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

private theorem transported_homEquiv
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C} (A : F ⊣ G) (B : F' ⊣ G')
    (s : F ≅ F') (r : G ≅ G')
    (hu : ∀ P, A.unit.app P ≫ G.map (s.hom.app P) ≫ r.hom.app (F'.obj P) =
      B.unit.app P) (P : C) (Q : D) (f : F.obj P ⟶ Q) :
    B.homEquiv P Q (s.inv.app P ≫ f) = A.homEquiv P Q f ≫ r.hom.app Q := by
  rw [A.homEquiv_unit, B.homEquiv_unit, ← hu P]
  simp only [Functor.map_comp, Category.assoc]
  rw [← r.hom.naturality_assoc (s.inv.app P)]
  rw [← G.map_comp_assoc, Iso.hom_inv_id_app, G.map_id, Category.id_comp]
  rw [r.hom.naturality]

private theorem scalarCoordinates_homEquiv (T : Scheme.{u})
    (a : SpCoefficientTowersAbelian l E T) {m n : ℕ} (h : m ≤ n)
    (s : ScalarCoordinates l E T a h)
    (P : proEtaleDerivedCategory T (SpTowerShriek.R l E n))
    (Q : proEtaleDerivedCategory T (SpTowerShriek.R l E m))
    (f : (systemScalar l E T a h).obj P ⟶ Q) :
    (proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := T) (quotient l E h))).homEquiv P Q
        (s.scalar.inv.app P ≫ f) =
    (SheafOfModules.systemDerivedTensorAdj.{u + 1, u, u + 1}
      a.scalar (spCoefficientCommRings l E T) h).homEquiv P Q f ≫
        (Functor.mapDerivedCategoryNatIso s.restriction).hom.app Q := by
  exact transported_homEquiv
    (SheafOfModules.systemDerivedTensorAdj.{u + 1, u, u + 1}
      a.scalar (spCoefficientCommRings l E T) h)
    (proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := T) (quotient l E h)))
    s.scalar (Functor.mapDerivedCategoryNatIso s.restriction) s.unit P Q f

/-- The adjoint of the recorded reduction, in intrinsic restriction coordinates.
This is an explicit construction from the recorded reduction and adjunction, not a
choice of a witness. Its identification with the localized horizontal transition is
part of realization_intrinsicTransition.
Source: Zheng 4.1 (blueprint: lem-sp-tower-intrinsic-transition-transpose). -/
def intrinsicTransition (T : Scheme.{u}) (a : SpCoefficientTowersAbelian l E T)
    {m n : ℕ} (h : m ≤ n) (s : ScalarCoordinates l E T a h)
    (K : spDerivedCoefficientTowers l E T a) :
    (spDerivedCoefficientEvaluation l E T a n).obj K ⟶
      (scalarRestriction (quotient l E h) T).obj
        ((spDerivedCoefficientEvaluation l E T a m).obj K) :=
  (SheafOfModules.systemDerivedTensorAdj.{u + 1, u, u + 1}
    a.scalar (spCoefficientCommRings l E T) h).homEquiv _ _ ((a.reduction h).app K) ≫
    (Functor.mapDerivedCategoryNatIso s.restriction).hom.app
      ((spDerivedCoefficientEvaluation l E T a m).obj K)

/-- The supplied scalar-coordinate comparison preserves the transpose of reduction.
Source: Zheng 4.1; Stacks 07A6.
Proof: expand the two Hom equivalences using their units. The scalar coordinate unit
identity transports one unit to the other. Naturality of the restriction comparison
moves the scalar inverse across it, and the scalar isomorphism cancels with its inverse.
(blueprint: lem-sp-tower-intrinsic-transition-transpose). -/
theorem reduction_homEquiv_intrinsicTransition (T : Scheme.{u})
    (a : SpCoefficientTowersAbelian l E T) {m n : ℕ} (h : m ≤ n)
    (s : ScalarCoordinates l E T a h) (K : spDerivedCoefficientTowers l E T a) :
    (proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := T) (quotient l E h))).homEquiv _ _
        (reduction l E T a h s K) = intrinsicTransition l E T a h s K := by
  exact scalarCoordinates_homEquiv l E T a h s _ _ ((a.reduction h).app K)

end AlgebraicGeometry.ProEtale.SpTowerCalculus
