/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import Sheaf.Paper.PrincipalKoszulStrictReplacement
public import Sheaf.Paper.SmoothPurityCoefficientTowers
public import Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
/-! # Canonical completeness of limits of power-torsion sheaf complexes

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower, completeness sentence;
Bhatt--Scholze, The pro-etale topology for schemes, Lemmas 3.5.4--3.5.7
(blueprint: def-sp-power-torsion-limit-models).

The index n denotes the positive level n+1. We reuse the principal Koszul tower in its
symmetric left-tensor model L_j tensor P. Its degree-zero inclusion is 1 tensor x, which
is x tensor 1 under symmetry. No bound on the different nilpotence exponents is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [local irreducible] WeilConjectures.completedIntegralCoefficientSheafUnrestricted
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.PrincipalKoszulStrictReplacement (uniformizer)

namespace WeilConjectures.PowerTorsionLimit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (T : AlgebraicGeometry.Scheme.{t})

/-- The existing strict Roos functor in the tower-of-complexes presentation.
Source: Stacks 0941 (blueprint: def-sp-power-torsion-limit-models). -/
abbrev roos : (ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ) ⥤
    CochainComplex (integralTowerModules l E T) ℤ :=
  letI := integralCoefficientAbSheafify.{t, u} T
  letI := integralCoefficientAbLocallyBijective.{t, u} T
  letI := integralOperationsCountableProducts.{t, u} l E T
  integralOperationsRoosFunctor

attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted

/-- The actual Koszul tensor tower, functorial in the input complex.
Source: the principal Koszul calculation in sk-lem-sp-tower
(blueprint: def-sp-power-torsion-limit-models). -/
abbrev tensorTower : CochainComplex (integralTowerModules l E T) ℤ ⥤
    (ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ) :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E T)
  letI := SheafOfModules.monoidalCategory
    (completedIntegralCommRingSheafUnrestricted l E T)
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E T)
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E T)
  { obj := fun P ↦ koszulTensorTower
      (completedIntegralCommRingSheafUnrestricted l E T) P (uniformizer l E T)
    map := fun f ↦ Functor.whiskerLeft
      (principalKoszulTower (completedIntegralCommRingSheafUnrestricted l E T)
        (uniformizer l E T))
      ((MonoidalCategory.curriedTensor (integralTowerModules l E T)).map₂CochainComplex.flip.map f)
    map_id := fun P ↦ by
      rw [CategoryTheory.Functor.map_id]
      apply NatTrans.ext
      funext n
      rfl
    map_comp := fun f g ↦ by
      simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.whiskerLeft_comp] }

/-- Koszul completion on strict complex representatives, with the existing Roos model.
Source: sk-lem-sp-tower (blueprint: def-sp-power-torsion-limit-models). -/
abbrev completion : CochainComplex (integralTowerModules l E T) ℤ ⥤
    CochainComplex (integralTowerModules l E T) ℤ :=
  tensorTower l E T ⋙ roos l E T

/-- The strict Koszul augmentations give a zero-homotopy Roos cocycle.
Source: sk-lem-sp-tower, canonical degree-zero inclusions
(blueprint: def-sp-power-torsion-limit-models).
Proof: the differential of the zero cochain is zero. Postcompose the product map
with every projection. The remaining equality says that the degree-zero Koszul
inclusion at j+1 followed by (pi,1) equals the inclusion at j; this is
koszulRepresentativeAugmentation_naturality. Thus the composite with one minus
shift is zero. This is precisely the condition defining the node's canonical unit. -/
theorem unit_condition (P : CochainComplex (integralTowerModules l E T) ℤ) :
    CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain P
          (∏ᶜ fun n : ℕ ↦ ((tensorTower l E T).obj P).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (Pi.lift (koszulRepresentativeAugmentation
          (completedIntegralCommRingSheafUnrestricted l E T) P (uniformizer l E T)) ≫
          towerTransitionEndomorphism
            (K := fun n : ℕ ↦ ((tensorTower l E T).obj P).obj (op n))
            (fun n ↦ ((tensorTower l E T).obj P).map (homOfLE n.le_succ).op)) = 0 := by
  let : EssentiallySmall.{max u (t + 1)} T.ProEt :=
    essentiallySmallSelf.{u} _
  let : (AlgebraicGeometry.Scheme.ProEt.topology T).HasSheafCompose
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}) :=
    hasSheafComposeEssentiallySmallSite _ CommRingCat.{max u (t + 1)}
      RingCat.{max u (t + 1)} (forget₂ _ _)
  let := integralCoefficientAbSheafify.{t, u} T
  let := integralCoefficientAbLocallyBijective.{t, u} T
  let := integralOperationsCountableProducts.{t, u} l E T
  let := SheafOfModules.isMonoidal_W_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E T)
  let := SheafOfModules.monoidalCategory
    (completedIntegralCommRingSheafUnrestricted l E T)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E T)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E T)
  have h : (Pi.lift (koszulRepresentativeAugmentation
      (completedIntegralCommRingSheafUnrestricted l E T) P (uniformizer l E T)) :
      P ⟶ ∏ᶜ fun n : ℕ ↦ ((tensorTower l E T).obj P).obj (op n)) ≫
      towerTransitionEndomorphism
        (K := fun n : ℕ ↦ ((tensorTower l E T).obj P).obj (op n))
        (fun n ↦ ((tensorTower l E T).obj P).map (homOfLE n.le_succ).op) = 0 := by
    apply Pi.hom_ext
    intro n
    simpa [towerTransitionEndomorphism, towerProductShift, Category.assoc] using
      sub_eq_zero.mpr (koszulRepresentativeAugmentation_naturality.{t + 1, t, max u (t + 1)}
        (completedIntegralCommRingSheafUnrestricted l E T) P (uniformizer l E T) n)
  rw [h]
  simp

/-- The completion unit is the specified strict augmentation with zero Roos homotopy.
Source: sk-lem-sp-tower, power-torsion calculation
(blueprint: def-sp-power-torsion-limit-models). -/
def unit (P : CochainComplex (integralTowerModules l E T) ℤ) :
    P ⟶ (completion l E T).obj P :=
  CochainComplex.mappingCocone.lift
    (towerTransitionEndomorphism
      (K := fun n : ℕ ↦ ((tensorTower l E T).obj P).obj (op n))
      (fun n ↦ ((tensorTower l E T).obj P).map (homOfLE n.le_succ).op))
    (Pi.lift (koszulRepresentativeAugmentation
      (completedIntegralCommRingSheafUnrestricted l E T) P (uniformizer l E T))) 0
    (unit_condition l E T P)

/-- The unshifted (p=0) coordinate of the strict Roos complex, at a fixed tower level.
Source: Stacks 0941 (blueprint: def-sp-power-torsion-limit-models). -/
def coordinateZero (X : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ)
    (k : ℤ) (n : ℕ) : ((roos l E T).obj X).X k ⟶ (X.obj (op n)).X k :=
  (CochainComplex.mappingCocone.fst
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ X.obj (op n))
      (fun n ↦ X.map (homOfLE n.le_succ).op))).f k ≫
    (Pi.π (fun n : ℕ ↦ X.obj (op n)) n).f k

/-- The shifted (p=1) coordinate. The target degree is k-1.
Source: Stacks 0941 (blueprint: def-sp-power-torsion-limit-models). -/
def coordinateOne (X : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ)
    (k : ℤ) (n : ℕ) : ((roos l E T).obj X).X k ⟶ (X.obj (op n)).X (k - 1) :=
  (CochainComplex.mappingCocone.snd
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ X.obj (op n))
      (fun n ↦ X.map (homOfLE n.le_succ).op))).v k (k - 1) (by omega) ≫
    (Pi.π (fun n : ℕ ↦ X.obj (op n)) n).f (k - 1)

/-- Evaluation of the existing Roos model as a chain map.
Source: Stacks 0941 (blueprint: def-sp-power-torsion-limit-models). -/
def evaluation (X : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ) (n : ℕ) :
    (roos l E T).obj X ⟶ X.obj (op n) :=
  CochainComplex.mappingCocone.fst
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ X.obj (op n))
      (fun n ↦ X.map (homOfLE n.le_succ).op)) ≫ Pi.π _ n

/-- The strict j-tower obtained by applying the n-Roos functor to each tensor column.
Source: sk-lem-sp-tower, double-product calculation
(blueprint: def-sp-power-torsion-limit-models). -/
abbrev columns (Q : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ) :=
  (Q ⋙ tensorTower l E T).flip ⋙ roos l E T

/-- The row coordinate of the iterated Roos complex.
Source: sk-lem-sp-tower, signed interchange calculation
(blueprint: def-sp-power-torsion-limit-models). -/
def rowCoordinate (Q : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ)
    (p q : Bool) (k : ℤ) (n j : ℕ) :
    ((roos l E T).obj (Q ⋙ completion l E T)).X k ⟶
      (((tensorTower l E T).obj (Q.obj (op n))).obj (op j)).X
        (match p, q with
        | false, false => k
        | false, true => k - 1
        | true, false => k - 1
        | true, true => k - 1 - 1) := by
  cases p <;> cases q
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero] using
      (coordinateZero l E T (Q ⋙ completion l E T) k n ≫
        coordinateZero l E T ((tensorTower l E T).obj (Q.obj (op n))) k j)
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero] using
      (coordinateZero l E T (Q ⋙ completion l E T) k n ≫
        coordinateOne l E T ((tensorTower l E T).obj (Q.obj (op n))) k j)
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero] using
      (coordinateOne l E T (Q ⋙ completion l E T) k n ≫
        coordinateZero l E T ((tensorTower l E T).obj (Q.obj (op n))) (k - 1) j)
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero] using
      (coordinateOne l E T (Q ⋙ completion l E T) k n ≫
        coordinateOne l E T ((tensorTower l E T).obj (Q.obj (op n))) (k - 1) j)

/-- The column coordinate of the iterated Roos complex.
Source: sk-lem-sp-tower, signed interchange calculation
(blueprint: def-sp-power-torsion-limit-models). -/
def columnCoordinate (Q : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ)
    (p q : Bool) (k : ℤ) (n j : ℕ) :
    ((roos l E T).obj (columns l E T Q)).X k ⟶
      (((tensorTower l E T).obj (Q.obj (op n))).obj (op j)).X
        (match p, q with
        | false, false => k
        | false, true => k - 1
        | true, false => k - 1
        | true, true => k - 1 - 1) := by
  cases p <;> cases q
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero,
      Functor.flip, Functor.comp_obj] using
      (coordinateZero l E T (columns l E T Q) k j ≫
        coordinateZero l E T ((Q ⋙ tensorTower l E T).flip.obj (op j)) k n)
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero,
      Functor.flip, Functor.comp_obj] using
      (coordinateOne l E T (columns l E T Q) k j ≫
        coordinateZero l E T ((Q ⋙ tensorTower l E T).flip.obj (op j)) (k - 1) n)
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero,
      Functor.flip, Functor.comp_obj] using
      (coordinateZero l E T (columns l E T Q) k j ≫
        coordinateOne l E T ((Q ⋙ tensorTower l E T).flip.obj (op j)) k n)
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero,
      Functor.flip, Functor.comp_obj] using
      (coordinateOne l E T (columns l E T Q) k j ≫
        coordinateOne l E T ((Q ⋙ tensorTower l E T).flip.obj (op j)) (k - 1) n)

end WeilConjectures.PowerTorsionLimit
