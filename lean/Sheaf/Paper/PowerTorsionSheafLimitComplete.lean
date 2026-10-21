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
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # Canonical completeness of limits of power-torsion sheaf complexes

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower, completeness sentence;
Bhatt--Scholze, The pro-etale topology for schemes, Lemmas 3.5.4--3.5.7
(blueprint: lem-sp-power-torsion-sheaf-limit-complete).

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
Source: Stacks 0941 (blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
abbrev roos : (ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ) ⥤
    CochainComplex (integralTowerModules l E T) ℤ :=
  letI := integralCoefficientAbSheafify.{t, u} T
  letI := integralCoefficientAbLocallyBijective.{t, u} T
  letI := integralOperationsCountableProducts.{t, u} l E T
  integralOperationsRoosFunctor

/-- The actual Koszul tensor tower, functorial in the input complex.
Source: the principal Koszul calculation in sk-lem-sp-tower
(blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
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
    map_id := fun P ↦ by ext n k; simp; rfl
    map_comp := fun f g ↦ by ext n k; simp; rfl }

/-- Koszul completion on strict complex representatives, with the existing Roos model.
Source: sk-lem-sp-tower (blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
abbrev completion : CochainComplex (integralTowerModules l E T) ℤ ⥤
    CochainComplex (integralTowerModules l E T) ℤ :=
  tensorTower l E T ⋙ roos l E T

/-- The strict Koszul augmentations give a zero-homotopy Roos cocycle.
Source: sk-lem-sp-tower, canonical degree-zero inclusions
(blueprint: lem-sp-power-torsion-sheaf-limit-complete).
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
(blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
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
Source: Stacks 0941 (blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
def coordinateZero (X : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ)
    (k : ℤ) (n : ℕ) : ((roos l E T).obj X).X k ⟶ (X.obj (op n)).X k :=
  (CochainComplex.mappingCocone.fst
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ X.obj (op n))
      (fun n ↦ X.map (homOfLE n.le_succ).op))).f k ≫
    (Pi.π (fun n : ℕ ↦ X.obj (op n)) n).f k

/-- The shifted (p=1) coordinate. The target degree is k-1.
Source: Stacks 0941 (blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
def coordinateOne (X : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ)
    (k : ℤ) (n : ℕ) : ((roos l E T).obj X).X k ⟶ (X.obj (op n)).X (k - 1) :=
  (CochainComplex.mappingCocone.snd
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ X.obj (op n))
      (fun n ↦ X.map (homOfLE n.le_succ).op))).v k (k - 1) (by omega) ≫
    (Pi.π (fun n : ℕ ↦ X.obj (op n)) n).f (k - 1)

/-- Evaluation of the existing Roos model as a chain map.
Source: Stacks 0941 (blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
def evaluation (X : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ) (n : ℕ) :
    (roos l E T).obj X ⟶ X.obj (op n) :=
  CochainComplex.mappingCocone.fst
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ X.obj (op n))
      (fun n ↦ X.map (homOfLE n.le_succ).op)) ≫ Pi.π _ n

/-- The strict j-tower obtained by applying the n-Roos functor to each tensor column.
Source: sk-lem-sp-tower, double-product calculation
(blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
abbrev columns (Q : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ) :=
  (Q ⋙ tensorTower l E T).flip ⋙ roos l E T

/-- The row coordinate of the iterated Roos complex.
Source: sk-lem-sp-tower, signed interchange calculation
(blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
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
(blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
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

/-- Canonical completeness, including the signed double-Roos interchange and the actual
quotient-reduction projections. The left-tensor Koszul presentation is identified with
the paper's right-tensor presentation by the standard signed tensor symmetry.

Source: blueprint main-20261015, sk-lem-sp-tower, completeness sentence;
Bhatt--Scholze Lemmas 3.5.4--3.5.7
(blueprint: lem-sp-power-torsion-sheaf-limit-complete).

Proof:
1. Countable products of pro-etale module sheaves are exact
(lem-weil-proetale-countable-products-exact). The normalized strict Roos comparison
(lem-weil-strict-roos-comparison) therefore computes total derived inverse limit,
including its evaluation and its strict zero-homotopy augmentations.
2. At level n the Koszul inclusion has quotient Q_n[1], with transition pi. The tensor
sign convention (def-pc-tensor-complex-sheaves) identifies its differential with -d_Q.
Levelwise exactness (lem-weil-tower-category-levelwise-abelian) and the complex short
exact sequence triangle (lem-weil-pbc-complex-ses-triangle) give the corresponding triangle.
3. An r_n-fold quotient transition is zero. The pro-zero criterion of
lem-weil-pbc-ringed-strict-tower-homotopy-limit kills its total limit. The constant tower
has diagonal limit Q_n, with a chain section of one minus shift given by finite partial
sums. The augmentation normalization identifies the resulting quasi-isomorphism with
unit Q_n. The construction is natural for every linear chain map.
4. Interchange the two product coordinates and multiply the (p,q) Roos coordinate by
(-1)^(pq). This interchanges the two transition differentials with their total signs;
the internal differentials agree. Squaring the sign is one, giving the inverse. The
q=0 inclusions are fixed. Only four summands occur in each total degree.
5. The two-term finite free Koszul complex commutes with products and the two Roos
coordinates. This gives gamma, compatible with Koszul transitions and inclusions.
6. Apply Roos to the levelwise units, interchange, and apply Roos to gamma inverse.
This is a quasi-isomorphism and is exactly unit H: its Koszul and inner Roos degrees
are zero, so the interchange sign is one. No common torsion exponent is used.
7. By lem-sp-ell-coefficient-fiber the augmented Koszul complexes resolve the actual
finite quotient sheaves and are K-flat. Choose a single flat-term K-flat resolution
P of H (lem-pc-kflat-resolution). Tensor its comparison with each Koszul complex, and
tensor each Koszul augmentation with P. Both are quasi-isomorphisms, by
lem-pur-kflat-tensor-quasiiso-independent, def-pc-kflat-complex,
lem-pur-quasi-iso-cone-acyclic and lem-pc-tensor-mapping-cone-iso. Derived change of rings
(lem-pur-derived-change-of-rings) followed by def-pc-sheaf-restrict-scalars identifies
the resulting quotient complexes with restricted derived reductions.
8. Use the same P at every level. The spans commute with all transitions and the maps
x to 1 tensor x. Strict Roos comparison gives the quotient limit isomorphism s and
identifies each projection with the canonical quotient reduction, through eP.
9. Transport the quotient tower's distinguished Roos triangle along this unit
isomorphism. Its first map has precisely those projections and its second is one
minus shift. This is def-weil-derived-complete, including its integral convention. -/
theorem power_torsion_sheaf_limit_complete
    (Q : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ)
    (hQ : ∀ n : ℕ, ∃ r : ℕ, 1 ≤ r ∧
      ∀ (a : ℤ) (U : T.ProEtᵒᵖ) (x : ((Q.obj (op n)).X a).val.obj U),
        (@id ((completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)
          ((uniformizer l E T).val U)) ^ r • x = 0) :
    ∃ η : 𝟭 (CochainComplex (integralTowerModules l E T) ℤ) ⟶ completion l E T,
      (∀ P, η.app P = unit l E T P) ∧
      (∀ n : ℕ, QuasiIso (unit l E T (Q.obj (op n)))) ∧
      ∃ (β : (roos l E T).obj (Q ⋙ completion l E T) ≅
          (roos l E T).obj (columns l E T Q)),
        (∀ (p q : Bool) (k : ℤ) (n j : ℕ),
          β.hom.f k ≫ columnCoordinate l E T Q p q k n j =
            if p && q then -rowCoordinate l E T Q p q k n j
            else rowCoordinate l E T Q p q k n j) ∧
        (∀ (k : ℤ) (n j : ℕ),
          (((roos l E T).map (Q.rightUnitor.inv ≫ Functor.whiskerLeft Q η)) ≫ β.hom).f k ≫
              columnCoordinate l E T Q false false k n j =
            coordinateZero l E T Q k n ≫
              (koszulRepresentativeAugmentation
                (completedIntegralCommRingSheafUnrestricted l E T)
                (Q.obj (op n)) (uniformizer l E T) j).f k ∧
          (((roos l E T).map (Q.rightUnitor.inv ≫ Functor.whiskerLeft Q η)) ≫ β.hom).f k ≫
              columnCoordinate l E T Q true false k n j =
            coordinateOne l E T Q k n ≫
              (koszulRepresentativeAugmentation
                (completedIntegralCommRingSheafUnrestricted l E T)
                (Q.obj (op n)) (uniformizer l E T) j).f (k - 1) ∧
          (((roos l E T).map (Q.rightUnitor.inv ≫ Functor.whiskerLeft Q η)) ≫ β.hom).f k ≫
              columnCoordinate l E T Q false true k n j = 0 ∧
          (((roos l E T).map (Q.rightUnitor.inv ≫ Functor.whiskerLeft Q η)) ≫ β.hom).f k ≫
              columnCoordinate l E T Q true true k n j = 0) ∧
        QuasiIso (unit l E T ((roos l E T).obj Q)) ∧
        ∃ (P : (IntegralOnSlice.Good l E T none).FullSubcategory)
          (f : P.obj ⟶ (roos l E T).obj Q)
          (eP : DerivedCategory.Q.obj P.obj ≅ DerivedCategory.Q.obj ((roos l E T).obj Q))
          (s : DerivedCategory.Q.obj ((completion l E T).obj ((roos l E T).obj Q)) ≅
            DerivedCategory.Q.obj ((roos l E T).obj
              ((IntegralOnSlice.tower l E T none).obj P.obj))),
          QuasiIso f ∧ eP.hom = DerivedCategory.Q.map f ∧
          DerivedCategory.Q.map (unit l E T ((roos l E T).obj Q)) ≫ s.hom =
            eP.inv ≫ DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E T none P.obj) ∧
          (∀ j : ℕ,
            DerivedCategory.Q.map (unit l E T ((roos l E T).obj Q)) ≫ s.hom ≫
                DerivedCategory.Q.map (evaluation l E T
                  ((IntegralOnSlice.tower l E T none).obj P.obj) j) =
              eP.inv ≫ DerivedCategory.Q.map
                (((IntegralOnSlice.augmentation l E T none).app P.obj).app (op j))) ∧
          (∃ (hprod : HasProduct (fun j : ℕ ↦
                (IntegralOnSlice.derivedTower l E T none P).obj (op j))),
            (fun [_hp : HasProduct (fun j : ℕ ↦
                (IntegralOnSlice.derivedTower l E T none P).obj (op j))] ↦
            ∃ (p : DerivedCategory.Q.obj ((roos l E T).obj Q) ⟶
                ∏ᶜ fun j : ℕ ↦ (IntegralOnSlice.derivedTower l E T none P).obj (op j))
            (δ : (∏ᶜ fun j : ℕ ↦
                (IntegralOnSlice.derivedTower l E T none P).obj (op j)) ⟶
              (DerivedCategory.Q.obj ((roos l E T).obj Q))⟦(1 : ℤ)⟧),
            IsDerivedLimitTriangle
              (fun j : ℕ ↦ (IntegralOnSlice.derivedTower l E T none P).map
                (homOfLE j.le_succ).op) (DerivedCategory.Q.obj ((roos l E T).obj Q)) p δ ∧
            ∀ j : ℕ, p ≫ Pi.π _ j = eP.inv ≫ DerivedCategory.Q.map
              (((IntegralOnSlice.augmentation l E T none).app P.obj).app (op j)))
              (_hp := hprod)) ∧
          IntegralOnSlice.IsComplete l E T none
            (DerivedCategory.Q.obj ((roos l E T).obj Q)) := by
  sorry

end WeilConjectures.PowerTorsionLimit
