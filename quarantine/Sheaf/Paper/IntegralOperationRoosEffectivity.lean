/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralDerivedOperations
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.Paper.SfDerivedCompleteLegacyComparison
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat

/-! # Effectivity of the strict finite-operation towers

Source: Stacks Tags 099M and 099N(5); Bhatt--Scholze, Lemmas 3.5.4--3.5.7
(blueprint: lem-pur-integral-operation-roos-effectivity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical projection of the strict Roos complex to its nth tower term.
Source: Stacks Tag 08TC (blueprint: lem-pur-integral-operations-preserve-constructible).
It is the first mapping-cocone projection followed by the nth product projection. -/
def integralOperationRoosProjection (W : AlgebraicGeometry.Scheme.{u})
    (T : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    DerivedCategory.Q.obj (integralOperationsRoos T) ⟶ DerivedCategory.Q.obj (T.obj (op n)) :=
  DerivedCategory.Q.map
    (CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism (K := fun m ↦ T.obj (op m))
        (integralOperationsTowerStep T)) ≫ Pi.π (fun m ↦ T.obj (op m)) n)

/-- The finite pullback of the nth reduction of a good integral representative.
The coefficient pullback is the canonical pro-etale inverse image with its
constant-ring action; exactness makes this compute `f⁻¹(K tensor^L A_(n+1))`.
Source: Bhatt--Scholze, Lemma 6.5.9(5); Stacks Tag 099N(5)
(blueprint: lem-pur-integral-operations-preserve-constructible). -/
def integralPullbackFiniteComplex {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :=
  ((integralOperationsLevelPullback l E f n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((unrestrictedIntegralFiniteComplex l E Y n).obj P)

/-- The finite derived tensor on the two reduced K-flat representatives.
This is the recorded total tensor, before restricting its scalar action to the completion.
Source: Bhatt--Scholze, Lemma 6.5.5; Stacks Tag 09BQ
(blueprint: lem-pur-integral-operations-preserve-constructible). -/
def integralTensorFiniteComplex (W : AlgebraicGeometry.Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :=
  (Functor.uncurry.obj
    ((MonoidalCategory.curriedTensor
      (integralOperationsFiniteModules l E W n)).map₂CochainComplex)).obj
        (((unrestrictedIntegralFiniteComplex l E W n).obj P),
          ((unrestrictedIntegralFiniteComplex l E W n).obj Q))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The strict mapping-cocone model has the actual localized projections.
Source: Stacks Tag 08TC. Exact products identify both product vertices; mapping the
mapping-cocone triangle and transporting those vertices gives the required triangle. -/
private theorem strictRoosTriangle {A : Type a} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [HasCountableProducts A] [CountableAB4Star A]
    [HasCountableProducts (DerivedCategory A)]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    ∃ δ, IsDerivedLimitTriangle
      (K := fun n ↦ DerivedCategory.Q.obj (C.obj (op n)))
      (fun n ↦ DerivedCategory.Q.map (integralOperationsTowerStep C n))
      (DerivedCategory.Q.obj (integralOperationsRoos C))
      (Pi.lift (fun n ↦ DerivedCategory.Q.map
        (CochainComplex.mappingCocone.fst
          (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
            (integralOperationsTowerStep C)) ≫
            Pi.π (fun n ↦ C.obj (op n)) n))) δ := by
  dsimp only [integralOperationsRoos]
  let Q := DerivedCategory.Q (C := A)
  let P := fun n ↦ C.obj (op n)
  let D := fun n ↦ Q.obj (P n)
  obtain ⟨_, hp, _⟩ := derivedCategory_countableProducts_core.{0} A
  obtain ⟨hlim⟩ := hp ℕ P
  let : PreservesLimit (Discrete.functor P) Q :=
    preservesLimit_of_preserves_limit_cone (limit.isLimit _) hlim
  let e : Q.obj (∏ᶜ P) ≅ ∏ᶜ D := PreservesProduct.iso Q P
  have he (n : ℕ) : e.hom ≫ Pi.π D n = Q.map (Pi.π P n) := by
    exact piComparison_comp_π Q P n
  dsimp only [D] at he
  let t := towerTransitionEndomorphism (K := P) (integralOperationsTowerStep C)
  have hmid : Q.map t ≫ e.hom = e.hom ≫
      towerTransitionEndomorphism (K := D)
        (fun n ↦ Q.map (integralOperationsTowerStep C n)) := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, he, ← Q.map_comp]
    rw [(towerTransitionEndomorphism_eq_iff (K := P) (integralOperationsTowerStep C) t).mp rfl n]
    simp only [Functor.map_sub, Functor.map_comp]
    rw [Category.assoc, (towerTransitionEndomorphism_eq_iff (K := D)
      (fun n ↦ Q.map (integralOperationsTowerStep C n)) _).mp rfl n]
    simp only [Preadditive.comp_sub, ← Category.assoc, D, he]
  let T := Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle t)
  refine ⟨e.inv ≫ T.mor₃, ?_⟩
  apply Pretriangulated.isomorphic_distinguished T
    (DerivedCategory.mappingCocone_triangle_distinguished t)
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm ?_ ?_ ?_
  · change (Pi.lift (fun n ↦ Q.map
        (CochainComplex.mappingCocone.fst t ≫ Pi.π P n))) ≫ e.inv =
      𝟙 _ ≫ Q.map (CochainComplex.mappingCocone.fst t)
    rw [Category.id_comp]
    apply (cancel_mono e.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, he, Pi.lift_π, Functor.map_comp]
  · change towerTransitionEndomorphism (fun n ↦ Q.map (integralOperationsTowerStep C n)) ≫
      e.inv = e.inv ≫ Q.map t
    apply (cancel_mono e.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hmid]
    simp only [Iso.inv_hom_id_assoc]
  · change (e.inv ≫ T.mor₃) ≫ (shiftFunctor _ (1 : ℤ)).map (𝟙 _) = e.inv ≫ T.mor₃
    rw [(shiftFunctor (DerivedCategory A) (1 : ℤ)).map_id T.obj₁, Category.comp_id]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

/-- The Roos limits of finite pullback and finite tensor towers are derived complete,
and their actual projection adjoints compute finite reduction. This assertion uses
only good representatives, with no boundedness or constructibility hypotheses.

Source: Stacks Tags 099M and 099N(5); Bhatt--Scholze, Lemmas 3.5.4--3.5.7
(blueprint: lem-pur-integral-operation-roos-effectivity).

Proof:
1. Ordinary reduction of a good representative is K-flat with flat terms by
changeOfRings_isKFlat_of_flat_terms. The map (x tensor a) tensor b mapped to
x tensor ab identifies two successive reductions with direct reduction. On pure
tensors these identifications satisfy the identity and the three-index cocycle.
2. Exact finite inverse image preserves K-flatness and commutes with tensor and
constant coefficient rings. Apply it to the preceding identifications to obtain
normalized finite pullback towers. For tensor towers, use tensor associativity:
(P_m tensor Q_m) tensor B_n identifies with P_n tensor Q_n. Totalization uses
direct sums and the signed differential; both coefficient maps commute with each
differential summand. The resulting transitions are the specified pure-tensor
transitions of integralOperationsPullbackTowerFunctor and integralOperationsTensorTowerFunctor.
3. Restrict the strict complexes to the completed coefficient ring. Their coherent
object in the derived category of towers, with its actual evaluation comparisons,
gives NormalizedDVRTower data. The preceding scalar-extension isomorphisms imply
its normalization condition by the tensor-restriction adjunction and Yoneda.
4. Exact countable products identify the localization of the strict mapping cocone
with a derived-limit triangle, preserving every product projection. Apply
normalizedDVRTower_effectivity to that triangle. Its canonical counits are adjoint
to exactly mappingCocone.fst followed by Pi.π and the inverse of the restriction
factorization. It also gives derived completeness, equivalent to IsSfDerivedComplete
by sfDerivedComplete_iff_legacy. This applies equally to both towers, without any
bound on their terms or cohomology.
5. Transport the limit vertex through the displayed isomorphism e. Distinguishedness
is invariant under triangle isomorphisms; naturality of the reduction unit identifies
the transported augmentation with the canonical augmentation. The adjoint comparison
is precomposed by derived reduction of e.hom and hence remains invertible. -/
theorem integralOperationRoos_effectivity :
    (∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (K : DerivedCategory (integralTowerModules l E X))
      (e : K ≅ DerivedCategory.Q.obj
        ((integralOperationsPullbackComplexFunctor l E f).obj P.obj)),
      IsSfDerivedComplete l E X K ∧ ∀ n : ℕ,
        IsIso ((((derivedScalarExtensionRestrictionAdjunction l E X n).choose).homEquiv _ _).symm
          (e.hom ≫ integralOperationRoosProjection l E X
            ((integralOperationsPullbackTowerFunctor l E f).obj P.obj) n ≫
            (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app
              (integralPullbackFiniteComplex l E f P.obj n)))) ∧
    (∀ (W : AlgebraicGeometry.Scheme.{u})
      (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
      (K : DerivedCategory (integralTowerModules l E W))
      (e : K ≅ DerivedCategory.Q.obj
        ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj))),
      IsSfDerivedComplete l E W K ∧ ∀ n : ℕ,
        IsIso ((((derivedScalarExtensionRestrictionAdjunction l E W n).choose).homEquiv _ _).symm
          (e.hom ≫ integralOperationRoosProjection l E W
            ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj)) n ≫
            (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.inv.app
              (integralTensorFiniteComplex l E W P.obj Q.obj n)))) := by
  sorry

end WeilConjectures
