/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.IntegralDerivedOperations
public import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Paper.IntegralOperationsWellDefined
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-! # Right shifts of the completed integral tensor

Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4), and the last sentence
of the main-20261015 blueprint proof of `lem-sf-twist-interchange`;
Stacks Project, Tags 011G, 012Z, 014E and 08TC
(blueprint: lem-sf-completed-tensor-shift-right).

The finite comparison has the same signed formula as Mathlib's right tensor shift.
Its formula is imposed directly on the recorded reduced tensor generators, without
extra tensor structure hypotheses. The strict tower comparison and the product and
cone formulas normalize the derived natural isomorphism on every good model.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

/-- Shift the second input of a bifunctor, retaining the first input.
Source: Stacks Tag 011G (blueprint: lem-sf-completed-tensor-shift-right). -/
noncomputable def completedTensorShiftSecond (A : Type a) [Category.{b} A] [HasShift A ℤ]
    (r : ℤ) : A × A ⥤ A × A :=
  (𝟭 A).prod (shiftFunctor A r)

section ProductCone

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

/-- The degreewise product shift identification, after the specified tower comparison.
Source: Stacks Tags 011G and 08TC (blueprint: lem-sf-completed-tensor-shift-right). -/
noncomputable def completedTensorShiftProductIso
    (C D : ℕᵒᵖ ⥤ CochainComplex A ℤ) (r : ℤ)
    (α : D ≅ C ⋙ shiftFunctor (CochainComplex A ℤ) r) :
    (∏ᶜ fun n : ℕ ↦ D.obj (op n)) ≅ (∏ᶜ fun n : ℕ ↦ C.obj (op n))⟦r⟧ :=
  Limits.Pi.mapIso (fun n ↦ α.app (op n)) ≪≫
    (PreservesProduct.iso (shiftFunctor (CochainComplex A ℤ) r)
      (fun n : ℕ ↦ C.obj (op n))).symm

/-- The actual endomorphism 1-s of the product of a strict tower.
Source: Stacks Tag 08TC (blueprint: lem-sf-completed-tensor-shift-right). -/
noncomputable def completedTensorShiftOneSub
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :=
  towerTransitionEndomorphism (K := fun n ↦ C.obj (op n)) (integralOperationsTowerStep C)

/-- Cone compatibility: the unshifted summand has coefficient 1 and the shifted
summand has coefficient (-1)^r, after the product identification. Mathlib orders
these summands as A[1], B, opposite to the written B ⊕ A[1].
Source: Stacks Tag 014E (blueprint: lem-sf-completed-tensor-shift-right). -/
def completedTensorShiftConeFormula
    (C D : ℕᵒᵖ ⥤ CochainComplex A ℤ) (r : ℤ)
    (α : D ≅ C ⋙ shiftFunctor (CochainComplex A ℤ) r)
    (δ : CochainComplex.mappingCone (completedTensorShiftOneSub D) ≅
      (CochainComplex.mappingCone (completedTensorShiftOneSub C))⟦r⟧) : Prop :=
  (∀ j : ℤ,
    (CochainComplex.mappingCone.inr (completedTensorShiftOneSub D)).f j ≫ δ.hom.f j =
      (completedTensorShiftProductIso C D r α).hom.f j ≫
        (CochainComplex.mappingCone.inr (completedTensorShiftOneSub C)).f (j + r) ≫
        (CochainComplex.shiftFunctorObjXIso
          (CochainComplex.mappingCone (completedTensorShiftOneSub C)) r j (j + r) rfl).inv) ∧
  (∀ (i j : ℤ) (h : i + (-1) = j),
    (CochainComplex.mappingCone.inl (completedTensorShiftOneSub D)).v i j h ≫
        δ.hom.f j =
      r.negOnePow • ((completedTensorShiftProductIso C D r α).hom.f i ≫
        (CochainComplex.mappingCone.inl (completedTensorShiftOneSub C)).v
          (i + r) (j + r) (by omega) ≫
        (CochainComplex.shiftFunctorObjXIso
          (CochainComplex.mappingCone (completedTensorShiftOneSub C)) r j (j + r) rfl).inv))

/-- Shift the cone comparison by -1 and interchange the two shifts. This is the
specified comparison of the product mapping-fiber complexes, without cone choices.
Source: Stacks Tags 014E and 08TC (blueprint: lem-sf-completed-tensor-shift-right). -/
noncomputable def completedTensorShiftRoosIso
    (C D : ℕᵒᵖ ⥤ CochainComplex A ℤ) (r : ℤ)
    (δ : CochainComplex.mappingCone (completedTensorShiftOneSub D) ≅
      (CochainComplex.mappingCone (completedTensorShiftOneSub C))⟦r⟧) :
    integralOperationsRoos D ≅ (integralOperationsRoos C)⟦r⟧ :=
  (shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).mapIso δ ≪≫
    (shiftFunctorComm (CochainComplex A ℤ) r (-1 : ℤ)).app
      (CochainComplex.mappingCone (completedTensorShiftOneSub C))

end ProductCone

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The signed formula on every finite-level total-tensor generator. The source
uses Q[r], so its q-th term is Q^(q+r); the target is reindexed by the displayed
shift identification. The tower isomorphism itself asserts transition compatibility.
Source: Stacks Tags 011G and 012Z (blueprint: lem-sf-completed-tensor-shift-right). -/
def integralCompletedTensorFiniteShiftFormula (W : AlgebraicGeometry.Scheme.{t})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (r : ℤ)
    (α : (integralOperationsTensorTowerFunctor l E W).obj (P, Q⟦r⟧) ≅
      (integralOperationsTensorTowerFunctor l E W).obj (P, Q) ⋙
        shiftFunctor (CochainComplex (integralTowerModules l E W) ℤ) r) : Prop :=
  ∀ (n : ℕ) (i j : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P).X i).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X (j + r)).val.obj U),
    (((α.hom.app (op n)).f (i + j)).val.app U)
      (integralOperationsTotalTensorSection l E W n P (Q⟦r⟧) i j U x y) =
    ((CochainComplex.shiftFunctorObjXIso
      ((integralOperationsTensorLevel l E W n).obj (P, Q))
        r (i + j) (i + (j + r)) (by omega)).inv.val.app U)
      ((r * i).negOnePow •
        integralOperationsTotalTensorSection l E W n P Q i (j + r) U x y)

/-- Normalization on every flat-term K-flat pair. The finite signed tower map
induces the product map, then the specified cone map, then its [-1] shift.
The last equality identifies this concrete map with the derived natural comparison.
It quantifies over all resolutions, rather than selecting a special pair.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4); Stacks Tags 014E,
08TC and 06YT (blueprint: lem-sf-completed-tensor-shift-right). -/
def integralCompletedTensorRightShiftProperty (W : AlgebraicGeometry.Scheme.{t}) (r : ℤ)
    (σ : completedTensorShiftSecond (DerivedCategory (integralTowerModules l E W)) r ⋙
        integralCompletedTensor l E W ≅
      integralCompletedTensor l E W ⋙
        shiftFunctor (DerivedCategory (integralTowerModules l E W)) r) : Prop :=
  ∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory),
    ∃ (hQ : integralOperationsGoodComplex l E W (Q.obj⟦r⟧))
      (α : (integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj⟦r⟧) ≅
        (integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj) ⋙
          shiftFunctor (CochainComplex (integralTowerModules l E W) ℤ) r),
      integralCompletedTensorFiniteShiftFormula l E W P.obj Q.obj r α ∧
      ∃ (δ : CochainComplex.mappingCone (completedTensorShiftOneSub
            ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj⟦r⟧))) ≅
          (CochainComplex.mappingCone (completedTensorShiftOneSub
            ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))))⟦r⟧),
        completedTensorShiftConeFormula
            ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))
            ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj⟦r⟧)) r α δ ∧
        (integralCompletedTensor l E W).map
            (𝟙 (DerivedCategory.Q.obj P.obj),
              ((DerivedCategory.Q.commShiftIso r).hom.app Q.obj)) ≫
          σ.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (shiftFunctor (DerivedCategory (integralTowerModules l E W)) r).map
            ((integralCompletedTensorComparison l E W).hom.app (P, Q)) =
        (integralCompletedTensorComparison l E W).hom.app (P, ⟨Q.obj⟦r⟧, hQ⟩) ≫
          DerivedCategory.Q.map
            (completedTensorShiftRoosIso
              ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))
              ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj⟦r⟧)) r δ).hom ≫
          (DerivedCategory.Q.commShiftIso r).hom.app
            ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj))

/-- Right shifts of the specified completed tensor, natural in both derived inputs
and independent of all flat-term K-flat representatives. The normalization uses
the explicit finite, product and cone formulas on every pair of representatives.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4), pp. 22–23;
main-20261015 blueprint, last sentence of lem-sf-twist-interchange.proof.md
(blueprint: lem-sf-completed-tensor-shift-right).

Proof:
1. On arbitrary complexes use the total tensor of def-pc-tensor-complex-sheaves.
Multiply its (i,j)-summand by (-1)^(ri). The first differential changes i to i+1,
so both chain-map composites have sign (-1)^(ri+r); the second has sign
(-1)^(ri+i+r). The same formula is the inverse. Degree-zero maps preserve i,
which proves naturality.
2. Choose flat-term K-flat resolutions by lem-pc-kflat-resolution. The shifted
second resolution is still flat termwise. By step 1, tensoring it with an acyclic
complex is the shift of an acyclic total tensor, so it remains K-flat by
def-pc-kflat-complex. Its shifted augmentation remains a quasi-isomorphism.
3. Termwise finite reduction commutes with shift. Apply step 1 at each positive
level. Quotient transitions preserve i and hence commute with the sign. These
maps give the strict tower isomorphism alpha in the statement.
4. Degreewise products commute with shifts, identifying 1-s with its shift.
For Cone(f)=B ⊕ A[1], the map Cone(f[r]) → Cone(f)[r] sends (b,a) to
(b,(-1)^r a). Both chain-map composites give ((-1)^r db+f(a),-da), and the
same diagonal sign is inverse. This calculation is natural in commuting squares.
Shift by [-1] and interchange [r],[-1] to get the Roos comparison.
5. Apply the product and cone constructions to alpha, then use step 4. By
def-pur-integral-derived-operations these are exactly the two completed tensors.
The displayed cone formulas specify this composite including both summands.
6. All formulas commute with maps of good representatives. By clauses (1) and
(2) of lem-pur-integral-operations-well-defined, they descend through localization
and its inverses. The defining comparison of integralCompletedTensor gives the
normalization equality. The comparison holds for every pair of representatives;
its generator and cone formulas determine it uniquely. Localization therefore
determines sigma uniquely, proving independence of the chosen resolutions. -/
theorem integralCompletedTensorShiftRight (W : AlgebraicGeometry.Scheme.{t})
    [∀ w : W, Invertible (l : W.residueField w)] (r : ℤ) :
    ∃ σ : completedTensorShiftSecond (DerivedCategory (integralTowerModules l E W)) r ⋙
        integralCompletedTensor l E W ≅
      integralCompletedTensor l E W ⋙
        shiftFunctor (DerivedCategory (integralTowerModules l E W)) r,
      integralCompletedTensorRightShiftProperty l E W r σ := by
  sorry

end WeilConjectures
