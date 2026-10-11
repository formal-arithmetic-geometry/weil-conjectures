/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Algebra.Homology.BalancedDerivedTensorModel
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# The mixed-ring K-flat tensor associator

Source: Stacks Project, Tag 0BYJ, with the mixed coefficient tensor construction of
Section 06Y5 (blueprint: lem-pc-kflat-derived-tensor-associator).

The summand equation specifies the canonical rebracketing, rather than an arbitrary chain
isomorphism. The natural model comparisons on the full subcategories of K-flat complexes
specify descent to the derived categories. Their compatibility with the derived associator
expresses independence of all three resolutions, including roofs rather than just chain maps.
-/

@[expose] public section

universe u wA wR

open CategoryTheory MonoidalCategory HomologicalComplex

namespace DerivedCategory

/-- (blueprint: lem-pc-kflat-derived-tensor-associator) The canonical mixed-ring total tensor
associator is a natural chain isomorphism. It descends, independently of K-flat resolutions,
to a natural isomorphism on derived categories, commuting with every derived endomorphism
of the second coefficient ring. Source: Stacks Project, Tag 0BYJ and Section 06Y5.

Proof:
1. Choose K-flat resolutions over `A`, `A`, and `R` (`lem-pc-kflat-resolution`, ordinary
   module specialization `def-pc-module-kflat-complex`). The total tensor models are the
   complexes of `def-pc-tensor-complex-sheaves` and `def-pc-mixed-total-tensor`.
2. Apply `HomologicalComplex.mapBifunctorAssociator`, the Mathlib leaf
   `lem-pc-kflat-total-tensor-associativity`, to the module associator. On each triple summand
   this is ordinary rebracketing; the total differential has the same three Koszul signs.
3. For an endomorphism in `D(R)`, use a roof through a common K-flat resolution, not a chain
   endomorphism of the chosen K-flat complex. Both total constructions preserve the
   quasi-isomorphism legs (`lem-pc-derived-tensor-second-factor-functor`). Chain naturality
   gives commutation with each leg and hence with the roof, in particular multiplication.
4. The canonical comparisons of `lem-pc-balanced-derived-tensor-model` identify each model
   with its derived value. Common K-flat resolutions and chain naturality give the comparison
   square, independence of resolutions, and naturality for derived morphisms in all variables.
   The same argument retains the endomorphism commutation under these identifications. -/
theorem exists_kFlatDerivedTensorAssociator
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)] :
    let CA := CochainComplex (ModuleCat.{u} A) ℤ
    let CR := CochainComplex (ModuleCat.{u} R) ℤ
    let DA := DerivedCategory (ModuleCat.{u} A)
    let DR := DerivedCategory (ModuleCat.{u} R)
    let T := (curriedTensor (ModuleCat.{u} A)).map₂CochainComplex
    let S := ModuleCat.mixedTotalTensor (algebraMap R A)
    let Lc := Functor.uncurry.obj (Functor.uncurry.obj (bifunctorComp₁₂ T S))
    let Uc := Functor.uncurry.obj (Functor.uncurry.obj (bifunctorComp₂₃ T S))
    let KA := CochainComplex.KFlat (ModuleCat.{u} A)
    let KR := CochainComplex.KFlat (ModuleCat.{u} R)
    let J : ((KA × KA) × KR) ⥤ ((CA × CA) × CR) :=
      ((CochainComplex.ιKFlat (ModuleCat.{u} A)).prod
        (CochainComplex.ιKFlat (ModuleCat.{u} A))).prod
          (CochainComplex.ιKFlat (ModuleCat.{u} R))
    let Qp : ((CA × CA) × CR) ⥤ ((DA × DA) × DR) :=
      ((Q (C := ModuleCat.{u} A)).prod (Q (C := ModuleCat.{u} A))).prod
        (Q (C := ModuleCat.{u} R))
    ∃ α : Lc ≅ Uc,
      (∀ (P N : CA) (F : CR) (i j k : ℤ),
        ((ModuleCat.mixedTensor (algebraMap R A)).map
          (ιMapBifunctor P N (curriedTensor _) (.up ℤ) i j (i + j) rfl)).app (F.X k) ≫
          ιMapBifunctor ((T.obj P).obj N) F
            (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ) (i + j) k ((i + j) + k) rfl ≫
          (α.hom.app ((P, N), F)).f ((i + j) + k) =
        (α_ (P.X i) (N.X j)
          ((ModuleCat.extendScalars (algebraMap R A)).obj (F.X k))).hom ≫
          ((curriedTensor (ModuleCat.{u} A)).obj (P.X i)).map
            (ιMapBifunctor N F (ModuleCat.mixedTensor (algebraMap R A))
              (.up ℤ) j k (j + k) rfl) ≫
          ιMapBifunctor P ((S.obj N).obj F) (curriedTensor _) (.up ℤ)
            i (j + k) ((i + j) + k) (Int.add_assoc i j k).symm) ∧
      ∃ (L U : ((DA × DA) × DR) ⥤ DA)
        (βL : J ⋙ Lc ⋙ Q ≅ J ⋙ Qp ⋙ L)
        (βU : J ⋙ Uc ⋙ Q ≅ J ⋙ Qp ⋙ U) (γ : L ≅ U),
        (∀ X : (KA × KA) × KR,
          (βL.hom.app X) ≫ γ.hom.app (Qp.obj (J.obj X)) =
            Q.map (α.hom.app (J.obj X)) ≫ βU.hom.app X) ∧
        ∀ (E K : CA) (P N : KA) (F : KR)
          (p : P.obj ⟶ E) (n : N.obj ⟶ K)
          (q : F.obj ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj
            (ModuleCat.of R B)),
          QuasiIso p → QuasiIso n → QuasiIso q →
          let X : (KA × KA) × KR := ((P, N), F)
          let Z : (CA × CA) × CR := ((E, K),
            (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R B))
          let f : Qp.obj (J.obj X) ⟶ Qp.obj Z := Qp.map ((p, n), q)
          IsIso (L.map f) ∧ IsIso (U.map f) ∧
          (βL.hom.app X ≫ L.map f) ≫ γ.hom.app (Qp.obj Z) =
            Q.map (α.hom.app (J.obj X)) ≫ (βU.hom.app X ≫ U.map f) ∧
          ∀ φ : End ((Q (C := ModuleCat.{u} R)).obj Z.2),
            let eL := βL.hom.app X ≫ L.map f
            let eU := βU.hom.app X ≫ U.map f
            ∀ (eLi : L.obj (Qp.obj Z) ⟶ Q.obj (Lc.obj (J.obj X)))
              (eUi : U.obj (Qp.obj Z) ⟶ Q.obj (Uc.obj (J.obj X))),
              eL ≫ eLi = 𝟙 _ → eLi ≫ eL = 𝟙 _ →
              eU ≫ eUi = 𝟙 _ → eUi ≫ eU = 𝟙 _ →
              Q.map (α.hom.app (J.obj X)) ≫
                (eU ≫ U.map ((𝟙 _, 𝟙 _), φ) ≫ eUi) =
              (eL ≫ L.map ((𝟙 _, 𝟙 _), φ) ≫ eLi) ≫
                Q.map (α.hom.app (J.obj X)) :=
  sorry

end DerivedCategory
