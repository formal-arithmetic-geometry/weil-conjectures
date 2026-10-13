/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Algebra.Homology.BalancedDerivedTensorModel
public import Mathlib.CategoryTheory.Functor.Currying
import Sheaf.Algebra.Homology.MixedTotalTensorAssociatorNaturality
import Sheaf.Algebra.Homology.MixedTotalTensorAssociatorDescent

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

private theorem conjugate_naturality {C D : Type*} [Category C] [Category D]
    (L U : C ⥤ D) (γ : L ⟶ U) {Z : C} {YL YU : D}
    (eL : YL ⟶ L.obj Z) (eU : YU ⟶ U.obj Z) (a : YL ⟶ YU)
    (eLi : L.obj Z ⟶ YL) (eUi : U.obj Z ⟶ YU)
    (hs : eL ≫ γ.app Z = a ≫ eU)
    (hLi : eLi ≫ eL = 𝟙 _) (hUi : eU ≫ eUi = 𝟙 _)
    (hUi' : eUi ≫ eU = 𝟙 _) (g : Z ⟶ Z) :
    a ≫ (eU ≫ U.map g ≫ eUi) = (eL ≫ L.map g ≫ eLi) ≫ a := by
  have ha : a = eL ≫ γ.app Z ≫ eUi := by
    calc
      a = (a ≫ eU) ≫ eUi := by rw [Category.assoc, hUi, Category.comp_id]
      _ = (eL ≫ γ.app Z) ≫ eUi := by rw [hs]
      _ = eL ≫ γ.app Z ≫ eUi := Category.assoc _ _ _
  rw [ha]
  simp only [Category.assoc]
  rw [← Category.assoc eUi eU, hUi', Category.id_comp,
    ← Category.assoc eLi eL, hLi, Category.id_comp]
  simpa only [Category.assoc] using
    congrArg (fun t ↦ eL ≫ t ≫ eUi) (γ.naturality g).symm

set_option maxHeartbeats 800000 in
-- The nested product functors and model comparisons require additional elaboration work.
set_option backward.isDefEq.respectTransparency false in
/-- (blueprint: lem-pc-kflat-derived-tensor-associator) The canonical mixed-ring total tensor
associator is a natural chain isomorphism. It descends, independently of K-flat resolutions,
to a natural isomorphism on derived categories, commuting with every derived endomorphism
of the second coefficient ring. Source: Stacks Project, Tag 0BYJ and Section 06Y5.

Proof:
1. Construct the canonical mixed total chain associator from the module associator using
   Mathlib's total bifunctor associator. Its naturality and summand formula are supplied by
   `lem-pc-mixed-total-tensor-associator-naturality`.
2. Descend this natural isomorphism through the K-flat models, using
   `lem-pc-mixed-total-tensor-associator-descent`. This supplies derived trifunctors,
   comparison isomorphisms and the compatible natural derived associator.
3. Each resolution map becomes invertible after Q. Their product is invertible, and both
   derived trifunctors preserve that invertibility. Naturality of the derived associator,
   combined with its model comparison equation, gives the resolution square.
4. Solve the square for the chain associator by composing with the inverse model comparison.
   Naturality at ((identity, identity), phi), followed by cancellation of the comparison
   inverses, gives the displayed conjugation equation for every derived endomorphism. -/
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
                Q.map (α.hom.app (J.obj X)) := by
  classical
  dsimp only
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
  let α : Lc ≅ Uc := NatIso.ofComponents
    (fun X ↦ mixedChainAssociator R A X.1.1 X.1.2 X.2)
    (fun {_ _} f ↦ mixedChainAssociator_naturality R A _ _ f)
  refine ⟨α, ?_, ?_⟩
  · intro P N F i j k
    exact mixedChainAssociator_summand R A P N F i j k
  obtain ⟨L, U, βL, βU, γ, hγ⟩ := exists_mixedTotalTensorAssociator_descent R A α
  refine ⟨L, U, βL, βU, γ, hγ, ?_⟩
  intro E K P N F p n q hp hn hq
  let X : (KA × KA) × KR := ((P, N), F)
  let Z : (CA × CA) × CR := ((E, K),
    (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R B))
  let f : Qp.obj (J.obj X) ⟶ Qp.obj Z := Qp.map ((p, n), q)
  have : IsIso (Q.map p) := (isIso_Q_map_iff_quasiIso (ModuleCat A) p).2 hp
  have : IsIso (Q.map n) := (isIso_Q_map_iff_quasiIso (ModuleCat A) n).2 hn
  have : IsIso (Q.map q) := (isIso_Q_map_iff_quasiIso (ModuleCat R) q).2 hq
  have : IsIso f := by
    dsimp [f, Qp]
    apply (CategoryTheory.isIso_prod_iff _ _).2
    refine ⟨?_, inferInstance⟩
    exact (CategoryTheory.isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have hsquare : (βL.hom.app X ≫ L.map f) ≫ γ.hom.app (Qp.obj Z) =
      Q.map (α.hom.app (J.obj X)) ≫ (βU.hom.app X ≫ U.map f) := by
    rw [Category.assoc, γ.hom.naturality, ← Category.assoc, hγ X, Category.assoc]
  refine ⟨inferInstance, inferInstance, hsquare, ?_⟩
  intro φ eLi eUi hLi hLi' hUi hUi'
  exact conjugate_naturality L U γ.hom
    (βL.hom.app X ≫ L.map f) (βU.hom.app X ≫ U.map f)
    (Q.map (α.hom.app (J.obj X))) eLi eUi hsquare hLi' hUi hUi'
    ((𝟙 _, 𝟙 _), φ)

end DerivedCategory
