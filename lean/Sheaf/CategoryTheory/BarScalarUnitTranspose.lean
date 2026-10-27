/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.CategoryTheory.DerivedColimitBar
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive

/-! # The bar scalar isomorphism and the coefficient unit

Source: Stacks Project, Cohomology on Sites, Tags 08PG, 08PH and 08Q8
(blueprint: lem-trf-bar-scalar-unit-transpose).

The scalar factor is written first, as in Mathlib: `s tensor x` denotes the
source's `x tensor s`. Derived scalar extensions are supplied as universal pairs;
the assertion supplies their representative-normalized adjunctions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex MonoidalCategory
open scoped ChangeOfRings

namespace CategoryTheory

/-- The scalar bar isomorphism is inverse to the transpose of the coefficient unit.
Source: Stacks 08PG, 08PH and 08Q8, with its typed order corrected
(blueprint: lem-trf-bar-scalar-unit-transpose).

Proof:
1. Apply lem-trf-derived-colimit-bar for the colimit units and semilinear generator map.
   Use lem-pur-sheaf-ring-derived-coefficient-adjunction to normalize the coefficient
   units to x mapped to 1 tensor x; lem-pur-derived-change-of-rings supplies the
   universal scalar extensions and their K-flat comparisons.
2. The balanced map on each summand sends (sigma,s tensor x) to
   s tensor (sigma,x). Its inverse distributes a tensor over a finite sum.
   Both composites fix the generators; positive terms are zero.
3. Each face commutes with this map. The last face restricts the coefficient,
   and tensor extension commutes with that restriction. The alternating signs agree.
4. Apply the representative Hom formula to the K-flat, flat-term bar complex.
   The adjunct sends s tensor (sigma,x) to (sigma,s tensor x), hence is Phi inverse.
5. Transpose the presheaf coefficient unit followed by the target colimit unit,
   using def-pc-sheaf-restrict-scalars for the underlying constant coefficients.
   The canonical semilinear map a has this transpose by the bar theorem. Transposing
   once more under the point coefficient adjunction. Expanding Adjunction.comp
   from def-weil-pbc-composite-adjunction
   gives the displayed composite-unit equation. The exact-composite factorization
   isomorphisms identify the two presentations of the same constant right adjoint.
6. Apply lem-weil-pbc-conjugate-iso-unit-equation with that common right adjoint.
   It gives a unique natural comparison, which is invertible. Injectivity of the
   Hom bijection identifies its component with beta, since both preserve the units.

The universal pairs are arbitrary presentations of the specified derived functors,
not additional coefficient-flatness hypotheses. The two returned adjunctions are
normalized on all complex representatives before F and its K-flat models are fixed.
K-flatness of F[0] (def-pc-kflat-complex) is expanded using the existing pointwise
tensor and total complex; no second K-flat predicate is defined.
-/
theorem categoryBarScalarUnitTranspose
    (B : CategoryColimitBarSystem.{u}) (E : Type u) [SmallCategory E]
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (T₀ : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (T₁ : DerivedCategory (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ DerivedCategory (Eᵒᵖ ⥤ ModuleCat.{u} S))
    (ε₀ : DerivedCategory.Q ⋙ T₀ ⟶ (ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q)
    (ε₁ : DerivedCategory.Q ⋙ T₁ ⟶ ((Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u} R) (ModuleCat.{u}
      S)).obj (ModuleCat.extendScalars φ)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (_h₀ : T₀.IsLeftDerivedFunctor ε₀ (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)))
    (_h₁ : T₁.IsLeftDerivedFunctor ε₁
      (HomologicalComplex.quasiIso (Eᵒᵖ ⥤ ModuleCat.{u} R) (.up ℤ))) :
    ∃ (a₀ : T₀ ⊣ (ModuleCat.restrictScalars φ).mapDerivedCategory) (a₁ : T₁ ⊣
      ((Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u} S) (ModuleCat.{u} R)).obj
      (ModuleCat.restrictScalars φ)).mapDerivedCategory),
    (∀ (P : CochainComplex (ModuleCat.{u} R) ℤ) (N : CochainComplex (ModuleCat.{u} S) ℤ) (f :
      ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P ⟶ N), a₀.homEquiv
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N) (ε₀.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map (((ModuleCat.extendRestrictScalarsAdj φ).mapHomologicalComplex (.up
      ℤ)).homEquiv P N f) ≫ (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.inv.app N) ∧
    (∀ (P : CochainComplex (Eᵒᵖ ⥤ ModuleCat.{u} R) ℤ) (N : CochainComplex (Eᵒᵖ ⥤ ModuleCat.{u} S) ℤ)
      (f : (((Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u} R) (ModuleCat.{u} S)).obj
      (ModuleCat.extendScalars φ)).mapHomologicalComplex (.up ℤ)).obj P ⟶ N), a₁.homEquiv
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N) (ε₁.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((((ModuleCat.extendRestrictScalarsAdj φ).whiskerRight
      Eᵒᵖ).mapHomologicalComplex (.up ℤ)).homEquiv P N f) ≫ ((Functor.whiskeringRight Eᵒᵖ
      (ModuleCat.{u} S) (ModuleCat.{u} R)).obj (ModuleCat.restrictScalars
      φ)).mapDerivedCategoryFactors.inv.app N) ∧
    ∀ F : Eᵒᵖ ⥤ ModuleCat.{u} R,
    (∀ P : CochainComplex (Eᵒᵖ ⥤ ModuleCat.{u} R) ℤ, P.Acyclic → (mapBifunctor P
      ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).obj F)
      (curriedTensor (Eᵒᵖ ⥤ ModuleCat.{u} R)) (.up ℤ)).Acyclic) →
    (∀ U : Eᵒᵖ, Module.Flat R (F.obj U)) →
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat ((B.models E R).bar.obj F) →
    (∀ q : ℤ, Module.Flat R (((B.models E R).bar.obj F).X q)) →
    IsIso (ε₁.app ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).obj F)) ∧ IsIso (ε₀.app
      ((B.models E R).bar.obj F)) ∧
    ∃ (Φ : ((B.models E S).bar.obj (((Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u} R) (ModuleCat.{u}
      S)).obj (ModuleCat.extendScalars φ)).obj F)) ≅ ((ModuleCat.extendScalars
      φ).mapHomologicalComplex (.up ℤ)).obj ((B.models E R).bar.obj F))
    (a : ((B.models E R).derived.obj (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (Eᵒᵖ ⥤
      ModuleCat.{u} R) 0).obj F))) ⟶ (ModuleCat.restrictScalars φ).mapDerivedCategory.obj ((B.models
      E S).derived.obj (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} S)
      0).obj (((Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u} R) (ModuleCat.{u} S)).obj
      (ModuleCat.extendScalars φ)).obj F)))))
    (β : T₀.obj ((B.models E R).derived.obj (DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).obj F))) ⟶ (B.models E S).derived.obj (T₁.obj
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).obj F)))),
    (∀ (n : ℕ) (σ : ComposableArrows E n) (x : F.obj (op σ.right)) (s : S), Φ.hom.f (-(n : ℤ))
      ((B.models E S).generator (((Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u} R) (ModuleCat.{u}
      S)).obj (ModuleCat.extendScalars φ)).obj F) n σ (s ⊗ₜ[R,φ] x)) = s ⊗ₜ[R,φ] ((B.models E
      R).generator F n σ x)) ∧
    (∀ (n : ℕ) (I : Type u) (J : Finset I) (σ : I → ComposableArrows E n) (x : ∀ i : I, F.obj (op (σ
      i).right)) (s : S), Φ.inv.f (-(n : ℤ)) (s ⊗ₜ[R,φ] (∑ i ∈ J, (B.models E R).generator F n (σ i)
      (x i))) = ∑ i ∈ J, (B.models E S).generator (((Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u} R)
      (ModuleCat.{u} S)).obj (ModuleCat.extendScalars φ)).obj F) n (σ i) (s ⊗ₜ[R,φ] (x i))) ∧
    a = (B.models E R).model.hom.app F ≫ DerivedCategory.Q.map (B.map (𝟭 E) φ
      (((ModuleCat.extendRestrictScalarsAdj φ).whiskerRight Eᵒᵖ).unit.app F)) ≫
      (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.inv.app ((B.models E S).bar.obj
      (((Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u} R) (ModuleCat.{u} S)).obj
      (ModuleCat.extendScalars φ)).obj F)) ≫ (ModuleCat.restrictScalars φ).mapDerivedCategory.map
      ((B.models E S).model.inv.app (((Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u} R) (ModuleCat.{u}
      S)).obj (ModuleCat.extendScalars φ)).obj F)) ∧
    a₀.homEquiv ((B.models E R).derived.obj (DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).obj F))) ((B.models E S).derived.obj (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} S) 0).obj (((Functor.whiskeringRight Eᵒᵖ
      (ModuleCat.{u} R) (ModuleCat.{u} S)).obj (ModuleCat.extendScalars φ)).obj F)))) (β ≫ (B.models
      E S).derived.map (ε₁.app ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).obj F)) ≫
      (B.models E S).derived.map (DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex ((Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u}
      R) (ModuleCat.{u} S)).obj (ModuleCat.extendScalars φ)) (.up ℤ) 0).hom.app F))) = a ∧
    β ≫ (B.models E S).derived.map (ε₁.app ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R)
      0).obj F)) ≫ (B.models E S).derived.map (DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex ((Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u}
      R) (ModuleCat.{u} S)).obj (ModuleCat.extendScalars φ)) (.up ℤ) 0).hom.app F)) ≫ (B.models E
      S).model.hom.app (((Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u} R) (ModuleCat.{u} S)).obj
      (ModuleCat.extendScalars φ)).obj F) = T₀.map ((B.models E R).model.hom.app F) ≫ ε₀.app
      ((B.models E R).bar.obj F) ≫ DerivedCategory.Q.map Φ.inv ∧
    (((B.models E R).adjunction.comp a₀).unit.app (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).obj F)) ≫
      ((ModuleCat.restrictScalars φ).mapDerivedCategory ⋙ (Functor.const Eᵒᵖ : (ModuleCat.{u} R) ⥤
      (Eᵒᵖ ⥤ ModuleCat.{u} R)).mapDerivedCategory).map (β) ≫ (Functor.mapDerivedCategoryCompIso
      (ModuleCat.restrictScalars φ) (Functor.const Eᵒᵖ : (ModuleCat.{u} R) ⥤ (Eᵒᵖ ⥤ ModuleCat.{u}
      R))).inv.app ((T₁ ⋙ (B.models E S).derived).obj (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).obj F))) = (a₁.comp (B.models E
      S).adjunction).unit.app (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (Eᵒᵖ ⥤
      ModuleCat.{u} R) 0).obj F)) ≫ (Functor.mapDerivedCategoryCompIso (Functor.const Eᵒᵖ :
      (ModuleCat.{u} S) ⥤ (Eᵒᵖ ⥤ ModuleCat.{u} S)) ((Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u} S)
      (ModuleCat.{u} R)).obj (ModuleCat.restrictScalars φ))).inv.app ((T₁ ⋙ (B.models E
      S).derived).obj (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R)
      0).obj F)))) ∧
    ∃ c : ((B.models E R).derived ⋙ T₀) ≅ (T₁ ⋙ (B.models E S).derived),
    (∀ X : DerivedCategory (Eᵒᵖ ⥤ ModuleCat.{u} R), ((B.models E R).adjunction.comp a₀).unit.app X ≫
      ((ModuleCat.restrictScalars φ).mapDerivedCategory ⋙ (Functor.const Eᵒᵖ : (ModuleCat.{u} R) ⥤
      (Eᵒᵖ ⥤ ModuleCat.{u} R)).mapDerivedCategory).map (c.hom.app X) ≫
      (Functor.mapDerivedCategoryCompIso (ModuleCat.restrictScalars φ) (Functor.const Eᵒᵖ :
      (ModuleCat.{u} R) ⥤ (Eᵒᵖ ⥤ ModuleCat.{u} R))).inv.app ((T₁ ⋙ (B.models E S).derived).obj X) =
      (a₁.comp (B.models E S).adjunction).unit.app X ≫ (Functor.mapDerivedCategoryCompIso
      (Functor.const Eᵒᵖ : (ModuleCat.{u} S) ⥤ (Eᵒᵖ ⥤ ModuleCat.{u} S)) ((Functor.whiskeringRight
      Eᵒᵖ (ModuleCat.{u} S) (ModuleCat.{u} R)).obj (ModuleCat.restrictScalars φ))).inv.app ((T₁ ⋙
      (B.models E S).derived).obj X)) ∧
    β = c.hom.app (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R)
      0).obj F)) ∧
    ∀ c' : (B.models E R).derived ⋙ T₀ ⟶ T₁ ⋙ (B.models E S).derived, (∀ X : DerivedCategory (Eᵒᵖ ⥤
      ModuleCat.{u} R), ((B.models E R).adjunction.comp a₀).unit.app X ≫ ((ModuleCat.restrictScalars
      φ).mapDerivedCategory ⋙ (Functor.const Eᵒᵖ : (ModuleCat.{u} R) ⥤ (Eᵒᵖ ⥤ ModuleCat.{u}
      R)).mapDerivedCategory).map (c'.app X) ≫ (Functor.mapDerivedCategoryCompIso
      (ModuleCat.restrictScalars φ) (Functor.const Eᵒᵖ : (ModuleCat.{u} R) ⥤ (Eᵒᵖ ⥤ ModuleCat.{u}
      R))).inv.app ((T₁ ⋙ (B.models E S).derived).obj X) = (a₁.comp (B.models E
      S).adjunction).unit.app X ≫ (Functor.mapDerivedCategoryCompIso (Functor.const Eᵒᵖ :
      (ModuleCat.{u} S) ⥤ (Eᵒᵖ ⥤ ModuleCat.{u} S)) ((Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u} S)
      (ModuleCat.{u} R)).obj (ModuleCat.restrictScalars φ))).inv.app ((T₁ ⋙ (B.models E
      S).derived).obj X)) → c' = c.hom
    := by
  sorry

end CategoryTheory
