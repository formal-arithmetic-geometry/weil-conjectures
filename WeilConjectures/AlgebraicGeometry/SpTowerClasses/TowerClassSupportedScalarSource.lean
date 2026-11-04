/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerClassScalarExtensionExact
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFiniteDiagonal
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryEndpointMaps
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerClassDiagonalFiniteSourceAux
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerClassDiagonalFiniteSourceAuxDerived
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerClassDiagonalFiniteSourceAuxPrecompose

/-! # The ordinary supported quotient system and its derived source equation

The supported finite quotients assemble to one ordinary map of module systems out of the
reduced supported integral source. Its two normalized transposes give the derived source
equation of the supported coefficient generator.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [local implicit_reducible] spCoefficientCommRings SpTowerShriek.tau lineModule

/-- A map out of a constant tower is determined levelwise; when the levelwise maps agree
with a given tower map after an epimorphism, they assemble to a tower map. -/
theorem constant_lift_of_epi {C : Type*} [Category C] {V Z : C} (v : V ⟶ Z) [Epi v]
    {K : ℕᵒᵖ ⥤ C} (Y : (Functor.const ℕᵒᵖ).obj V ⟶ K) (f : ∀ n : ℕ, Z ⟶ K.obj (op n))
    (hf : ∀ n, v ≫ f n = Y.app (op n)) :
    ∃ f₀ : (Functor.const ℕᵒᵖ).obj Z ⟶ K,
      (Functor.const ℕᵒᵖ).map v ≫ f₀ = Y ∧ ∀ n, f₀.app (op n) = f n := by
  refine ⟨{ app := fun n ↦ f n.unop, naturality := ?_ }, ?_, fun n ↦ rfl⟩
  · intro i j φ
    rw [← cancel_epi v]
    have hY := Y.naturality φ
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at hY ⊢
    rw [hf, ← Category.assoc, hf]
    exact hY
  · ext n
    exact hf n.unop

/-- The constant-tower version of `constant_lift_of_epi`. -/
theorem constantTower_lift_of_epi {T : Scheme.{u}} {V Z : DiagonalAb T} (v : V ⟶ Z) [Epi v]
    {K : Ab T} (Y : (constant T).obj V ⟶ K) (f : ∀ n : ℕ, Z ⟶ K.obj (op n))
    (hf : ∀ n, v ≫ f n = Y.app (op n)) :
    ∃ f₀ : (constant T).obj Z ⟶ K,
      (constant T).map v ≫ f₀ = Y ∧ ∀ n, f₀.app (op n) = f n := by
  unfold constant
  exact constant_lift_of_epi v Y f hf

/-- Left naturality of a composite adjunction, with the composite left functor written
as two successive maps. -/
theorem _root_.CategoryTheory.Adjunction.comp_homEquiv_naturality_left'
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F₁ : A ⥤ B} {G₁ : B ⥤ A} {F₂ : B ⥤ C} {G₂ : C ⥤ B}
    (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂) {X' X : A} {Y : C} (k : X' ⟶ X)
    (f : F₂.obj (F₁.obj X) ⟶ Y) :
    ((adj₁.comp adj₂).homEquiv X' Y) (F₂.map (F₁.map k) ≫ f) =
      k ≫ ((adj₁.comp adj₂).homEquiv X Y) f :=
  Adjunction.homEquiv_naturality_left _ _ _

/-- Naturality of a composite of two exact single comparisons. -/
theorem _root_.CategoryTheory.Functor.mapDerivedCategorySingleFunctor_comp_naturality
    {A B C : Type*} [Category A] [Category B] [Category C] [Abelian A] [Abelian B]
    [Abelian C] [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F₁ : A ⥤ B) (F₂ : B ⥤ C) [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂] {Y Y' : A} (f : Y ⟶ Y') :
    F₂.mapDerivedCategory.map (F₁.mapDerivedCategory.map
        ((DerivedCategory.singleFunctor A 0).map f)) ≫
      F₂.mapDerivedCategory.map ((F₁.mapDerivedCategorySingleFunctor 0).hom.app Y') ≫
      (F₂.mapDerivedCategorySingleFunctor 0).hom.app (F₁.obj Y') =
    F₂.mapDerivedCategory.map ((F₁.mapDerivedCategorySingleFunctor 0).hom.app Y) ≫
      (F₂.mapDerivedCategorySingleFunctor 0).hom.app (F₁.obj Y) ≫
      (DerivedCategory.singleFunctor C 0).map (F₂.map (F₁.map f)) := by
  have h₁ := (F₁.mapDerivedCategorySingleFunctor 0).hom.naturality f
  have h₂ := (F₂.mapDerivedCategorySingleFunctor 0).hom.naturality (F₁.map f)
  simp only [Functor.comp_map] at h₁ h₂
  rw [← F₂.mapDerivedCategory.map_comp_assoc, h₁, F₂.mapDerivedCategory.map_comp,
    Category.assoc, h₂]

/-- Two successive normalized adjunction transposes: the composite transpose of a scalar
extension of a normalized reduction comparison is the composite ordinary map. -/
theorem _root_.CategoryTheory.Adjunction.comp_transpose_of_normalized
    {𝒜 ℛ 𝒮 : Type*} {_ : Category 𝒜} {_ : Category ℛ} {_ : Category 𝒮} {_ : Abelian 𝒜}
    {_ : Abelian ℛ} {_ : Abelian 𝒮} {_ : HasDerivedCategory 𝒜} {_ : HasDerivedCategory ℛ}
    {_ : HasDerivedCategory 𝒮} {G : ℛ ⥤ 𝒜} {H : 𝒮 ⥤ ℛ} {_ : G.Additive} {_ : H.Additive}
    {_ : PreservesFiniteLimits G} {_ : PreservesFiniteColimits G}
    {_ : PreservesFiniteLimits H} {_ : PreservesFiniteColimits H}
    {red : DerivedCategory 𝒜 ⥤ DerivedCategory ℛ} {T : DerivedCategory ℛ ⥤ DerivedCategory 𝒮}
    (radj : red ⊣ G.mapDerivedCategory) (sadj : T ⊣ H.mapDerivedCategory)
    {X : 𝒜} {M : ℛ} {N : 𝒮} (η : X ⟶ G.obj M) (q : M ⟶ H.obj N)
    (a : red.obj ((DerivedCategory.singleFunctor 𝒜 0).obj X) ≅
      (DerivedCategory.singleFunctor ℛ 0).obj M)
    (s : T.obj ((DerivedCategory.singleFunctor ℛ 0).obj M) ⟶
      (DerivedCategory.singleFunctor 𝒮 0).obj N)
    (ha : (radj.homEquiv _ _) a.hom ≫ (G.mapDerivedCategorySingleFunctor 0).hom.app M =
      (DerivedCategory.singleFunctor 𝒜 0).map η)
    (hs : (sadj.homEquiv _ _) s ≫ (H.mapDerivedCategorySingleFunctor 0).hom.app N =
      (DerivedCategory.singleFunctor ℛ 0).map q) :
    ((radj.comp sadj).homEquiv _ _) (T.map a.hom ≫ s) ≫
        G.mapDerivedCategory.map ((H.mapDerivedCategorySingleFunctor 0).hom.app N) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app (H.obj N) =
      (DerivedCategory.singleFunctor 𝒜 0).map (η ≫ G.map q) := by
  simp only [Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply]
  erw [sadj.homEquiv_naturality_left]
  rw [radj.homEquiv_naturality_right]
  simp only [Category.assoc, ← G.mapDerivedCategory.map_comp_assoc]
  rw [hs]
  have hn := (G.mapDerivedCategorySingleFunctor 0).hom.naturality q
  simp only [Functor.comp_map] at hn
  rw [hn, ← Category.assoc, ha, Functor.map_comp]

/-- Abstract form of the supported source equation: normalized reduction and scalar
comparisons and an ordinary generator equation give the derived source equation. -/
theorem _root_.CategoryTheory.Adjunction.sourceEquation_of_normalized
    {𝒜 ℛ 𝒮 : Type*} {_ : Category 𝒜} {_ : Category ℛ} {_ : Category 𝒮} {_ : Abelian 𝒜}
    {_ : Abelian ℛ} {_ : Abelian 𝒮} {_ : HasDerivedCategory 𝒜} {_ : HasDerivedCategory ℛ}
    {_ : HasDerivedCategory 𝒮} {G : ℛ ⥤ 𝒜} {H : 𝒮 ⥤ ℛ} {_ : G.Additive} {_ : H.Additive}
    {_ : PreservesFiniteLimits G} {_ : PreservesFiniteColimits G}
    {_ : PreservesFiniteLimits H} {_ : PreservesFiniteColimits H}
    {red : DerivedCategory 𝒜 ⥤ DerivedCategory ℛ} {T : DerivedCategory ℛ ⥤ DerivedCategory 𝒮}
    (radj : red ⊣ G.mapDerivedCategory) (sadj : T ⊣ H.mapDerivedCategory)
    {X Z : 𝒜} {M R₀ : ℛ} {A₀ N : 𝒮} (v : Z ⟶ X) (η : X ⟶ G.obj M) (gen : Z ⟶ G.obj R₀)
    (sg : R₀ ⟶ H.obj A₀) (t : A₀ ⟶ N) (q : M ⟶ H.obj N)
    (a : red.obj ((DerivedCategory.singleFunctor 𝒜 0).obj X) ≅
      (DerivedCategory.singleFunctor ℛ 0).obj M)
    (uI : red.obj ((DerivedCategory.singleFunctor 𝒜 0).obj Z) ≅
      (DerivedCategory.singleFunctor ℛ 0).obj R₀)
    (sU : T.obj ((DerivedCategory.singleFunctor ℛ 0).obj R₀) ≅
      (DerivedCategory.singleFunctor 𝒮 0).obj A₀)
    (s₀ : T.obj ((DerivedCategory.singleFunctor ℛ 0).obj M) ⟶
      (DerivedCategory.singleFunctor 𝒮 0).obj N)
    (ha : (radj.homEquiv _ _) a.hom ≫ (G.mapDerivedCategorySingleFunctor 0).hom.app M =
      (DerivedCategory.singleFunctor 𝒜 0).map η)
    (hu : (radj.homEquiv _ _) uI.hom ≫ (G.mapDerivedCategorySingleFunctor 0).hom.app R₀ =
      (DerivedCategory.singleFunctor 𝒜 0).map gen)
    (hsU : (sadj.homEquiv _ _) sU.hom ≫ (H.mapDerivedCategorySingleFunctor 0).hom.app A₀ =
      (DerivedCategory.singleFunctor ℛ 0).map sg)
    (hs : (sadj.homEquiv _ _) s₀ ≫ (H.mapDerivedCategorySingleFunctor 0).hom.app N =
      (DerivedCategory.singleFunctor ℛ 0).map q)
    (hq : v ≫ η ≫ G.map q = gen ≫ G.map (sg ≫ H.map t)) :
    (sU.inv ≫ T.map (uI.inv ≫ red.map ((DerivedCategory.singleFunctor 𝒜 0).map v))) ≫
        T.map a.hom ≫ s₀ =
      (DerivedCategory.singleFunctor 𝒮 0).map t := by
  have h₁ := Adjunction.comp_transpose_of_normalized radj sadj η q a s₀ ha hs
  have h₂ := Adjunction.comp_transpose_of_normalized radj sadj gen sg uI sU.hom hu hsU
  rw [← cancel_epi (T.mapIso uI ≪≫ sU).hom]
  have hE : (T.mapIso uI ≪≫ sU).hom ≫ sU.inv ≫
      T.map (uI.inv ≫ red.map ((DerivedCategory.singleFunctor 𝒜 0).map v)) =
      T.map (red.map ((DerivedCategory.singleFunctor 𝒜 0).map v)) := by
    simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
      ← Functor.map_comp, Iso.hom_inv_id_assoc]
  rw [Category.assoc, reassoc_of% hE]
  apply ((radj.comp sadj).homEquiv _ _).injective
  refine (cancel_mono (G.mapDerivedCategory.mapIso
      ((H.mapDerivedCategorySingleFunctor 0).app N) ≪≫
      (G.mapDerivedCategorySingleFunctor 0).app (H.obj N)).hom).1 ?_
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [Adjunction.comp_homEquiv_naturality_left', Category.assoc, h₁, ← Functor.map_comp, hq,
    Adjunction.homEquiv_naturality_right, Category.assoc, Functor.comp_map,
    Functor.mapDerivedCategorySingleFunctor_comp_naturality, Functor.map_comp G,
    ← Category.assoc gen, Functor.map_comp (DerivedCategory.singleFunctor 𝒜 0) (gen ≫ _),
    ← h₂]
  simp only [Category.assoc]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The ordinary supported quotient map of systems: it is the canonical supported finite
quotient at every level, and it is the coefficient-pullback adjunct on the integral
generators. -/
theorem exists_supportedQuotientSystem {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    (c : Chern l E (diagonalSurface S))
    (g : SpTowerShriek.Geometry l E b (diagonalImmersion S))
    (p : CoefficientPullback l E b (diagonalImmersion S) g) :
    ∃ q : c.reduction.ordinary.obj
        ((constant (diagonalSurface S)).obj (diagonalIntegralSource S)) ⟶
        (WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E (diagonalSurface S))).obj
          (g.push.obj (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))),
      (constant (diagonalSurface S)).map (supportedIntegralUnit S) ≫
          c.reduction.model.adjunction.unit.app
            ((constant (diagonalSurface S)).obj (diagonalIntegralSource S)) ≫
          c.reduction.forget.F.map q =
        integerGenerator (diagonalSurface S) (Rrings l (diagonalSurface S))
            c.reduction.forget ≫
          c.reduction.forget.F.map (scalarGenerator l E (diagonalSurface S) ≫
            (WeilConjectures.SemilinearSections.res
              (coefficientSystemMap l E (diagonalSurface S))).map
                ((g.ordinaryAdjunction.homEquiv _ _) p.iso.hom)) ∧
      ∀ n : ℕ,
        (abEvaluation (diagonalSurface S) n).map
            (c.reduction.model.adjunction.unit.app
              ((constant (diagonalSurface S)).obj (diagonalIntegralSource S))) ≫
          (c.reduction.forget.F ⋙ abEvaluation (diagonalSurface S) n).map q ≫
          (finiteScalarForgetIso l E c n).hom.app
            (g.push.obj (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))) =
        finiteSupportedQuotient l E g n := by
  let W := diagonalSurface S
  let X := (constant W).obj (diagonalIntegralSource S)
  let N := g.push.obj (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
  let H := WeilConjectures.SemilinearSections.res (coefficientSystemMap l E W)
  let t := (g.ordinaryAdjunction.homEquiv _ _) p.iso.hom
  let Y := integerGenerator W (Rrings l W) c.reduction.forget ≫
    c.reduction.forget.F.map (scalarGenerator l E W ≫ H.map t)
  have := supported_integral_unit_epi S
  have hf (n : ℕ) : supportedIntegralUnit S ≫ finiteSupportedQuotient l E g n ≫
      (finiteScalarForgetIso l E c n).inv.app N = Y.app (op n) := by
    have h₁ : supportedIntegralUnit S ≫ finiteSupportedQuotient l E g n =
        Y.app (op n) ≫ (finiteScalarForgetIso l E c n).hom.app N := by
      rw [supportedIntegralUnit_comp_finiteSupportedQuotient l E g p n,
        ← finiteBoundary_sourceMap l E c n]
      have hn := (finiteScalarForgetIso l E c n).hom.naturality t
      simp only [Functor.comp_map] at hn
      simp only [Y, Category.assoc, Functor.map_comp, NatTrans.comp_app]
      erw [← hn]
      rfl
    rw [← Category.assoc, h₁, Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  obtain ⟨f₀, hf₀, hf₀n⟩ := constantTower_lift_of_epi (supportedIntegralUnit S) Y _ hf
  let q := (c.reduction.model.adjunction.homEquiv _ _).symm f₀
  have hη : c.reduction.model.adjunction.unit.app X ≫ c.reduction.forget.F.map q = f₀ := by
    exact (c.reduction.model.adjunction.homEquiv_unit _ _ q).symm.trans
      ((c.reduction.model.adjunction.homEquiv _ _).apply_symm_apply f₀)
  refine ⟨q, ?_, fun n ↦ ?_⟩
  · rw [hη]
    exact hf₀
  · rw [Functor.comp_map, ← Functor.map_comp_assoc, hη]
    have h := hf₀n n
    simp only [abEvaluation, evaluation_obj_map]
    rw [h, Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _

/-- The derived source equation from the ordinary generator equation, for an arbitrary
target system `N` with coefficient map `t`. -/
theorem supportedScalar_sourceEquation {S : Scheme.{u}}
    {c : Chern l E (diagonalSurface S)} (hc : c.Normalized l E)
    (a : c.reduction.derived.obj
        ((DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).obj
          ((constant (diagonalSurface S)).obj (diagonalIntegralSource S))) ≅
      (DerivedCategory.singleFunctor (Systems (diagonalSurface S)
        (Rrings l (diagonalSurface S))) 0).obj
        (c.reduction.ordinary.obj
          ((constant (diagonalSurface S)).obj (diagonalIntegralSource S))))
    (ha : c.reduction.model.sourceNormalization a
      (c.reduction.model.adjunction.unit.app
        ((constant (diagonalSurface S)).obj (diagonalIntegralSource S))))
    (N : Systems (diagonalSurface S) (Arings l E (diagonalSurface S)))
    (t : coefficient (diagonalSurface S) (Arings l E (diagonalSurface S)) ⟶ N)
    (q : c.reduction.ordinary.obj
        ((constant (diagonalSurface S)).obj (diagonalIntegralSource S)) ⟶
        (WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E (diagonalSurface S))).obj N)
    (hq : (constant (diagonalSurface S)).map (supportedIntegralUnit S) ≫
          c.reduction.model.adjunction.unit.app
            ((constant (diagonalSurface S)).obj (diagonalIntegralSource S)) ≫
          c.reduction.forget.F.map q =
        integerGenerator (diagonalSurface S) (Rrings l (diagonalSurface S))
            c.reduction.forget ≫
          c.reduction.forget.F.map (scalarGenerator l E (diagonalSurface S) ≫
            (WeilConjectures.SemilinearSections.res
              (coefficientSystemMap l E (diagonalSurface S))).map t))
    (s₀ : c.scalar.T.obj
        ((DerivedCategory.singleFunctor (Systems (diagonalSurface S)
          (Rrings l (diagonalSurface S))) 0).obj
          (c.reduction.ordinary.obj
            ((constant (diagonalSurface S)).obj (diagonalIntegralSource S)))) ⟶
      (DerivedCategory.singleFunctor (Systems (diagonalSurface S)
        (Arings l E (diagonalSurface S))) 0).obj N)
    (hs : (c.scalar.adjunction.homEquiv _ _) s₀ ≫
        ((WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E (diagonalSurface S))).mapDerivedCategorySingleFunctor
            0).hom.app N =
        (DerivedCategory.singleFunctor (Systems (diagonalSurface S)
          (Rrings l (diagonalSurface S))) 0).map q) :
    diagonalExtendedUnit l E c ≫ c.scalar.T.map a.hom ≫ s₀ =
      (DerivedCategory.singleFunctor (Systems (diagonalSurface S)
        (Arings l E (diagonalSurface S))) 0).map t :=
  Adjunction.sourceEquation_of_normalized c.reduction.model.derivedAdjunction
    c.scalar.adjunction _ _ _ _ t q a c.unitIso c.scalarUnit s₀ ha hc.1 hc.2.2 hs hq

/-- Compose an equation through an isomorphism to a common target. -/
theorem _root_.CategoryTheory.Iso.comp_hom_eq_of_comp_eq {C : Type*} [Category C]
    {A A' B P Y : C} (x₁ : A ⟶ A') (x₂ : A' ⟶ B) (s : B ≅ P) (σ : P ≅ Y) (s₀ : B ⟶ Y)
    (u : A ⟶ P) (w : A ⟶ Y) (hs : s.hom ≫ σ.hom = s₀) (h₁ : x₁ ≫ x₂ ≫ s₀ = w)
    (h₂ : u ≫ σ.hom = w) : x₁ ≫ x₂ ≫ s.hom = u := by
  rw [← cancel_mono σ.hom, h₂, ← h₁, ← hs]
  simp only [Category.assoc]

/-- The supported scalar comparison, given an ordinary supported quotient map whose
ordinary scalar adjunct is invertible: the source isomorphism is the single scalar counit
followed by this adjunct and the exact direct-image single comparison. -/
theorem supportedScalarPush_of_isIso {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    {c : Chern l E (diagonalSurface S)} (hc : c.Normalized l E)
    (g : SpTowerShriek.Geometry l E b (diagonalImmersion S))
    (p : CoefficientPullback l E b (diagonalImmersion S) g)
    (a : c.reduction.derived.obj
        ((DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).obj
          ((constant (diagonalSurface S)).obj (diagonalIntegralSource S))) ≅
      (DerivedCategory.singleFunctor (Systems (diagonalSurface S)
        (Rrings l (diagonalSurface S))) 0).obj
        (c.reduction.ordinary.obj
          ((constant (diagonalSurface S)).obj (diagonalIntegralSource S))))
    (ha : c.reduction.model.sourceNormalization a
      (c.reduction.model.adjunction.unit.app
        ((constant (diagonalSurface S)).obj (diagonalIntegralSource S))))
    (q : c.reduction.ordinary.obj
        ((constant (diagonalSurface S)).obj (diagonalIntegralSource S)) ⟶
        (WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E (diagonalSurface S))).obj
          (g.push.obj (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))))
    (hq : (constant (diagonalSurface S)).map (supportedIntegralUnit S) ≫
          c.reduction.model.adjunction.unit.app
            ((constant (diagonalSurface S)).obj (diagonalIntegralSource S)) ≫
          c.reduction.forget.F.map q =
        integerGenerator (diagonalSurface S) (Rrings l (diagonalSurface S))
            c.reduction.forget ≫
          c.reduction.forget.F.map (scalarGenerator l E (diagonalSurface S) ≫
            (WeilConjectures.SemilinearSections.res
              (coefficientSystemMap l E (diagonalSurface S))).map
                ((g.ordinaryAdjunction.homEquiv _ _) p.iso.hom)))
    (hΦ : IsIso ((c.scalar.ordinaryAdjunction.homEquiv _ _).symm q)) :
    ∃ s : c.scalar.T.obj
        ((DerivedCategory.singleFunctor (Systems (diagonalSurface S)
          (Rrings l (diagonalSurface S))) 0).obj
          (c.reduction.ordinary.obj
            ((constant (diagonalSurface S)).obj (diagonalIntegralSource S)))) ≅
        (SpTowerShriek.push l E b g).obj
          (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))),
      diagonalExtendedUnit l E c ≫ (c.scalar.T.map a.hom ≫ s.hom) = unitArrow l E p := by
  have : ∀ n, Finite (SpTowerShriek.R l E n) := b.finite
  have := scalarSingleCounit_isIso l E c
  have hs := scalarSingleCounit_transpose l E c _ _
    ((c.scalar.ordinaryAdjunction.homEquiv _ _).symm q)
  rw [Equiv.apply_symm_apply] at hs
  have key := supportedScalar_sourceEquation l E hc a ha _ _ q hq _ hs
  refine ⟨asIso ((scalarSingleCounit c).app _ ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((c.scalar.ordinaryAdjunction.homEquiv _ _).symm q)) ≪≫
    (g.push.singleFunctorCompRightDerivedFunctorIso.app
      (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))).symm,
    Iso.comp_hom_eq_of_comp_eq _ _ _ (g.push.singleFunctorCompRightDerivedFunctorIso.app
      (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))) _ _ _ ?_ key
      (coefficient_unit_single l E g p)⟩
  simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Category.assoc,
    Iso.inv_hom_id_app]
  exact congrArg ((scalarSingleCounit c).app _ ≫ ·) (Category.comp_id _)

end AlgebraicGeometry.ProEtale.SpTowerClasses
