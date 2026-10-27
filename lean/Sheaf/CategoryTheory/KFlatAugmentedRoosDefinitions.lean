/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.Algebra.Homology.TotalTensorHomotopyConeSigns
public import WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # K-flat tensor and augmented derived Roos fibres

Source: Stacks Project, sites-cohomology.tex, Tags 0941, 06YM and 06YS;
blueprint det-lem-int-tensor-product, first proof paragraph.
(blueprint: def-sfb-kflat-augmented-roos-interface)

The existing shifted cone uses coordinates (y,x). Changing these to (x,-y)
gives exactly H with differential (dx,(1-s)x-dy). Both coordinate equations below
are therefore the specified signed formula, including its shifted coordinate.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe a b w u v r

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CochainComplex

namespace CategoryTheory.KFlatAugmentedRoos

variable {M : Type a} [Category.{b} M] [Abelian M]

/-- Apply a functor on complexes to every level and transition of a strict tower.
Source: Stacks Tag 0941, strict tower interpretation
(blueprint: lem-sfb-kflat-augmented-roos-comparison).
The existing equivalence merely exchanges the tower and complex indices. -/
def tower (F : CochainComplex M ℤ ⥤ CochainComplex M ℤ) :
    CochainComplex (ℕᵒᵖ ⥤ M) ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ M) ℤ :=
  HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj F ⋙
      (HomologicalComplex.functorEquivalence M (.up ℤ) ℕᵒᵖ).inverse

/-- Apply a transformation on complexes to all levels of a strict tower.
Source: Stacks Tag 0941, strict tower interpretation
(blueprint: lem-sfb-kflat-augmented-roos-comparison). -/
def towerMap {F G : CochainComplex M ℤ ⥤ CochainComplex M ℤ} (α : F ⟶ G) :
    tower F ⟶ tower G :=
  Functor.whiskerRight
    (Functor.whiskerLeft HomologicalComplex.complexOfFunctorsToFunctorToComplex
      ((Functor.whiskeringRight ℕᵒᵖ _ _).map α))
    (HomologicalComplex.functorEquivalence M (.up ℤ) ℕᵒᵖ).inverse

variable [HasCountableProducts M] [HasLimitsOfShape ℕᵒᵖ M]
  [HasDerivedCategory.{w} M] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ M)]

/-- Every resolution gives the ordinary-limit and signed Roos representative of beta.
Source: Stacks Tags 0941 and 06YM; the explicit signed refinement in proof steps 2, 5--7
(blueprint: lem-sfb-kflat-augmented-roos-comparison).
The quantifiers over resolutions and their normalized identifications enforce independence
of all choices. The two summand equations specify the whole chain map, not its projections
onto the tower levels alone. -/
def ResolutionFormula
    (F : CochainComplex M ℤ ⥤ CochainComplex M ℤ)
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ M) ⥤ DerivedCategory.{w} M)
    (η : roosLimitFunctor ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF)
    (T : DerivedCategory.{w} M ⥤ DerivedCategory.{w} M)
    (e : DerivedCategory.Q.{w} ⋙ T ≅ F ⋙ DerivedCategory.Q.{w})
    (β : DerivedCategory.Q.{w} ⋙ RF ⋙ T ⟶ tower F ⋙ DerivedCategory.Q.{w} ⋙ RF)
    (coordinates : ∀ (I J : CochainComplex (ℕᵒᵖ ⥤ M) ℤ),
      (F.obj (roosP I) ⟶ roosP J) → (F.obj (roosF.obj I) ⟶ roosF.obj J) → Prop) :
    Prop :=
  ∀ (X I J : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) (s : X ⟶ I) (q : (tower F).obj I ⟶ J),
    QuasiIso s → I.IsKInjective → (∀ k : ℤ, Injective (I.X k)) →
    QuasiIso q → J.IsKInjective → (∀ k : ℤ, Injective (J.X k)) →
    ∃ (dI : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅
        RF.obj (DerivedCategory.Q.{w}.obj X))
      (dJ : DerivedCategory.Q.{w}.obj (limit J.asFunctor) ≅
        RF.obj (DerivedCategory.Q.{w}.obj ((tower F).obj X)))
      (b : F.obj (roosP I) ⟶ roosP J)
      (θ : F.obj (limit I.asFunctor) ⟶ limit J.asFunctor)
      (ψ : F.obj (roosF.obj I) ⟶ roosF.obj J),
      dI.hom ≫ RF.map (DerivedCategory.Q.{w}.map s) = η.app I ∧
      dJ.hom ≫ RF.map (DerivedCategory.Q.{w}.map ((tower F).map s ≫ q)) = η.app J ∧
      (∀ n : ℕ, b ≫ Pi.π (fun k : ℕ ↦ J.asFunctor.obj (.op k)) n =
        F.map (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (.op k)) n) ≫
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (.op n)) ∧
      (∀ n : ℕ, θ ≫ limit.π J.asFunctor (.op n) =
        F.map (limit.π I.asFunctor (.op n)) ≫
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (.op n)) ∧
      coordinates I J b ψ ∧
      F.map (roosU I) ≫ b = b ≫ roosU J ∧
      F.map (roosι I) ≫ ψ = θ ≫ roosι J ∧
      β.app X = T.map dI.inv ≫ e.hom.app (limit I.asFunctor) ≫
        DerivedCategory.Q.{w}.map θ ≫ dJ.hom ∧
      QuasiIso (roosι I) ∧ QuasiIso (roosι J) ∧
      ∃ (εI : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅
          DerivedCategory.Q.{w}.obj (roosF.obj I))
        (εJ : DerivedCategory.Q.{w}.obj (limit J.asFunctor) ≅
          DerivedCategory.Q.{w}.obj (roosF.obj J)),
        εI.hom = DerivedCategory.Q.{w}.map (roosι I) ∧
        εJ.hom = DerivedCategory.Q.{w}.map (roosι J) ∧
        β.app X = T.map (dI.inv ≫ εI.hom) ≫ e.hom.app (roosF.obj I) ≫
          DerivedCategory.Q.{w}.map ψ ≫ εJ.inv ≫ dJ.hom

/-- The two summand equations for a tensor comparison of normalized Roos fibres.
Source: Stacks Tags 06YM and 0941, explicit signed calculation in proof step 6
(blueprint: lem-sfb-kflat-augmented-roos-comparison).
Here the supplied F is the actual signed total tensor with A. In the library's (y,x)
coordinates the equations are y'=(-1)^p b(y), x'=b(x). In (x,-y) they are precisely
the node's (b(x),(-1)^p b(y)). -/
def SignedCoordinates [MonoidalCategory M] [MonoidalPreadditive M]
    (A : CochainComplex M ℤ)
    [∀ U : CochainComplex M ℤ,
      HomologicalComplex.HasMapBifunctor A U (curriedTensor M) (.up ℤ)]
    (I J : CochainComplex (ℕᵒᵖ ⥤ M) ℤ)
    (b : CochainComplex.mapBifunctor A (roosP I) (curriedTensor M) ⟶ roosP J)
    (ψ : CochainComplex.mapBifunctor A (roosF.obj I) (curriedTensor M) ⟶ roosF.obj J) :
    Prop :=
  ∀ (p q n : ℤ) (hpq : p + q = n),
    (CochainComplex.ιMapBifunctor A (roosF.obj I) (curriedTensor M)
        p (q + 1) (n + 1) (by omega) ≫ ψ.f (n + 1) ≫
          (roosχ J n).hom ≫ biprod.snd =
      A.X p ◁ ((roosχ I q).hom ≫ biprod.snd) ≫
        CochainComplex.ιMapBifunctor A (roosP I) (curriedTensor M)
          p (q + 1) (n + 1) (by omega) ≫ b.f (n + 1)) ∧
    (CochainComplex.ιMapBifunctor A (roosF.obj I) (curriedTensor M)
        p (q + 1) (n + 1) (by omega) ≫ ψ.f (n + 1) ≫
          (roosχ J n).hom ≫ biprod.fst =
      p.negOnePow • (A.X p ◁ ((roosχ I q).hom ≫ biprod.fst) ≫
        CochainComplex.ιMapBifunctor A (roosP I) (curriedTensor M) p q n hpq ≫ b.f n))

/-- The complete comparison assertion, packaged as a transparent predicate.
Source: Stacks Tags 0941, 06YM, 06YS and 070I; blueprint det-lem-int-tensor-product
(blueprint: lem-sfb-kflat-augmented-roos-comparison).
The functors B, the K-flat predicate and the coordinate predicate are specialized below
to the existing sheaf total tensor, K-flatness and signed summand formulas. No arbitrary
comparison map is a hypothesis. Naturality in both arguments, inversion of their
quasi-isomorphisms, and equality of the full augmentation arrows are conclusions. -/
structure ComparisonData
    (B : CochainComplex M ℤ ⥤ CochainComplex M ℤ ⥤ CochainComplex M ℤ)
    (flat : CochainComplex M ℤ → Prop)
    (coordinates : ∀ (A : CochainComplex M ℤ) (I J : CochainComplex (ℕᵒᵖ ⥤ M) ℤ),
      ((B.obj A).obj (roosP I) ⟶ roosP J) →
        ((B.obj A).obj (roosF.obj I) ⟶ roosF.obj J) → Prop)
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ M) ⥤ DerivedCategory.{w} M)
    (η : roosLimitFunctor ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF) :
    Type _ where
  products : HasCountableProducts (DerivedCategory.{w} M)
  T : {A : CochainComplex M ℤ // flat A} →
      DerivedCategory.{w} M ⥤ DerivedCategory.{w} M
  e : ∀ K : {A : CochainComplex M ℤ // flat A},
      DerivedCategory.Q.{w} ⋙ T K ≅ B.obj K.val ⋙ DerivedCategory.Q.{w}
  β : ∀ K : {A : CochainComplex M ℤ // flat A},
      DerivedCategory.Q.{w} ⋙ RF ⋙ T K ⟶
        tower (B.obj K.val) ⋙ DerivedCategory.Q.{w} ⋙ RF
  μ : ∀ (K L : {A : CochainComplex M ℤ // flat A}) (_α : K.val ⟶ L.val),
      T K ⟶ T L
  exactness :
    (∀ K : {A : CochainComplex M ℤ // flat A},
      ∃ _cs : (T K).CommShift ℤ, (T K).IsTriangulated)
  resolution :
    (∀ K : {A : CochainComplex M ℤ // flat A},
      ResolutionFormula (B.obj K.val) RF η (T K) (e K) (β K) (coordinates K.val))
  tensorMap_fac :
    (∀ (K L : {A : CochainComplex M ℤ // flat A}) (α : K.val ⟶ L.val)
        (U : CochainComplex M ℤ),
      (μ K L α).app (DerivedCategory.Q.{w}.obj U) ≫ (e L).hom.app U =
        (e K).hom.app U ≫ DerivedCategory.Q.{w}.map ((B.map α).app U))
  naturality :
    (∀ (K L : {A : CochainComplex M ℤ // flat A}) (α : K.val ⟶ L.val)
        (X : CochainComplex (ℕᵒᵖ ⥤ M) ℤ),
      (μ K L α).app (RF.obj (DerivedCategory.Q.{w}.obj X)) ≫ (β L).app X =
        (β K).app X ≫ RF.map (DerivedCategory.Q.{w}.map ((towerMap (B.map α)).app X)))
  tensorMap_isIso :
    (∀ (K L : {A : CochainComplex M ℤ // flat A}) (α : K.val ⟶ L.val),
      QuasiIso α → IsIso (μ K L α))
  tower_invariance :
    (∀ (K : {A : CochainComplex M ℤ // flat A})
        (X Y : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) (f : X ⟶ Y),
      QuasiIso f → IsIso ((T K).map (RF.map (DerivedCategory.Q.{w}.map f))) ∧
        IsIso (RF.map (DerivedCategory.Q.{w}.map ((tower (B.obj K.val)).map f))))
  product_isIso :
    let := products
    (∀ (K : {A : CochainComplex M ℤ // flat A})
        (X : CochainComplex (ℕᵒᵖ ⥤ M) ℤ),
      IsIso (piComparison (T K)
        (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (X.asFunctor.obj (.op n)))) →
          IsIso ((β K).app X))
  augmentation :
    (∀ (K : {A : CochainComplex M ℤ // flat A})
        (X : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) (γ : Cone X.asFunctor),
      (T K).map (DerivedCategory.Q.{w}.map (limit.lift X.asFunctor γ) ≫ η.app X) ≫
          (β K).app X =
        (e K).hom.app γ.pt ≫
          DerivedCategory.Q.{w}.map
            (limit.lift ((tower (B.obj K.val)).obj X).asFunctor
              ((B.obj K.val).mapCone γ)) ≫ η.app ((tower (B.obj K.val)).obj X))


/-- The unchanged comparison conditions, with their witnesses packaged in a record. -/
def ComparisonFormulas
    (B : CochainComplex M ℤ ⥤ CochainComplex M ℤ ⥤ CochainComplex M ℤ)
    (flat : CochainComplex M ℤ → Prop)
    (coordinates : ∀ (A : CochainComplex M ℤ) (I J : CochainComplex (ℕᵒᵖ ⥤ M) ℤ),
      ((B.obj A).obj (roosP I) ⟶ roosP J) →
        ((B.obj A).obj (roosF.obj I) ⟶ roosF.obj J) → Prop)
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ M) ⥤ DerivedCategory.{w} M)
    (η : roosLimitFunctor ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF) :
    Prop :=
  Nonempty (ComparisonData B flat coordinates RF η)

/-- Record packaging is equivalent to the original existential comparison formula.
Source: the comparison interface (blueprint: def-sfb-kflat-augmented-roos-interface).
Proof: pack or unpack the five witnesses and their conjunction of properties. -/
theorem comparisonFormulas_iff
    (B : CochainComplex M ℤ ⥤ CochainComplex M ℤ ⥤ CochainComplex M ℤ)
    (flat : CochainComplex M ℤ → Prop)
    (coordinates : ∀ (A : CochainComplex M ℤ) (I J : CochainComplex (ℕᵒᵖ ⥤ M) ℤ),
      ((B.obj A).obj (roosP I) ⟶ roosP J) →
        ((B.obj A).obj (roosF.obj I) ⟶ roosF.obj J) → Prop)
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ M) ⥤ DerivedCategory.{w} M)
    (η : roosLimitFunctor ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF) :
    ComparisonFormulas B flat coordinates RF η ↔
  ∃ (_products : HasCountableProducts (DerivedCategory.{w} M))
    (T : {A : CochainComplex M ℤ // flat A} →
      DerivedCategory.{w} M ⥤ DerivedCategory.{w} M)
    (e : ∀ K : {A : CochainComplex M ℤ // flat A},
      DerivedCategory.Q.{w} ⋙ T K ≅ B.obj K.val ⋙ DerivedCategory.Q.{w})
    (β : ∀ K : {A : CochainComplex M ℤ // flat A},
      DerivedCategory.Q.{w} ⋙ RF ⋙ T K ⟶
        tower (B.obj K.val) ⋙ DerivedCategory.Q.{w} ⋙ RF)
    (μ : ∀ (K L : {A : CochainComplex M ℤ // flat A}) (_α : K.val ⟶ L.val),
      T K ⟶ T L),
    (∀ K : {A : CochainComplex M ℤ // flat A},
      ∃ _cs : (T K).CommShift ℤ, (T K).IsTriangulated) ∧
    (∀ K : {A : CochainComplex M ℤ // flat A},
      ResolutionFormula (B.obj K.val) RF η (T K) (e K) (β K) (coordinates K.val)) ∧
    (∀ (K L : {A : CochainComplex M ℤ // flat A}) (α : K.val ⟶ L.val)
        (U : CochainComplex M ℤ),
      (μ K L α).app (DerivedCategory.Q.{w}.obj U) ≫ (e L).hom.app U =
        (e K).hom.app U ≫ DerivedCategory.Q.{w}.map ((B.map α).app U)) ∧
    (∀ (K L : {A : CochainComplex M ℤ // flat A}) (α : K.val ⟶ L.val)
        (X : CochainComplex (ℕᵒᵖ ⥤ M) ℤ),
      (μ K L α).app (RF.obj (DerivedCategory.Q.{w}.obj X)) ≫ (β L).app X =
        (β K).app X ≫ RF.map (DerivedCategory.Q.{w}.map ((towerMap (B.map α)).app X))) ∧
    (∀ (K L : {A : CochainComplex M ℤ // flat A}) (α : K.val ⟶ L.val),
      QuasiIso α → IsIso (μ K L α)) ∧
    (∀ (K : {A : CochainComplex M ℤ // flat A})
        (X Y : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) (f : X ⟶ Y),
      QuasiIso f → IsIso ((T K).map (RF.map (DerivedCategory.Q.{w}.map f))) ∧
        IsIso (RF.map (DerivedCategory.Q.{w}.map ((tower (B.obj K.val)).map f)))) ∧
    (∀ (K : {A : CochainComplex M ℤ // flat A})
        (X : CochainComplex (ℕᵒᵖ ⥤ M) ℤ),
      IsIso (piComparison (T K)
        (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (X.asFunctor.obj (.op n)))) →
          IsIso ((β K).app X)) ∧
    (∀ (K : {A : CochainComplex M ℤ // flat A})
        (X : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) (γ : Cone X.asFunctor),
      (T K).map (DerivedCategory.Q.{w}.map (limit.lift X.asFunctor γ) ≫ η.app X) ≫
          (β K).app X =
        (e K).hom.app γ.pt ≫
          DerivedCategory.Q.{w}.map
            (limit.lift ((tower (B.obj K.val)).obj X).asFunctor
              ((B.obj K.val).mapCone γ)) ≫ η.app ((tower (B.obj K.val)).obj X))
 := by
  constructor
  · rintro ⟨d⟩
    exact ⟨d.products, d.T, d.e, d.β, d.μ, d.exactness, d.resolution,
      d.tensorMap_fac, d.naturality, d.tensorMap_isIso, d.tower_invariance,
      d.product_isIso, d.augmentation⟩
  · rintro ⟨products, T, e, β, μ, h0, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨⟨products, T, e, β, μ, h0, h1, h2, h3, h4, h5, h6, h7⟩⟩

end CategoryTheory.KFlatAugmentedRoos
