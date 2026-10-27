# CategoryTheory.KFlatAugmentedRoos comparison interface relocation

## Reason

The canonical derived comparison, tensor descent, signed fibre calculation and
product criterion share the original comparison predicates and tower construction.
Move the interface into KFlatAugmentedRoosDefinitions and re-export that module
from the item. Package the existential comparison witnesses in ComparisonData to
avoid repeated elaboration of their dependent types. The proved
comparisonFormulas_iff is exactly the original existential formula. This avoids import cycles between the proved helper
results and their assembly. No target or existing declaration signature changes. The four smaller definition
bodies stay verbatim; ComparisonFormulas has equivalent record packaging. No source-library module is edited.

## Old

The following declarations were in
lean/Sheaf/CategoryTheory/KFlatAugmentedRoosComparison.lean:

```lean
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
def ComparisonFormulas
    (B : CochainComplex M ℤ ⥤ CochainComplex M ℤ ⥤ CochainComplex M ℤ)
    (flat : CochainComplex M ℤ → Prop)
    (coordinates : ∀ (A : CochainComplex M ℤ) (I J : CochainComplex (ℕᵒᵖ ⥤ M) ℤ),
      ((B.obj A).obj (roosP I) ⟶ roosP J) →
        ((B.obj A).obj (roosF.obj I) ⟶ roosF.obj J) → Prop)
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ M) ⥤ DerivedCategory.{w} M)
    (η : roosLimitFunctor ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF) :
    Prop :=
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

end CategoryTheory.KFlatAugmentedRoos
```

## New

The declarations are in
lean/Sheaf/CategoryTheory/KFlatAugmentedRoosDefinitions.lean. The item exports them with:

```lean
public import Sheaf.CategoryTheory.KFlatAugmentedRoosDefinitions
```

The first four bodies are unchanged. The final body is:

```lean
  Nonempty (ComparisonData B flat coordinates RF η)
```

ComparisonData has fields products, T, e, β and μ of exactly the old existential
types, and eight proof fields equal to the original eight conjuncts. Its constructor and
projections prove comparisonFormulas_iff by packing and unpacking the witnesses.
The complete new structure and equivalence are in the interface module.
Four original public imports are preserved through this public import.
The unused RingedStrictTowerHomotopyLimitIndependentCoefficients public import
is removed: the proof derives the necessary limit unit directly from its supplied
universal right-derived property. No original signature mentions a declaration
owned by that removed import.
The KInjective import is public in the interface because the existing resolution
predicate mentions K-injectivity in its signature. The main theorem has its
original signature and a complete proof.

## Users

The downstream and named-use checks were run for tower, towerMap,
ResolutionFormula, SignedCoordinates and ComparisonFormulas. There are no current
Lean importers and every current named use is in the item itself. Unfinished DAG
parents still depend on the item and are retained.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.KFlatAugmentedRoosComparison | D6 | Re-exports identical definitions and assembles the proof. |
| Sheaf.CategoryTheory.KFlatRoosDerivedComparison | D6, new | Uses tower and towerMap for the universal derived comparison. |
| Sheaf.CategoryTheory.KFlatRoosTensorDescent | D6, new | Uses the tower construction for localization. |
| Sheaf.CategoryTheory.KFlatRoosSignedMap | D6, new | Proves the existing SignedCoordinates predicate. |
| Sheaf.CategoryTheory.KFlatRoosProductCriterion | D6, new | Uses the strict comparison on resolved towers. |

## Status

landed 20261024T184854-L-3238630 2026-10-24 (merge of deliver/D6/Sheaf.CategoryTheory.KFlatAugmentedRoosComparison)
