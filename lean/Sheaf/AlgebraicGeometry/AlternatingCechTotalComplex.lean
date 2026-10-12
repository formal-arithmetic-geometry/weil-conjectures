/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z2
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCechComparison
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Sheaf.Topology.RingedSpaceModuleCohomology

/-! # Alternating Čech total complexes on finite open families

Source: Stacks, Cohomology, Section on Čech cohomology of unbounded complexes,
equation-global-sections-to-alternating-cech and lemma-alternating-cech-complex-complex
(blueprint: def-sc-alternating-cech-total-complex).

Čech degree is first. The total differential is d₁ + (-1)^p d₂.
All data are explicit; only identities needed by the constructions are postponed.

## Main definitions

- `alternatingCechComplexFunctor`: increasing-tuple cochains and signed face restrictions.
- `alternatingCechDoubleFunctor`: the double complex with Čech degree first.
- `alternatingCechTotalFunctor`: direct-sum totalization, including unbounded coefficients.
- `alternatingCechAugmentation`: restriction into Čech degree zero.
- `IsAlternatingCechDerivedComparison`: the canonical-map equation on K-injectives.
-/

@[expose] public section

universe u w v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

noncomputable section

variable {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)

/-- The intersection belonging to an increasing tuple.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechIntersection {p : ℕ} (t : Fin (p + 1) ↪o Fin r) : X.Opens :=
  ⨅ k, U (t k)

/-- Deleting one entry enlarges the intersection.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex).
Proof: Each factor of the face intersection is a factor of the full intersection; apply the
infimum universal property. -/
theorem alternatingCechIntersection_face_le (p : ℕ)
    (t : Fin (p + 2) ↪o Fin r) (j : Fin (p + 2)) :
    alternatingCechIntersection U t ≤
      alternatingCechIntersection U ((Fin.succAboveOrderEmb j).trans t) := by
  sorry

variable
  (G : X.Opensᵒᵖ ⥤ ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))

/-- Products of sections over strictly increasing tuples.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechTerms (p : ℕ) :
    ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  ModuleCat.of _ (∀ t : Fin (p + 1) ↪o Fin r,
    G.obj (op (alternatingCechIntersection U t)))

/-- The signed sum of face restrictions; linear maps specify its actual data.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechDifferential (p : ℕ) :
    alternatingCechTerms U G p ⟶ alternatingCechTerms U G (p + 1) :=
  ModuleCat.ofHom (LinearMap.pi fun t ↦
    ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
      (G.map (homOfLE (alternatingCechIntersection_face_le U p t j)).op).hom.comp
        (LinearMap.proj ((Fin.succAboveOrderEmb j).trans t)))

/-- The alternating face differential squares to zero.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex).
Proof: In the double sum, pair the two orders of deleting each pair of indices. The
restriction composites agree by presheaf functoriality; their face signs are opposite. -/
theorem alternatingCechDifferential_square (p : ℕ) :
    alternatingCechDifferential U G p ≫ alternatingCechDifferential U G (p + 1) = 0 := by
  sorry

/-- The nonnegative alternating Čech complex of a presheaf of global-ring modules.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechComplex :
    CochainComplex (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ℕ :=
  CochainComplex.of (alternatingCechTerms U G) (alternatingCechDifferential U G)
    (alternatingCechDifferential_square U G)

variable {G}
  {H K : X.Opensᵒᵖ ⥤ ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))}

/-- A morphism of presheaves acts componentwise on cochains.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechTermsMap (g : G ⟶ H) (p : ℕ) :
    alternatingCechTerms U G p ⟶ alternatingCechTerms U H p :=
  ModuleCat.ofHom (LinearMap.pi fun t ↦
    (g.app (op (alternatingCechIntersection U t))).hom.comp (LinearMap.proj t))

/-- Componentwise maps commute with the signed face differential.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex).
Proof: Naturality of g commutes with every face restriction. Apply it to each summand
of the finite signed sum and use linearity. -/
theorem alternatingCechTermsMap_comm (g : G ⟶ H) (p : ℕ) :
    alternatingCechTermsMap U g p ≫ (alternatingCechComplex U H).d p (p + 1) =
      (alternatingCechComplex U G).d p (p + 1) ≫ alternatingCechTermsMap U g (p + 1) := by
  sorry

/-- The induced cochain map.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechComplexMap (g : G ⟶ H) :
    alternatingCechComplex U G ⟶ alternatingCechComplex U H :=
  CochainComplex.ofHom (fun p ↦ alternatingCechTermsMap U g p)
    (alternatingCechTermsMap_comm U g)

/-- Identity morphisms act as identity cochain maps.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex).
Proof: Evaluate in each degree and tuple; the component is the identity linear map. -/
theorem alternatingCechComplexMap_id :
    alternatingCechComplexMap U (𝟙 G) = 𝟙 (alternatingCechComplex U G) := by
  sorry

/-- Composition is componentwise composition.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex).
Proof: Evaluate in each degree and tuple; natural transformation composition is
componentwise composition, so both sides apply g and then h. -/
theorem alternatingCechComplexMap_comp (g : G ⟶ H) (h : H ⟶ K) :
    alternatingCechComplexMap U (g ≫ h) =
      alternatingCechComplexMap U g ≫ alternatingCechComplexMap U h := by
  sorry

/-- Alternating Čech cochains as a functor of the presheaf.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechComplexFunctor :
    (X.Opensᵒᵖ ⥤ ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ⥤
      CochainComplex (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ℕ where
  obj := alternatingCechComplex U
  map := alternatingCechComplexMap U
  map_id := fun G ↦ alternatingCechComplexMap_id U (G := G)
  map_comp := fun g h ↦ alternatingCechComplexMap_comp U g h

/-- The alternating Čech functor is additive.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex).
Proof: Addition of natural transformations and cochain maps is componentwise. The
explicit tuple maps preserve addition in every degree. -/
theorem alternatingCechComplexFunctor_additive :
    (alternatingCechComplexFunctor U).Additive := by
  sorry

attribute [instance] alternatingCechComplexFunctor_additive

/-- The presheaf of Γ(X,O_X)-modules underlying an O_X-module.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechModulePresheaf :
    SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      (X.Opensᵒᵖ ⥤ ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) :=
  SheafOfModules.forget (moduleRings X.toRingedSpace) ⋙
    PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op

/-- The integer Čech complex, extended by zero in negative Čech degree.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechModuleFunctor :
    SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      CochainComplex (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ℤ :=
  alternatingCechModulePresheaf (X := X) ⋙ alternatingCechComplexFunctor U ⋙
    ComplexShape.embeddingUpNat.extendFunctor _

/-- The integer module Čech functor is additive.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex).
Proof: Forgetting to global-ring presheaves is additive, as are the tuple maps and
Mathlib extension by zero. The composite is therefore additive. -/
theorem alternatingCechModuleFunctor_additive :
    (alternatingCechModuleFunctor U).Additive := by
  sorry

attribute [instance] alternatingCechModuleFunctor_additive

/-- The double complex functor with Čech degree first and coefficient degree second.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechDoubleFunctor :
    CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ ⥤
      HomologicalComplex₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (alternatingCechModuleFunctor U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.flipFunctor _ (ComplexShape.up ℤ) (ComplexShape.up ℤ)

/-- The total complex functor, with differential d₁ + (-1)^p d₂.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechTotalFunctor :
    CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ ⥤
      CochainComplex (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ℤ :=
  alternatingCechDoubleFunctor U ⋙
    HomologicalComplex₂.totalFunctor _ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)

/-- Alternating Čech totalization is additive in the coefficient complex.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex).
Proof: coefficient maps act linearly on every tuple. Mapping complexes and flipping
preserve addition componentwise. The coproduct universal property of totalization
then shows that total.map preserves addition in every degree. -/
theorem alternatingCechTotalFunctor_additive :
    (alternatingCechTotalFunctor U).Additive := by
  sorry

attribute [instance] alternatingCechTotalFunctor_additive

variable (F : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)

/-- Restriction from the top open set to the zero Čech row of a presheaf.
Source: Stacks, Cohomology, equation-global-sections-to-alternating-cech
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechPresheafZero
    (P : X.Opensᵒᵖ ⥤ ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) :
    P.obj (op ⊤) ⟶ (alternatingCechComplex U P).X 0 :=
  ModuleCat.ofHom (LinearMap.pi fun t : Fin 1 ↪o Fin r ↦
    (P.map (homOfLE (le_top (a := alternatingCechIntersection U t))).op).hom)

/-- Restriction of global sections into the extended zero Čech row.
Source: Stacks, Cohomology, equation-global-sections-to-alternating-cech and
lemma-alternating-cech-complex-complex (blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechZero (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M ⟶
      ((alternatingCechModuleFunctor U).obj M).X 0 :=
  (ModuleCat.restrictScalarsId'App
      ((moduleRings X.toRingedSpace).obj.map (isTerminalTop.op.to (op ⊤))).hom
      (Scheme.Modules.moduleCech_top_restriction X) (M.val.obj (op ⊤))).inv ≫
    alternatingCechPresheafZero U ((alternatingCechModulePresheaf (X := X)).obj M) ≫
    ((alternatingCechComplex U ((alternatingCechModulePresheaf (X := X)).obj M)).extendXIso
      ComplexShape.embeddingUpNat (i := 0) rfl).inv

/-- The augmentation component is restriction in Čech degree zero, included in total degree n.
Source: Stacks, Cohomology, equation-global-sections-to-alternating-cech and
lemma-alternating-cech-complex-complex (blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechAugmentationComponent (n : ℤ) :
    (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj F).X n ⟶ ((alternatingCechTotalFunctor U).obj F).X n :=
  alternatingCechZero U (F.X n) ≫
    ((alternatingCechDoubleFunctor U).obj F).ιTotal (ComplexShape.up ℤ) 0 n n
      (Int.zero_add n)

/-- The restriction components commute with the total differential.
Source: Stacks, Cohomology, equation-global-sections-to-alternating-cech and
lemma-alternating-cech-complex-complex (blueprint: def-sc-alternating-cech-total-complex).
Proof: Restrictions commute with d_F. The signed face differential of global-section
restrictions is zero by cancellation on each pair of opens. In Čech degree zero the
vertical sign is +1. Other components of the augmentation vanish. -/
theorem alternatingCechAugmentation_comm (n m : ℤ) :
    alternatingCechAugmentationComponent U F n ≫
        ((alternatingCechTotalFunctor U).obj F).d n m =
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj F).d n m ≫
          alternatingCechAugmentationComponent U F m := by
  sorry

/-- The explicit section-to-total augmentation cochain map.
Source: Stacks, Cohomology, equation-global-sections-to-alternating-cech and
lemma-alternating-cech-complex-complex (blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechAugmentationMap :
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj F ⟶ (alternatingCechTotalFunctor U).obj F where
  f := alternatingCechAugmentationComponent U F
  comm' := fun n m _ ↦ alternatingCechAugmentation_comm U F n m

/-- The augmentation is natural in the coefficient complex.
Source: Stacks, Cohomology, equation-global-sections-to-alternating-cech and
lemma-alternating-cech-complex-complex (blueprint: def-sc-alternating-cech-total-complex).
Proof: Evaluate in each total degree. Naturality of a module morphism commutes with
each restriction to a cover member, and total.map commutes with each summand inclusion.
There are no positive Čech-degree components in the augmentation. -/
theorem alternatingCechAugmentation_naturality
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (g : F ⟶ G) :
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g ≫ alternatingCechAugmentationMap U G =
        alternatingCechAugmentationMap U F ≫ (alternatingCechTotalFunctor U).map g := by
  sorry

/-- The section-to-total augmentation as a natural transformation.
Source: Stacks, Cohomology, equation-global-sections-to-alternating-cech and
lemma-alternating-cech-complex-complex (blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechAugmentation :
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ) ⟶ alternatingCechTotalFunctor U where
  app := alternatingCechAugmentationMap U
  naturality := fun F G g ↦ alternatingCechAugmentation_naturality U F G g

variable
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{v}
    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]

/-- The canonical comparison is characterized through every K-injective resolution.
This equation specifies the roof without choosing any unproved data.
The resolution need not have injective terms: compare it with one that does. The
comparison is a homotopy equivalence, preserved by sections and by the explicit
Čech totalization, so naturality transports the equation to this resolution.
Source: Stacks, Cohomology, equation-global-sections-to-alternating-cech and
lemma-alternating-cech-complex-complex (blueprint: def-sc-alternating-cech-total-complex). -/
def IsAlternatingCechDerivedComparison
    (β : DerivedCategory.Q.obj ((alternatingCechTotalFunctor U).obj F) ⟶
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj
        (DerivedCategory.Q.obj F)) : Prop :=
  ∀ (J : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [J.IsKInjective] (i : F ⟶ J) [QuasiIso i],
    β ≫ (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map
        (DerivedCategory.Q.map i) ≫
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorObjQIso J).hom ≫
      DerivedCategory.Q.map ((alternatingCechAugmentation U).app J) =
        DerivedCategory.Q.map ((alternatingCechTotalFunctor U).map i)

end
end AlgebraicGeometry
