/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.KummerCechDescent
public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import Sheaf.Paper.RootTowerPunctureInvariance
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Normalized coherent comparison data

Source: main-20261015, direct-image proof (3), augmented root-nerve calculation.
(blueprint: def-sfb-normalized-kummer-comparison).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Alternating cofaces on the explicit diagram category, avoiding a second category
instance on the definitional wrapper CosimplicialObject.
Source: direct-image proof (3), signed nerve complex
(blueprint: def-sfb-normalized-kummer-comparison). -/
def kummerAlternating (S : Scheme.{u}) :
    (SimplexCategory ⥤ KummerModules Λ S) ⥤ CochainComplex (KummerModules Λ S) ℕ where
  obj K := AlgebraicTopology.AlternatingCofaceMapComplex.obj K
  map f := AlgebraicTopology.AlternatingCofaceMapComplex.map f

/-- The explicit alternating functor preserves addition.
Source: direct-image proof (3), coherent signed total
(blueprint: def-sfb-normalized-kummer-comparison).
Proof: its map in degree n is the component at simplex n. Natural transformation
addition is componentwise, so the component is the sum of the two components. -/
theorem kummerAlternating_additive (S : Scheme.{u}) :
    (kummerAlternating Λ S).Additive := by
  sorry
attribute [instance] kummerAlternating_additive

/-- The actual Cech cochain functor, retaining all simplicial operators.
Source: direct-image proof (3), compatible resolutions
(blueprint: def-sfb-normalized-kummer-comparison). -/
def kummerCochains {T W Y S : Scheme.{u}}
    (a : W ⟶ Y) (s : S ⟶ Y) (v : T ⟶ W) :
    KummerModules Λ W ⥤ CochainComplex (KummerModules Λ S) ℕ :=
  cechImage Λ a s v ⋙ kummerAlternating Λ S

/-- Cochains are additive because every simplex functor is additive.
Source: direct-image proof (3), compatible resolutions
(blueprint: def-sfb-normalized-kummer-comparison).

Proof: the alternating-coface construction retains morphisms termwise. The
Cech functor is additive termwise, so the induced chain maps preserve sums. -/
theorem kummerCochains_additive {T W Y S : Scheme.{u}}
    (a : W ⟶ Y) (s : S ⟶ Y) (v : T ⟶ W) :
    (kummerCochains Λ a s v).Additive := by
  sorry
attribute [instance] kummerCochains_additive

/-- The actual finite-diagonal total of a coherent nerve resolution.
Source: direct-image proof (3), compatible first-quadrant total
(blueprint: def-sfb-normalized-kummer-comparison). -/
def kummerDiagramTotal (S : Scheme.{u}) :
    CochainComplex (SimplexCategory ⥤ KummerModules Λ S) ℕ ⥤
      CochainComplex (KummerModules Λ S) ℕ :=
  (kummerAlternating Λ S).mapHomologicalComplex (.up ℕ) ⋙
    HomologicalComplex₂.flipFunctor _ (.up ℕ) (.up ℕ) ⋙
    HomologicalComplex₂.totalFunctor _ (.up ℕ) (.up ℕ) (.up ℕ)

/-- The compatible first-quadrant double complex: Cech degree first.
Source: direct-image proof (3), finite diagonal total
(blueprint: def-sfb-normalized-kummer-comparison). -/
def kummerBicomplex {T W Y S : Scheme.{u}}
    (a : W ⟶ Y) (s : S ⟶ Y) (v : T ⟶ W)
    (I : CochainComplex (KummerModules Λ W) ℕ) :
    HomologicalComplex₂ (KummerModules Λ S) (.up ℕ) (.up ℕ) :=
  HomologicalComplex₂.flip
    (((kummerAlternating Λ S).mapHomologicalComplex (.up ℕ)).obj
      (kummerCechResolution Λ a s v I))

/-- The finite diagonal total has sign d_Cech + (-1)^n d_resolution.
Source: direct-image proof (3), coherent total
(blueprint: def-sfb-normalized-kummer-comparison). -/
def kummerTotal {T W Y S : Scheme.{u}}
    (a : W ⟶ Y) (s : S ⟶ Y) (v : T ⟶ W)
    (I : CochainComplex (KummerModules Λ W) ℕ) :
    CochainComplex (KummerModules Λ S) ℕ :=
  (kummerDiagramTotal Λ S).obj (kummerCechResolution Λ a s v I)

/-- The cochain term is the corresponding actual nerve term.
Source: direct-image proof (3), alternating cofaces
(blueprint: def-sfb-normalized-kummer-comparison).

Proof: the alternating-coface construction leaves objects unchanged in each degree.
The Cech image evaluates the section functor at the actual augmented nerve projection;
expanding functor composition and flip gives precisely cechImageTerm. -/
theorem kummerCochains_term {T W Y S : Scheme.{u}}
    (a : W ⟶ Y) (s : S ⟶ Y) (v : T ⟶ W)
    (L : KummerModules Λ W) (n : ℕ) :
    cechImageTerm Λ a s v L (.mk n) = ((kummerCochains Λ a s v).obj L).X n := by
  sorry

/-- The actual augmentation is inserted into Cech degree zero in each resolution degree.
Source: direct-image proof (3), restriction of sections and the adjunction counit
(blueprint: def-sfb-normalized-kummer-comparison). -/
def IsKummerAugmentation {T W Y S : Scheme.{u}}
    (a : W ⟶ Y) (s : S ⟶ Y) (v : T ⟶ W)
    (I : CochainComplex (KummerModules Λ W) ℕ)
    (b : ((lowerStar Λ a ⋙ upperStar Λ s).mapHomologicalComplex (.up ℕ)).obj I ⟶
      kummerTotal Λ a s v I) : Prop :=
  ∀ q : ℕ, b.f q = cechAugmentationComponent Λ a s v (I.X q) (.mk 0) ≫
    eqToHom (kummerCochains_term Λ a s v (I.X q) 0) ≫
      (kummerBicomplex Λ a s v I).ιTotal (.up ℕ) 0 q q (zero_add q)

/-- Computation of the ordinary right derived image by a nonnegative injective resolution.
Source: direct-image proof (3), normalized derived localization
(blueprint: def-sfb-normalized-kummer-comparison). -/
def kummerResolutionComparison {W Y S : Scheme.{u}} (a : W ⟶ Y) (s : S ⟶ Y)
    {L : KummerModules Λ W} (I : InjectiveResolution L) :
    (upperStar Λ s).mapDerivedCategory.obj
        ((moduleObjectDerivedPushforward Λ a).obj
          ((DerivedCategory.singleFunctor _ 0).obj L)) ≅
      DerivedCategory.Q.obj
        ((((lowerStar Λ a ⋙ upperStar Λ s).mapHomologicalComplex (.up ℕ)).obj
          I.cocomplex).extend ComplexShape.embeddingUpNat) := by
  letI : I.cochainComplex.IsKInjective := by
    dsimp only [InjectiveResolution.cochainComplex]
    infer_instance
  exact (upperStar Λ s).mapDerivedCategory.mapIso
      ((lowerStar Λ a).rightDerivedFunctor.mapIso
          (asIso (DerivedCategory.Q.map I.ι')) ≪≫
        (lowerStar Λ a).rightDerivedFunctorObjQIso I.cochainComplex) ≪≫
    (upperStar Λ s).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso
      (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat
        (lowerStar Λ a ⋙ upperStar Λ s))

end AlgebraicGeometry.ProEtale.CondensedRing
