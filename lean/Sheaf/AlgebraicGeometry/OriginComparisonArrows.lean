/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
public import Sheaf.SixFunctors.OpenTensorNormalizationData
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.AlgebraicGeometry.Sites.ArtinVanishing.ProjectiveLine

/-!
# The origin class and the positive projective Chern class

Source: main-20261015 sec-smooth-purity/sk-prop-an,
thm-pur-rank-one-thom.proof.md, Step 2; master sk-prop-an, Step 5(d).
(blueprint: def-pur-origin-comparison-arrows).

The library's `infinityChart` is [1:t], namely D(x₀); its `infinity` is [1:0].
The definitions retain the actual localized counits and constant-section unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace

section
universe vC vD wC wD oC oD
variable {C : Type oC} {D : Type oD} [Category.{vC} C] [Category.{vD} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

/-- Realize a sheaf-level arrow through the canonical exact single-object comparison.
Source: Stacks 015F (blueprint: def-pur-origin-comparison-arrows). -/
@[irreducible]
def originExactSingleMap (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : C) (Y : D) (c : F.obj X ⟶ Y) :
    F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C 0).obj X) ⟶
      (DerivedCategory.singleFunctor D 0).obj Y :=
  (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫
    (DerivedCategory.singleFunctor D 0).map c

/-- Shift the same termwise-localized arrow by two, with the actual shift comparison.
Source: Stacks 015F (blueprint: def-pur-origin-comparison-arrows). -/
@[irreducible]
def originExactShiftedMap (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : C) (Y : D) (c : F.obj X ⟶ Y) :
    F.mapDerivedCategory.obj (((DerivedCategory.singleFunctor C 0).obj X)⟦(2 : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor D 0).obj Y)⟦(2 : ℤ)⟧ :=
  (F.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
    (shiftFunctor _ (2 : ℤ)).map (originExactSingleMap F X Y c)
end

section
universe oC oD oE vC vD vE
variable {C : Type oC} {D : Type oD} {E : Type oE}
  [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]

/-- The five actual-arrow equations for the origin comparison, with abstract categories
so that the concrete derived instances are shared. This includes both counit compatibility
and the section-one normalization, as well as the resulting compact-image equality.
Source: blueprint rank-one Thom, Step 2
(blueprint: def-pur-origin-comparison-arrows). -/
def originComparisonEquations (F : C ⥤ D) (G : D ⥤ E)
    {B K : C} {B' K' U : D} {R : E}
    (b : B ⟶ K) (b' : B' ⟶ K') (e : F.obj B ⟶ B') (epsilon : F.obj K ⟶ K')
    (unit : U ⟶ B') (chern : U ⟶ K') (eta : R ⟶ G.obj U)
    (lambda : R ≅ G.obj (F.obj B)) : Prop :=
  IsIso e ∧ F.map b ≫ epsilon = e ≫ b' ∧ unit ≫ b' = chern ∧
    lambda.hom ≫ G.map e = eta ≫ G.map unit ∧
    lambda.hom ≫ (F ⋙ G).map b ≫ G.map epsilon = eta ≫ G.map chern
end

/-- Exact extension by zero for D(x₀), with its ordinary module instances fixed once.
Source: Stacks 03S3, 015F (blueprint: def-pur-origin-comparison-arrows). -/
@[implicit_reducible]
def originOpenExtension (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    DerivedCategoryModule A (AffineSpace PUnit.{u + 1} S) ⥤
      DerivedCategoryModule A (ProjectiveLine S) :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} A)
    (ProjectiveLine.infinityChart S)).mapDerivedCategory

/-- Derived global sections with the existing ordinary module instances.
Source: Stacks 03FD (blueprint: def-pur-origin-comparison-arrows). -/
@[implicit_reducible]
def originSections (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    DerivedCategoryModule A T ⥤ DerivedCategory (ModuleCat.{u + 1} A) :=
  rightDerivedGlobalSections (ModuleCat.{u + 1} A) T

/-- The affine supported constant sheaf, using exact closed direct image.
Source: Stacks 03S3 (blueprint: def-pur-origin-comparison-arrows). -/
abbrev originAffineSheaf (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :=
  (lowerStar (ModuleCat.{u + 1} A) (AffineSpace.zeroSection PUnit.{u + 1} S)).obj
    (ordinaryFiniteConstant A S)

/-- The projective supported constant sheaf, using the same origin [1:0].
Source: Stacks 03S3 (blueprint: def-pur-origin-comparison-arrows). -/
abbrev originProjectiveSheaf (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :=
  (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine.infinity S)).obj
    (ordinaryFiniteConstant A S)

/-- The canonical restriction exchange, with identity on the closed point.
Source: Stacks 0A45 (blueprint: def-pur-origin-comparison-arrows). -/
@[irreducible]
def originRestrictionExchange (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :=
  supportedConstantExchange A (ProjectiveLine.infinity S)
    (AffineSpace.zeroSection PUnit.{u + 1} S) (ProjectiveLine.infinityChart S) (𝟙 S)
    ⟨Category.id_comp (ProjectiveLine.infinity S)⟩

/-- The sheaf counit transported by the canonical restriction comparison.
Source: Stacks 03S3 (blueprint: def-pur-origin-comparison-arrows). -/
@[irreducible]
def originSheafSupportCounit (A : Type (u + 1)) [CommRing A] (S : Scheme.{u})
    (r : (upperStar (ModuleCat.{u + 1} A) (ProjectiveLine.infinityChart S)).obj
      (originProjectiveSheaf A S) ≅ originAffineSheaf A S) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A)
      (ProjectiveLine.infinityChart S)).obj (originAffineSheaf A S) ⟶
        originProjectiveSheaf A S :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} A)
    (ProjectiveLine.infinityChart S)).map r.inv ≫
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
        (ProjectiveLine.infinityChart S)).counit.app (originProjectiveSheaf A S)

/-- The actual localized counit on the degree-zero supported sheaf. This is its
termwise realization, transported by the exact single-object comparison.
Source: Stacks 03S3, 015F (blueprint: def-pur-origin-comparison-arrows). -/
@[irreducible]
def originSupportCounit (A : Type (u + 1)) [CommRing A] (S : Scheme.{u})
    (r : (upperStar (ModuleCat.{u + 1} A) (ProjectiveLine.infinityChart S)).obj
      (originProjectiveSheaf A S) ≅ originAffineSheaf A S) :
    (originOpenExtension A S).obj
      ((DerivedCategory.singleFunctor _ 0).obj (originAffineSheaf A S)) ⟶
        (DerivedCategory.singleFunctor _ 0).obj (originProjectiveSheaf A S) :=
  originExactSingleMap (openImmersionLowerShriek (ModuleCat.{u + 1} A)
    (ProjectiveLine.infinityChart S)) (originAffineSheaf A S) (originProjectiveSheaf A S)
      (originSheafSupportCounit A S r)

/-- The sheaf counit at the finite twist, with normalized inverse-image source.
Source: Stacks 03S3, 03Q1 (blueprint: def-pur-origin-comparison-arrows). -/
@[irreducible]
def originSheafTwistCounit (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA) (S : Scheme.{u})
    (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤))) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A)
      (ProjectiveLine.infinityChart S)).obj
        (Scheme.finiteEtaleTateLine (AffineSpace PUnit.{u + 1} S) N A hA) ⟶
      Scheme.finiteEtaleTateLine (ProjectiveLine S) N A hA :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} A)
    (ProjectiveLine.infinityChart S)).map (t.line (ProjectiveLine.infinityChart S) hP).inv ≫
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
        (ProjectiveLine.infinityChart S)).counit.app
          (Scheme.finiteEtaleTateLine (ProjectiveLine S) N A hA)

/-- The actual localized counit at L_P[2], realized termwise and shifted by two.
The source is identified with j_!L_X[2] by the canonical exact and shift comparisons.
Source: Stacks 03S3, 015F (blueprint: def-pur-origin-comparison-arrows). -/
@[irreducible]
def originTwistCounit (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA) (S : Scheme.{u})
    (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤))) :
    (originOpenExtension A S).obj
      ((ordinaryFiniteLine A N hA (AffineSpace PUnit.{u + 1} S))⟦(2 : ℤ)⟧) ⟶
        (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧ :=
  originExactShiftedMap (openImmersionLowerShriek (ModuleCat.{u + 1} A)
    (ProjectiveLine.infinityChart S))
      (Scheme.finiteEtaleTateLine (AffineSpace PUnit.{u + 1} S) N A hA)
      (Scheme.finiteEtaleTateLine (ProjectiveLine S) N A hA)
      (originSheafTwistCounit A N hA t S hP)

/-- Constant sections from the original adjunction and its exact single-object comparison.
Source: Stacks 03FD (blueprint: def-pur-origin-comparison-arrows). -/
@[irreducible]
def originConstantSectionsUnit (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj (ModuleCat.of A A) ⟶
      (originSections A T).obj (ordinaryFiniteUnit A T) :=
  ((constantSheafΓAdj T.smallEtaleTopology
    (ModuleCat.{u + 1} A)).mapDerivedCategoryRightDerivedAdjunction).unit.app
      ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of A A)) ≫
    (originSections A T).map
      (((constantSheaf T.smallEtaleTopology
        (ModuleCat.{u + 1} A)).mapDerivedCategorySingleFunctor 0).hom.app (ModuleCat.of A A))

/-- Compact sections in the fixed projective compactification, namely RΓ(P,j_! -).
This is ordinary compact support, using the proper Leray comparison.
Source: blueprint Step 2 (blueprint: def-pur-origin-comparison-arrows). -/
abbrev originCompactSections (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :=
  originOpenExtension A S ⋙ originSections A (ProjectiveLine S)

/-- The actual derived arrow of a supported Ext class, without a choice of generator.
Source: Stacks 0A45 (blueprint: def-pur-origin-comparison-arrows). -/
@[irreducible]
def originBoundaryArrow (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (κ : Ext F (Scheme.finiteEtaleTateLine T N A hA) 2) :
    (DerivedCategory.singleFunctor _ 0).obj F ⟶
      (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧ :=
  κ.hom


end AlgebraicGeometry.Etale
