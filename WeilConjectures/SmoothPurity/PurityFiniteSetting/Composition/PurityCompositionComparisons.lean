/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
public import WeilConjectures.AlgebraicGeometry.Standing.StandingExceptionalComposition
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothExceptionalPreservation
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegration
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

import WeilConjectures.AlgebraicGeometry.Standing.StandingExceptionalComposition
import WeilConjectures.AlgebraicGeometry.Standing.StandingExceptionalCompositionInverseRight
public import Mathlib.Lean.Meta.CongrTheorems

/-! # Composition coherence for the specified smooth purity maps

Source: main-20261015, sec-smooth-purity/sk-prop-sp-composition,
thm-pur-composition-coherence (blueprint: thm-pur-composition-coherence).

The source identification is assembled from the ordered shifted Tate tensor powers,
monoidal comparison, pullback composition and the shift reassociation used by gamma.
The exceptional comparison is the recorded standing counit mate, transported through
the canonical constant-scalar equivalences. All objects are on the small pro-etale site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u v w t
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The actual functor M ↦ M(d)[2d] in fixed coefficient coordinates.
Source: main-20261015 composition statement, source identification
(blueprint: thm-pur-composition-coherence). -/
def compositionTwistShift (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (d : ℕ) :
    _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) ⥤
    _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) :=
  (smoothPurityTensor P.Coefficient X).flip.obj
    ((P.diagonalTwist X d)⟦-(2 * (d : ℤ))⟧) ⋙ shiftFunctor _ (2 * (d : ℤ))

/-- Shifted pullback on the original intrinsic category; this is exactly gamma's source.
Source: main-20261015 composition statement
(blueprint: thm-pur-composition-coherence). -/
def compositionShiftedPullback (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (d : ℕ) :
    Scheme.proEtaleDerivedCategory Y P.Ring ⥤ Scheme.proEtaleDerivedCategory X P.Ring :=
  (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse ⋙ P.smoothPurityPullback f ⋙
    P.compositionTwistShift X d ⋙ (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor

/-- Map the specified tensor bifunctor on two isomorphisms.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence). -/
def compositionTensorMapIso {C : Type v} [Category.{w} C] (T : C ⥤ C ⥤ C)
    {M M' N N' : C} (a : M ≅ M') (b : N ≅ N') :
    (T.obj M).obj N ≅ (T.obj M').obj N' :=
  (T.mapIso a).app N ≪≫ (T.obj M').mapIso b

/-- Concatenate ordered tensor powers using the specified tensor associator and unit.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence). -/
def compositionOrderedPowerAdd {C : Type v} [Category.{w} C] (T : C ⥤ C ⥤ C)
    (B : ℕ → C) (L : C) (z : ∀ M : C, (T.obj M).obj (B 0) ≅ M)
    (a : ∀ M N V : C, (T.obj ((T.obj M).obj N)).obj V ≅ (T.obj M).obj ((T.obj N).obj V))
    (s : ∀ n : ℕ, B (n + 1) ≅ (T.obj (B n)).obj L)
    (d : ℕ) : ∀ e : ℕ, B (d + e) ≅ (T.obj (B d)).obj (B e)
  | 0 => (z (B d)).symm
  | e + 1 => s (d + e) ≪≫
      compositionTensorMapIso T (compositionOrderedPowerAdd T B L z a s d e) (Iso.refl L) ≪≫
      a (B d) (B e) L ≪≫ (T.obj (B d)).mapIso (s e).symm

/-- Assemble tensor powers for a fixed etale coefficient category.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence). -/
def compositionEtalePowerAssembly (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) (B : ℕ → _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (z : B 0 ≅ 𝟙_ (_root_.DerivedCategory (Sheaf X.smallEtaleTopology C)))
    (s : ∀ n : ℕ, B (n + 1) ≅ ((Etale.derivedTensor C X).obj (B n)).obj L)
    (d e : ℕ) : B (d + e) ≅ ((Etale.derivedTensor C X).obj (B d)).obj (B e) :=
  compositionOrderedPowerAdd (Etale.derivedTensor C X) B L
    (fun M ↦ (Etale.derivedTensor C X).obj M |>.mapIso z |>.trans
      (Etale.derivedTensorRightUnitor C X M))
    (Etale.derivedTensorAssociator C X) s d e

/-- Degree zero of the published tensor power.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence).
Proof: unfold the zero branch of affineLinearBaseCoefficient;
both objects are the ordinary finite constant unit. -/
theorem compositionEtalePowerZero (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (X : Scheme.{u}) :
    Etale.affineLinearBaseCoefficient A N hA X 0 = Etale.ordinaryFiniteUnit A X := by
  rfl

/-- Successor of the published ordered tensor power.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence).
Proof: unfold the successor branch of
affineLinearBaseCoefficient: the right tensor functor is
exactly tensoring the preceding power with the shifted ordinary finite line. -/
theorem compositionEtalePowerSuccessor (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0)
    (X : Scheme.{u}) (n : ℕ) :
    Etale.affineLinearBaseCoefficient A N hA X (n + 1) =
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        (Etale.affineLinearBaseCoefficient A N hA X n)).obj
        ((Etale.ordinaryFiniteLine A N
          hA X)⟦(2 : ℤ)⟧) := by
  rfl

/-- Concatenation for the published even-shifted finite Tate powers.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence). -/
def compositionEtalePowerAdd (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0)
    (X : Scheme.{u}) (d e : ℕ) :
    Etale.affineLinearBaseCoefficient A N hA X (d + e) ≅
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        (Etale.affineLinearBaseCoefficient A N hA X d)).obj
        (Etale.affineLinearBaseCoefficient A N hA X e) :=
  compositionEtalePowerAssembly (ModuleCat.{u + 1} A) X
    (Etale.affineLinearBaseCoefficient A N hA X)
    ((Etale.ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)
    (eqToIso (compositionEtalePowerZero A N hA X) ≪≫ smoothPurityUnitIso A X)
    (fun n ↦ eqToIso (compositionEtalePowerSuccessor A N hA X n)) d e

/-- Compare and reverse the two blocks of an ordered finite Tate power.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence). -/
def compositionComparisonPowerAdd (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0)
    (X : Scheme.{u}) (d e : ℕ) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
      (Etale.affineLinearBaseCoefficient A N hA X (d + e)) ≅
    ((smoothPurityTensor A X).obj
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
        (Etale.affineLinearBaseCoefficient A N hA X e))).obj
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
        (Etale.affineLinearBaseCoefficient A N hA X d)) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.mapIso
    (compositionEtalePowerAdd A N hA X d e ≪≫
      ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) X).app
        (Etale.affineLinearBaseCoefficient A N hA X d)).app
          (Etale.affineLinearBaseCoefficient A N hA X e)) ≪≫
    smoothPurityComparisonTensor A X
      (Etale.affineLinearBaseCoefficient A N hA X e)
      (Etale.affineLinearBaseCoefficient A N hA X d)

/-- Split the shifted Tate power in the order e,d needed by the iterated source.
The symmetry is the derived symmetry, hence includes its Koszul sign (even here).
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence). -/
def compositionPowerAdd (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (d e : ℕ) :
    P.diagonalTwist X (d + e) ≅
      ((smoothPurityTensor P.Coefficient X).obj (P.diagonalTwist X e)).obj
        (P.diagonalTwist X d) :=
  compositionComparisonPowerAdd P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates X d e

/-- Pullback of the shifted Tate power, fixed by roots restriction and pure tensors.
Source: main-20261015 composition proof Step 9, twist-pullback identification
(blueprint: thm-pur-composition-coherence). -/
def compositionTwistPullback (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [Y.Over (Spec (.of P.field.k))] (f : X ⟶ Y) (e : ℕ) :
    (P.smoothPurityPullback f).obj (P.diagonalTwist Y e) ≅ P.diagonalTwist X e :=
  (ProEtale.sfDerivedComparisonPullbackIso P.Ring f).app (P.diagonalTwistEtale Y e) ≪≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
      (((Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} P.Coefficient) f).app (P.diagonalTwistEtale Y e)).symm ≪≫
        Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates
          (Etale.projectiveLineTraceTransport P.diagonalExponent
            (pow_pos (Fact.out : Nat.Prime P.coefficients.l).pos P.level)
            P.Coefficient P.diagonalExponent_annihilates)
          f (P.diagonalExponent_isUnit (Y ↘ Spec (.of P.field.k))) e)

/-- The monoidal pullback iso, normalized to the published derived comparison.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence).
Proof: rewrite smoothPurityTensor by smoothPurityTensorPresentation. The exact-derived
comparison identifies termwise inverse image with left-derived inverse image. Its inverse,
the published tensor comparison, and the tensor of the two exact-derived comparisons
have exactly the displayed endpoints. HEq specifies that composite itself and gives
uniqueness by equality of the underlying maps. -/
theorem existsUnique_compositionPullbackTensor (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [ProEtale.UpperStarPreservesFlat C]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) C)) :
    ∃! a : ((ProEtale.upperStar C f).mapDerivedCategory).obj
        (((ProEtale.derivedTensor C Y).obj M).obj N) ≅
      ((ProEtale.derivedTensor C X).obj
        (((ProEtale.upperStar C f).mapDerivedCategory).obj M)).obj
        (((ProEtale.upperStar C f).mapDerivedCategory).obj N),
      HEq a
        (((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
            C f).app
              (((ProEtale.derivedTensor C Y).obj M).obj N)).symm
          ≪≫ ProEtale.leftDerivedUpperStarTensorIso
            C f M N ≪≫
          compositionTensorMapIso (ProEtale.derivedTensor C X)
            ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
              C f).app M)
            ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
              C f).app N)) := by
  refine ⟨_, HEq.rfl, ?_⟩
  intro a ha
  exact eq_of_heq ha

/-- The specified exact tensor-pullback comparison, with all map data fixed above.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence). -/
def compositionPullbackTensor (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [ProEtale.UpperStarPreservesFlat C] {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (M N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) C)) :
    ((ProEtale.upperStar C f).mapDerivedCategory).obj
      (((ProEtale.derivedTensor C Y).obj M).obj N) ≅
    ((ProEtale.derivedTensor C X).obj
      (((ProEtale.upperStar C f).mapDerivedCategory).obj M)).obj
        (((ProEtale.upperStar C f).mapDerivedCategory).obj N) :=
  (existsUnique_compositionPullbackTensor C f M N).exists.choose

/-- Finite coefficient rings are Noetherian after the standard universe lift.
Source: main-20261015 finite-coefficient conventions
(blueprint: thm-pur-composition-coherence).
Proof: every ideal is finite, hence generated by its finitely many elements. -/
theorem compositionCoefficientNoetherian (A : Type u) [CommRing A] [Finite A] :
    IsNoetherianRing (ULift.{u + 1} A) := by
  exact isNoetherian_of_finite _ _

/-- Type of the canonical fixed-coordinate tensor-pullback comparison.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence). -/
def CompositionPullbackTensorType (A : Type u) [CommRing A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :=
  (ProEtale.sfFixedDerivedPullback A f).obj
    (((smoothPurityTensor (ULift.{u + 1} A) Y).obj M).obj N) ≅
  ((smoothPurityTensor (ULift.{u + 1} A) X).obj
    ((ProEtale.sfFixedDerivedPullback A f).obj M)).obj
      ((ProEtale.sfFixedDerivedPullback A f).obj N)

/-- The normalization requires equality to the specified published tensor comparison.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence). -/
def CompositionPullbackTensorNormalized (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} A))))
    (a : CompositionPullbackTensorType A f M N) : Prop :=
  HEq a (@compositionPullbackTensor _ _ _ _ _ _ _ _ _
        (@ProEtale.upperStarPreservesFlat_moduleCat.{u} (ULift.{u + 1} A)
          inferInstance (compositionCoefficientNoetherian A)) X Y f M N)

/-- The fixed-coordinate tensor comparison is uniquely the published map.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence).
Proof: unfold sfFixedDerivedPullback and smoothPurityTensor. Both presentations
have the exact tensor comparison as witness. Its entire isomorphism is fixed by HEq,
so heterogeneous transitivity gives ordinary equality of any two witnesses. -/
theorem existsUnique_compositionPullbackTensorFixed (A : Type u) [CommRing A]
    [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    ∃! a : CompositionPullbackTensorType A f M N,
      CompositionPullbackTensorNormalized A f M N a := by
  unfold CompositionPullbackTensorType CompositionPullbackTensorNormalized
  unfold smoothPurityTensor
  refine ⟨_, HEq.rfl, ?_⟩
  intro a ha
  exact eq_of_heq ha

/-- The unique transport of the published exact tensor comparison.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence). -/
def compositionPullbackTensorFixed (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :=
  Classical.choose (existsUnique_compositionPullbackTensorFixed A f M N)

/-- Canonical derivation of a specified exact-functor compositor.
Source: main-20261015 composition proof Step 9, exact pullback composition
(blueprint: thm-pur-composition-coherence). -/
def compositionExactDerivedComp {C D E : Type v}
    [Category.{w} C] [Category.{w} D] [Category.{w} E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory.{t} C] [HasDerivedCategory.{t} D] [HasDerivedCategory.{t} E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : H ≅ F ⋙ G) :
    H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory :=
  letI := comp_preservesFiniteLimits F G
  letI := comp_preservesFiniteColimits F G
  Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso F G

/-- Exact derived pullback composition, with the actual upper-star compositor.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence). -/
def compositionPullbackComp (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (ProEtale.upperStar C (f ≫ g)).mapDerivedCategory ≅
      (ProEtale.upperStar C g).mapDerivedCategory ⋙
        (ProEtale.upperStar C f).mapDerivedCategory :=
  compositionExactDerivedComp (ProEtale.upperStar C g) (ProEtale.upperStar C f)
    (ProEtale.upperStar C (f ≫ g)) (ProEtale.upperStarComp C f g)

/-- Fixed coordinates have exactly the canonical pullback compositor.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence).
Proof: unfold sfFixedDerivedPullback. The generic exact pullback compositor has these
endpoints. Its heterogeneous equality fixes the complete natural isomorphism uniquely.
Only cached instances are transported. -/
theorem existsUnique_compositionFixedPullbackComp (A : Type u) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃! a : ProEtale.sfFixedDerivedPullback A (f ≫ g) ≅
      ProEtale.sfFixedDerivedPullback A g ⋙ ProEtale.sfFixedDerivedPullback A f,
      HEq a (compositionPullbackComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g) := by
  refine ⟨_, HEq.rfl, ?_⟩
  intro a ha
  exact eq_of_heq ha

/-- The canonical pullback compositor in fixed scalar coordinates.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence). -/
def compositionFixedPullbackComp (A : Type u) [CommRing A] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ProEtale.sfFixedDerivedPullback A (f ≫ g) ≅
      ProEtale.sfFixedDerivedPullback A g ⋙ ProEtale.sfFixedDerivedPullback A f :=
  Classical.choose (existsUnique_compositionFixedPullbackComp A f g)

/-- Type of the associator in the published tensor presentation.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence). -/
def CompositionTensorAssociatorType (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (M N L : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :=
  ((smoothPurityTensor A X).obj (((smoothPurityTensor A X).obj M).obj N)).obj L ≅
    ((smoothPurityTensor A X).obj M).obj (((smoothPurityTensor A X).obj N).obj L)

/-- The associator normalization fixes the map to be the ordinary monoidal associator.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence). -/
def CompositionTensorAssociatorNormalized (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (M N L : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : CompositionTensorAssociatorType A X M N L) : Prop := HEq a (α_ M N L)

/-- The specified associator is uniquely the ordinary monoidal associator.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence).
Proof: unfold the type alias and smoothPurityTensorPresentation. These are the endpoints
of the ordinary associator. HEq fixes both its morphism and inverse, giving uniqueness. -/
theorem existsUnique_compositionTensorAssociatorFixed (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (M N L : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    ∃! a : CompositionTensorAssociatorType A X M N L,
      CompositionTensorAssociatorNormalized A X M N L a := by
  unfold CompositionTensorAssociatorType CompositionTensorAssociatorNormalized
  unfold smoothPurityTensor
  refine ⟨_, HEq.rfl, ?_⟩
  intro a ha
  exact eq_of_heq ha

/-- The unique published associator in fixed coefficient coordinates.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence). -/
def compositionTensorAssociatorFixed (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (M N L : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :=
  Classical.choose (existsUnique_compositionTensorAssociatorFixed A X M N L)

/-- Type of the fixed-coordinate source identification in the composition display.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence). -/
def CompositionSourceType (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    [Y.Over (Spec (.of P.field.k))] (f : X ⟶ Y) (g : Y ⟶ Z) (d e : ℕ)
    (K : Scheme.proEtaleDerivedCategory Z P.Ring) :=
  (P.compositionTwistShift X (d + e)).obj
    ((P.smoothPurityPullback (f ≫ g)).obj
      ((Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).inverse.obj K)) ≅
  (P.compositionTwistShift X d).obj ((P.smoothPurityPullback f).obj
    ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj
      ((P.compositionShiftedPullback g e).obj K)))

/-- Intermediate objects of the canonical source identification. Step 3 to step 5
separates twist pullback from tensor pullback, making every interface explicit.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence). -/
def compositionSourceStage (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    [Y.Over (Spec (.of P.field.k))] (f : X ⟶ Y) (g : Y ⟶ Z) (d e : ℕ)
    (K : Scheme.proEtaleDerivedCategory Z P.Ring) (j : ℕ) :
    _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) :=
  let M := (Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).inverse.obj K
  let F := P.smoothPurityPullback f
  let G := P.smoothPurityPullback g
  let T := smoothPurityTensor P.Coefficient X
  let V := ((smoothPurityTensor P.Coefficient Y).obj (G.obj M)).obj (P.diagonalTwist Y e)
  let B := (P.compositionTwistShift Y e).obj (G.obj M)
  match j with
  | 0 => (P.compositionTwistShift X (d + e)).obj
      ((P.smoothPurityPullback (f ≫ g)).obj M)
  | 1 => (T.obj ((P.smoothPurityPullback (f ≫ g)).obj M)).obj
      (P.diagonalTwist X (d + e))
  | 2 => (T.obj (F.obj (G.obj M))).obj
      ((T.obj (P.diagonalTwist X e)).obj (P.diagonalTwist X d))
  | 3 => (T.obj ((T.obj (F.obj (G.obj M))).obj (P.diagonalTwist X e))).obj
      (P.diagonalTwist X d)
  | 4 => (T.obj ((T.obj (F.obj (G.obj M))).obj (F.obj (P.diagonalTwist Y e)))).obj
      (P.diagonalTwist X d)
  | 5 => (T.obj (F.obj V)).obj (P.diagonalTwist X d)
  | 6 => (P.compositionTwistShift X d).obj (F.obj V)
  | 7 => (P.compositionTwistShift X d).obj (F.obj B)
  | _ => (P.compositionTwistShift X d).obj
      (F.obj ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj
        ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).functor.obj B)))

/-- The complete normalization fixes each factor to its published canonical map,
then fixes a to their ordered composite. The intermediate isomorphisms are bound
only inside this proposition; each is uniquely fixed by its HEq clause.
Source: main-20261015 composition proof Step 9
(blueprint: thm-pur-composition-coherence). -/
def CompositionSourceNormalized (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    [Y.Over (Spec (.of P.field.k))] (f : X ⟶ Y) (g : Y ⟶ Z) (d e : ℕ)
    (K : Scheme.proEtaleDerivedCategory Z P.Ring)
    (a : P.CompositionSourceType f g d e K) : Prop :=
  let M := (Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).inverse.obj K
  let F := P.smoothPurityPullback f
  let G := P.smoothPurityPullback g
  let T := P.compositionTwistShift X d
  let B := (P.compositionTwistShift Y e).obj (G.obj M)
  let S := P.compositionSourceStage f g d e K
  ∃ i₀ : S 0 ≅ S 1, ∃ i₁ : S 1 ≅ S 2, ∃ i₂ : S 2 ≅ S 3,
    ∃ i₃ : S 3 ≅ S 4, ∃ i₄ : S 4 ≅ S 5, ∃ i₅ : S 5 ≅ S 6,
      ∃ i₆ : S 6 ≅ S 7, ∃ i₇ : S 7 ≅ S 8,
  HEq i₀ (P.smoothPurityReassociation X (d + e)
    ((P.smoothPurityPullback (f ≫ g)).obj M)) ∧
  HEq i₁ (compositionTensorMapIso (smoothPurityTensor P.Coefficient X)
    ((compositionFixedPullbackComp P.Ring f g).app M) (P.compositionPowerAdd X d e)) ∧
  HEq i₂ ((compositionTensorAssociatorFixed P.Coefficient X
    (F.obj (G.obj M)) (P.diagonalTwist X e) (P.diagonalTwist X d)).symm) ∧
  HEq i₃ (compositionTensorMapIso (smoothPurityTensor P.Coefficient X)
    (compositionTensorMapIso (smoothPurityTensor P.Coefficient X)
      (Iso.refl (F.obj (G.obj M))) (P.compositionTwistPullback f e).symm)
    (Iso.refl (P.diagonalTwist X d))) ∧
  HEq i₄ (compositionTensorMapIso (smoothPurityTensor P.Coefficient X)
    (compositionPullbackTensorFixed P.Ring f (G.obj M) (P.diagonalTwist Y e)).symm
    (Iso.refl (P.diagonalTwist X d))) ∧
  HEq i₅ ((P.smoothPurityReassociation X d
    (F.obj (((smoothPurityTensor P.Coefficient Y).obj (G.obj M)).obj
      (P.diagonalTwist Y e)))).symm) ∧
  HEq i₆ (T.mapIso (F.mapIso (P.smoothPurityReassociation Y e (G.obj M)).symm)) ∧
  HEq i₇ (T.mapIso (F.mapIso ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).unitIso.app B))) ∧
  HEq a (i₀ ≪≫ i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ i₄ ≪≫ i₅ ≪≫ i₆ ≪≫ i₇)

/-- There is exactly one source identification with this complete map normalization.
Source: main-20261015 composition statement, source identification, and proof Step 9
(blueprint: thm-pur-composition-coherence).
Proof: unfold CompositionSourceType and CompositionSourceNormalized. Each of the eight
factors is the specified canonical isomorphism, with the adjacent endpoints matching
by the pullback compositor, ordered power splitting, tensor associator, tensor and
Tate pullback comparisons, two shift reassociations and the realization unit. Their
composite has exactly the displayed endpoints. It gives existence with reflexive HEq.
If two isomorphisms satisfy the normalization, heterogeneous transitivity gives their
ordinary equality, proving uniqueness of the full morphism and inverse. -/
theorem existsUnique_compositionSourceFixed (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    [Y.Over (Spec (.of P.field.k))] (f : X ⟶ Y) (g : Y ⟶ Z) (d e : ℕ)
    (K : Scheme.proEtaleDerivedCategory Z P.Ring) :
    ∃! a : P.CompositionSourceType f g d e K,
      P.CompositionSourceNormalized f g d e K a := by
  let M := (Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).inverse.obj K
  let F := P.smoothPurityPullback f
  let G := P.smoothPurityPullback g
  let T := P.compositionTwistShift X d
  let B := (P.compositionTwistShift Y e).obj (G.obj M)
  let S := P.compositionSourceStage f g d e K
  let i₀ : S 0 ≅ S 1 := P.smoothPurityReassociation X (d + e)
    ((P.smoothPurityPullback (f ≫ g)).obj M)
  let i₁ : S 1 ≅ S 2 := compositionTensorMapIso (smoothPurityTensor P.Coefficient X)
    ((compositionFixedPullbackComp P.Ring f g).app M) (P.compositionPowerAdd X d e)
  let i₂ : S 2 ≅ S 3 := (compositionTensorAssociatorFixed P.Coefficient X
    (F.obj (G.obj M)) (P.diagonalTwist X e) (P.diagonalTwist X d)).symm
  let i₃ : S 3 ≅ S 4 := compositionTensorMapIso (smoothPurityTensor P.Coefficient X)
    (compositionTensorMapIso (smoothPurityTensor P.Coefficient X)
      (Iso.refl (F.obj (G.obj M))) (P.compositionTwistPullback f e).symm)
    (Iso.refl (P.diagonalTwist X d))
  let i₄ : S 4 ≅ S 5 := compositionTensorMapIso (smoothPurityTensor P.Coefficient X)
    (compositionPullbackTensorFixed P.Ring f (G.obj M) (P.diagonalTwist Y e)).symm
    (Iso.refl (P.diagonalTwist X d))
  let i₅ : S 5 ≅ S 6 := (P.smoothPurityReassociation X d
    (F.obj (((smoothPurityTensor P.Coefficient Y).obj (G.obj M)).obj
      (P.diagonalTwist Y e)))).symm
  let i₆ : S 6 ≅ S 7 :=
    T.mapIso (F.mapIso (P.smoothPurityReassociation Y e (G.obj M)).symm)
  let i₇ : S 7 ≅ S 8 :=
    T.mapIso (F.mapIso ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).unitIso.app B))
  refine ⟨i₀ ≪≫ i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ i₄ ≪≫ i₅ ≪≫ i₆ ≪≫ i₇, ?_, ?_⟩
  · exact ⟨i₀, i₁, i₂, i₃, i₄, i₅, i₆, i₇,
      HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl,
      HEq.rfl⟩
  · rintro a ⟨j₀, j₁, j₂, j₃, j₄, j₅, j₆, j₇,
      h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, ha⟩
    have hj₀ : j₀ = i₀ := eq_of_heq h₀
    have hj₁ : j₁ = i₁ := eq_of_heq h₁
    have hj₂ : j₂ = i₂ := eq_of_heq h₂
    have hj₃ : j₃ = i₃ := eq_of_heq h₃
    have hj₄ : j₄ = i₄ := eq_of_heq h₄
    have hj₅ : j₅ = i₅ := eq_of_heq h₅
    have hj₆ : j₆ = i₆ := eq_of_heq h₆
    have hj₇ : j₇ = i₇ := eq_of_heq h₇
    simpa only [hj₀, hj₁, hj₂, hj₃, hj₄, hj₅, hj₆, hj₇] using eq_of_heq ha

/-- The source identification, uniquely fixed by its explicit canonical eight factors.
Only the equality of endpoint presentations is postponed; all map data is fixed above.
Source: main-20261015 composition statement, displayed identification
(blueprint: thm-pur-composition-coherence). -/
def compositionSourceFixed (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    [Y.Over (Spec (.of P.field.k))] (f : X ⟶ Y) (g : Y ⟶ Z) (d e : ℕ)
    (K : Scheme.proEtaleDerivedCategory Z P.Ring) :=
  Classical.choose (P.existsUnique_compositionSourceFixed f g d e K)

/-- The canonical identification on the original pro-etale derived category.
Source: main-20261015 composition statement, displayed identification
(blueprint: thm-pur-composition-coherence). -/
def compositionSourceIdentification (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    [Y.Over (Spec (.of P.field.k))] (f : X ⟶ Y) (g : Y ⟶ Z) (d e : ℕ)
    (K : Scheme.proEtaleDerivedCategory Z P.Ring) :=
  (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.mapIso
    (P.compositionSourceFixed f g d e K)

section Geometry
variable (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [Z.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]

/-- The same standing exceptional inverse image, on intrinsic constant-ring modules.
Source: main-20261015 composition statement, Rf! (exclamation superscript)
(blueprint: thm-pur-composition-coherence). -/
def compositionExceptional (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Scheme.proEtaleDerivedCategory Y P.Ring ⥤ Scheme.proEtaleDerivedCategory X P.Ring :=
  (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse ⋙
    P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k)) ⋙
      (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor

/-- Smooth exceptional inverse image has the finite-Tor constructible domain required
for the second purity map. This is a consequence, not a hypothesis on the composite.
Source: main-20261015 composition statement and cor-pur-smooth-admissibility (2)
(blueprint: thm-pur-composition-coherence).
Proof: cor-pur-smooth-admissibility gives finite-Tor constructible preservation for
finiteExceptionalInverseImage. Its formula and the present functor are Rnu_* followed
by the ordinary etale exceptional adjoint and nu^*, conjugated by the same constant
scalar equivalences. The canonical mapDerivedCategory composition comparisons identify
these formulas. Exact equivalences commute with homology and tensor, so transport
bounded constructibility and the finite Tor interval along these comparisons. -/
theorem compositionExceptional_ctf (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (e : ℕ) [SmoothOfRelativeDimension e g]
    (K : Scheme.proEtaleDerivedCategory Z P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Z K) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
      ((P.compositionExceptional g).obj K) := by
  have h := (smooth_exceptional_preservation P Y Z g e).2.2 K hK
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y
  let R := ProEtale.finiteCoefficientIntrinsicRealization Y P.Ring
  have : R.Additive := ProEtale.finiteCoefficientIntrinsicRealization_additive Y P.Ring
  have : PreservesFiniteLimits R :=
    ProEtale.finiteCoefficientIntrinsicRealization_preservesFiniteLimits Y P.Ring
  have : PreservesFiniteColimits R :=
    ProEtale.finiteCoefficientIntrinsicRealization_preservesFiniteColimits Y P.Ring
  let a : (Scheme.finiteExceptionalInverseImage P.coefficients.l P.extension P.level
      P.level_pos P.field.k Y Z g).obj K ≅ (P.compositionExceptional g).obj K :=
    (Functor.mapDerivedCategoryCompIso ν R).app _
  have : (finiteTorConstructible P.coefficients.l P.extension P.level
      P.level_pos Y).IsClosedUnderIsomorphisms :=
    (Scheme.finite_ctf_isTriangulated P.coefficients.l P.extension P.level P.level_pos Y).1
  exact (finiteTorConstructible P.coefficients.l P.extension P.level
    P.level_pos Y).prop_of_iso a h

set_option linter.unusedSectionVars false in
/-- Intrinsic Dctf gives precisely the bounded constructible fixed-coordinate input
required by the standing composition mate.
Source: main-20261015 composition statement, finite coefficient domain
(blueprint: thm-pur-composition-coherence).
Proof: forget the finite-Tor conjunct of hK. The finite-ring constructible origin
comparison lifts bounded constructible cohomology to a bounded constructible etale
complex. The exact scalar realization equivalence and its unit identify its pro-etale
comparison with the inverse realization of K. This is boundedConstructible by definition.
No representative is selected as data. -/
theorem compositionInput_bounded (K : Scheme.proEtaleDerivedCategory Z P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Z K) :
    ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} P.Coefficient) Z
      ((Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).inverse.obj K) := by
  classical
  obtain ⟨a, ha⟩ := hK.1.1.bddBelow
  obtain ⟨b, hb⟩ := hK.1.1.bddAbove
  have hv (i : ℤ) (hi : i < min a b ∨ max a b < i) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj K) := by
    by_contra hn
    rcases hi with hi | hi
    · exact (not_lt_of_ge (le_trans (min_le_left _ _) (ha hn))) hi
    · exact (not_lt_of_ge (le_trans (hb hn) (le_max_right _ _))) hi
  obtain ⟨G, ⟨e⟩⟩ :=
    ((Scheme.finiteRing_constructibleDerived_origin Z P.Ring).2.2.1 K).mpr
      ⟨hK.1.2, min a b, max a b, min_le_max, hv⟩
  refine ⟨G.obj, ?_, ⟨?_⟩⟩
  · obtain ⟨hc, c, d, _, hz⟩ := G.property
    refine ⟨⟨⟨c, (_root_.DerivedCategory.isGE_iff G.obj c).mpr
      (fun i hi ↦ hz i (Or.inl hi))⟩,
      ⟨d, (_root_.DerivedCategory.isLE_iff G.obj d).mpr
        (fun i hi ↦ hz i (Or.inr hi))⟩⟩, fun i ↦ ?_⟩
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc i)
  · let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Z
    let R := ProEtale.finiteCoefficientIntrinsicRealization Z P.Ring
    have : R.Additive :=
      ProEtale.finiteCoefficientIntrinsicRealization_additive Z P.Ring
    have : PreservesFiniteLimits R :=
      ProEtale.finiteCoefficientIntrinsicRealization_preservesFiniteLimits Z P.Ring
    have : PreservesFiniteColimits R :=
      ProEtale.finiteCoefficientIntrinsicRealization_preservesFiniteColimits Z P.Ring
    exact (Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).unitIso.app _ ≪≫
      (Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).inverse.mapIso
        ((Functor.mapDerivedCategoryCompIso C R).symm.app G.obj ≪≫ e)

/-- The actual c_{g,f,K}, not a variable: realize the standing exceptional mate,
then insert the realization unit at its intermediate exceptional value.
Source: main-20261015 composition statement and pur9-def-upper-shriek-composition
(blueprint: thm-pur-composition-coherence). -/
def compositionExceptionalMap (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (K : Scheme.proEtaleDerivedCategory Z P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Z K) :
    (P.compositionExceptional (f ≫ g)).obj K ⟶
      (P.compositionExceptional f).obj ((P.compositionExceptional g).obj K) :=
  (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.map
    (ProEtale.standingExceptionalComposition P f g
      ⟨(Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).inverse.obj K,
        P.compositionInput_bounded K hK⟩ ≫
      (P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))).map
        ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).unitIso.hom.app
          ((P.smoothPurityExceptionalOver g (Z ↘ Spec (.of P.field.k))).obj
            ((Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).inverse.obj K))))

end Geometry
end WeilConjectures.PurityFiniteSetting
