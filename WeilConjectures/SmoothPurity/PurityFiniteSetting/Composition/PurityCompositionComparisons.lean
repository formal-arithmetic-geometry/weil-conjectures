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
public import WeilConjectures.AlgebraicGeometry.Standing.StandingExceptionalCompositionInverseLeft

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

/-- The specified counit mate c is invertible on this domain.
Source: main-20261015 composition statement, composition isomorphism c
(blueprint: thm-pur-composition-coherence).
Proof: alpha from thm-sf-comp-composition is invertible and natural on bounded-below
etale-origin inputs. The standing Hom bijections identify both exceptional objects
as representatives of the same compact-support Hom functor on bounded constructible
objects. Transpose alpha inverse for the inverse map. Naturality and the two triangle
identities give the two inverse equations, by the two adjunction hom bijections.
Finally realize through the coefficient equivalence and its intermediate unit. -/
theorem isIso_compositionExceptionalMap (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (K : Scheme.proEtaleDerivedCategory Z P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Z K) :
    IsIso (P.compositionExceptionalMap f g K hK) := by
  let L : ProEtale.DerivedCategoryBoundedConstructible
      (ModuleCat.{u + 1} P.Coefficient) Z :=
    ⟨(Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).inverse.obj K,
      P.compositionInput_bounded K hK⟩
  have hc : IsIso (ProEtale.standingExceptionalComposition P f g L) :=
    ⟨⟨ProEtale.standingExceptionalCompositionInverse P f g L,
      ProEtale.standingExceptionalComposition_inverse_hom P f g L,
      ProEtale.standingExceptionalComposition_hom_inverse P f g L⟩⟩
  unfold compositionExceptionalMap
  refine @Functor.map_isIso _ _ _ _ _ _ _ _ ?_
  refine IsIso.comp_isIso' hc ?_
  infer_instance

/-- The inverse of the specified standing composition map.
Source: main-20261015 composition statement, last arrow c inverse
(blueprint: thm-pur-composition-coherence). -/
def compositionExceptionalIso (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (K : Scheme.proEtaleDerivedCategory Z P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Z K) :
    (P.compositionExceptional (f ≫ g)).obj K ≅
      (P.compositionExceptional f).obj ((P.compositionExceptional g).obj K) :=
  letI := P.isIso_compositionExceptionalMap f g K hK
  asIso (P.compositionExceptionalMap f g K hK)

end Geometry
end WeilConjectures.PurityFiniteSetting
