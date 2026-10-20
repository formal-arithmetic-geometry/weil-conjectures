/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.AlgebraicGeometry.CompactProductArrows
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek

/-! # Proper support and compact cohomology maps

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-proper-support-compact-maps).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A]

/-- A proper closed support is closed in every compactification over the base.
Source: blueprint Step 1, proper-support paragraph
(blueprint: def-pur-proper-support-compact-maps).
Proof: the composite is an immersion. Its source is proper over the base and its
 target is separated over the base, so the composite is proper; a proper immersion
is closed. -/
@[instance]
theorem compactProperSupportClosed {B X Z : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)] :
    IsClosedImmersion (i ≫ c.i) := by
  sorry

/-- Restriction of supported constants along the compactifying open, uniquely
normalized on the constant quotient sections.
Source: blueprint Step 1, proper-support paragraph
(blueprint: def-pur-proper-support-compact-maps).
Proof: restriction to the open containing the entire closed support is the closed
base-change identification. Both quotient maps restrict the same constant sections.
The quotient is epic, so this normalization determines the isomorphism uniquely. -/
theorem compactSupportCoefficientRestriction_existsUnique
    {B X Z : Scheme.{u}} {f : X ⟶ B} (c : Compactification f)
    (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)] :
    ∃! e : supportedCoefficients A (i ≫ c.i) ⋙ upperStar (ModuleCat.{u + 1} A) c.i ≅
        supportedCoefficients A i,
      ∀ M : ModuleCat.{u + 1} A,
        (upperStar (ModuleCat.{u + 1} A) c.i).map
            (supportedCoefficientQuotient A (i ≫ c.i) M) ≫ e.hom.app M =
          (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) c.i).hom.app M ≫
            supportedCoefficientQuotient A i M := by
  sorry

/-- The quotient-normalized closed-coefficient restriction.
Source: blueprint Step 1, proper-support paragraph
(blueprint: def-pur-proper-support-compact-maps). -/
def compactSupportCoefficientRestriction {B X Z : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)] :=
  (compactSupportCoefficientRestriction_existsUnique A c i).choose

/-- The same coefficient restriction on the derived categories.
Source: blueprint Step 1, proper-support paragraph
(blueprint: def-pur-proper-support-compact-maps). -/
def compactSupportDerivedCoefficientRestriction {B X Z : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)] :
    (supportedCoefficients A (i ≫ c.i)).mapDerivedCategory ⋙
      compactProductPullback (ModuleCat.{u + 1} A) c.i ≅
      (supportedCoefficients A i).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (compactSupportCoefficientRestriction A c i)

/-- The canonical `j_! i_* = bar_i_*` map, as the open-adjunction mate of the
normalized closed-coefficient restriction.
Source: blueprint Step 1, proper-support paragraph
(blueprint: def-pur-proper-support-compact-maps). -/
def compactSupportCoefficientExtension {B X Z : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)]
    (M : DerivedCategory (ModuleCat.{u + 1} A)) :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) c.i).homEquiv _ _).symm
      ((compactSupportDerivedCoefficientRestriction A c i).inv.app M)

/-- Properness makes the supported coefficient extension comparison invertible.
Source: blueprint Step 1, proper-support paragraph
(blueprint: def-pur-proper-support-compact-maps).
Proof: cover the compactification by the compactifying open and the complement
of the closed support. On the first open the comparison is the normalized
restriction isomorphism; on the second both supported coefficient sheaves vanish.
Sheaf locality makes the ordinary comparison invertible. The same calculation
holds termwise, and exact zero extension and restriction descend it to localization. -/
@[instance]
theorem compactSupportCoefficientExtension_isIso {B X Z : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)]
    (M : DerivedCategory (ModuleCat.{u + 1} A)) :
    IsIso (compactSupportCoefficientExtension A c i M) := by
  sorry

/-- The ordinary derived map forgetting support, using the recorded kernel inclusion.
Source: blueprint Step 1, forgetting supports
(blueprint: def-pur-proper-support-compact-maps). -/
def compactProductForget {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    supportedSectionsDerived A i ⟶ rightDerivedGlobalSections (ModuleCat.{u + 1} A) X :=
  Functor.rightDerivedFunctorNatTrans (supportedEtaleSectionsι A X i.openComplement)

/-- The constant-section unit for the closed coefficient object in the compactification.
This is the support adjunction unit followed by the derived kernel inclusion, hence
is the unit M to RΓ(Z,constant M) under the normalized closed-support identification.
Source: blueprint Step 1, definition of u_Z
(blueprint: def-pur-proper-support-compact-maps). -/
def compactSupportConstantUnit {B X Z : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)]
    (M : DerivedCategory (ModuleCat.{u + 1} A)) :=
  (supportedCoefficientDerivedAdjunction A (i ≫ c.i)).unit.app M ≫
    (compactProductForget A (i ≫ c.i)).app
      ((supportedCoefficients A (i ≫ c.i)).mapDerivedCategory.obj M)

/-- Image of a supported morphism in compact cohomology: take its compact-support
direct image and precompose with the constant-section unit. M=A[0] and target K[a]
gives the stated formula on H^a, including negative degrees.
Source: blueprint Step 1, supported class formula
(blueprint: def-pur-proper-support-compact-maps). -/
def compactSupportClassImage {B X Z : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)]
    {M : DerivedCategory (ModuleCat.{u + 1} A)}
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (α : (supportedCoefficients A i).mapDerivedCategory.obj M ⟶ K) :
    M ⟶ (compactProductSections (ModuleCat.{u + 1} A) c).obj K :=
  compactSupportConstantUnit A c i M ≫
    (rightDerivedGlobalSections (ModuleCat.{u + 1} A) c.Z).map
      (inv (compactSupportCoefficientExtension A c i M) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.map α)

/-- The canonical proper-support to compact-support map. This is precisely the
constant-section unit followed by the compact-support image of the support counit.
Source: blueprint Step 1, definition of u_Z
(blueprint: def-pur-proper-support-compact-maps). -/
def compactSupportFromProperSupport {B X Z : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (supportedSectionsDerived A i).obj K ⟶ (compactProductSections (ModuleCat.{u + 1} A) c).obj K :=
  compactSupportClassImage A c i ((supportedCoefficientDerivedAdjunction A i).counit.app K)

/-- Restriction on support complexes, as the transpose of the restricted support
counit through the canonical closed-coefficient restriction.
Source: blueprint Step 1, excision paragraph
(blueprint: def-pur-proper-support-compact-maps). -/
def compactProperSupportRestriction {B X Z : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)]
    (F : DerivedCategory (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (supportedCoefficientDerivedAdjunction A i).homEquiv _ _
    ((compactSupportDerivedCoefficientRestriction A c i).inv.app
        ((supportedSectionsDerived A (i ≫ c.i)).obj F) ≫
      (compactProductPullback (ModuleCat.{u + 1} A) c.i).map
        ((supportedCoefficientDerivedAdjunction A (i ≫ c.i)).counit.app F))

/-- Map from compact cohomology into any specified extension, adjoint to the inverse
of the specified restriction isomorphism. No arbitrary extension map is chosen.
Source: blueprint Step 1, excision paragraph
(blueprint: def-pur-proper-support-compact-maps). -/
def compactSupportToExtension {B X : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (F : DerivedCategory (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (e : (compactProductPullback (ModuleCat.{u + 1} A) c.i).obj F ≅ K) :=
  (rightDerivedGlobalSections (ModuleCat.{u + 1} A) c.Z).map
    (((derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) c.i).homEquiv _ _).symm e.inv)

/-- A product of proper supports is proper over the base.
Source: blueprint Step 1, product proper support
(blueprint: def-pur-proper-support-compact-maps).
Proof: the structure map factors into a base change of one proper structure map
and the other proper structure map. Proper maps are stable under base change and composition. -/
@[instance]
theorem compactProductSupportProper {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsProper (i ≫ f)] [IsProper (j ≫ g)] :
    IsProper (supportedProductImmersion f g i j ≫ pullback.toBase f g) := by
  sorry

/-- Excision with the specified restriction identification of an arbitrary extension.
Source: blueprint Step 1, excision paragraph
(blueprint: def-pur-proper-support-compact-maps). -/
def compactSupportExcisionMap {B X Z : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (F : DerivedCategory (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (e : (compactProductPullback (ModuleCat.{u + 1} A) c.i).obj F ≅ K) :=
  compactProperSupportRestriction A c i F ≫ (supportedSectionsDerived A i).map e.hom

/-- The identification with the recorded compact-support direct-image functor,
using the canonical composition comparison for derived global sections.
Source: blueprint Step 1, compact-support convention
(blueprint: def-pur-proper-support-compact-maps). -/
def compactProductDirectImageIso {B X : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) :
    compactProductSections (ModuleCat.{u + 1} A) c ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        rightDerivedGlobalSections (ModuleCat.{u + 1} A) B :=
  Functor.isoWhiskerLeft _
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u + 1} A) c.g).symm ≪≫
    (Functor.associator _ _ _).symm

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Restriction of supported constants along the compactifying open, uniquely
normalized on the constant quotient sections.
Source: blueprint Step 1, proper-support paragraph
(blueprint: def-pur-proper-support-compact-maps).
Proof: restriction to the open containing the entire closed support is the closed
base-change identification. Both quotient maps restrict the same constant sections.
The quotient is epic, so this normalization determines the isomorphism uniquely. -/
theorem compactSupportCoefficientRestriction_existsUnique
    {B X Z : Scheme.{u}} {f : X ⟶ B} (c : Compactification f) [IsLocallyNoetherian X]
      [IsLocallyNoetherian c.Z]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)] :
    ∃! e : supportedCoefficients A (i ≫ c.i) ⋙ upperStar (ModuleCat.{u + 1} A) c.i ≅
        supportedCoefficients A i,
      ∀ M : ModuleCat.{u + 1} A,
        (upperStar (ModuleCat.{u + 1} A) c.i).map
            (supportedCoefficientQuotient A (i ≫ c.i) M) ≫ e.hom.app M =
          (constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) c.i).hom.app M ≫
            supportedCoefficientQuotient A i M := by
  sorry

/-- The quotient-normalized closed-coefficient restriction.
Source: blueprint Step 1, proper-support paragraph
(blueprint: def-pur-proper-support-compact-maps). -/
def compactSupportCoefficientRestriction {B X Z : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) [IsLocallyNoetherian X] [IsLocallyNoetherian c.Z] (i : Z ⟶ X)
      [IsClosedImmersion i] [IsProper (i ≫ f)] :=
  (compactSupportCoefficientRestriction_existsUnique A c i).choose

/-- The same coefficient restriction on the derived categories.
Source: blueprint Step 1, proper-support paragraph
(blueprint: def-pur-proper-support-compact-maps). -/
def compactSupportDerivedCoefficientRestriction {B X Z : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) [IsLocallyNoetherian X] [IsLocallyNoetherian c.Z] (i : Z ⟶ X)
      [IsClosedImmersion i] [IsProper (i ≫ f)] :
    (supportedCoefficients A (i ≫ c.i)).mapDerivedCategory ⋙
      (upperStar (ModuleCat.{u + 1} A) c.i).mapDerivedCategory ≅
      (supportedCoefficients A i).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (compactSupportCoefficientRestriction A c i)

/-- The canonical `j_! i_* = bar_i_*` map, as the open-adjunction mate of the
normalized closed-coefficient restriction.
Source: blueprint Step 1, proper-support paragraph
(blueprint: def-pur-proper-support-compact-maps). -/
def compactSupportCoefficientExtension {B X Z : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) [IsLocallyNoetherian X] [IsLocallyNoetherian c.Z] (i : Z ⟶ X)
      [IsClosedImmersion i] [IsProper (i ≫ f)]
    (M : DerivedCategory (ModuleCat.{u + 1} A)) :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) c.i).homEquiv _ _).symm
      ((compactSupportDerivedCoefficientRestriction A c i).inv.app M)

/-- Properness makes the supported coefficient extension comparison invertible.
Source: blueprint Step 1, proper-support paragraph
(blueprint: def-pur-proper-support-compact-maps).
Proof: cover the compactification by the compactifying open and the complement
of the closed support. On the first open the comparison is the normalized
restriction isomorphism; on the second both supported coefficient sheaves vanish.
Sheaf locality makes the ordinary comparison invertible. The same calculation
holds termwise, and exact zero extension and restriction descend it to localization. -/
@[instance]
theorem compactSupportCoefficientExtension_isIso {B X Z : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) [IsLocallyNoetherian X] [IsLocallyNoetherian c.Z] (i : Z ⟶ X)
      [IsClosedImmersion i] [IsProper (i ≫ f)]
    (M : DerivedCategory (ModuleCat.{u + 1} A)) :
    IsIso (compactSupportCoefficientExtension A c i M) := by
  sorry

/-- The ordinary derived map forgetting support, using the recorded kernel inclusion.
Source: blueprint Step 1, forgetting supports
(blueprint: def-pur-proper-support-compact-maps). -/
def compactProductForget {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    supportedSectionsDerived A i ⟶ (Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1}
      A)).rightDerivedFunctor :=
  Functor.rightDerivedFunctorNatTrans (proEtaleSupportForget A i)

/-- The constant-section unit for the closed coefficient object in the compactification.
This is the support adjunction unit followed by the derived kernel inclusion, hence
is the unit M to RΓ(Z,constant M) under the normalized closed-support identification.
Source: blueprint Step 1, definition of u_Z
(blueprint: def-pur-proper-support-compact-maps). -/
def compactSupportConstantUnit {B X Z : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) [IsLocallyNoetherian X] [IsLocallyNoetherian c.Z] (i : Z ⟶ X)
      [IsClosedImmersion i] [IsProper (i ≫ f)]
    (M : DerivedCategory (ModuleCat.{u + 1} A)) :=
  (supportedCoefficientDerivedAdjunction A (i ≫ c.i)).unit.app M ≫
    (compactProductForget A (i ≫ c.i)).app
      ((supportedCoefficients A (i ≫ c.i)).mapDerivedCategory.obj M)

/-- Image of a supported morphism in compact cohomology: take its compact-support
direct image and precompose with the constant-section unit. M=A[0] and target K[a]
gives the stated formula on H^a, including negative degrees.
Source: blueprint Step 1, supported class formula
(blueprint: def-pur-proper-support-compact-maps). -/
def compactSupportClassImage {B X Z : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) [IsLocallyNoetherian X] [IsLocallyNoetherian c.Z] (i : Z ⟶ X)
      [IsClosedImmersion i] [IsProper (i ≫ f)]
    {M : DerivedCategory (ModuleCat.{u + 1} A)}
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (α : (supportedCoefficients A i).mapDerivedCategory.obj M ⟶ K) :
    M ⟶ ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory ⋙
      (Sheaf.Γ (Scheme.ProEt.topology c.Z) (ModuleCat.{u + 1} A)).rightDerivedFunctor).obj K :=
  compactSupportConstantUnit A c i M ≫
    ((Sheaf.Γ (Scheme.ProEt.topology c.Z) (ModuleCat.{u + 1} A)).rightDerivedFunctor).map
      (inv (compactSupportCoefficientExtension A c i M) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.map α)

/-- The canonical proper-support to compact-support map. This is precisely the
constant-section unit followed by the compact-support image of the support counit.
Source: blueprint Step 1, definition of u_Z
(blueprint: def-pur-proper-support-compact-maps). -/
def compactSupportFromProperSupport {B X Z : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) [IsLocallyNoetherian X] [IsLocallyNoetherian c.Z] (i : Z ⟶ X)
      [IsClosedImmersion i] [IsProper (i ≫ f)]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (supportedSectionsDerived A i).obj K ⟶ ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
      c.i).mapDerivedCategory ⋙
      (Sheaf.Γ (Scheme.ProEt.topology c.Z) (ModuleCat.{u + 1} A)).rightDerivedFunctor).obj K :=
  compactSupportClassImage A c i ((supportedCoefficientDerivedAdjunction A i).counit.app K)

/-- Restriction on support complexes, as the transpose of the restricted support
counit through the canonical closed-coefficient restriction.
Source: blueprint Step 1, excision paragraph
(blueprint: def-pur-proper-support-compact-maps). -/
def compactProperSupportRestriction {B X Z : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) [IsLocallyNoetherian X] [IsLocallyNoetherian c.Z] (i : Z ⟶ X)
      [IsClosedImmersion i] [IsProper (i ≫ f)]
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology c.Z) (ModuleCat.{u + 1} A))) :=
  (supportedCoefficientDerivedAdjunction A i).homEquiv _ _
    ((compactSupportDerivedCoefficientRestriction A c i).inv.app
        ((supportedSectionsDerived A (i ≫ c.i)).obj F) ≫
      ((upperStar (ModuleCat.{u + 1} A) c.i).mapDerivedCategory).map
        ((supportedCoefficientDerivedAdjunction A (i ≫ c.i)).counit.app F))

/-- Map from compact cohomology into any specified extension, adjoint to the inverse
of the specified restriction isomorphism. No arbitrary extension map is chosen.
Source: blueprint Step 1, excision paragraph
(blueprint: def-pur-proper-support-compact-maps). -/
def compactSupportToExtension {B X : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) [IsLocallyNoetherian X] [IsLocallyNoetherian c.Z]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology c.Z) (ModuleCat.{u + 1} A)))
    (e : ((upperStar (ModuleCat.{u + 1} A) c.i).mapDerivedCategory).obj F ≅ K) :=
  ((Sheaf.Γ (Scheme.ProEt.topology c.Z) (ModuleCat.{u + 1} A)).rightDerivedFunctor).map
    (((derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) c.i).homEquiv _ _).symm e.inv)

/-- Excision with the specified restriction identification of an arbitrary extension.
Source: blueprint Step 1, excision paragraph
(blueprint: def-pur-proper-support-compact-maps). -/
def compactSupportExcisionMap {B X Z : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) [IsLocallyNoetherian X] [IsLocallyNoetherian c.Z] (i : Z ⟶ X)
      [IsClosedImmersion i] [IsProper (i ≫ f)]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology c.Z) (ModuleCat.{u + 1} A)))
    (e : ((upperStar (ModuleCat.{u + 1} A) c.i).mapDerivedCategory).obj F ≅ K) :=
  compactProperSupportRestriction A c i F ≫ (supportedSectionsDerived A i).map e.hom

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {k : Type u} [Field k] {X Z : Scheme.{u}}

/-- The actual pro-etale unit/counit proper-support map over a field. The ambient
Noetherian instances are derived from the given finite-type structure maps.
Source: blueprint Step 1, proper-support maps on specified realizations
(blueprint: def-pur-proper-support-compact-maps). -/
def proCompactSupportOverField (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (c : Compactification f) (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  ProEtale.compactSupportFromProperSupport A c i K

/-- The supported-morphism type on the pro-etale site, with its ambient exactness
instance obtained from finite type, rather than imposed as a new hypothesis.
Source: blueprint Step 1, supported class formula
(blueprint: def-pur-proper-support-compact-maps). -/
def ProCompactSupportClassHom (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (M : DerivedCategory (ModuleCat.{u + 1} A))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  (ProEtale.supportedCoefficients A i).mapDerivedCategory.obj M ⟶ K

/-- Transpose of the actual supported morphism under the pro-etale support
adjunction. Source: blueprint Step 1, supported class formula
(blueprint: def-pur-proper-support-compact-maps). -/
def proCompactSupportClassAdjoint (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (M : DerivedCategory (ModuleCat.{u + 1} A))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (α : ProCompactSupportClassHom A f i M K) :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  (ProEtale.supportedCoefficientDerivedAdjunction A i).homEquiv _ _ α

/-- Compact image of the supported pro-etale morphism, using the actual
constant-section unit and exact extension by zero.
Source: blueprint Step 1, supported class formula
(blueprint: def-pur-proper-support-compact-maps). -/
def proCompactSupportClassImage (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (c : Compactification f) (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)]
    (M : DerivedCategory (ModuleCat.{u + 1} A))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (α : ProCompactSupportClassHom A f i M K) :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  ProEtale.compactSupportClassImage A c i α

/-- Excision for an arbitrary specified pro-etale extension over the field.
Source: blueprint Step 1, excision on specified realizations
(blueprint: def-pur-proper-support-compact-maps). -/
def proCompactSupportExcision (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (c : Compactification f) (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology c.Z) (ModuleCat.{u + 1} A)))
    (e : (ProEtale.upperStar (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj F ≅ K) :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  ProEtale.compactSupportExcisionMap A c i K F e

/-- The map to an arbitrary pro-etale extension, induced by the open-adjunction
mate of its specified restriction isomorphism.
Source: blueprint Step 1, excision on specified realizations
(blueprint: def-pur-proper-support-compact-maps). -/
def proCompactSupportToExtension (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (c : Compactification f)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology c.Z) (ModuleCat.{u + 1} A)))
    (e : (ProEtale.upperStar (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj F ≅ K) :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  ProEtale.compactSupportToExtension A c K F e

end AlgebraicGeometry.Etale
