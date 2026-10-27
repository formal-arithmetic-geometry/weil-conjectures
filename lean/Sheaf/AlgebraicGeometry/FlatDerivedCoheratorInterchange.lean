/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedCoheratorAdjunction
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.FlatModulePullbackExact
import Sheaf.AlgebraicGeometry.QuasiCoherentGrothendieckGenerators
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
import Sheaf.CategoryTheory.ExactSquareRightDerivedUnit
import Sheaf.CategoryTheory.DerivedCategory.AdjointSquareComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift
import Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection

/-!
# Flat direct image and the normalized derived coherator interchange

Source: Stacks Project, Tag 08D8, lemma-flat-pushforward-coherator, and the
adjunction maps used in Tag 09T6
(blueprint: lem-sfb-flat-derived-coherator-interchange).

The restrictions are Mathlib full-subcategory lifts of the actual tensor pullback
and sectionwise pushforward. The package asserts their exactness and derived
adjunctions; it does not assume those conclusions. All comparisons use the
recorded unbounded derived functors and their units.
-/

@[expose] public section

set_option autoImplicit false

universe u wZ wY uA uB uC uD vA vB vC vD wA wB wC wD

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Restrict tensor pullback to the existing full quasi-coherent categories.
Source: Stacks Tag 08D8 (blueprint: lem-sfb-flat-derived-coherator-interchange). -/
noncomputable def flatCoheratorPullback {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    (h : ∀ M : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory,
      ((tensorPullback f).obj M.obj).IsQuasicoherent) :
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Z.ringCatSheaf).FullSubcategory :=
  (SheafOfModules.isQuasicoherent Z.ringCatSheaf).lift
    ((SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι ⋙ tensorPullback f) h

/-- Restrict the actual module pushforward to the full quasi-coherent categories.
Source: Stacks Tag 08D8 (blueprint: lem-sfb-flat-derived-coherator-interchange). -/
noncomputable def flatCoheratorPushforward {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    (h : ∀ M : (SheafOfModules.isQuasicoherent Z.ringCatSheaf).FullSubcategory,
      ((pushforward f).obj M.obj).IsQuasicoherent) :
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).lift
    ((SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι ⋙ pushforward f) h

/-- Express a homotopy-category derived unit on an actual complex, using the
canonical quotient/localization comparisons, in the direction QF to RFQ.
Source: Stacks Tags 070K, 070Y and 08D8
(blueprint: lem-sfb-flat-derived-coherator-interchange). -/
noncomputable def flatCoheratorLocalizedUnit
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] (RF : DerivedCategory A ⥤ DerivedCategory B)
    (η : F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (K : CochainComplex A ℤ) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      RF.obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso B).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
    DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).inv.app K) ≫
    η.app ((HomotopyCategory.quotient A (.up ℤ)).obj K) ≫
    RF.map ((DerivedCategory.quotientCompQhIso A).hom.app K)

/-- The canonical comparison of the two composite right adjoints, obtained from
exactly the four Hom identifications of Tag 08D8. No isomorphism is chosen.
Source: Stacks Tag 08D8 (blueprint: lem-sfb-flat-derived-coherator-interchange). -/
noncomputable def flatCoheratorRightAdjointComparison
    {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
    {IY : A ⥤ B} {IZ : C ⥤ D} {CY : B ⥤ A} {CZ : D ⥤ C}
    {P : A ⥤ C} {Φ : C ⥤ A} {K : B ⥤ D} {R : D ⥤ B}
    (eY : IY ⊣ CY) (eZ : IZ ⊣ CZ) (a : P ⊣ Φ) (b : K ⊣ R)
    (s : P ⋙ IZ ≅ IY ⋙ K) : R ⋙ CY ≅ CZ ⋙ Φ :=
  ((eY.comp b).ofNatIsoLeft s.symm).rightAdjointUniq (a.comp eZ)

/-- The three normalized identities, with the exact pullback/inclusion comparison
explicit in the third one. The first two use the canonical comparison just defined.
Source: Stacks Tags 08D8 and 09T6
(blueprint: lem-sfb-flat-derived-coherator-interchange). -/
def FlatCoheratorInterchangeIdentities
    {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
    {IY : A ⥤ B} {IZ : C ⥤ D} {CY : B ⥤ A} {CZ : D ⥤ C}
    {P : A ⥤ C} {Φ : C ⥤ A} {K : B ⥤ D} {R : D ⥤ B}
    (eY : IY ⊣ CY) (eZ : IZ ⊣ CZ) (a : P ⊣ Φ) (b : K ⊣ R)
    (s : P ⋙ IZ ≅ IY ⋙ K) (c : Φ ⋙ IY ≅ IZ ⋙ R) : Prop :=
  (∀ B₀ : C, eY.unit.app (Φ.obj B₀) ≫ CY.map (c.hom.app B₀) ≫
      (flatCoheratorRightAdjointComparison eY eZ a b s).hom.app (IZ.obj B₀) =
        Φ.map (eZ.unit.app B₀)) ∧
    (∀ E : D, eY.counit.app (R.obj E) =
      IY.map ((flatCoheratorRightAdjointComparison eY eZ a b s).hom.app E) ≫
        c.hom.app (CZ.obj E) ≫ R.map (eZ.counit.app E)) ∧
    (∀ H : A, IY.map (a.unit.app H) ≫ c.hom.app (P.obj H) =
      b.unit.app (IY.obj H) ≫ R.map (s.inv.app H))

/-- All constructions and identities, parametrized by the actual ordinary
inclusion square to avoid changing any of its abelian structures.
Source: Stacks Tags 08D8, 070K, 09T5 and 09T6
(blueprint: lem-sfb-flat-derived-coherator-interchange). -/
structure FlatDerivedCoheratorInterchangeData
    {AZ : Type uA} {AY : Type uB} {MZ : Type uC} {MY : Type uD}
    [Category.{vA} AZ] [Category.{vB} AY] [Category.{vC} MZ] [Category.{vD} MY]
    [Abelian AZ] [Abelian AY] [Abelian MZ] [Abelian MY]
    [HasDerivedCategory.{wA} AZ] [HasDerivedCategory.{wB} AY]
    [HasDerivedCategory.{wC} MZ] [HasDerivedCategory.{wD} MY]
    (iZ : AZ ⥤ MZ) (iY : AY ⥤ MY) [iZ.Additive] [iY.Additive]
    [PreservesFiniteLimits iZ] [PreservesFiniteColimits iZ]
    [PreservesFiniteLimits iY] [PreservesFiniteColimits iY]
    (P₀ : AY ⥤ AZ) (F : AZ ⥤ AY) (K₀ : MY ⥤ MZ) (G : MZ ⥤ MY) [G.Additive]
    (ordinaryModuleAdjunction : K₀ ⊣ G)
    (a₀ : P₀ ⋙ iZ ≅ iY ⋙ K₀) (c₀ : F ⋙ iY ≅ iZ ⋙ G)
    (R : DerivedCategory MZ ⥤ DerivedCategory MY)
    (ηG : G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    [R.CommShift ℤ]
    (CZ : DerivedCategory MZ ⥤ DerivedCategory AZ)
    (CY : DerivedCategory MY ⥤ DerivedCategory AY) [CZ.CommShift ℤ] [CY.CommShift ℤ]
    (eZ : iZ.mapDerivedCategory ⊣ CZ) (eY : iY.mapDerivedCategory ⊣ CY) where
  /-- Flatness gives additivity and exactness of module tensor pullback. -/
  [modulePullbackAdditive : K₀.Additive]
  [modulePullbackFiniteLimits : PreservesFiniteLimits K₀]
  [modulePullbackFiniteColimits : PreservesFiniteColimits K₀]
  /-- Exactness and additivity of the restricted tensor pullback. -/
  [pullbackAdditive : P₀.Additive]
  [pullbackFiniteLimits : PreservesFiniteLimits P₀]
  [pullbackFiniteColimits : PreservesFiniteColimits P₀]
  /-- Additivity of quasi-coherent direct image. -/
  [pushforwardAdditive : F.Additive]
  /-- Unbounded resolutions, with no extra monicity requirement. -/
  resolutions : ∀ K : CochainComplex AZ ℤ,
    ∃ (J : CochainComplex AZ ℤ) (s : K ⟶ J), J.IsKInjective ∧ QuasiIso s
  /-- The restricted ordinary adjunction. -/
  ordinaryAdjunction : P₀ ⊣ F
  /-- Its Hom bijection is the restriction of the module Hom bijection. -/
  ordinaryNormalization : ∀ (M : AY) (N : AZ) (t : P₀.obj M ⟶ N),
    ordinaryModuleAdjunction.homEquiv (iY.obj M) (iZ.obj N)
        (a₀.inv.app M ≫ iZ.map t) =
      iY.map (ordinaryAdjunction.homEquiv M N t) ≫ c₀.hom.app N
  /-- The right functor is precisely the recorded total unbounded derived functor. -/
  adjunction : P₀.mapDerivedCategory ⊣ F.rightDerivedFunctorOfQuasiIsoResolutions resolutions
  /-- Its normalization is the canonical derived-adjunction formula. -/
  derivedNormalization : ∀ (M : HomotopyCategory AY (.up ℤ))
    (N : HomotopyCategory AZ (.up ℤ)) (t : (P₀.mapHomotopyCategory (.up ℤ)).obj M ⟶ N),
    adjunction.homEquiv (DerivedCategory.Qh.obj M) (DerivedCategory.Qh.obj N)
        (P₀.mapDerivedCategoryFactorsh.hom.app M ≫ DerivedCategory.Qh.map t) =
      DerivedCategory.Qh.map
        ((ordinaryAdjunction.mapHomotopyCategory (.up ℤ)).homEquiv M N t) ≫
      (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit resolutions).app N
  /-- Exact module tensor pullback is left adjoint to the actual derived direct image. -/
  moduleAdjunction : K₀.mapDerivedCategory ⊣ R
  /-- The module adjunction is induced using the K-injective derived comparison unit. -/
  moduleNormalization : ∀ (M : HomotopyCategory MY (.up ℤ))
    (N : HomotopyCategory MZ (.up ℤ)) (t : (K₀.mapHomotopyCategory (.up ℤ)).obj M ⟶ N),
    moduleAdjunction.homEquiv (DerivedCategory.Qh.obj M) (DerivedCategory.Qh.obj N)
        (K₀.mapDerivedCategoryFactorsh.hom.app M ≫ DerivedCategory.Qh.map t) =
      DerivedCategory.Qh.map
        ((ordinaryModuleAdjunction.mapHomotopyCategory (.up ℤ)).homEquiv M N t) ≫ ηG.app N
  /-- Canonical shift structure on the quasi-coherent right-derived functor. -/
  [shift : (F.rightDerivedFunctorOfQuasiIsoResolutions resolutions).CommShift ℤ]
  /-- Its derived unit fixes that shift structure on K-injective representatives. -/
  canonicalShift : NatTrans.CommShift
    (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit resolutions) ℤ
  /-- The quasi-coherent right-derived direct image is triangulated. -/
  [triangulated : (F.rightDerivedFunctorOfQuasiIsoResolutions resolutions).IsTriangulated]
  /-- Units and counits commute with those same shift comparisons. -/
  compatible : adjunction.CommShift ℤ
  moduleCompatible : moduleAdjunction.CommShift ℤ
  /-- The exact derived pullback/inclusion identification. -/
  pullbackInclusion : P₀.mapDerivedCategory ⋙ iZ.mapDerivedCategory ≅
    iY.mapDerivedCategory ⋙ K₀.mapDerivedCategory
  /-- Its value is exactly the localized ordinary square. -/
  pullbackInclusionNormalization : pullbackInclusion =
    (Functor.mapDerivedCategoryCompIso P₀ iZ).symm ≪≫
      Functor.mapDerivedCategoryNatIso a₀ ≪≫ Functor.mapDerivedCategoryCompIso iY K₀
  /-- The canonical right-adjoint comparison commutes with the fixed shifts. -/
  comparisonShift : NatTrans.CommShift
    (flatCoheratorRightAdjointComparison eY eZ adjunction moduleAdjunction
      pullbackInclusion).hom ℤ
  /-- Exactly the hypothesis on c in the node, followed by all three identities.
  It uses the canonical derived module unit on every complex, not preservation of
  K-injectives by the inclusion. -/
  identities : ∀ c : F.rightDerivedFunctorOfQuasiIsoResolutions resolutions ⋙
      iY.mapDerivedCategory ≅ iZ.mapDerivedCategory ⋙ R,
    (∀ B : CochainComplex AZ ℤ,
      iY.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj B) ≫
        iY.mapDerivedCategory.map (flatCoheratorLocalizedUnit F
          (F.rightDerivedFunctorOfQuasiIsoResolutions resolutions)
          (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit resolutions) B) ≫
        c.hom.app (DerivedCategory.Q.obj B) =
      DerivedCategory.Q.map ((c₀.hom.mapHomologicalComplex (.up ℤ)).app B) ≫
        flatCoheratorLocalizedUnit G R ηG ((iZ.mapHomologicalComplex (.up ℤ)).obj B) ≫
        R.map (iZ.mapDerivedCategoryFactors.inv.app B)) →
    FlatCoheratorInterchangeIdentities eY eZ adjunction moduleAdjunction pullbackInclusion c

/-- Specialize to the exact abelian/localization structures of the given coherators.
The two predicates in the dependent sum assert that the actual module functors land
in the existing quasi-coherent subcategories; they are conclusions, not hypotheses.
Source: Stacks Tag 08D8 (blueprint: lem-sfb-flat-derived-coherator-interchange). -/
noncomputable def flatDerivedCoheratorInterchangeType {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} Z.ringCatSheaf)]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} Y.ringCatSheaf)]
    (dZ : DerivedCoheratorAdjunctionData
      (SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι)
    (dY : DerivedCoheratorAdjunctionData
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι) : Type _ := by
  letI := dZ.abelian
  letI := dZ.derivedCategory
  letI := dZ.inclusionAdditive
  letI := dZ.inclusionFiniteLimits
  letI := dZ.inclusionFiniteColimits
  letI := dY.abelian
  letI := dY.derivedCategory
  letI := dY.inclusionAdditive
  letI := dY.inclusionFiniteLimits
  letI := dY.inclusionFiniteColimits
  letI := dZ.additive
  letI := dY.additive
  letI : (pushforward f).Additive :=
    RingedSpace.moduleDirectImage_additive f.toLRSHom.toShHom
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u} Z.ringCatSheaf) :=
    RingedSpace.moduleGrothendieckAbelian Z.toRingedSpace
  letI : Abelian.HasKInjectiveResolutions (SheafOfModules.{u} Z.ringCatSheaf) :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  letI : (schemeDerivedDirectImage f).CommShift ℤ :=
    Functor.instCommShiftDerivedCategoryRightDerivedFunctorInt
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom)
  letI := dZ.shift
  letI := dY.shift
  exact Σ' (hP : ∀ M : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory,
      ((tensorPullback f).obj M.obj).IsQuasicoherent)
    (hF : ∀ M : (SheafOfModules.isQuasicoherent Z.ringCatSheaf).FullSubcategory,
      ((pushforward f).obj M.obj).IsQuasicoherent),
    FlatDerivedCoheratorInterchangeData
      (SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι
      (flatCoheratorPullback f hP) (flatCoheratorPushforward f hF)
      (tensorPullback f) (pushforward f) (tensorPullbackSectionAdjunction f)
      (Iso.refl ((SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι ⋙ tensorPullback f))
      (Iso.refl ((SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι ⋙ pushforward f))
      (schemeDerivedDirectImage f)
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit
      (dZ.coherator.rightDerivedFunctorOfQuasiIsoResolutions dZ.resolutions)
      (dY.coherator.rightDerivedFunctorOfQuasiIsoResolutions dY.resolutions)
      dZ.derivedAdjunction dY.derivedAdjunction

/-- Flat quasi-compact quasi-separated direct image commutes with the unbounded
derived coherator, with the normalized unit and counit identities.
Source: Stacks Tag 08D8, lemma-flat-pushforward-coherator, and the normalized
adjunction maps used in Tag 09T6 (blueprint: lem-sfb-flat-derived-coherator-interchange).

Proof:
1. Quasi-coherent pushforward exists by `pqf-lem-pushforward-qcoh`. Pullback preserves
   quasi-coherence by `lem-weil-pbc-module-pullback-quasi-coherent`; flatness makes
   tensor pullback exact by `lem-weil-pbc-flat-module-pullback-exact-pushforward-injective`.
   The exact full inclusions reflect exactness, so their restrictions are exact.
   Restrict the actual tensor/module adjunction to obtain the ordinary Hom bijection.
2. `lem-sfb-qcoh-grothendieck-generators` and
   `lem-pc-scheme-modules-grothendieck-abelian` give unbounded K-injective resolutions.
   Apply `lem-weil-pbc-kinjective-total-derived` and `def-sfb-right-derived-functor`
   to the actual restricted direct image. Exact-functor factorization gives P and K.
   `lem-pc-derived-adjoint-functors` and `lem-pc-ringed-spaces-derived-adjoint` give
   their induced adjunctions and exactly the displayed derived-unit normalizations.
3. Compose the inclusion/coherator and pullback/direct-image Hom bijections. Using
   the canonical exact-square identification, `def-weil-pbc-composite-adjunction`
   and `det-sp-unique-right-adjoint` give the explicitly defined comparison lambda.
4. `lem-sfb-exact-square-right-derived-unit` identifies the supplied normalized c
   uniquely. `lem-kun-derived-adjoint-square-comparison` then gives its unit equation
   (the third identity) and its counit equation IZ(w) = epsilon K(c).
5. Transpose the first identity through the four Hom bijections of step 3. Both
   inverse transposes equal IZ(w), by step 4, counit naturality and the triangle
   identities for the supplied coherator adjunctions. This proves the first identity.
6. Transpose the second identity under K adjoint R. Its two inverse transposes
   agree by step 4 and the defining composite-counit equation for lambda. Injectivity
   of the Hom bijection proves the second identity.
7. Exact derived functors have their canonical shifts. The right-derived unit
   determines the right-derived shifts on K-injectives and hence on resolutions.
   `lem-pc-right-derived-functor-triangulated` and
   `lem-sp-canonical-right-derived-adjunction-shift` give the stated triangulated
   structures and shift-compatible adjunctions. The defining Hom bijections for
   lambda commute with shifts, so uniqueness gives its shift compatibility. -/
theorem exists_flatDerivedCoheratorInterchange {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [Flat f] [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} Z.ringCatSheaf)]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} Y.ringCatSheaf)]
    (dZ : DerivedCoheratorAdjunctionData
      (SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι)
    (dY : DerivedCoheratorAdjunctionData
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι) :
    Nonempty (flatDerivedCoheratorInterchangeType f dZ dY) := by
  sorry

/-- In particular the entire interchange package applies to every affine open of
an arbitrary quasi-compact quasi-separated scheme, including the empty affine open.
Source: Stacks Tag 09T6, application of Tag 08D8
(blueprint: lem-sfb-flat-derived-coherator-interchange).

Proof (step 8 of the node): an affine open U is quasi-compact by
`lem-weil-pbc-affine-scheme-qcqs`. Its intersection with every affine open of Y is
quasi-compact by `pqf-lem-qs-intersection-qc`, hence its inclusion is quasi-compact.
The inclusion's stalk maps are isomorphisms, hence flat; its diagonal is an
isomorphism, hence quasi-compact. Thus it is quasi-separated. Apply the preceding
theorem with the same supplied coherator adjunctions and their actual units/counits. -/
theorem exists_flatDerivedCoheratorInterchange_affineOpen (Y : Scheme.{u})
    [CompactSpace Y] [QuasiSeparatedSpace Y] (U : Y.Opens) (hU : IsAffineOpen U)
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} U.toScheme.ringCatSheaf)]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} Y.ringCatSheaf)]
    (dU : DerivedCoheratorAdjunctionData
      (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι)
    (dY : DerivedCoheratorAdjunctionData
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι) :
    Nonempty (flatDerivedCoheratorInterchangeType U.ι dU dY) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
