/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.WitnessCompatibility
public import Sheaf.Paper.FiniteDirectImageComposition
public import Sheaf.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import Sheaf.Paper.EtaleProEtaleScalarMate
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.EtaleDirectImageVanishing
import Sheaf.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities
import Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.DirectImageTorAmplitude
import Sheaf.Paper.EtaleUnboundedRestrictionComparison
import Sheaf.Paper.FiniteCoefficientFlatModel
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat

/-!
# Finite coefficient change for ordinary direct image

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-biduality-general,
node order 2130 (blueprint: lem-coef-finite-direct-image).

Scalar extension is the published left adjoint to exact derived restriction.
The coefficient map is uniquely fixed by its scalar-unit/counit equation in D(B).
The equation is the scalar-adjunction form of extending the A-coefficient counit.
It does not use faithfulness of derived scalar restriction.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

private theorem coefficient_existsUnique
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (P : A ⥤ B) (Q : B ⥤ A) (adjA : Q ⊣ P)
    (P' : C ⥤ D) (Q' : D ⥤ C) (adjB : Q' ⊣ P')
    (S : B ⥤ D) (R : D ⥤ B) (adjX : S ⊣ R)
    (S' : A ⥤ C) (R' : C ⥤ A) (adjT : S' ⊣ R')
    (e : R ⋙ Q ≅ Q' ⋙ R')
    (hk : IsIso (((mateEquiv adjX adjT).symm
      (TwoSquare.mk _ _ _ _ e.hom)).natTrans)) (K : A) :
    ∃! c : S.obj (P.obj K) ⟶ P'.obj (S'.obj K),
      Q.map (adjX.unit.app (P.obj K)) ≫ e.hom.app (S.obj (P.obj K)) ≫
        R'.map (Q'.map c ≫ adjB.counit.app (S'.obj K)) =
          adjA.counit.app K ≫ adjT.unit.app K := by
  let k := ((mateEquiv adjX adjT).symm (TwoSquare.mk _ _ _ _ e.hom)).natTrans
  have : IsIso k := hk
  let t := inv (k.app (P.obj K)) ≫ S'.map (adjA.counit.app K)
  let c := adjB.homEquiv _ _ t
  have hunit := unit_mateEquiv_symm adjX adjT (TwoSquare.mk _ _ _ _ e.hom) (P.obj K)
  have hc : Q'.map c ≫ adjB.counit.app (S'.obj K) = t := by
    exact (adjB.homEquiv _ _).symm_apply_apply t
  have eqn (d : S.obj (P.obj K) ⟶ P'.obj (S'.obj K)) :
      Q.map (adjX.unit.app (P.obj K)) ≫ e.hom.app (S.obj (P.obj K)) ≫
        R'.map (Q'.map d ≫ adjB.counit.app (S'.obj K)) =
      adjT.homEquiv _ _ (k.app (P.obj K) ≫
        (Q'.map d ≫ adjB.counit.app (S'.obj K))) := by
    rw [Adjunction.homEquiv_unit]
    rw [← Category.assoc, hunit]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  refine ⟨c, ?_, ?_⟩
  · dsimp only
    rw [eqn, hc]
    dsimp only [t]
    rw [IsIso.hom_inv_id_assoc, Adjunction.homEquiv_unit]
    exact adjT.unit.naturality (adjA.counit.app K) |>.symm
  · intro d hd
    rw [eqn] at hd
    have hc' : adjT.homEquiv _ _ (k.app (P.obj K) ≫
        (Q'.map c ≫ adjB.counit.app (S'.obj K))) =
        adjA.counit.app K ≫ adjT.unit.app K := by
      rw [hc]
      dsimp only [t]
      rw [IsIso.hom_inv_id_assoc, Adjunction.homEquiv_unit]
      exact adjT.unit.naturality (adjA.counit.app K) |>.symm
    apply (adjB.homEquiv _ _).symm.injective
    apply (cancel_epi (k.app (P.obj K))).mp
    exact (adjT.homEquiv _ _).injective (hd.trans hc'.symm)

private theorem coefficient_naturality
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (P : A ⥤ B) (Q : B ⥤ A) (adjA : Q ⊣ P)
    (P' : C ⥤ D) (Q' : D ⥤ C) (adjB : Q' ⊣ P')
    (S : B ⥤ D) (R : D ⥤ B) (adjX : S ⊣ R)
    (S' : A ⥤ C) (R' : C ⥤ A) (adjT : S' ⊣ R')
    (e : R ⋙ Q ≅ Q' ⋙ R')
    (hk : IsIso (((mateEquiv adjX adjT).symm
      (TwoSquare.mk _ _ _ _ e.hom)).natTrans))
    (c : ∀ K, S.obj (P.obj K) ⟶ P'.obj (S'.obj K))
    (hu : ∀ K (d : S.obj (P.obj K) ⟶ P'.obj (S'.obj K)),
      Q.map (adjX.unit.app (P.obj K)) ≫ e.hom.app (S.obj (P.obj K)) ≫
        R'.map (Q'.map d ≫ adjB.counit.app (S'.obj K)) =
          adjA.counit.app K ≫ adjT.unit.app K → d = c K)
    {K L : A} (h : K ⟶ L) :
    S.map (P.map h) ≫ c L = c K ≫ P'.map (S'.map h) := by
  let k := ((mateEquiv adjX adjT).symm (TwoSquare.mk _ _ _ _ e.hom)).natTrans
  have : IsIso k := hk
  let γ := (mateEquiv adjA adjB (TwoSquare.mk _ _ _ _ (asIso k).inv)).natTrans
  have heq (M : A) : γ.app M = c M := by
    apply hu M
    have hunit := unit_mateEquiv_symm adjX adjT
      (TwoSquare.mk _ _ _ _ e.hom) (P.obj M)
    change Q.map (adjX.unit.app (P.obj M)) ≫ e.hom.app (S.obj (P.obj M)) =
      adjT.unit.app (Q.obj (P.obj M)) ≫ R'.map (k.app (P.obj M)) at hunit
    have hc := mateEquiv_counit adjA adjB (TwoSquare.mk _ _ _ _ (asIso k).inv) M
    change Q'.map (γ.app M) ≫ adjB.counit.app (S'.obj M) =
      (asIso k).inv.app (P.obj M) ≫ S'.map (adjA.counit.app M) at hc
    rw [hc, ← Category.assoc, hunit, Category.assoc, ← R'.map_comp]
    change adjT.unit.app _ ≫
      R'.map ((asIso k).hom.app _ ≫ (asIso k).inv.app _ ≫ _) = _
    rw [Iso.hom_inv_id_app_assoc]
    exact (adjT.unit.naturality (adjA.counit.app M)).symm
  simpa only [Functor.comp_map, heq] using γ.naturality h

/-- Explicit size witness for the small etale site; no universe equality is imposed.
Source: Mathlib essentiallySmall_of_small_of_locallySmall; blueprint order 2130
(blueprint: lem-coef-finite-direct-image). -/
instance AlgebraicGeometry.Etale.finiteCoefficientSiteSize (X : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

namespace AlgebraicGeometry.Etale

/-- Canonical exact restriction/pullback comparison, in the unbounded categories.
Source: blueprint order 2130; Stacks Tags 07A4 and 07A6
(blueprint: lem-coef-finite-direct-image). -/
def finiteCoefficientRestrictionPullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) :
    Sheaf.derivedRestrictScalars (X.smallEtaleTopology) φ ⋙
        L(upperStar (ModuleCat.{u + 1} A) f) ≅
      L(upperStar (ModuleCat.{u + 1} B) f) ⋙
        Sheaf.derivedRestrictScalars (T.smallEtaleTopology) φ :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) ≪≫
    Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ f) ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f).symm _

/-- The equation fixing the coefficient projection map. Precomposing its B-counit
transpose with the pulled-back scalar unit gives the A-counit followed by the input
scalar unit. This is precisely extension of the counit after pullback/scalar
extension, expressed without choosing flat resolutions or an arbitrary comparison.
Source: blueprint order 2130, statement and proof Step 3; Stacks Tag 07A6
(blueprint: lem-coef-finite-direct-image). -/
def IsFiniteCoefficientDirectImageMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A)))
    (c : (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (X.smallEtaleTopology) φ).obj
      ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K) ⟶
      (R(lowerStar (ModuleCat.{u + 1} B) f)).obj
        ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (T.smallEtaleTopology) φ).obj K)) :
    Prop :=
  L(upperStar (ModuleCat.{u + 1} A) f).map
      ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars (X.smallEtaleTopology) φ)).unit.app
          ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K)) ≫
    (finiteCoefficientRestrictionPullback φ f).hom.app
      ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (X.smallEtaleTopology) φ).obj
        ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K)) ≫
    (Sheaf.derivedRestrictScalars (T.smallEtaleTopology) φ).map
      (L(upperStar (ModuleCat.{u + 1} B) f).map c ≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).counit.app
          ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (T.smallEtaleTopology) φ).obj K)) =
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app K ≫
      (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars (T.smallEtaleTopology) φ)).unit.app K

/-- Existence and uniqueness of the specified coefficient map, without finiteness or
flatness of the coefficient morphism. These are properties of its construction.
Source: blueprint order 2130, coefficient-map definition and proof Steps 2--3
(blueprint: lem-coef-finite-direct-image).

Proof: use lem-pur-derived-change-of-rings to compute scalar extension on flat K-flat
representatives. Inverse image commutes with it by the canonical balancing comparison
of lem-weil-pbc-ringed-topoi-derived-tensor-pullback. Transpose scalar extension of the
A-counit through the B inverse-image/direct-image adjunction. The scalar adjunction
unit identity gives the displayed equation. Conversely that equation determines the
B-transpose by universality of the pulled-back scalar unit, then determines the map
by injectivity of the B geometric adjunction. No isomorphism assertion is used here. -/
theorem finiteCoefficientDirectImageMap_existsUnique
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A))) :
    ∃! c : (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (X.smallEtaleTopology) φ).obj
      ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K) ⟶
      (R(lowerStar (ModuleCat.{u + 1} B) f)).obj
        ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (T.smallEtaleTopology) φ).obj K),
      IsFiniteCoefficientDirectImageMap φ f K c := by
  exact coefficient_existsUnique _ _
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f) _ _
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f) _ _
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)) _ _
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
    (finiteCoefficientRestrictionPullback φ f) (ProEtale.scalarPullbackReverse_isIso φ f).2 K

/-- The actual B-linear coefficient projection map, chosen from a theorem that
uniquely determines it by the extended counit. Only that proof is postponed.
Source: blueprint order 2130 (blueprint: lem-coef-finite-direct-image). -/
def finiteCoefficientDirectImageMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A))) :
    (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (X.smallEtaleTopology) φ).obj
      ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K) ⟶
      (R(lowerStar (ModuleCat.{u + 1} B) f)).obj
        ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (T.smallEtaleTopology) φ).obj K) :=
  (finiteCoefficientDirectImageMap_existsUnique φ f K).choose

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- The equation fixing the coefficient projection map. Precomposing its B-counit
transpose with the pulled-back scalar unit gives the A-counit followed by the input
scalar unit. This is precisely extension of the counit after pullback/scalar
extension, expressed without choosing flat resolutions or an arbitrary comparison.
Source: blueprint order 2130, statement and proof Step 3; Stacks Tag 07A6
(blueprint: lem-coef-finite-direct-image). -/
def IsFiniteCoefficientDirectImageMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (c : (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).obj
      ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K) ⟶
      (R(lowerStar (ModuleCat.{u + 1} B) f)).obj
        ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology T) φ).obj K)) :
    Prop :=
  L(upperStar (ModuleCat.{u + 1} A) f).map
      ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ)).unit.app
          ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K)) ≫
    (leftDerivedUpperStarRestrictScalarsIso φ f).hom.app
      ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).obj
        ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K)) ≫
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ).map
      (L(upperStar (ModuleCat.{u + 1} B) f).map c ≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).counit.app
          ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology T) φ).obj K))
            =
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app K ≫
      (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ)).unit.app K

/-- Existence and uniqueness of the specified coefficient map, without finiteness or
flatness of the coefficient morphism. These are properties of its construction.
Source: blueprint order 2130, coefficient-map definition and proof Steps 2--3
(blueprint: lem-coef-finite-direct-image).

Proof: use lem-pur-derived-change-of-rings to compute scalar extension on flat K-flat
representatives. Inverse image commutes with it by the canonical balancing comparison
of lem-weil-pbc-ringed-topoi-derived-tensor-pullback. Transpose scalar extension of the
A-counit through the B inverse-image/direct-image adjunction. The scalar adjunction
unit identity gives the displayed equation. Conversely that equation determines the
B-transpose by universality of the pulled-back scalar unit, then determines the map
by injectivity of the B geometric adjunction. No isomorphism assertion is used here. -/
theorem finiteCoefficientDirectImageMap_existsUnique
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    ∃! c : (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).obj
      ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K) ⟶
      (R(lowerStar (ModuleCat.{u + 1} B) f)).obj
        ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology T) φ).obj K),
      IsFiniteCoefficientDirectImageMap φ f K c := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let aa := derivedUpperStarLowerStarAdjunction.{u + 2, u} (ModuleCat.{u + 1} A) f
  let ab := derivedUpperStarLowerStarAdjunction.{u + 2, u} (ModuleCat.{u + 1} B) f
  let ax := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X) φ)
  let adt := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology T) φ)
  let e := leftDerivedUpperStarRestrictScalarsIso.{u} φ f
  have hk := (scalarPullbackReverse_isIso.{u} φ f).1
  exact @coefficient_existsUnique.{u + 2, u + 2, u + 2, u + 2,
      u + 1, u + 1, u + 1, u + 1}
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} B)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)))
    inferInstance inferInstance inferInstance inferInstance
    (R(lowerStar (ModuleCat.{u + 1} A) f)) (L(upperStar (ModuleCat.{u + 1} A) f)) aa
    (R(lowerStar (ModuleCat.{u + 1} B) f)) (L(upperStar (ModuleCat.{u + 1} B) f)) ab
    (pbcFixedScalarExtension (Scheme.ProEt.topology X) φ)
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ) ax
    (pbcFixedScalarExtension (Scheme.ProEt.topology T) φ)
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ) adt e hk K

/-- The actual B-linear coefficient projection map, chosen from a theorem that
uniquely determines it by the extended counit. Only that proof is postponed.
Source: blueprint order 2130 (blueprint: lem-coef-finite-direct-image). -/
def finiteCoefficientChangeDirectImageMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).obj
      ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K) ⟶
      (R(lowerStar (ModuleCat.{u + 1} B) f)).obj
        ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology T) φ).obj K) :=
  (finiteCoefficientDirectImageMap_existsUnique φ f K).choose

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Etale

/-- Naturality of the specified coefficient projection, as an equality in D(X,B).
Source: blueprint order 2130, naturality clause and proof Step 3
(blueprint: lem-coef-finite-direct-image).

Proof: take B-geometric transposes. Naturality of the A-counit and the scalar units
makes the two scalar-unit precomposites equal. The scalar-adjunction bijection and
then the B-geometric adjunction bijection are injective, proving the equality. -/
theorem finiteCoefficientDirectImageMap_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    {K L : _root_.DerivedCategory (Sheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A))}
    (h : K ⟶ L) :
    (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (X.smallEtaleTopology) φ).map ((R(lowerStar
        (ModuleCat.{u + 1} A) f)).map h) ≫
        finiteCoefficientDirectImageMap φ f L =
      finiteCoefficientDirectImageMap φ f K ≫
        (R(lowerStar (ModuleCat.{u + 1} B) f)).map
          ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (T.smallEtaleTopology) φ).map h) :=
          by
  refine coefficient_naturality _ _
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f) _ _
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f) _ _
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (X.smallEtaleTopology) φ)) _ _
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (T.smallEtaleTopology) φ))
    (finiteCoefficientRestrictionPullback φ f) (ProEtale.scalarPullbackReverse_isIso φ f).2
    (finiteCoefficientDirectImageMap φ f) ?_ h
  · intro K d hd
    exact (finiteCoefficientDirectImageMap_existsUnique φ f K).choose_spec.2 d hd

/-- Geometric composition coherence, with the canonical direct-image compositors.
Source: blueprint order 2130, composition clause and proof Step 3
(blueprint: lem-coef-finite-direct-image).

Proof: the canonical compositor is normalized by the pasted inverse-image adjunction.
Take the B-coefficient composite geometric transpose. The one-step map transposes to
scalar extension of the pasted A-counit. For the two-step map, counit naturality
moves c_f past the g-counit; the defining transpose equations for c_g and c_f reduce
it to that same scalar extension of the pasted A-counit. The injectivity of the
B-coefficient adjunction gives equality, without faithfulness of scalar restriction. -/
theorem finiteCoefficientDirectImageMap_comp
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X Y : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y)
    (K : _root_.DerivedCategory (Sheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A))) :
    finiteCoefficientDirectImageMap φ (f ≫ g) K =
      (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Y.smallEtaleTopology) φ).map
        ((rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f g).symm.hom.app K) ≫
        finiteCoefficientDirectImageMap φ g ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K) ≫
        (R(lowerStar (ModuleCat.{u + 1} B) g)).map (finiteCoefficientDirectImageMap φ f K) ≫
        (rightDerivedLowerStarComp (ModuleCat.{u + 1} B) f g).symm.inv.app
          ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (T.smallEtaleTopology) φ).obj K) :=
          by
  sorry

/-- Successive coefficient changes, including nonquotient maps and identity changes.
Source: blueprint order 2130, coefficient-chain clause and proof Step 3
(blueprint: lem-coef-finite-direct-image).

Proof: take C-geometric transposes. The B-to-C defining equation followed by
naturality reduces the two-step transpose to S_BC(S_AB(ε_A)). On flat K-flat models,
the scalar compositor is (x tensor b) tensor c ↦ x tensor φ(b)c, with inverse
x tensor c ↦ (x tensor 1) tensor c. Its compatibility with the same pullback
balancing map identifies this with S_AC(ε_A). Injectivity of the C-geometric
adjunction proves equality in D(C). There is no requirement that B be an A_E,m. -/
theorem finiteCoefficientDirectImageMap_coefficientChain
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A))) :
    finiteCoefficientDirectImageMap (ψ.comp φ) f K =
      (AlgebraicGeometry.ProEtale.pbcFixedScalarExtensionComp
          (X.smallEtaleTopology) φ ψ (ψ.comp φ) rfl).inv.app ((R(lowerStar (ModuleCat.{u + 1} A)
            f)).obj K) ≫
        (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (X.smallEtaleTopology) ψ).map
          (finiteCoefficientDirectImageMap φ f K) ≫
        finiteCoefficientDirectImageMap ψ f ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension
          (T.smallEtaleTopology) φ).obj K) ≫
        (R(lowerStar (ModuleCat.{u + 1} C) f)).map
          ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtensionComp
          (T.smallEtaleTopology) φ ψ (ψ.comp φ) rfl).hom.app K) := by
  sorry

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- Naturality of the specified coefficient projection, as an equality in D(X,B).
Source: blueprint order 2130, naturality clause and proof Step 3
(blueprint: lem-coef-finite-direct-image).

Proof: take B-geometric transposes. Naturality of the A-counit and the scalar units
makes the two scalar-unit precomposites equal. The scalar-adjunction bijection and
then the B-geometric adjunction bijection are injective, proving the equality. -/
theorem finiteCoefficientDirectImageMap_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    {K L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))}
    (h : K ⟶ L) :
    (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).map
        ((R(lowerStar (ModuleCat.{u + 1} A) f)).map h) ≫
        finiteCoefficientChangeDirectImageMap φ f L =
      finiteCoefficientChangeDirectImageMap φ f K ≫
        (R(lowerStar (ModuleCat.{u + 1} B) f)).map
          ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology T) φ).map h)
          := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let aa := derivedUpperStarLowerStarAdjunction.{u + 2, u} (ModuleCat.{u + 1} A) f
  let ab := derivedUpperStarLowerStarAdjunction.{u + 2, u} (ModuleCat.{u + 1} B) f
  let ax := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X) φ)
  let adt := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology T) φ)
  let e := leftDerivedUpperStarRestrictScalarsIso.{u} φ f
  have hk := (scalarPullbackReverse_isIso.{u} φ f).1
  have hu (M : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
      (d : (pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).obj
        ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj M) ⟶
        (R(lowerStar (ModuleCat.{u + 1} B) f)).obj
          ((pbcFixedScalarExtension (Scheme.ProEt.topology T) φ).obj M))
      (hd : IsFiniteCoefficientDirectImageMap φ f M d) :
      d = finiteCoefficientChangeDirectImageMap φ f M :=
    (finiteCoefficientDirectImageMap_existsUnique φ f M).choose_spec.2 d hd
  have hn := @coefficient_naturality.{u + 2, u + 2, u + 2, u + 2,
      u + 1, u + 1, u + 1, u + 1}
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} B)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)))
    inferInstance inferInstance inferInstance inferInstance
    _ _ aa _ _ ab _ _ ax _ _ adt e hk
    (finiteCoefficientChangeDirectImageMap φ f) hu K L h
  exact hn

/-- Geometric composition coherence, with the canonical direct-image compositors.
Source: blueprint order 2130, composition clause and proof Step 3
(blueprint: lem-coef-finite-direct-image).

Proof: the canonical compositor is normalized by the pasted inverse-image adjunction.
Take the B-coefficient composite geometric transpose. The one-step map transposes to
scalar extension of the pasted A-counit. For the two-step map, counit naturality
moves c_f past the g-counit; the defining transpose equations for c_g and c_f reduce
it to that same scalar extension of the pasted A-counit. The injectivity of the
B-coefficient adjunction gives equality, without faithfulness of scalar restriction. -/
theorem finiteCoefficientDirectImageMap_comp
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X Y : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    finiteCoefficientChangeDirectImageMap φ (f ≫ g) K =
      (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology Y) φ).map
        ((finiteDirectImageComposition A f g).hom.app K) ≫
        finiteCoefficientChangeDirectImageMap φ g ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K) ≫
        (R(lowerStar (ModuleCat.{u + 1} B) g)).map (finiteCoefficientChangeDirectImageMap φ f K) ≫
        (finiteDirectImageComposition B f g).inv.app
          ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology T) φ).obj K)
          := by
  sorry

/-- Successive coefficient changes, including nonquotient maps and identity changes.
Source: blueprint order 2130, coefficient-chain clause and proof Step 3
(blueprint: lem-coef-finite-direct-image).

Proof: take C-geometric transposes. The B-to-C defining equation followed by
naturality reduces the two-step transpose to S_BC(S_AB(ε_A)). On flat K-flat models,
the scalar compositor is (x tensor b) tensor c ↦ x tensor φ(b)c, with inverse
x tensor c ↦ (x tensor 1) tensor c. Its compatibility with the same pullback
balancing map identifies this with S_AC(ε_A). Injectivity of the C-geometric
adjunction proves equality in D(C). There is no requirement that B be an A_E,m. -/
theorem finiteCoefficientDirectImageMap_coefficientChain
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    finiteCoefficientChangeDirectImageMap (ψ.comp φ) f K =
      (AlgebraicGeometry.ProEtale.pbcFixedScalarExtensionComp
          (Scheme.ProEt.topology X) φ ψ (ψ.comp φ) rfl).inv.app ((R(lowerStar (ModuleCat.{u + 1} A)
            f)).obj K) ≫
        (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) ψ).map
          (finiteCoefficientChangeDirectImageMap φ f K) ≫
        finiteCoefficientChangeDirectImageMap ψ f
          ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension
            (Scheme.ProEt.topology T) φ).obj K) ≫
        (R(lowerStar (ModuleCat.{u + 1} C) f)).map
          ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtensionComp
          (Scheme.ProEt.topology T) φ ψ (ψ.comp φ) rfl).hom.app K) := by
  sorry

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Etale

/-- Ordinary uncompleted finite coefficient change commutes with a separated
finite-type direct image on a bounded constructible complex of finite Tor amplitude.
No flatness of the finite algebra B over A is assumed.
Source: blueprint order 2130, etale isomorphism clause
(blueprint: lem-coef-finite-direct-image).

Proof:
1. The coefficient datum writes l = unit times a positive power of the uniformizer.
Thus some power of l kills A and is invertible on the finite-type schemes over D.k.
Choose a nonnegative bound d on the source dimension by lem-kun-dimension-finite-type;
for the empty source use d=0 and zero sheaves. By lem-sf-etale-direct-image-vanishing
and def-sf-uniform-direct-image-vanishing, Rf_* has the all-sheaf bound N=2d.
2. The finite ring A is Noetherian, so the finite A-module B is finitely presented.
Apply lem-sf-projection-finite-constant to the ordinary uncompleted derived tensor
and K-injective direct image. On bounded-below inputs this agrees with
 def-weil-pbc-direct-image. The coefficient map is the B-adjunction transpose of
scalar extension of the A-counit, as fixed by IsFiniteCoefficientDirectImageMap.
3. By lem-sf-flat-model choose a bounded flat constructible model P for K.
Its extension P tensor_A B is bounded and B-flat, and is constructible termwise on
a common finite stratification. The bounded-below canonical restriction comparison
lem-sbc-canonical-restrict-scalars-functor-comparisons applies to this model.
Its counit identity lem-sbc-restrict-scalars-derived-adjunction-identities identifies
the restriction of our map with the projection map followed by that comparison.
Restriction leaves underlying abelian cohomology sheaves unchanged, so reflects
isomorphisms. Consequently the map is invertible in D(X,B).
4. thm-sf-direct-image-tor-amplitude bounds Rf_*K in [a,b+N] and makes it bounded
constructible, so this is also an allowed input for geometric composition. Its
bounded flat model Q gives the same constructible B-models after scalar extension.
For B-to-C the all-sheaf bound is unchanged by restriction; B need not be A_E,m.
Naturality and both coherence identities are the preceding counit computations. -/
theorem finiteCoefficientDirectImageMap_isIso
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n)
    (B : Type (u + 1)) [CommRing B]
    [Algebra (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) B]
    [Module.Finite (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) B]
    (T X : Over (Spec (CommRingCat.of D.k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : T ⟶ X) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (K : DerivedCategoryModule (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) T.left)
    (_hK : @DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) inferInstance
      (Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n hn)) T.left K)
    (_hTor : ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) T.left a b K) :
    IsIso (finiteCoefficientDirectImageMap
      (algebraMap (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) B) f.left K) := by
  sorry

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- The pro-etale finite coefficient comparison on the specified etale realization.
The target coefficient object is literally nu_T^*(K tensor_A^L B), by the published
canonical comparison pbcComparisonReduction. The preceding naturality, geometric
composition and coefficient-chain identities are its coherence identities after
this canonical scalar identification.
Source: blueprint order 2130, pro-etale clause and proof Step 4
(blueprint: lem-coef-finite-direct-image).

Proof: f is qcqs. Apply prop-weil-pbc-comparison-direct-image and its canonical
counit normalization lem-weil-pbc-comparison-direct-image-canonical-mate to K and K_B.
Use bounded flat models for both K and Rf_*K; comparison inverse image is exact,
preserves flatness (lem-exc-constant-inverse-image-flat), and commutes with termwise
tensor (lem-weil-pbc-ringed-topoi-module-pullback-tensor). Thus its derived scalar
comparison is exactly pbcComparisonReduction. Conjugate the etale isomorphism by
the two direct-image comparison isomorphisms and this scalar comparison. Take its
B-pro-etale geometric transpose. The counit normalizations and the etale defining
transpose equation reduce it to extension of the pro-etale A-counit; uniqueness
identifies it with the map defined here. All factors are invertible. Restriction
of scalars is the canonical comparison of
lem-weil-proetale-direct-image-restriction-of-scalars. The same transpose
calculations prove naturality and both coherence identities. Finite-Tor and
constructibility of the inputs follow from lem-sf-comparison-tor-amplitude;
only bounded etale-origin inputs are used for the isomorphism conclusion. -/
theorem finiteCoefficientDirectImageMap_etaleOrigin_isIso
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n)
    (B : Type (u + 1)) [CommRing B]
    [Algebra (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) B]
    [Module.Finite (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) B]
    (T X : Over (Spec (CommRingCat.of D.k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : T ⟶ X) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (K : Etale.DerivedCategoryModule
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) T.left)
    (_hK : @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) inferInstance
      (Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n hn)) T.left K)
    (_hTor : ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) T.left a b K) :
    IsIso (finiteCoefficientChangeDirectImageMap
      (algebraMap (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) B) f.left
      ((comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))
          T.left).mapDerivedCategory.obj K) ≫
      (R(lowerStar (ModuleCat.{u + 1} B) f.left)).map
        ((pbcComparisonReduction T.left
          (algebraMap (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) B)).hom.app K)) := by
  sorry

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Etale

/-- The canonical unbounded restriction/direct-image comparison, as the mate of the
exact inverse-image/restriction identification. On bounded-below objects this is
`derivedLowerStarRestrictScalarsMap`, with its published counit normalization.
Source: blueprint order 2130, restriction clause; Stacks Tags 0D6J and 07A6
(blueprint: lem-coef-finite-direct-image). -/
def finiteCoefficientRestrictionDirectImageMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) :
    R(lowerStar (ModuleCat.{u + 1} B) f) ⋙
        Sheaf.derivedRestrictScalars X.smallEtaleTopology φ ⟶
      Sheaf.derivedRestrictScalars T.smallEtaleTopology φ ⋙
        R(lowerStar (ModuleCat.{u + 1} A) f) :=
  mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (finiteCoefficientRestrictionPullback φ f).hom

/-- The restriction/projection identity in scalar-unit form. The projection formula
mate, after the canonical underlying-tensor identifications, is the unique B-linear
map whose restriction has this composite with the scalar unit. The last comparison
is the canonical restriction/direct-image mate, not an arbitrary isomorphism.
Source: blueprint order 2130, restriction clause and proof Step 2
(blueprint: lem-coef-finite-direct-image).

Proof: transpose the equality through the A geometric adjunction. The mate/counit
identity for finiteCoefficientRestrictionDirectImageMap replaces its counit composite
by restriction of the B counit and the inverse-image/restriction comparison. The
result is exactly the defining equation IsFiniteCoefficientDirectImageMap. The
bounded-below comparison is the one of
lem-sbc-canonical-restrict-scalars-functor-comparisons, by its derived universal
property; lem-sbc-restrict-scalars-derived-adjunction-identities supplies its counit
normalization. On K-flat models, restriction of scalar extension is the ordinary
derived tensor, and the tensor-unit arrow is x maps to x tensor 1. Thus this is
precisely the recorded projection-formula mate followed by the canonical comparison.
Injectivity of the scalar adjunction fixes the map in D(B), without assuming that
restriction of derived morphisms is faithful. -/
theorem finiteCoefficientDirectImageMap_restriction_projection
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).unit.app
          ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K) ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map
        (finiteCoefficientDirectImageMap φ f K) ≫
      (finiteCoefficientRestrictionDirectImageMap φ f).app
        ((ProEtale.pbcFixedScalarExtension T.smallEtaleTopology φ).obj K) =
    (R(lowerStar (ModuleCat.{u + 1} A) f)).map
      ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)).unit.app K) := by
  let adjA := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let adjB := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  let e := finiteCoefficientRestrictionPullback φ f
  let S := ProEtale.pbcFixedScalarExtension T.smallEtaleTopology φ
  have hc := (finiteCoefficientDirectImageMap_existsUnique φ f K).choose_spec.1
  change IsFiniteCoefficientDirectImageMap φ f K
    (finiteCoefficientDirectImageMap φ f K) at hc
  apply (adjA.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [show L(upperStar (ModuleCat.{u + 1} A) f).map
      ((finiteCoefficientRestrictionDirectImageMap φ f).app (S.obj K)) ≫
      adjA.counit.app _ =
      e.hom.app _ ≫
        (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map
          (adjB.counit.app (S.obj K)) from
    mateEquiv_counit adjB adjA e.hom (S.obj K)]
  rw [← Functor.comp_map,
    e.hom.naturality_assoc (finiteCoefficientDirectImageMap φ f K)]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp]
  exact hc.trans (adjA.counit.naturality
    ((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)).unit.app K)).symm


end AlgebraicGeometry.Etale
