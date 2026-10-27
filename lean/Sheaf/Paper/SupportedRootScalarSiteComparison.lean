/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q124
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.Etale.ForgetModuleCohomology
public import WeilConjectures.SixFunctors.ProEtale.ForgetModuleCohomology
public import Sheaf.Paper.SupportedCoefficientHomNaturality
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.ClosedSupportHom
public import Sheaf.Paper.SupportedHomCocycleNormalization
public import Sheaf.Paper.EtaleDerivedScalarTensor
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer
public import Sheaf.Paper.SupportedHomPullback
public import Sheaf.Paper.PurityFrameClass
public import Sheaf.SixFunctors.GeoCartierCoeffExtension
public import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
public import Sheaf.AlgebraicGeometry.PurityRelativeCone
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Paper.SupportedCohomologyHom
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import all Sheaf.CategoryTheory.ExactDegreeZeroAdjoint
import Sheaf.Paper.P1KummerScalarEndpointExistence
import all Sheaf.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.AlgebraicGeometry.ResidueFiniteRootMapIso

/-! # Supported root scalar extension and change of site

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-geo-cartier,
lem-amb-cartier-kummer-map.proof.md, final scalar-extension paragraph.
(blueprint: lem-pur-supported-root-scalar-site-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor ChangeOfRings
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategory
private theorem cachedModSheafify (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    HasSheafify T.smallEtaleTopology (ModuleCat.{u + 1} A) := inferInstance
attribute [local instance] cachedModSheafify
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify


namespace AlgebraicGeometry

namespace SupportedRootScalar

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
set_option backward.defeqAttrib.useBackward true

/-- The standard size lift of Z/(ell^n), without a ramification divisibility restriction.
Source: blueprint lem-amb-cartier-kummer-map, final paragraph.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
abbrev Residue (P : WeilConjectures.PurityFiniteSetting.{u}) :=
  ULift.{u + 1} (ZMod P.diagonalExponent)

/-- The published root module, identified with mu_N by its scalar unit for R.
Source: Stacks 03PK; blueprint scalar-extension paragraph.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
abbrev rootModule (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  Scheme.finiteEtaleTateLine T P.diagonalExponent (Residue P)
    (congrArg ULift.up (ZMod.natCast_self P.diagonalExponent))

/-- The canonical coefficient map from the lifted residue ring to A, obtained from
`finiteEtaleTwistScalar` by the standard lift equivalence.
Source: blueprint scalar-extension paragraph, 1_R maps to 1_A.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
abbrev scalar (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Residue P →+* P.Coefficient :=
  (Scheme.finiteEtaleTwistScalar P.diagonalExponent P.Coefficient
    P.diagonalExponent_annihilates).comp ULift.ringEquiv.toRingHom

/-- The degree-zero coefficient map on the bounded-below category, including the exact
restriction/single comparison. Source: Stacks 07A6, normalized unit.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
def unitPlus {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (T : Scheme.{u}) (phi : R →+* A)
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))
    (B : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (theta : M ⟶ (Sheaf.restrictScalars T.smallEtaleTopology phi).obj B) :
    singlePlus M ⟶ (Sheaf.restrictScalars T.smallEtaleTopology phi).mapDerivedCategoryPlus.obj
      (singlePlus B) :=
  ObjectProperty.homMk
    (SheafExactDegreeZero.scalarUnit T.smallEtaleTopology phi M B theta)

/-- The unit at the shifted root sheaf, with the exact restriction shift comparison.
Source: Stacks 07A6; the normalized unit is termwise x maps to x tensor 1.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
def shiftedRootUnit (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (theta : rootModule P T ⟶ (Sheaf.restrictScalars T.smallEtaleTopology (scalar P)).obj
      (P.frameTwistEtale T 1)) :
    (SheafExactDegreeZero.obj _ (rootModule P T))⟦(2 : ℤ)⟧ ⟶
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology (scalar P)).obj
        ((SheafExactDegreeZero.obj _ (P.frameTwistEtale T 1))⟦(2 : ℤ)⟧) :=
  (SheafExactDegreeZero.scalarUnit T.smallEtaleTopology (scalar P)
      (rootModule P T) (P.frameTwistEtale T 1) theta)⟦(2 : ℤ)⟧' ≫
    ((Sheaf.derivedRestrictScalars T.smallEtaleTopology (scalar P)).commShiftIso
      (2 : ℤ)).inv.app (SheafExactDegreeZero.obj _ (P.frameTwistEtale T 1))

/-- The arrow L_A(b) after the specified source and shifted-target identifications.
Source: blueprint final scalar-extension paragraph. Both comparisons will be normalized
by their adjuncts in the theorem, so these are the actual canonical comparisons.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
def scalarArrow (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (alpha : (Etale.scalarExtension (scalar P) T).obj
      (Etale.supportedConstantDerived (A := Residue P) i) ≅
        Etale.supportedConstantDerived (A := P.Coefficient) i)
    (c2 : (Etale.scalarExtension (scalar P) T).obj
      ((SheafExactDegreeZero.obj _ (rootModule P T))⟦(2 : ℤ)⟧) ≅
        (SheafExactDegreeZero.obj _ (P.frameTwistEtale T 1))⟦(2 : ℤ)⟧)
    (b : zeroHom (rootScalarSupportPair (Residue P) i) (rootModule P T)) :
    zeroHom (etaleSupportHomPair P i) (P.frameTwistEtale T 1) :=
  alpha.inv ≫ (Etale.scalarExtension (scalar P) T).map b ≫ c2.hom

/-- The restriction-kernel class equality defining the underlying coefficient image.
The map on the left forgets A to R using the actual derived kernel comparison; the
map on the right applies the coefficient morphism before deriving support. Thus
this concerns the supported class, including its relative lift.
Source: Stacks 03FD and 093X; blueprint final scalar-extension paragraph.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
def CoefficientImage (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (theta : rootModule P T ⟶ (Sheaf.restrictScalars T.smallEtaleTopology (scalar P)).obj
      (P.frameTwistEtale T 1))
    (beta : (rootScalarSupportPair (Residue P) i).group (singlePlus (rootModule P T)) 2)
    (gamma : (etaleSupportHomPair P i).group (singlePlus (P.frameTwistEtale T 1)) 2) : Prop :=
  (coefficientGroupMap
      (dA := HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u + 1} P.Coefficient))
      (dB := HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u + 1} (Residue P)))
      T.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} (scalar P))
      (Etale.supportRestrictionArrow i) (singlePlus (P.frameTwistEtale T 1)) 2).hom gamma =
    ((@Sheaf.supportHypercohomologyFunctor.{u + 1, u, u + 2, u + 1, u + 1, u + 1}
      _ _ T.smallEtaleTopology (ModuleCat.{u + 1} (Residue P)) _ _ _ _
      (Etale.supportRestrictionArrow i) _ _ _
      (HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u + 1} (Residue P))) 2).map
        (unitPlus T (scalar P) (rootModule P T) (P.frameTwistEtale T 1) theta)).hom beta

/-- The site image of the supported coefficient class. It uses the bounded-below
witness B[0], via the normalized transport's actual derived-kernel map.
Source: blueprint final scalar-extension paragraph; Stacks 099R.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
def siteClass (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (v : siteSupportHomTransport P i)
    (gamma : (etaleSupportHomPair P i).group (singlePlus (P.frameTwistEtale T 1)) 2) :
    (proEtaleSupportHomPair P i).group
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategoryPlus.obj
        (singlePlus (P.frameTwistEtale T 1))) 2 :=
  (@DerivedCategory.Plus.homologyFunctor.{u + 1, u + 2, u + 1}
    (ModuleCat.{u + 1} P.Coefficient) _ _
    (HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u + 1} P.Coefficient)) 2).map
    (v.derivedMap.app (singlePlus (P.frameTwistEtale T 1))) gamma

/-- The projection-induced q in the published finite root-tensor presentation.
The recorded frame twist is literally the inverse image of B in this presentation.
Source: def-pur-frame-class, theta and sigma; finite-root site comparison.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
def rootTwistIso (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).obj
      (P.frameTwistEtale T 1) ≅ P.frameTwist T 1 := Iso.refl _

/-- A local root tensor on the pro-etale site, obtained from the identical etale root
and scalar using the actual site adjunction unit. At a=1 this is sigma rho on that root.
Source: def-pur-frame-class, theta; lem-amb-finite-root-site-comparison, tensor_unit.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
def siteTensor (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ) (f : W.unop ⟶ (Scheme.toProEt T).obj U.unop)
    (a : P.Coefficient) (z : (T.rootsOfUnitySheaf P.diagonalExponent).obj.obj U) :
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).obj
      (P.frameTwistEtale T 1)).obj.obj W :=
  ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).obj
    (P.frameTwistEtale T 1)).obj.map f.op
      (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) T).unit.app
        (P.frameTwistEtale T 1)).hom.app U
          (Scheme.finiteEtaleTateOneGenerator P.Coefficient P.diagonalExponent T
            P.diagonalExponent_annihilates U a z))

private theorem adjunct_source_injective
    {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {X : C} {Y N : D} (alpha : L.obj X ≅ Y) (w : X ⟶ R.obj Y)
    (hw : adj.homEquiv X Y alpha.hom = w) :
    Function.Injective (fun f : Y ⟶ N ↦ w ≫ R.map f) := by
  intro f g h
  apply (cancel_epi alpha.hom).1
  apply (adj.homEquiv _ _).injective
  simpa only [adj.homEquiv_naturality_right, hw] using h

private theorem transpose_shift
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    {L : C ⥤ D} {R : D ⥤ C} [R.CommShift ℤ] (adj : L ⊣ R)
    (n : ℤ) {X : C} {Y : D} (f : L.obj X ⟶ Y) :
    adj.homEquiv _ _
        ((Adjunction.LeftAdjointCommShift.iso adj n).hom.app X ≫ f⟦n⟧') =
      (adj.homEquiv _ _ f)⟦n⟧' ≫ (R.commShiftIso n).inv.app Y := by
  apply (cancel_mono ((R.commShiftIso n).hom.app Y)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [Adjunction.homEquiv_unit, R.map_comp]
  have hn := (R.commShiftIso n).hom.naturality f
  change R.map (f⟦n⟧') ≫ (R.commShiftIso n).hom.app Y =
    (R.commShiftIso n).hom.app (L.obj X) ≫ (R.map f)⟦n⟧' at hn
  simp only [Category.assoc]
  rw [hn, ← Category.assoc, ← Category.assoc]
  rw [Category.assoc (adj.unit.app _) (R.map _) ((R.commShiftIso n).hom.app _),
    ← Adjunction.LeftAdjointCommShift.compatibilityUnit_iso adj n X]
  rw [← Functor.map_comp, Adjunction.homEquiv_unit]
  exact (Category.comp_id _).symm

private theorem scalarArrow_unit
    {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {X M : C} {Y N : D} (alpha : L.obj X ≅ Y) (c : L.obj M ≅ N)
    (w : X ⟶ R.obj Y) (u : M ⟶ R.obj N)
    (hw : adj.homEquiv X Y alpha.hom = w)
    (hu : adj.homEquiv M N c.hom = u) (b : X ⟶ M) :
    w ≫ R.map (alpha.inv ≫ L.map b ≫ c.hom) = b ≫ u := by
  rw [← hw, ← adj.homEquiv_naturality_right]
  simp only [← Category.assoc, alpha.hom_inv_id, Category.id_comp]
  rw [adj.homEquiv_naturality_left, hu]

private theorem siteTensor_smul (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
    (f : W.unop ⟶ (Scheme.toProEt T).obj U.unop) (a : P.Coefficient)
    (z : (T.rootsOfUnitySheaf P.diagonalExponent).obj.obj U) :
    (rootTwistIso P T).hom.hom.app W (siteTensor P T U W f a z) =
      a • (rootTwistIso P T).hom.hom.app W (siteTensor P T U W f 1 z) := by
  have hz : Scheme.finiteEtaleTateOneGenerator P.Coefficient P.diagonalExponent T
      P.diagonalExponent_annihilates U a z =
      a • Scheme.finiteEtaleTateOneGenerator P.Coefficient P.diagonalExponent T
        P.diagonalExponent_annihilates U 1 z := by
    exact Scheme.finiteEtaleGenerator_smul T P.diagonalExponent P.Coefficient
      P.diagonalExponent_annihilates U a z
  unfold siteTensor
  rw [hz, map_smul, map_smul, map_smul]

private theorem insertion_transpose
    {V W : Type*} [Category V] [Category W] [Abelian V] [Abelian W]
    [HasDerivedCategory V] [HasDerivedCategory W]
    (R : W ⥤ V) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {L : DerivedCategory V ⥤ DerivedCategory W} (a : L ⊣ R.mapDerivedCategory)
    {F : V} {G : W} (eta : F ⟶ R.obj G) :
    a.homEquiv _ _
      (eqToHom (congrArg L.obj (SheafExactDegreeZero.obj_eq F)) ≫
        SheafExactDegreeZero.adjointInsertion R a eta ≫
          eqToHom (SheafExactDegreeZero.obj_eq G).symm) =
      SheafExactDegreeZero.unit R eta := by
  unfold SheafExactDegreeZero.adjointInsertion SheafExactDegreeZero.unit
    SheafExactDegreeZero.map SheafExactDegreeZero.comparison
    SheafExactDegreeZero.functor SheafExactDegreeZero.obj
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Equiv.apply_symm_apply]
  rfl

private theorem endpoint_iso
    {V W : Type*} [Category V] [Category W] [Abelian V] [Abelian W]
    [HasDerivedCategory V] [HasDerivedCategory W]
    (R : W ⥤ V) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {L : DerivedCategory V ⥤ DerivedCategory W} (a : L ⊣ R.mapDerivedCategory)
    {F : V} {G : W} (eta : F ⟶ R.obj G)
    (e : L.obj ((DerivedCategory.singleFunctor V 0).obj F) ≅
      (DerivedCategory.singleFunctor W 0).obj G)
    (he : e.hom = SheafExactDegreeZero.adjointInsertion R a eta) :
    ∃ c : L.obj (SheafExactDegreeZero.obj V F) ≅ SheafExactDegreeZero.obj W G,
    ∃ c2 : L.obj ((SheafExactDegreeZero.obj V F)⟦(2 : ℤ)⟧) ≅
        (SheafExactDegreeZero.obj W G)⟦(2 : ℤ)⟧,
      a.homEquiv _ _ c.hom = SheafExactDegreeZero.unit R eta ∧
      a.homEquiv _ _ c2.hom =
        (SheafExactDegreeZero.unit R eta)⟦(2 : ℤ)⟧' ≫
          (R.mapDerivedCategory.commShiftIso (2 : ℤ)).inv.app
            (SheafExactDegreeZero.obj W G) := by
  let c : L.obj (SheafExactDegreeZero.obj V F) ≅ SheafExactDegreeZero.obj W G :=
    eqToIso (congrArg L.obj (SheafExactDegreeZero.obj_eq F)) ≪≫ e ≪≫
      (eqToIso (SheafExactDegreeZero.obj_eq G)).symm
  have hc : a.homEquiv _ _ c.hom = SheafExactDegreeZero.unit R eta := by
    change a.homEquiv _ _ (_ ≫ e.hom ≫ _) = _
    rw [he]
    exact insertion_transpose R a eta
  let c2 : L.obj ((SheafExactDegreeZero.obj V F)⟦(2 : ℤ)⟧) ≅
      (SheafExactDegreeZero.obj W G)⟦(2 : ℤ)⟧ :=
    (Adjunction.LeftAdjointCommShift.iso a (2 : ℤ)).app _ ≪≫
      (shiftFunctor _ (2 : ℤ)).mapIso c
  refine ⟨c, c2, hc, ?_⟩
  change a.homEquiv _ _ (_ ≫ c.hom⟦(2 : ℤ)⟧') = _
  exact (transpose_shift a (2 : ℤ) c.hom).trans
    (congrArg (fun f ↦ f⟦(2 : ℤ)⟧' ≫
      (R.mapDerivedCategory.commShiftIso (2 : ℤ)).inv.app _) hc)

/-- The normalized finite root endpoint and its degree-zero and shifted derived
identifications. This is the scalar endpoint construction for the residue line.
Source: Stacks 03PK and 06YY; blueprint lem-sp-pur-supported-root-scalar-site-comparison.
(blueprint: lem-pur-supported-root-scalar-endpoints)

The endpoint is obtained by the finite root tensor construction. Its universal property
is the usual scalar extension adjunction on the root generator, and the shifted map is
transported by the canonical commutation isomorphism. The proof is split off because
it is independent of the supported-Hom and site transport argument. -/
theorem rootScalarEndpointData
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] :
    ∃ theta : rootModule P T ⟶ (Sheaf.restrictScalars T.smallEtaleTopology (scalar P)).obj
        (P.frameTwistEtale T 1),
    ∃ c : (Etale.scalarExtension (scalar P) T).obj
        (SheafExactDegreeZero.obj _ (rootModule P T)) ≅
          SheafExactDegreeZero.obj _ (P.frameTwistEtale T 1),
    ∃ c2 : (Etale.scalarExtension (scalar P) T).obj
        ((SheafExactDegreeZero.obj _ (rootModule P T))⟦(2 : ℤ)⟧) ≅
          (SheafExactDegreeZero.obj _ (P.frameTwistEtale T 1))⟦(2 : ℤ)⟧,
      (∀ (U : T.Etaleᵒᵖ) (r : Residue P)
          (z : (T.rootsOfUnitySheaf P.diagonalExponent).obj.obj U),
        theta.hom.app U (Scheme.finiteEtaleTateOneGenerator (Residue P)
          P.diagonalExponent T (congrArg ULift.up (ZMod.natCast_self P.diagonalExponent))
            U r z) =
          Scheme.finiteEtaleTateOneGenerator P.Coefficient P.diagonalExponent T
            P.diagonalExponent_annihilates U (scalar P r) z) ∧
      ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars T.smallEtaleTopology (scalar P))).homEquiv _ _)
          c.hom = SheafExactDegreeZero.scalarUnit T.smallEtaleTopology (scalar P)
            (rootModule P T) (P.frameTwistEtale T 1) theta ∧
      ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars T.smallEtaleTopology (scalar P))).homEquiv _ _)
          c2.hom = shiftedRootUnit P T theta := by
  classical
  let : NeZero P.diagonalExponent :=
    ⟨by change P.coefficients.l ^ P.level ≠ 0
        exact pow_ne_zero _ P.coefficients.prime.out.ne_zero⟩
  obtain ⟨e⟩ := Etale.p1KummerScalarEndpointExistence T P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level)
    (P.diagonalExponent_isUnit (T ↘ Spec (.of P.field.k)))
    (Residue P) P.Coefficient (scalar P)
    (congrArg ULift.up (ZMod.natCast_self P.diagonalExponent))
    P.diagonalExponent_annihilates
  obtain ⟨c, c2, hc, hc2⟩ := endpoint_iso
    (Sheaf.restrictScalars T.smallEtaleTopology (scalar P))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology (scalar P)))
    e.lineInsertion e.lineIso (by
      have h := e.line_derived
      unfold Etale.p1KummerDerivedInsertion SheafExactDegreeZero.scalarAdjointInsertion at h
      exact h)
  refine ⟨e.lineInsertion, c, c2, e.line_normalization, ?_, ?_⟩
  · unfold SheafExactDegreeZero.scalarUnit
    exact hc
  · unfold shiftedRootUnit SheafExactDegreeZero.scalarUnit
    exact hc2

/-- Scalar extension of every full supported root class agrees with its coefficient
image and with the change from the etale to the pro-etale site. The root tensor
presentation of `frameTwist` makes the projection-induced q the identity on this
presentation; its root-unit normalization is retained by the local tensor formula.
The target witness for every site comparison is B[0].

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-geo-cartier,
lem-amb-cartier-kummer-map.proof.md, final scalar-extension paragraph; Milne,
Section 9, Example 9.5 and the Ext proof of Theorem 9.4; Stacks 03FD, 093X, 06YQ,
06YY, 07A6 and 09XQ.
(blueprint: lem-pur-supported-root-scalar-site-comparison)

Proof plan, following the seven DAG steps:
1. The finite datum gives N A = 0 and invertibility of N on T. By
   lem-asd-finite-etale-twist-line and lem-pur-etale-closed-constant-tensor the
   root sheaf and supported R-unit are flat. By
   lem-pur-etale-supported-kernel-adjunction closed pushforward is exact, so its
   canonical right-derived-functor unit on the single complex of A_Z is invertible.
2. Degree-zero flat complexes are K-flat by
   lem-weil-pbc-independent-bounded-flat-kflat. Apply lem-pur-derived-change-of-rings
   and lem-geo-cartier-coeff-extension on these representatives. The source
   comparison is the adjunct of 1_R to 1_A; by
   lem-pur-sheaf-ring-derived-coefficient-adjunction the root unit is v to v tensor 1.
3. Naturality of the normalized unit, with its termwise shift comparison, gives
   w followed by Res(b_A) = b followed by u[2]. This identifies b_A with L_A(b).
4. By lem-pur-module-restriction-kernel-comparison, the actual derived kernel
   comparisons for forgetting coefficients are isomorphisms. Evaluation at one
   in lem-pur-supported-hom-cocycle-normalization identifies coefficient change
   on Hom with precomposition by w. Compare injective models by
   lem-weil-pbc-bounded-below-injectives-kinjective and
   lem-sp-kinjective-comparison-principle. No restricted injective is assumed
   injective. Adjunction bijectivity identifies the realized coefficient image
   with b_A.
5. By lem-pur-divisor-relative-cone the kernel inclusion is the signed relative
   lift and sends s to (s,0). Coefficient change acts on both components and
   commutes with D(a,b)=(da,r(a)-db) and boundary b to (0,-b), so the equality
   precedes forgetting support. The SignedIdentification clauses retain this
   normalization from lem-amb-closed-support-hom.
6. Apply lem-pur-supported-hom-pullback only to B[0]. Its normalized closed
   exchange and derived-kernel map give nu inverse image of b_A precomposed
   with a_T inverse. Coefficient and site naturality give nu*(u*beta)=t*nu*beta.
7. By lem-amb-finite-root-site-comparison inverse image retains the same root
   and scalar. The root-tensor presentation of def-pur-frame-class identifies
   q(v tensor a) with a sigma rho(v). Naturality of lem-pur-supported-hom in
   the coefficient object gives the stated site formula. All these arguments
   apply to an arbitrary closed immersion and use neither Cartier regularity
   nor a purity isomorphism. -/
theorem supported_root_scalar_site_comparison
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    [IsSeparated (T ↘ Spec (.of P.field.k))]
    {Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    ∃ chiR : (rootScalarSupportPair (Residue P) i).Identification,
    ∃ chiA : (etaleSupportHomPair P i).Identification,
    ∃ chiP : (proEtaleSupportHomPair P i).Identification,
    ∃ theta : rootModule P T ⟶ (Sheaf.restrictScalars T.smallEtaleTopology (scalar P)).obj
        (P.frameTwistEtale T 1),
    ∃ alpha : (Etale.scalarExtension (scalar P) T).obj
        (Etale.supportedConstantDerived (A := Residue P) i) ≅
          Etale.supportedConstantDerived (A := P.Coefficient) i,
    ∃ c : (Etale.scalarExtension (scalar P) T).obj
        (SheafExactDegreeZero.obj _ (rootModule P T)) ≅
          SheafExactDegreeZero.obj _ (P.frameTwistEtale T 1),
    ∃ c2 : (Etale.scalarExtension (scalar P) T).obj
        ((SheafExactDegreeZero.obj _ (rootModule P T))⟦(2 : ℤ)⟧) ≅
          (SheafExactDegreeZero.obj _ (P.frameTwistEtale T 1))⟦(2 : ℤ)⟧,
    ∃ v : siteSupportHomTransport P i,
      SignedIdentification (rootScalarSupportPair (Residue P) i) chiR ∧
      SignedIdentification (etaleSupportHomPair P i) chiA ∧
      SignedIdentification (proEtaleSupportHomPair P i) chiP ∧
      IsIso (Etale.ordinaryFiniteRootMap (Residue P) P.diagonalExponent
        (congrArg ULift.up (ZMod.natCast_self P.diagonalExponent)) T) ∧
      IsIso ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          ((CochainComplex.singleFunctor _ 0).obj (P.constantEtale Z)))) ∧
      alpha.hom = Etale.supportedCoefficientComparison (scalar P) i ∧
      ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars T.smallEtaleTopology (scalar P))).homEquiv _ _)
          alpha.hom = Etale.coefficientUnitDerived (scalar P) i ∧
      (∀ (U : T.Etaleᵒᵖ) (r : Residue P)
          (z : (T.rootsOfUnitySheaf P.diagonalExponent).obj.obj U),
        theta.hom.app U (Scheme.finiteEtaleTateOneGenerator (Residue P)
          P.diagonalExponent T (congrArg ULift.up (ZMod.natCast_self P.diagonalExponent))
            U r z) =
          Scheme.finiteEtaleTateOneGenerator P.Coefficient P.diagonalExponent T
            P.diagonalExponent_annihilates U (scalar P r) z) ∧
      ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars T.smallEtaleTopology (scalar P))).homEquiv _ _)
          c.hom = SheafExactDegreeZero.scalarUnit T.smallEtaleTopology (scalar P)
            (rootModule P T) (P.frameTwistEtale T 1) theta ∧
      ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars T.smallEtaleTopology (scalar P))).homEquiv _ _)
          c2.hom = shiftedRootUnit P T theta ∧
      IsIso ((derivedCoefficientComparison
        (dA := HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u + 1} (Residue P)))
        (dB := HasDerivedCategory.ofIsGrothendieckAbelian AddCommGrpCat.{u + 1})
        T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (Residue P)) AddCommGrpCat.{u + 1})
          (Etale.supportRestrictionArrow i)).app (singlePlus (rootModule P T))) ∧
      IsIso ((derivedCoefficientComparison
        (dA := HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u + 1} P.Coefficient))
        (dB := HasDerivedCategory.ofIsGrothendieckAbelian AddCommGrpCat.{u + 1})
        T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1})
          (Etale.supportRestrictionArrow i)).app (singlePlus (P.frameTwistEtale T 1))) ∧
      IsIso ((derivedCoefficientComparison
        (dA := HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u + 1} P.Coefficient))
        (dB := HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u + 1} (Residue P)))
        T.smallEtaleTopology
        (ModuleCat.restrictScalars.{u + 1} (scalar P)) (Etale.supportRestrictionArrow i)).app
          (singlePlus (P.frameTwistEtale T 1))) ∧
      (∀ (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
          (f : W.unop ⟶ (Scheme.toProEt T).obj U.unop)
          (a : P.Coefficient) (z : (T.rootsOfUnitySheaf P.diagonalExponent).obj.obj U),
        (rootTwistIso P T).hom.hom.app W (siteTensor P T U W f a z) =
          a • (rootTwistIso P T).hom.hom.app W (siteTensor P T U W f 1 z)) ∧
      IsIso ((derivedCoefficientComparison
        (dA := HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u + 1} P.Coefficient))
        (dB := HasDerivedCategory.ofIsGrothendieckAbelian AddCommGrpCat.{u + 1})
        (Scheme.ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1})
          (ProEtale.supportRestrictionArrow i)).app
            ((ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategoryPlus.obj
              (singlePlus (P.frameTwistEtale T 1)))) ∧
      v.Compatible (hB := Scheme.isContinuous_toProEt T) chiA chiP
        (singlePlus (P.frameTwistEtale T 1)) 2 ∧
      (∀ beta : (rootScalarSupportPair (Residue P) i).group (singlePlus (rootModule P T)) 2,
        ∃! gamma : (etaleSupportHomPair P i).group (singlePlus (P.frameTwistEtale T 1)) 2,
          CoefficientImage P i theta beta gamma) ∧
      ∀ (beta : (rootScalarSupportPair (Residue P) i).group (singlePlus (rootModule P T)) 2)
        (gamma : (etaleSupportHomPair P i).group (singlePlus (P.frameTwistEtale T 1)) 2),
        CoefficientImage P i theta beta gamma →
        realize (etaleSupportHomPair P i) chiA (P.frameTwistEtale T 1) gamma =
          scalarArrow P i alpha c2
            (realize (rootScalarSupportPair (Residue P) i) chiR (rootModule P T) beta) ∧
        Etale.coefficientUnitDerived (scalar P) i ≫
          (Sheaf.derivedRestrictScalars T.smallEtaleTopology (scalar P)).map
            (scalarArrow P i alpha c2
              (realize (rootScalarSupportPair (Residue P) i) chiR (rootModule P T) beta)) =
          realize (rootScalarSupportPair (Residue P) i) chiR (rootModule P T) beta ≫
            shiftedRootUnit P T theta ∧
        chiP.chi _ 2 (siteClass P i v gamma) =
          v.homMap (singlePlus (P.frameTwistEtale T 1)) 2
            (homFromZero (etaleSupportHomPair P i) (P.frameTwistEtale T 1)
              (scalarArrow P i alpha c2
                (realize (rootScalarSupportPair (Residue P) i) chiR (rootModule P T) beta))) := by
  classical
  let : NeZero P.diagonalExponent :=
    ⟨by change P.coefficients.l ^ P.level ≠ 0
        exact pow_ne_zero _ P.coefficients.prime.out.ne_zero⟩
  obtain ⟨chiR, chiA, chiP, v, hR, hA, hP, hn⟩ :=
    supportedCoefficientHomNaturality P (Residue P) (scalar P) T i
  obtain ⟨theta, c, c2, htheta, hc, hc2⟩ := rootScalarEndpointData P T
  obtain ⟨hRf, hAf, hRes, hPf, hv, heq⟩ := hn (rootModule P T) (P.frameTwistEtale T 1) theta
  let : IsIso (Etale.supportedCoefficientComparison (scalar P) i) :=
    (Etale.geoCartierCoeffExtension i (scalar P) (RingHom.id P.Coefficient)).1
  let alpha := asIso (Etale.supportedCoefficientComparison (scalar P) i)
  have hunit : ((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology (scalar P))).homEquiv _ _)
        alpha.hom = Etale.coefficientUnitDerived (scalar P) i := by
    change ((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology (scalar P))).homEquiv _ _)
      (Etale.supportedCoefficientComparison (scalar P) i) = _
    unfold Etale.supportedCoefficientComparison
    exact Equiv.apply_symm_apply _ _
  have harrow (beta : (rootScalarSupportPair (Residue P) i).group
      (singlePlus (rootModule P T)) 2) :
      Etale.coefficientUnitDerived (scalar P) i ≫
        (Sheaf.derivedRestrictScalars T.smallEtaleTopology (scalar P)).map
          (scalarArrow P i alpha c2
            (realize (rootScalarSupportPair (Residue P) i) chiR (rootModule P T) beta)) =
        realize (rootScalarSupportPair (Residue P) i) chiR (rootModule P T) beta ≫
          shiftedRootUnit P T theta := by
    exact scalarArrow_unit (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology (scalar P)))
      alpha c2 _ _ hunit hc2 _
  have himage (beta : (rootScalarSupportPair (Residue P) i).group
      (singlePlus (rootModule P T)) 2)
      (gamma : (etaleSupportHomPair P i).group (singlePlus (P.frameTwistEtale T 1)) 2) :
      CoefficientImage P i theta beta gamma ↔
        realize (etaleSupportHomPair P i) chiA (P.frameTwistEtale T 1) gamma =
          scalarArrow P i alpha c2
            (realize (rootScalarSupportPair (Residue P) i) chiR (rootModule P T) beta) := by
    constructor
    · intro h
      apply adjunct_source_injective (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars T.smallEtaleTopology (scalar P))) alpha _ hunit
      exact ((heq beta gamma).mp h).trans (harrow beta).symm
    · intro h
      apply (heq beta gamma).mpr
      rw [h]
      exact harrow beta
  refine ⟨chiR, chiA, chiP, theta, alpha, c, c2, v, hR, hA, hP,
    Etale.residueFiniteRootMap_isIso T P.diagonalExponent _, ?_, rfl, hunit,
    htheta, hc, hc2, hRf, hAf, hRes, siteTensor_smul P T, hPf, hv, ?_, ?_⟩
  · infer_instance
  · intro beta
    let e := realizationEquiv (etaleSupportHomPair P i) chiA (P.frameTwistEtale T 1)
    let b := scalarArrow P i alpha c2
      (realize (rootScalarSupportPair (Residue P) i) chiR (rootModule P T) beta)
    refine ⟨e.symm b, (himage beta _).mpr ?_, ?_⟩
    · rw [← realizationEquiv_apply]
      exact e.apply_symm_apply b
    · intro gamma hgamma
      apply e.injective
      rw [realizationEquiv_apply, realizationEquiv_apply]
      exact ((himage beta gamma).mp hgamma).trans (by
        rw [← realizationEquiv_apply]
        exact (e.apply_symm_apply b).symm)
  · intro beta gamma hgamma
    have h := (himage beta gamma).mp hgamma
    refine ⟨h, harrow beta, ?_⟩
    have hsite := hv gamma
    change chiP.chi _ 2 (siteClass P i v gamma) =
      v.homMap (singlePlus (P.frameTwistEtale T 1)) 2
        (chiA.chi (singlePlus (P.frameTwistEtale T 1)) 2 gamma) at hsite
    rw [← h, homFromZero_realize]
    exact hsite


end SupportedRootScalar
end AlgebraicGeometry
