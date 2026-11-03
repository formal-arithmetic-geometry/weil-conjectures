/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.LocalizedTopChern
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupComparisonBasic
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionFrame
public import WeilConjectures.SmoothPurity.DivisorClass.DivisorClass
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion
public import WeilConjectures.EtaleCohomology.TateTwist.KummerLevelIndependence
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCanonicalEtale
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
/-!
# Localized top Chern coefficient comparisons and law predicates

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
thm-pur-localized-top-chern.md`, L1--L4 and the final local-frame display;
`thm-pur-localized-top-chern.proof.md`, its six DAG proof paragraphs
(blueprint: thm-pur-localized-top-chern).

The finite-root Tate isomorphism and the supported-adjunction/site comparisons
are constructed explicitly. The line clause uses the current interface Cartier
map, with the sign `c = -cD`. The frame clause uses the current upstream
`Etale.frameClass`, whose definition is the ordered Kummer boundary product.
The family, base-change law, direct-sum law, and ordinary Chern construction are
the published declarations. This module replaces the superseded theorem as the
statement attachment without changing those public constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u c v
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry
open scoped CategoryTheory.Functor
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PurityFiniteSetting

/-- The supported target in codimension one. -/
abbrev localizedTopChernDivisorTarget {T D : Scheme.{u}} (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [AlgebraicGeometry.Etale.HasTateTwist Λ]
    (i : D ⟶ T) [IsClosedImmersion i] :
    DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (AlgebraicGeometry.Etale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} Λ) i).obj
    ((AlgebraicGeometry.Etale.rightDerivedUpperShriek Λ i).obj
      ((AlgebraicGeometry.Etale.tateObject Λ T 1)⟦(2 : ℤ)⟧))

/-- A class with support on a closed divisor. -/
abbrev localizedTopChernDivisorHom {T D : Scheme.{u}} (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [AlgebraicGeometry.Etale.HasTateTwist Λ]
    (i : D ⟶ T) [IsClosedImmersion i] : Type (u + 1) :=
  AlgebraicGeometry.Etale.constantComplex Λ T ⟶ localizedTopChernDivisorTarget Λ i

/-- The supported morphism obtained from an ordinary Cartier Ext class.

The formula reads the Ext class `κ : Ext²(i_* Λ_D, μ_N ⊗ Λ)` as a derived morphism, precomposes
it with the canonical identification `Ri_! Λ_D ≅ Ri_* Λ_D ≅ i_* Λ_D` (proper `i`, degree-zero
single functor), transports the finite Tate line through `q`, and applies the `Ri_! ⊣ Ri^!`
hom-equivalence.  The inverse of the published
`supportedClassMap` bijection then gives a class with support.  Thus the output is constructed
from `κ`; it is not an existentially chosen negative of another class.

Source: `OrdinarySupportedKummerBoundary.lean`, `KummerClass.lean`, and the
coefficient-extension Tate-line comparison stated below (blueprint:
`def-pur-localized-chern-statement-models`). -/
noncomputable def localizedTopChernCartierSupportedMap
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [AlgebraicGeometry.Etale.HasTateTwist Λ]
    (N : ℕ) (hN : (N : Λ) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (q : (DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateLine T N Λ hN) ≅
        AlgebraicGeometry.Etale.tateObject Λ T 1)
    (κ : Ext ((AlgebraicGeometry.Etale.lowerStar
        (ModuleCat.{u + 1} Λ) i).obj
        (AlgebraicGeometry.Etale.ordinaryFiniteConstant Λ D))
        (Scheme.finiteEtaleTateLine T N Λ hN) 2) :
    localizedTopChernDivisorHom Λ i := by
  let L := (AlgebraicGeometry.Etale.tateObject Λ T 1)⟦(2 : ℤ)⟧
  let eShriek :=
    AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} Λ) i
  let lower := AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} Λ) i
  let eLower := eShriek.hom.app
      ((DerivedCategory.singleFunctor _ 0).obj
        (AlgebraicGeometry.Etale.ordinaryFiniteConstant Λ D)) ≫
    lower.singleFunctorCompRightDerivedFunctorIso.hom.app
      (AlgebraicGeometry.Etale.ordinaryFiniteConstant Λ D)
  let eκ := Abelian.Ext.homEquiv κ
  let hκ :
      (AlgebraicGeometry.Etale.rightDerivedLowerShriek
          (ModuleCat.{u + 1} Λ) i).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (AlgebraicGeometry.Etale.ordinaryFiniteConstant Λ D)) ⟶ L :=
    eLower ≫ eκ ≫ (CategoryTheory.shiftFunctor _ (2 : ℤ)).map q.hom
  let hD : AlgebraicGeometry.Etale.constantComplex Λ D ⟶
      (AlgebraicGeometry.Etale.rightDerivedUpperShriek Λ i).obj L :=
    (AlgebraicGeometry.Etale.constantComplexIsoSingleFunctor Λ D).hom ≫
      (AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction Λ i).homEquiv _ _ hκ
  let E := Equiv.ofBijective
    (AlgebraicGeometry.Etale.supportedClassMap Λ i (L := L))
    (AlgebraicGeometry.Etale.supportedClassMap_bijective Λ i L)
  exact E.symm hD

/-- The scalar-extension functor along `ℤ/N → Λ` agrees with forgetting to abelian groups
followed by `- ⊗_ℤ Λ`; the isomorphism is the uniqueness of left adjoints of restriction of
scalars, so on elements it is `m ⊗ λ ↦ m ⊗ λ`.

Source: `def-pur-affine-line-datum`, the coefficient extension `u ↦ u ⊗ 1_Λ` of the roots of
unity (blueprint: `lem-pur-divisor-class`, clause (b), coefficient extension). -/
noncomputable def localizedTopChernScalarExtensionIso
    (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    ModuleCat.extendScalars (Scheme.finiteEtaleTwistScalar N A hA) ≅
      forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat ⋙
        ModuleCat.extendScalarsAddCommGrp A := by
  let f := Scheme.finiteEtaleTwistScalar N A hA
  let adj := ModuleCat.extendScalarsAddCommGrpAdj A
  let e (M : ModuleCat.{u + 1} (ZMod N)) (P : ModuleCat.{u + 1} A) :
      ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat).obj M ⟶
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat).obj P) ≃
        (M ⟶ (ModuleCat.restrictScalars f).obj P) :=
    { toFun := fun g ↦ ModuleCat.ofHom (X := M) (Y := (ModuleCat.restrictScalars f).obj P)
        (AddMonoidHom.toZModLinearMap N (M := M)
          (M₁ := (ModuleCat.restrictScalars f).obj P) g.hom)
      invFun := fun g ↦ AddCommGrpCat.ofHom g.hom.toAddMonoidHom
      left_inv := fun g ↦ rfl
      right_inv := fun g ↦ by ext; rfl }
  let adj' : (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat ⋙
      ModuleCat.extendScalarsAddCommGrp A) ⊣ ModuleCat.restrictScalars f :=
    Adjunction.mkOfHomEquiv
      { homEquiv := fun M P ↦ (adj.homEquiv _ _).trans (e M P)
        homEquiv_naturality_left_symm := by
          intro M' M P g k
          change (adj.homEquiv _ _).symm
            ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat).map g ≫
              (e M P).symm k) = _
          exact adj.homEquiv_naturality_left_symm _ _
        homEquiv_naturality_right := by
          intro M P P' g k
          change e M P' (adj.homEquiv _ _ (g ≫ k)) = _
          rw [adj.homEquiv_naturality_right]
          rfl }
  exact (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} f).leftAdjointUniq adj'

/-- The published finite Tate line `μ_N ⊗_{ℤ/N} Λ` is the étale sheaf `μ_N ⊗_ℤ Λ`, by the
scalar-extension identification above applied objectwise before sheafification.

Source: `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist` (`finiteEtaleTateLine`) and
`def-pur-affine-line-datum` (blueprint: `lem-pur-divisor-class`, clause (b), coefficient
extension). -/
noncomputable def localizedTopChernRootLineAbIso
    (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    Scheme.finiteEtaleTateLine T N A hA ≅
      (AlgebraicGeometry.Etale.extendScalars A T).obj (T.rootsOfUnitySheaf N) :=
  (presheafToSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapIso
    (Functor.isoWhiskerLeft (Scheme.finiteEtaleMuModulePresheaf T N)
      (localizedTopChernScalarExtensionIso N A hA))


set_option backward.isDefEq.respectTransparency true in
private theorem localizedTopChernSingleTensorMap_isIso {C : Type c} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] [hD : HasDerivedCategory.{v} C]
    [HasColimitsOfSize.{0, 0} C] [hM : MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C]
    [hB : BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] (L M : C) (hL : ObjectProperty.flat L) :
    IsIso (ProEtale.cupSingleTensorMap L M) := by
  let K := (HomologicalComplex.single C (.up ℤ) 0).obj L
  let T := (HomologicalComplex.single C (.up ℤ) 0).obj M
  let H := HomotopyCategory.quotient C (.up ℤ)
  have hK : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat (H.obj K) :=
    (HomotopyCategory.kFlat_quotient_obj_iff K).2
      ((CochainComplex.kFlat_single_obj_iff_flat L 0).2 hL)
  have := DerivedCategory.isIso_μ_Qh_of_kFlat (H.obj K) (H.obj T) hK
  have : IsIso (Functor.LaxMonoidal.μ (H ⋙ DerivedCategory.Qh) K T) := by
    rw [Functor.LaxMonoidal.comp_μ]
    infer_instance
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q K T) := by
    change IsIso (tensorHom _ _ ≫
      Functor.LaxMonoidal.μ (H ⋙ DerivedCategory.Qh) K T ≫ _)
    infer_instance
  dsimp only [K, T] at this
  unfold ProEtale.cupSingleTensorMap
  have hμ : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
      ((HomologicalComplex.single C (.up ℤ) 0).obj L)
      ((HomologicalComplex.single C (.up ℤ) 0).obj M)) := this
  have hmap : IsIso (DerivedCategory.Q.map
      ((((CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor C) L).app
          ((HomologicalComplex.single C (.up ℤ) 0).obj M)) ≪≫
        ((HomologicalComplex.singleMapHomologicalComplex (tensorLeft L) (.up ℤ) 0).app M)).hom)) :=
    inferInstance
  have ht : IsIso (tensorIso ((DerivedCategory.singleFunctorIsoCompQ C 0).app L)
      ((DerivedCategory.singleFunctorIsoCompQ C 0).app M)).hom := inferInstance
  have hi : IsIso ((DerivedCategory.singleFunctorIsoCompQ C 0).app (L ⊗ M)).inv :=
    inferInstance
  exact IsIso.comp_isIso' ht (IsIso.comp_isIso' hμ (IsIso.comp_isIso' hmap hi))


/-- The single-complex tensor comparison is invertible for the finite Tate lines.
Source: finite twists are locally free of rank one, hence flat; degree-zero flat
complexes compute the derived tensor (blueprint: thm-pur-localized-top-chern,
coefficient comparison for the local frame formula).
Proof: trivialize the root line on its primitive-root étale cover. Its positive
powers are free rank one there, so both degree-zero complexes are K-flat. The
localization tensor comparison is therefore the ordinary tensor comparison and
is an isomorphism. Reflect this along the covering inverse images. -/
theorem localizedTopChernSingleTensor_isIso (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (a : T ⟶ Spec (.of P.field.k)) (r : ℕ) :
    IsIso (ProEtale.cupSingleTensorMap
      (P.functorialCupTwist false T r) (P.functorialCupTwist false T 1)) := by
  let inverse : TensorInverse (P.functorialCupTwist false T r) :=
    { obj := P.functorialCupTwist false T (-(r : ℤ))
      rightIso := P.functorialCupTwistProduct false T a r (-(r : ℤ)) ≪≫
        eqToIso (congrArg (P.functorialCupTwist false T) (add_neg_cancel (r : ℤ)))
      leftIso := P.functorialCupTwistProduct false T a (-(r : ℤ)) r ≪≫
        eqToIso (congrArg (P.functorialCupTwist false T) (neg_add_cancel (r : ℤ))) }
  exact localizedTopChernSingleTensorMap_isIso _ _ inverse.flat

/-- The rank-one root-insertion comparison, with the exact three factors of the
current divisor interface's canonicalFiniteTateLineIso. Source: its coefficient
extension construction (blueprint: thm-pur-localized-top-chern, L1). -/
def localizedTopChernTateOneIso (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (a : T ⟶ Spec (.of P.field.k)) :
    (DerivedCategory.singleFunctor _ 0).obj (P.functorialCupTwist false T 1) ≅
      Etale.tateObject P.Coefficient T 1 := by
  letI := P.localizedTopChernInvertibleExponent a
  exact (DerivedCategory.singleFunctor _ 0).mapIso
      (localizedTopChernRootLineAbIso T
        P.diagonalExponent P.Coefficient P.diagonalExponent_annihilates) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (Etale.extendScalarsRootsOfUnityIsoTateTwistSheaf P.Coefficient
        P.diagonalExponent P.diagonalExponent_annihilates (P.diagonalExponent_isUnit a)) ≪≫
    (Etale.tateTwistObjectIsoSingleFunctor P.Coefficient T 1).symm

/-- L1: the class is minus the canonical Cartier class cD, hence the positive
local Kummer boundary cl. Source: lem-pur-divisor-class(b)
(blueprint: thm-pur-localized-top-chern, L1). -/
def LocalizedTopChernStatementLine (P : PurityFiniteSetting.{u})
    (c : P.LocalizedTopChernClasses) : Prop :=
  ∀ {T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a]
    [LocallyOfFiniteType a] [QuasiCompact a] (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank 1] (s : F.sections)
    (hs : IsRegularSection P T a F 1 s),
  ∃ hc : IsClosedImmersion (regularSectionZeroProjection P T a F 1 s),
    letI := hc
    ∃ hI : (regularSectionZeroProjection P T a F 1 s).ker.IsInvertible,
    ∃ cD : localizedTopChernDivisorHom P.Coefficient
        (regularSectionZeroProjection P T a F 1 s),
      cD = localizedTopChernCartierSupportedMap P.Coefficient
        P.diagonalExponent P.diagonalExponent_annihilates
        (regularSectionZeroProjection P T a F 1 s) (P.localizedTopChernTateIso T a 1)
        (Etale.geoCartierEtaleClass P.Coefficient P.diagonalExponent
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level)
          P.diagonalExponent_annihilates (regularSectionZeroProjection P T a F 1 s)
          hI (P.diagonalExponent_isUnit a)) ∧
      P.localizedTopChernSupported a (regularSectionZeroProjection P T a F 1 s)
        1 (c a F 1 s hs) = -cD

end WeilConjectures.PurityFiniteSetting
