/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceZeroSectionPurity
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.KummerClass
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.SupportedCohomologyHomSpecified
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFramePrincipalBoundary
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass.TwistPullback
public import WeilConjectures.EtaleCohomology.TateTwist.KummerLevelIndependence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ExtendScalars
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceCoordinateBoundaries
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSupportedIntegralDerivedUnit
public import WeilConjectures.AlgebraicGeometry.KummerLocalizationSplice
public import WeilConjectures.AlgebraicGeometry.KummerLocalizationSpliceDefs
public import WeilConjectures.AlgebraicGeometry.Principal.PrincipalTorsorYonedaSign
public import WeilConjectures.AlgebraicGeometry.ScalarUnitExt
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedKummerIntegralEquation
public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift

/-!
# Signed zero-section purity in affine space

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
cor-pur-affine-space-zero-section-purity.md`
(blueprint: cor-pur-affine-space-zero-section-purity).

The existing affine-space construction `thom` is the ordered product of the
coordinate Cartier classes, while `kummerThom` below is built independently from
the actual principal-open Kummer support boundaries and their canonical Tate-line transport.
The theorem states the complete signed zero-section purity assertion: the
Kummer orientation is invertible with both composites equal to `(-1)^c`, the
Cartier product integrates to one, the negative-twist form exists, and the
ordered Kummer product is preserved by arbitrary base change.

Proof route from the current blueprint:

1. On the ordinary étale site, iterate the affine-line adjunction and use
   `p_c ≫ z = id` to identify the exceptional target with the coefficient unit.
2. Compute the rank-one sign on the projective-line compactification: the
   Cartier class integrates to `1`, while [lem-pur-divisor-class](b) identifies
   the Kummer boundary with its negative, hence the Kummer integral is `-1`.
3. Iterate the normalized rank-one calculation with the ordered supported cup;
   the Kummer product is `(-1)^c` times the Cartier product, and the Cartier
   product is the inverse of the affine-space comparison.
4. Transport the construction through the finite étale-origin comparison and
   the specified Tate twists, retaining the actual Kummer product at every
   coefficient level.
5. Pullback of the coordinate equations, boundaries, cup operations, and the
   unique support identification gives arbitrary base-change compatibility;
   moving the invertible negative twist through the closed exceptional functor
   gives the untwisted conjunct.
-/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry WeilConjectures

namespace AlgebraicGeometry.ProEtale.AffineZeroPurity

private theorem signed_inverse {C : Type*} [Category C] [Preadditive C]
    {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) (r : ℤ)
    (hr : r * r = 1) (hfg : f ≫ g = 𝟙 X) (hgf : g ≫ f = 𝟙 Y) :
    IsIso (r • f) ∧ (r • f) ≫ g = r • 𝟙 X ∧ g ≫ (r • f) = r • 𝟙 Y := by
  refine ⟨⟨r • g, ?_, ?_⟩, ?_, ?_⟩
  · rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, hfg, smul_smul, hr, one_smul]
  · rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, hgf, smul_smul, hr, one_smul]
  · rw [Preadditive.zsmul_comp, hfg]
  · rw [Preadditive.comp_zsmul, hgf]

/-- Extending scalars from a `ZMod N`-module agrees with extending its underlying
abelian group: all additive maps between `ZMod N`-modules are automatically linear.
This is the adjoint-uniqueness comparison, not a choice of a coefficient generator.
Source: finite coefficient transport in the corollary proof
(blueprint: cor-pur-affine-space-zero-section-purity). -/
noncomputable def kummerZmodScalarExtensionIso
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

/-- The published finite twist line as the existing abelian-sheaf scalar extension.
Sheafify the preceding canonical scalar comparison, retaining the same roots of unity.
Source: finite coefficient transport in the corollary proof
(blueprint: cor-pur-affine-space-zero-section-purity). -/
noncomputable def kummerFiniteEtaleLineAbIso
    (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    Scheme.finiteEtaleTateLine T N A hA ≅
      (AlgebraicGeometry.Etale.extendScalars A T).obj (T.rootsOfUnitySheaf N) :=
  (presheafToSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapIso
    (Functor.isoWhiskerLeft (Scheme.finiteEtaleMuModulePresheaf T N)
      (kummerZmodScalarExtensionIso N A hA))

private theorem scalarUnit_comparison (N : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (M : ModuleCat.{u + 1} (ZMod N)) :
    ((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
      (Scheme.finiteEtaleTwistScalar N A hA)).homEquiv _ _
      ((kummerZmodScalarExtensionIso N A hA).hom.app M)).hom.toAddMonoidHom =
        ((ModuleCat.extendScalarsAddCommGrpAdj A).unit.app
          ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat).obj M)).hom := by
  unfold kummerZmodScalarExtensionIso
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rfl

private theorem rootUnit_comparison (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    Etale.ordinaryFiniteRootMap A N hA T ≫
      (Etale.moduleAbelianForget A T).map (kummerFiniteEtaleLineAbIso T N A hA).hom =
        (Etale.extendScalarsAdjunction A T).unit.app (T.rootsOfUnitySheaf N) := by
  apply Sheaf.hom_ext
  rw [Etale.extendScalarsAdjunction, Sheaf.adjunction_unit_app_hom]
  ext U z
  change (Scheme.finiteEtaleMuModulePresheaf T N).obj U at z
  have ht := congrArg (fun α ↦ α.app U)
    (toSheafify_naturality T.smallEtaleTopology
      (Functor.whiskerLeft (Scheme.finiteEtaleMuModulePresheaf T N)
        (kummerZmodScalarExtensionIso N A hA).hom))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at ht
  let adj := ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
    (Scheme.finiteEtaleTwistScalar N A hA)
  have hs := congrArg (fun k ↦ (adj.homEquiv _ _ k).hom.toAddMonoidHom) ht.symm
  simp only [Adjunction.homEquiv_naturality_right] at hs
  have hsEval := congrArg (fun k ↦ k z) hs
  have hz := congrArg (fun k ↦ k z)
    (scalarUnit_comparison N A hA ((Scheme.finiteEtaleMuModulePresheaf T N).obj U))
  simp only [ModuleCat.hom_comp, LinearMap.toAddMonoidHom_coe,
    LinearMap.coe_comp, Function.comp_apply] at hsEval hz
  dsimp only [adj, Functor.comp_obj] at hsEval hz
  rw [hz] at hsEval
  with_unfolding_all exact hsEval

/-- The root-normalized identification of the actual finite Tate boundary target
with the shifted line used by the affine-space comparison. The power map on roots
of unity supplies exponent independence; it fixes the Kummer normalization.
Source: finite etale-origin transport in the corollary proof
(blueprint: cor-pur-affine-space-zero-section-purity). -/
def kummerBoundaryTargetIso (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) :
    ((setting P n).principalSupportTate X)⟦(2 : ℤ)⟧ ≅
      AffineSpacePurity.shiftedLine (setting P n) X := by
  let Q := setting P n
  letI := Q.coefficientNeZero
  letI := Q.coefficientHasInvertibleExponent X aX
  let N := P.coefficients.l ^ (n + 1 + 1)
  let e := kummerFiniteEtaleLineAbIso X N Q.Coefficient
      (AffineSpacePurity.annihilates Q) ≪≫
    Etale.extendScalarsRootsOfUnityIsoTateTwistSheaf Q.Coefficient N
      (AffineSpacePurity.annihilates Q) (AffineSpacePurity.exponentUnit Q X aX)
  let F := VectorIntegrationSite.comparison Q.Coefficient X
  exact ((F.commShiftIso (2 : ℤ)).app _).symm ≪≫
    F.mapIso ((shiftFunctor _ (2 : ℤ)).mapIso
      (Etale.tateTwistObjectIsoSingleFunctor Q.Coefficient X 1 ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso e.symm))

private theorem principal_cartier_eq_neg_localization
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (X : Scheme.{u}) (f : Γ(X, ⊤))
    (hI : (X.zeroLocusSubschemeι {f}).ker.IsInvertible)
    (hX : IsUnit (N : Γ(X, ⊤)))
    (h : Set.range (X.zeroLocusSubschemeι {f}).base =
      (Set.range (X.basicOpen f).ι.base)ᶜ)
    (κ : Abelian.Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} A) (X.zeroLocusSubschemeι {f})).obj
        (Etale.ordinaryFiniteConstant A (X.zeroLocusSubscheme {f})))
      (Scheme.finiteEtaleTateLine X N A hA) 2)
    (hκ : Etale.SupportedKummerBoundary A N hA (X.zeroLocusSubschemeι {f}) hI hX κ) :
    κ = -Etale.finiteKummerLocalizationBoundary A N hA t
      (X.zeroLocusSubschemeι {f}) (X.basicOpen f) h hX (X.basicOpenUnit f) := by
  let k := X.zeroLocusSubschemeι {f}
  obtain ⟨C, hC, _, hCF⟩ := Etale.principal_torsor_yoneda_sign.{u}
  have heq := Etale.supported_kummer_integral_equation A N hA k hI hX κ hκ
  have hpole := Etale.principalCartierPoleLocalization X f hI C hCF h
  have hcoef := Etale.kummerLocalizationSplice A N hA t C hC k (X.basicOpen f) h hX
    (X.basicOpenUnit f)
  apply (Abelian.scalar_unit_ext_bijective (Etale.RawModuleScalarComparison.forget A X)
    (Etale.supportedIntegralGenerator A k)
    (Etale.supported_integral_derived_unit X N hN A hA k) 2).1
  dsimp only
  erw [heq, hpole]
  simpa only [← Functor.mapExtAddHom_apply, map_neg, Abelian.Ext.comp_neg,
    Abelian.Ext.neg_comp] using congrArg Neg.neg hcoef.symm

/-- The actual coordinate Kummer support boundary, before the ordered supported cup.
It is the connecting morphism of the finite coefficient sequence on the principal
open, followed by the Kummer class of the coordinate unit; no Cartier class is
chosen. Source: the principal-support boundary construction
(blueprint: cor-pur-affine-space-zero-section-purity). -/
@[irreducible]
def kummerBoundaryPro (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) (i : Fin c) :
    (cupSingle (setting P n) (iteratedAffineLine B c)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient)
        (inclusion B c i)).obj ((setting P n).constant (divisor B c i))) ⟶
      AffineSpacePurity.shiftedLine (setting P n) (iteratedAffineLine B c) :=
  (setting P n).principalSupportBoundary (iteratedAffineLine B c)
    (AffineSpacePurity.towerBase aB c) (iteratedAffineLine.coord B c i) ≫
      (kummerBoundaryTargetIso P n (iteratedAffineLine B c)
        (AffineSpacePurity.towerBase aB c)).hom

/-- The ordered supported cup product of the coordinate Kummer boundaries.
The recursion is the same canonical support intersection and cup transport as
`product`, but every factor is `kummerBoundaryPro`; thus this is a genuine
construction of `∂κ(t₁) ∪ ⋯ ∪ ∂κ(t_c)`, including the empty product.
Source: the ordered product of the coordinate Kummer boundaries in the corollary statement
(blueprint: cor-pur-affine-space-zero-section-purity). -/
@[irreducible]
def kummerProduct (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) :
    (is : List (Fin c)) →
    classSource P n B c is ⟶ target P n (iteratedAffineLine B c) is.length :=
  coordinateProductFold (classSource P n B c) (target P n (iteratedAffineLine B c))
    (coordinateProductStart (classSource_nil P n B c)
      ((cupSingle (setting P n) (iteratedAffineLine B c)).map
        ((lowerStarId (ModuleCat.{u + 1} (setting P n).Coefficient)
          (iteratedAffineLine B c)).hom.app
            ((setting P n).constant (iteratedAffineLine B c)))))
    (fun i is previous ↦ coordinateProductTransport (classSource_cons P n B c i is)
      (cupZero (setting P n) (AffineSpacePurity.towerBase aB c)
        (supportMap B c is) (inclusion B c i)
        ⟨target P n (iteratedAffineLine B c) is.length,
          target_plus P n _ (AffineSpacePurity.towerBase aB c) is.length⟩
        ⟨AffineSpacePurity.shiftedLine (setting P n) (iteratedAffineLine B c),
          boundary_plus P n _⟩
        (coordinateProductStart (classSource_eq P n B c is).symm previous)
        (kummerBoundaryPro P n B aB c i))
      (target_succ P n (iteratedAffineLine B c) is.length))

private theorem zero_shift_tensor {C : Type*} [Category C] [MonoidalCategory C]
    [HasShift C ℤ]
    [∀ K : C, ((curriedTensor C).obj K).CommShift ℤ]
    [∀ K : C, ((curriedTensor C).flip.obj K).CommShift ℤ]
    {L M F G : C} (α : L ⟶ F) (β : M ⟶ G) :
    ((α ≫ (shiftFunctorZero C ℤ).inv.app F) ⊗ₘ
      (β ≫ (shiftFunctorZero C ℤ).inv.app G)) ≫
        (cupTensorShiftIso F G 0 0).hom ≫
          (shiftFunctorZero C ℤ).hom.app (F ⊗ G) = α ⊗ₘ β := by
  simp only [cupTensorShiftIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.commShiftIso_zero,
    Functor.CommShift.isoZero_hom_app, shiftFunctorAdd_zero_add_inv_app,
    eqToHom_refl, Category.comp_id, Category.assoc]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [← (shiftFunctorZero C ℤ).inv.naturality_assoc]
  dsimp only [Functor.id_map, Functor.id_obj, curriedTensor_obj_obj,
    curriedTensor_obj_map, Functor.flip_obj_map, curriedTensor_map_app]
  simp only [Category.comp_id]
  simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  dsimp only [Functor.id_obj, Functor.flip_obj_obj, curriedTensor_obj_obj]
  simp only [Category.comp_id, Iso.inv_hom_id_app]
  simp only [Category.id_comp]
  change (α ≫ (shiftFunctorZero C ℤ).inv.app F ≫
      (shiftFunctorZero C ℤ).hom.app F ⊗ₘ β) ≫ 𝟙 (F ⊗ G) = α ⊗ₘ β
  simp

/-- The inverse coefficient tensor comparison followed by the tensor of two inputs.
Source: the supported cup composite, with both cohomological degrees zero.
(blueprint: lem-pur-coordinate-zero-cup-tensor). -/
private def zeroCupTensor (P : PurityFiniteSetting.{u}) {Z W X : Scheme.{u}}
    (i : Z ⟶ X) (j : W ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (F G : CupPlus P X)
    (α : (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)) ⟶ F.obj)
    (β : (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) j).obj (P.constant W)) ⟶ G.obj) :
    (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection i j)).obj
        (P.constant (CategoryTheory.Limits.pullback i j))) ⟶
      cupTensorObject P X F.obj G.obj :=
  @inv (CupDerivedCategory P X) _ _ _
      (cupDerivedCoefficientMap (hD := cupHasDerivedCategory P X)
        (hDM := cupMonoidal P X) (cupCoefficientMap P i j))
      (cupDerivedCoefficientMap_isIso P i j) ≫
    @MonoidalCategory.tensorHom (CupDerivedCategory P X) _
      (cupMonoidal P X).toMonoidalCategoryStruct _ _ _ _ α β

/-- The existing zero-degree supported cup is literally the unshifted tensor composite.
Source: def-pur-supported-cup and the definition of cupZero.
(blueprint: lem-pur-coordinate-zero-cup-tensor).
Proof: expand the two zero commutation isomorphisms using the commShiftIso_zero
identity, and the additive shift isomorphism using shiftFunctorAdd_zero_add. The
naturality of shiftFunctorZero moves its inverse through the shifted map.
Cancel the inverse pairs and combine tensor maps by bifunctoriality. The
coefficient comparison is the common first map and remains unchanged. -/
private theorem cupZero_tensor (P : PurityFiniteSetting.{u}) {Z W X : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k))
    (i : Z ⟶ X) (j : W ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (F G : CupPlus P X)
    (α : (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)) ⟶ F.obj)
    (β : (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) j).obj (P.constant W)) ⟶ G.obj) :
    cupZero P aX i j F G α β = zeroCupTensor P i j F G α β := by
  unfold cupZero supportedCup cupComposite zeroCupTensor
  simp only [Category.assoc]
  congr 1
  exact zero_shift_tensor α β

private theorem tensor_zsmul_neg {C : Type*} [Category C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C] {W X Y Z : C}
    (α : W ⟶ X) (β : Y ⟶ Z) (r : ℤ) :
    (r • α) ⊗ₘ (-β) = (-r) • (α ⊗ₘ β) := by
  simp only [MonoidalCategory.tensorHom_def]
  change (tensorRight Y).map (r • α) ≫ (tensorLeft X).map (-β) = _
  rw [Functor.map_zsmul, Functor.map_neg, Preadditive.zsmul_comp, Preadditive.comp_neg]
  simp only [smul_neg, neg_smul]
  rfl

private theorem cupZero_zsmul_neg (Q : PurityFiniteSetting.{u})
    {Z W X : Scheme.{u}} (aX : X ⟶ Spec (.of Q.field.k))
    (i : Z ⟶ X) (j : W ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (F G : CupPlus Q X)
    (α : (cupSingle Q X).obj
      ((lowerStar (ModuleCat.{u + 1} Q.Coefficient) i).obj (Q.constant Z)) ⟶ F.obj)
    (β : (cupSingle Q X).obj
      ((lowerStar (ModuleCat.{u + 1} Q.Coefficient) j).obj (Q.constant W)) ⟶ G.obj)
    (r : ℤ) :
    cupZero Q aX i j F G (r • α) (-β) = (-r) • cupZero Q aX i j F G α β := by
  rw [cupZero_tensor, cupZero_tensor]
  unfold zeroCupTensor
  rw [tensor_zsmul_neg, Preadditive.comp_zsmul]

private theorem kummerProduct_eq_signed_of_boundary
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ)
    (h : ∀ i : Fin c, kummerBoundaryPro P n B aB c i = -boundary P n B aB c i)
    (is : List (Fin c)) :
    kummerProduct P n B aB c is =
      ((-1 : ℤ) ^ is.length) • product P n B aB c is := by
  induction is with
  | nil => simp only [kummerProduct, product, coordinateProductFold,
      List.length_nil, pow_zero, one_smul]
  | cons i is ih =>
    simp only [kummerProduct, product, coordinateProductFold] at ih ⊢
    rw [ih, h i]
    simp only [coordinateProductStart, Preadditive.comp_zsmul]
    rw [cupZero_zsmul_neg]
    simp only [coordinateProductTransport, Preadditive.comp_zsmul,
      Preadditive.zsmul_comp, List.length_cons, pow_succ, mul_neg_one]

/-- The Kummer product transported from its literal intersection support to the
zero section by the unique support identification. Source: the class of the zero section
in the corollary statement (blueprint: cor-pur-affine-space-zero-section-purity). -/
@[irreducible]
def kummerSupportedClass (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) :
    (cupSingle (setting P n) (iteratedAffineLine B c)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B c)).obj
        ((setting P n).constant B)) ⟶ target P n (iteratedAffineLine B c) c :=
  coordinateSupportedCompose ((cupSingle (setting P n) (iteratedAffineLine B c)).map
      ((setting P n).functorialCupSupportMap true (zero B c)
        (supportMap B c (List.finRange c)) (supportIso B c).hom
        (supportIso_existsUnique B c).exists.choose_spec))
    (classSource_eq P n B c (List.finRange c)).symm
    (kummerProduct P n B aB c (List.finRange c))
    (congrArg (target P n (iteratedAffineLine B c)) (@List.length_finRange c))

/-- The closed exceptional adjunct of the actual ordered Kummer product.
Source: the isomorphism `Λ_B → Rz^!Λ(c)[2c]` of the corollary statement
(blueprint: cor-pur-affine-space-zero-section-purity). -/
@[irreducible]
def kummerThom (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    unit P n B ⟶
      (rightDerivedUpperShriek (setting P n).Coefficient (zero B c)).obj
        (target P n (iteratedAffineLine B c) c) :=
  letI := zero_exact P n B aB c
  letI : IsNoetherian (iteratedAffineLine B c) :=
    AffineSpacePurity.tower_noetherian (setting P n) B aB c
  coordinateThomAdjunct (setting P n).Coefficient (zero B c)
      (unit P n B) (target P n (iteratedAffineLine B c) c)
      (unit_origin P n B)
      (target_plus P n (iteratedAffineLine B c) (AffineSpacePurity.towerBase aB c) c) _
      (closedSingleIso (setting P n).Coefficient (zero B c) ((setting P n).constant B))
      (kummerSupportedClass P n B aB c)

private theorem kummerSupportedClass_eq_signed_of_boundary
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ)
    (h : ∀ i : Fin c, kummerBoundaryPro P n B aB c i = -boundary P n B aB c i) :
    kummerSupportedClass P n B aB c =
      ((-1 : ℤ) ^ c) • supportedClass P n B aB c := by
  unfold kummerSupportedClass supportedClass
  rw [kummerProduct_eq_signed_of_boundary P n B aB c h]
  simp only [coordinateSupportedCompose, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, List.length_finRange]

private theorem kummerThom_eq_signed_of_supported
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ)
    (h : kummerSupportedClass P n B aB c =
      ((-1 : ℤ) ^ c) • supportedClass P n B aB c) :
    kummerThom P n B aB c = ((-1 : ℤ) ^ c) • thom P n B aB c := by
  let := zero_exact P n B aB c
  let : IsNoetherian (iteratedAffineLine B c) :=
    AffineSpacePurity.tower_noetherian (setting P n) B aB c
  let e := rightDerivedUpperShriekHomEquiv (zero B c)
    (unit_origin P n B)
    (target_plus P n _ (AffineSpacePurity.towerBase aB c) c)
  have he (α) (r : ℤ) : e (r • α) = r • e α := by
    apply e.symm.injective
    rw [Equiv.symm_apply_apply]
    change _ = (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
      (zero B c)).map (r • e α) ≫ _
    rw [Functor.map_zsmul, Preadditive.zsmul_comp]
    exact congrArg (fun k ↦ r • k) (e.symm_apply_apply α).symm
  unfold kummerThom thom coordinateThomAdjunct
  change e (_ ≫ kummerSupportedClass P n B aB c) =
    ((-1 : ℤ) ^ c) • e (_ ≫ supportedClass P n B aB c)
  rw [h, Preadditive.comp_zsmul, he]

/-- The canonical closed exceptional base-change transport for the Kummer
product.  This local interface records the construction needed here because
the older generic `classBaseChange` declaration has no surviving DAG owner.
Source: base-change compatibility in the corollary statement and proof step 5
(blueprint: cor-pur-affine-space-zero-section-purity). -/
@[irreducible]
def kummerClassBaseChange (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ)
    (α : (cupSingle (setting P n) (iteratedAffineLine B c)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B c)).obj
        ((setting P n).constant B)) ⟶ target P n (iteratedAffineLine B c) c) :
    (cupSingle (setting P n) (iteratedAffineLine B' c)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B' c)).obj
        ((setting P n).constant B')) ⟶ target P n (iteratedAffineLine B' c) c :=
  classBaseChange P n g aB c α

private theorem kummerClassBaseChange_eq_signed
    (P : PurityFiniteSetting.{u}) (n : ℕ) {B' B : Scheme.{u}}
    (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ)
    (α : (cupSingle (setting P n) (iteratedAffineLine B c)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B c)).obj
        ((setting P n).constant B)) ⟶ target P n (iteratedAffineLine B c) c)
    (r : ℤ) :
    kummerClassBaseChange P n g aB c (r • α) =
      r • kummerClassBaseChange P n g aB c α := by
  unfold kummerClassBaseChange classBaseChange
  let : (AffineSpacePurity.inverseImage (setting P n).Coefficient (spaceMap g c)).Additive := by
    unfold AffineSpacePurity.inverseImage
    infer_instance
  simp only [Functor.map_zsmul, Preadditive.comp_zsmul, Preadditive.zsmul_comp]

private theorem kummer_baseChange_of_signed
    (P : PurityFiniteSetting.{u}) (n : ℕ) {B' B : Scheme.{u}}
    (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k))
    (aB' : B' ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    [LocallyOfFiniteType aB'] [QuasiCompact aB'] [IsSeparated aB']
    (hg : g ≫ aB = aB') (c : ℕ)
    (hB : kummerSupportedClass P n B aB c =
      ((-1 : ℤ) ^ c) • supportedClass P n B aB c)
    (hB' : kummerSupportedClass P n B' aB' c =
      ((-1 : ℤ) ^ c) • supportedClass P n B' aB' c) :
    kummerClassBaseChange P n g aB c (kummerSupportedClass P n B aB c) =
      kummerSupportedClass P n B' aB' c := by
  rw [hB, hB', kummerClassBaseChange_eq_signed]
  simpa only [kummerClassBaseChange] using
    congrArg (fun k ↦ ((-1 : ℤ) ^ c) • k)
      (zeroSection_purity_baseChange P n g aB aB' hg c)

private theorem kummer_normalization_of_signed
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ)
    (h : kummerThom P n B aB c = ((-1 : ℤ) ^ c) • thom P n B aB c) :
    IsIso (kummerThom P n B aB c) ∧
      kummerThom P n B aB c ≫ normalization P n B aB c =
        ((-1 : ℤ) ^ c) • 𝟙 _ ∧
      normalization P n B aB c ≫ kummerThom P n B aB c =
        ((-1 : ℤ) ^ c) • 𝟙 _ := by
  rw [h]
  have hr : ((-1 : ℤ) ^ c) * ((-1 : ℤ) ^ c) = 1 := by
    rw [← mul_pow]
    simp only [neg_one_mul, neg_neg, one_pow]
  obtain ⟨_, hfg, hgf⟩ := zeroSection_purity P n B aB c
  exact signed_inverse _ _ _ hr hfg hgf

private theorem kummerBoundaryPro_eq_neg
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) (i : Fin c) :
    kummerBoundaryPro P n B aB c i = -boundary P n B aB c i := by
  let Q := setting P n
  let X := iteratedAffineLine B c
  let f := iteratedAffineLine.coord B c i
  let N := P.coefficients.l ^ (n + 1 + 1)
  let hN : 0 < N := pow_pos (Fact.out : P.coefficients.l.Prime).pos _
  let hA := AffineSpacePurity.annihilates Q
  let hX := AffineSpacePurity.exponentUnit Q X (AffineSpacePurity.towerBase aB c)
  let t := Etale.projectiveLineTraceTransport N hN Q.Coefficient hA
  have hκ : Etale.SupportedKummerBoundary Q.Coefficient N hA
      (inclusion B c i) (coordinate_cartier B c i) hX
      (ordinaryBoundary P n B aB c i) := by
    have h := (Etale.cartier_kummer_map P.coefficients.l P.extension).2.exists.choose_spec.1
    unfold Etale.CartierEtaleKummerNormalization at h
    unfold ordinaryBoundary
    dsimp only [setting, PurityFiniteSetting.Coefficient, PurityFiniteSetting.Ring,
      PurityFiniteSetting.coefficientCommRing, PurityFiniteSetting.ringCommRing]
    with_unfolding_all
      exact h n (n + 1) hA (inclusion B c i) (coordinate_cartier B c i)
        (AffineLinePurity.primeUnit Q X (AffineSpacePurity.towerBase aB c))
  have hsign := principal_cartier_eq_neg_localization Q.Coefficient N hN hA t X f
    (coordinate_cartier B c i) hX
    (by rw [Scheme.range_zeroLocusSubschemeι_singleton, Scheme.Opens.range_ι])
    (ordinaryBoundary P n B aB c i) hκ
  have hcompare := principalSupportBoundary_finiteComparison Q N hA t
    (fun Y ↦ kummerFiniteEtaleLineAbIso Y N Q.Coefficient hA)
    (fun Y ↦ rootUnit_comparison Y N Q.Coefficient hA)
    (fun W aW hW s ↦ by
      let := Q.coefficientNeZero
      let := Q.coefficientHasInvertibleExponent W aW
      exact Etale.finiteKummerUnit_normalization Q.Coefficient W N hA hW
        (kummerFiniteEtaleLineAbIso W N Q.Coefficient hA)
        (rootUnit_comparison W N Q.Coefficient hA) s)
    X (AffineSpacePurity.towerBase aB c) hX f
  have hk : kummerBoundaryPro P n B aB c i =
      realizeBoundary Q.Coefficient (inclusion B c i) _ _
        (Etale.finiteKummerLocalizationBoundary Q.Coefficient N hA t
          (inclusion B c i) (X.basicOpen f)
          (by rw [Scheme.range_zeroLocusSubschemeι_singleton, Scheme.Opens.range_ι])
          hX (X.basicOpenUnit f)) := by
    with_unfolding_all
      simpa only [Q, X, f, N, kummerBoundaryPro, kummerBoundaryTargetIso,
        cupSingle, supportedHomSource, PurityFiniteSetting.constant,
        PurityFiniteSetting.constantEtale, Etale.ordinaryFiniteConstant,
        AffineSpacePurity.shiftedLine, Etale.ordinaryFiniteLine,
        Etale.ordinaryFiniteDegreeZero,
        Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
        Category.assoc] using hcompare
  rw [hk]
  unfold boundary
  rw [hsign]
  simp only [realizeBoundary, Abelian.Ext.neg_hom, Functor.map_neg,
    Preadditive.comp_neg, neg_neg]
  rfl

/-- The signed, base-change-compatible zero-section purity statement.

Source: the complete statement of
`literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
cor-pur-affine-space-zero-section-purity.md`
(blueprint: cor-pur-affine-space-zero-section-purity).

The first three conjuncts render the canonical Kummer orientation, the signed
inverse normalization, and both inverse equations.  The next two conjuncts
render the Cartier product normalization.  The sixth conjunct is the
untwisted form.  The final universal conjunct renders arbitrary base change of
the actual ordered Kummer product through `kummerClassBaseChange`.

The proof follows the five blueprint steps recorded in the module
docstring: ordinary affine-line adjunction and the zero-section composition;
the projective-line Cartier normalization with the principal-torsor sign;
iteration of the ordered supported cup and the comparison inverse; transport
to the finite étale-origin coefficient objects; and arbitrary base change of
all coordinate maps, support maps, and cup operations.  The base-change mate
is written as a separate concrete definition because the older generic
`classBaseChange` declaration has no surviving DAG owner.
-/
theorem zeroSection_purity_signed_statement (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    let n := P.level - 1
    IsIso (kummerThom P n B aB c) ∧
      kummerThom P n B aB c ≫ normalization P n B aB c =
        ((-1 : ℤ) ^ c) • 𝟙 _ ∧
      normalization P n B aB c ≫ kummerThom P n B aB c =
        ((-1 : ℤ) ^ c) • 𝟙 _ ∧
      thom P n B aB c ≫ normalization P n B aB c = 𝟙 _ ∧
      normalization P n B aB c ≫ thom P n B aB c = 𝟙 _ ∧
      Nonempty
        ((rightDerivedUpperShriek (setting P n).Coefficient (zero B c)).obj
            (unit P n (iteratedAffineLine B c)) ≅
          ((setting P n).functorialCupSingle true B).obj
            ((setting P n).functorialCupTwist true B (-(c : ℤ)))⟦-(2 * (c : ℤ))⟧) ∧
      (∀ {B' B₀ : Scheme.{u}} (g : B' ⟶ B₀)
          (aB₀ : B₀ ⟶ Spec (.of P.field.k))
          (aB' : B' ⟶ Spec (.of P.field.k))
          [LocallyOfFiniteType aB₀] [QuasiCompact aB₀] [IsSeparated aB₀]
          [LocallyOfFiniteType aB'] [QuasiCompact aB'] [IsSeparated aB']
          (hg : g ≫ aB₀ = aB') ,
          kummerClassBaseChange P n g aB₀ c (kummerSupportedClass P n B₀ aB₀ c) =
            kummerSupportedClass P n B' aB' c)
    := by
  let n := P.level - 1
  have hsign (X : Scheme.{u}) (aX : X ⟶ Spec (.of P.field.k)) :
      kummerSupportedClass P n X aX c =
        ((-1 : ℤ) ^ c) • supportedClass P n X aX c :=
    kummerSupportedClass_eq_signed_of_boundary P n X aX c
      (kummerBoundaryPro_eq_neg P n X aX c)
  obtain ⟨hiso, hleft, hright⟩ := kummer_normalization_of_signed P n B aB c
    (kummerThom_eq_signed_of_supported P n B aB c (hsign B aB))
  obtain ⟨_, hcartier, hcartier'⟩ := zeroSection_purity P n B aB c
  refine ⟨hiso, hleft, hright, hcartier, hcartier',
    zeroSection_purity_untwisted P n B aB c, ?_⟩
  intro B' B₀ g aB₀ aB' _ _ _ _ _ _ hg
  exact kummer_baseChange_of_signed P n g aB₀ aB' hg c (hsign B₀ aB₀) (hsign B' aB')

end AlgebraicGeometry.ProEtale.AffineZeroPurity
