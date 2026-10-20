/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
public import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import Sheaf.Algebra.Homology.SignedDoubleHomCone

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.CategoryTheory.ScalarLocalization
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.HomComplexGlobalHomotopyOfUniverses
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.HomTensorTotal
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-! # Coefficient biduality, signed shifts, triangles and scalar localization

Source: Stacks Project, sites-cohomology.tex, Tags 08JC, 0A97 and 08JB;
blueprint lem-coef-rational-retract-evaluation, proof paragraph 3
(blueprint: lem-coef-rational-bidual-triangle-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe c v r w w' a b k
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RingedHomUniverses CategoryTheory.Pretriangulated
namespace CategoryTheory.CoefficientBidual

section General
variable {E : Type a} [Category.{b} E] [Preadditive E] [HasZeroObject E]
  [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
  (F : E ⥤ E) (d : 𝟭 E ⟶ F) [F.CommShift ℤ]

/-- All three triangle squares, and closure of the invertibility locus.
Source: Stacks 08JC and derived.tex 0144
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def TriangleCompatibility : Prop :=
  F.IsTriangulated ∧ NatTrans.CommShift d ℤ ∧
    (∀ T : Triangle E, T ∈ distTriang E →
      ∃ m : T ⟶ F.mapTriangle.obj T,
        m.hom₁ = d.app T.obj₁ ∧ m.hom₂ = d.app T.obj₂ ∧ m.hom₃ = d.app T.obj₃) ∧
    (∀ (X : E) (n : ℤ), IsIso (d.app X) ↔ IsIso (d.app (X⟦n⟧))) ∧
    (∀ T : Triangle E, T ∈ distTriang E →
      (IsIso (d.app T.obj₁) ∧ IsIso (d.app T.obj₂) → IsIso (d.app T.obj₃)) ∧
      (IsIso (d.app T.obj₁) ∧ IsIso (d.app T.obj₃) → IsIso (d.app T.obj₂)) ∧
      (IsIso (d.app T.obj₂) ∧ IsIso (d.app T.obj₃) → IsIso (d.app T.obj₁)))

/-- Scalar extension of an exact shift-compatible transformation: its components are Q(d), and its
shift comparison is the scalar extension of the given comparison.
Source: blueprint scalar localization and Stacks 08JC
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def ScalarCompatibility (A : Type k) [CommRing A] [Linear A E]
    [F.Additive] [F.Linear A] (s : A)
    [HasZeroObject (ScalarLocalization A E s)] [HasShift (ScalarLocalization A E s) ℤ]
    [∀ n : ℤ, (shiftFunctor (ScalarLocalization A E s) n).Additive]
    [Pretriangulated (ScalarLocalization A E s)]
    [(ScalarLocalization.localization A E s).CommShift ℤ] : Prop :=
  ∃ S : (ScalarLocalization.map A E s F).CommShift ℤ,
    (fun [_shiftInst : (ScalarLocalization.map A E s F).CommShift ℤ] ↦
      ∃ delta : 𝟭 (ScalarLocalization A E s) ⟶ ScalarLocalization.map A E s F,
        (∀ X : ScalarLocalization A E s,
          delta.app X = (ScalarLocalization.localization A E s).map (d.app X.obj)) ∧
        (∀ (X : E) (n : ℤ),
          (ScalarLocalization.map A E s F).map
              (((ScalarLocalization.localization A E s).commShiftIso n).hom.app X) ≫
            ((ScalarLocalization.map A E s F).commShiftIso n).hom.app
              ((ScalarLocalization.localization A E s).obj X) =
          (ScalarLocalization.localization A E s).map ((F.commShiftIso n).hom.app X) ≫
            ((ScalarLocalization.localization A E s).commShiftIso n).hom.app (F.obj X)) ∧
        TriangleCompatibility (ScalarLocalization.map A E s F) delta) (_shiftInst := S)
end General

section Site
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]

/-- Coefficient duality is the recorded Hom with target O[0].
Source: Stacks 0A97
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def dual : (D.{c, v, r, w} J R)ᵒᵖ ⥤ D.{c, v, r, w} J R :=
  Prod.sectL _ (ringedSiteDualityUnit.{c, v, r, w} J R) ⋙
    derivedInternalHomOfUniverses.{c, v, r, w} J R

/-- The actual double application of coefficient duality.
Source: Stacks 0A97
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def bidual : D.{c, v, r, w} J R ⥤ D.{c, v, r, w} J R :=
  (dual.{c, v, r, w} J R).rightOp ⋙ dual.{c, v, r, w} J R

/-- The evaluation-transpose natural transformation from the dependency, unchanged.
Source: Stacks 0A97
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def evaluation (M : RingedSiteDualityModel.{c, v, r, w} J R) :
    𝟭 (D.{c, v, r, w} J R) ⟶ bidual.{c, v, r, w} J R where
  app X := ringedSiteBidual M.closed M.symmetric (ringedSiteDualityUnit.{c, v, r, w} J R) X
  naturality _ _ f := ringedSiteBidual_naturality M.closed M.symmetric
    (ringedSiteDualityUnit.{c, v, r, w} J R) f

/-- The normalized degree-one comparison, including the leading minus sign of chi.
Source: Stacks 08JC; lem-sf-double-hom-cone-comparison, formula for chi
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def signedShift (X : D.{c, v, r, w} J R) :
    (bidual.{c, v, r, w} J R).obj (X⟦(1 : ℤ)⟧) ⟶ ((bidual.{c, v, r, w} J R).obj X)⟦(1 : ℤ)⟧ :=
  -((derivedInternalHomOfUniverses.{c, v, r, w} J R).map
      (Prod.mkHom ((sourceShift.{c, v, r, w} J R X 1).hom.app
          (ringedSiteDualityUnit.{c, v, r, w} J R)).op
        (𝟙 (ringedSiteDualityUnit.{c, v, r, w} J R))) ≫
    (sourceShift.{c, v, r, w} J R ((dual.{c, v, r, w} J R).obj (op X)) (-1)).inv.app
      (ringedSiteDualityUnit.{c, v, r, w} J R))

/-- The bidual map is compatible with the precisely signed exact structure.
Source: Stacks 08JC, 0A97; derived.tex 0144
(blueprint: lem-coef-rational-bidual-triangle-compatibility).
Proof: (1) Fix a K-injective coefficient resolution I. Hom(-,I) inverts quasi-isomorphisms,
twice, so its double application represents bidual. (2) On K-flat representatives tensor-Hom
currying sends g to (x tensor y ↦ g(x)(y)); the differential is d_I g(x)(y) - (-1)^n g(dx)(y) -
(-1)^(n+p) g(x)(dy). (3) The chain map b(x)(f)=(-1)^(pq)f(x) is natural: expanding the Hom
differential gives b(dx)(f)=(-1)^((p+1)q)f(dx). (4) Resolve Hom(P,I) by a K-flat L. Evaluation
after symmetry is x tensor l ↦ (-1)^(pq)r(l)(x). (5) Its curry is Hom(r,I)b_P, identifying b
with the evaluation-transpose map on every derived object, by quasi-isomorphism descent. (6) The
signed double-Hom cone comparison gives chi=-s_{T(E),-1}T(s_{E,1})^{-1} and theta, intertwining
both cone arrows including -pi. Thus this exact signed comparison, rather than an arbitrary
shift comparison, preserves distinguished triangles. (7) Evaluating chi b_{E[1]} gives exponent
p+t+p(t+1)=(p+1)t modulo 2; iterate and invert for all integer shifts with coherent zero and
addition laws. (8) Naturality gives the first two squares. For the third, d_Z ≫ F(w) ≫ psi_V = w
≫ d_{V[1]} ≫ psi_V = w ≫ d_V[1]. (13) Apply triangle two-out-of-three to id and bidual, then
shift compatibility and its inverse to obtain the asserted invertibility locus. No general
reflexivity assumption is used. Slice and scalar descent are stated separately below. -/
theorem compatibility (M : RingedSiteDualityModel.{c, v, r, w} J R) :
    ∃ S : (bidual.{c, v, r, w} J R).CommShift ℤ,
      (∀ X : D.{c, v, r, w} J R,
        (@Functor.commShiftIso _ _ _ _ (bidual.{c, v, r, w} J R) ℤ _ _ _ S 1).hom.app X =
          signedShift.{c, v, r, w} J R X) ∧
      (fun [_shiftInst : (bidual.{c, v, r, w} J R).CommShift ℤ] ↦
        TriangleCompatibility (bidual.{c, v, r, w} J R) (evaluation.{c, v, r, w} J R M))
        (_shiftInst := S) := by
  sorry

section Slice
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (U : C)
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w'} (Modules.{max c v, v, r} (J.over U) (R.over U))]

/-- The existing exact slice restriction, applied to the unbounded derived category.
Source: Stacks 03DJ, 08JB
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def restriction : D.{c, v, r, w} J R ⥤ D.{max c v, v, r, w'} (J.over U) (R.over U) :=
  letI : (SheafOfModules.localizedSystemRestriction.{c, v, r} R U).Additive :=
    SheafOfModules.localizedSystemRestrictionAdditive.{c, v, r} R U
  letI := SheafOfModules.localizedSystemRestrictionLimits.{c, v, r} R U
  letI := SheafOfModules.localizedSystemRestrictionColimits.{c, v, r} R U
  Functor.mapDerivedCategory.{w, w'}
    (C₁ := Modules.{c, v, r} J R)
    (C₂ := Modules.{max c v, v, r} (J.over U) (R.over U))
    (SheafOfModules.localizedSystemRestriction.{c, v, r} R U)

/-- The inherited shift comparison of exact slice restriction.
Source: Stacks 03DJ, 08JB
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
instance restrictionCommShift : (restriction.{c, v, r, w, w'} J R U).CommShift ℤ :=
  letI : (SheafOfModules.localizedSystemRestriction.{c, v, r} R U).Additive :=
    SheafOfModules.localizedSystemRestrictionAdditive.{c, v, r} R U
  letI := SheafOfModules.localizedSystemRestrictionLimits.{c, v, r} R U
  letI := SheafOfModules.localizedSystemRestrictionColimits.{c, v, r} R U
  inferInstanceAs ((Functor.mapDerivedCategory.{w, w'}
    (C₁ := Modules.{c, v, r} J R)
    (C₂ := Modules.{max c v, v, r} (J.over U) (R.over U))
    (SheafOfModules.localizedSystemRestriction.{c, v, r} R U)).CommShift ℤ)

/-- The double-Hom comparison formed from the restriction comparison and coefficient unit.
Source: Stacks 08JB, 0A97
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def restrictionBidualIso
    (h : derivedInternalHomOfUniverses.{c, v, r, w} J R ⋙ restriction.{c, v, r, w, w'} J R U ≅
      ((restriction.{c, v, r, w, w'} J R U).op.prod
        (restriction.{c, v, r, w, w'} J R U)) ⋙
          derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U))
    (o : (restriction.{c, v, r, w, w'} J R U).obj (ringedSiteDualityUnit.{c, v, r, w} J R) ≅
      ringedSiteDualityUnit.{max c v, v, r, w'} (J.over U) (R.over U))
    (X : D.{c, v, r, w} J R) :
    (restriction.{c, v, r, w, w'} J R U).obj ((bidual.{c, v, r, w} J R).obj X) ≅
      (bidual.{max c v, v, r, w'} (J.over U) (R.over U)).obj
        ((restriction.{c, v, r, w, w'} J R U).obj X) :=
  h.app (op ((dual.{c, v, r, w} J R).obj (op X)),
      ringedSiteDualityUnit.{c, v, r, w} J R) ≪≫
    (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)).mapIso
      (((h.app (op X, ringedSiteDualityUnit.{c, v, r, w} J R)).symm.op).prod o) ≪≫
    (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)).mapIso
      (((derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)).mapIso
        ((Iso.refl (op ((restriction.{c, v, r, w, w'} J R U).obj X))).prod o.symm)).op.prod
          (Iso.refl _))

/-- Exact slice restriction transports the signed bidual triangle morphism. The comparisons are
formed from the evaluation-compatible tensor/Hom restriction comparisons, by the same double-Hom
formula as the dependency's restriction theorem.
Source: Stacks 08JB, 0A97, 08JC
(blueprint: lem-coef-rational-bidual-triangle-compatibility).
Proof: (9) On V to U, both restricted Hom complexes consist of the same families of module maps
on C/V, with differential d_I f-(-1)^n f d_E. Products are sectionwise.The exact j_! adjunction
shows j*I is K-injective, so these componentwise identities compute the derived restriction
comparisons. (10) Reindexing and the signs in s, and the leading minus in chi, restrict
unchanged. Change of K-injective target commutes with evaluation and those signs, so this
calculation is independent of the chosen resolutions. The dependency's evaluation-transpose
restriction square is exactly the equation for beta below. Naturality and the shift equation for
beta transport all three triangle squares; the last displayed equation records the connecting
square explicitly. Restriction is exact because termwise restriction preserves kernels and
cokernels and commutes with cones and shifts. -/
theorem slice_compatibility
    (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (MU : RingedSiteDualityModel.{max c v, v, r, w'} (J.over U) (R.over U))
    [(bidual.{c, v, r, w} J R).CommShift ℤ]
    [(bidual.{max c v, v, r, w'} (J.over U) (R.over U)).CommShift ℤ]
    (hS : ∀ X : D.{c, v, r, w} J R,
      ((bidual.{c, v, r, w} J R).commShiftIso (1 : ℤ)).hom.app X =
        signedShift.{c, v, r, w} J R X)
    (hSU : ∀ X : D.{max c v, v, r, w'} (J.over U) (R.over U),
      ((bidual.{max c v, v, r, w'} (J.over U) (R.over U)).commShiftIso (1 : ℤ)).hom.app X =
        signedShift.{max c v, v, r, w'} (J.over U) (R.over U) X) :
    ∃ (h : derivedInternalHomOfUniverses.{c, v, r, w} J R ⋙
          restriction.{c, v, r, w, w'} J R U ≅
        ((restriction.{c, v, r, w, w'} J R U).op.prod
          (restriction.{c, v, r, w, w'} J R U)) ⋙
            derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U))
      (o : (restriction.{c, v, r, w, w'} J R U).obj (ringedSiteDualityUnit.{c, v, r, w} J R) ≅
        ringedSiteDualityUnit.{max c v, v, r, w'} (J.over U) (R.over U))
      (t : M.closed.tensor ⋙ restriction.{c, v, r, w, w'} J R U ≅
        ((restriction.{c, v, r, w, w'} J R U).prod
          (restriction.{c, v, r, w, w'} J R U)) ⋙ MU.closed.tensor),
      (∀ X Y : D.{c, v, r, w} J R,
        (restriction.{c, v, r, w, w'} J R U).map (M.closed.evaluation X Y) =
          t.hom.app ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op X, Y), X) ≫
            MU.closed.tensor.map (Prod.mkHom (h.hom.app (op X, Y)) (𝟙 _)) ≫
              MU.closed.evaluation ((restriction.{c, v, r, w, w'} J R U).obj X)
                ((restriction.{c, v, r, w, w'} J R U).obj Y)) ∧
      ∃ beta : bidual.{c, v, r, w} J R ⋙ restriction.{c, v, r, w, w'} J R U ≅
          restriction.{c, v, r, w, w'} J R U ⋙
            bidual.{max c v, v, r, w'} (J.over U) (R.over U),
        (∀ X : D.{c, v, r, w} J R, beta.app X =
          restrictionBidualIso.{c, v, r, w, w'} J R U h o X) ∧
        NatTrans.CommShift beta.hom ℤ ∧
        (∀ X : D.{c, v, r, w} J R,
          (restriction.{c, v, r, w, w'} J R U).map ((evaluation.{c, v, r, w} J R M).app X) ≫
            beta.hom.app X =
              (evaluation.{max c v, v, r, w'} (J.over U) (R.over U) MU).app
                ((restriction.{c, v, r, w, w'} J R U).obj X)) ∧
        (∀ T : Triangle (D.{c, v, r, w} J R), T ∈ distTriang _ →
          (restriction.{c, v, r, w, w'} J R U).map
              ((evaluation.{c, v, r, w} J R M).app T.obj₃ ≫
                (bidual.{c, v, r, w} J R).map T.mor₃ ≫
                  signedShift.{c, v, r, w} J R T.obj₁) ≫
            ((restriction.{c, v, r, w, w'} J R U).commShiftIso (1 : ℤ)).hom.app
              ((bidual.{c, v, r, w} J R).obj T.obj₁) ≫ (beta.hom.app T.obj₁)⟦(1 : ℤ)⟧' =
          (evaluation.{max c v, v, r, w'} (J.over U) (R.over U) MU).app
              ((restriction.{c, v, r, w, w'} J R U).obj T.obj₃) ≫
            (bidual.{max c v, v, r, w'} (J.over U) (R.over U)).map
              (((restriction.{c, v, r, w, w'} J R U).mapTriangle.obj T).mor₃) ≫
            signedShift.{max c v, v, r, w'} (J.over U) (R.over U)
              ((restriction.{c, v, r, w, w'} J R U).obj T.obj₁)) := by
  sorry
end Slice

/-- The induced action of a coefficient endomorphism, through the tensor unit.Endomorphisms of O[0]
are global coefficient sections, so a ring map into this endomorphism ring is the central
coefficient action in the statement.
Source: Stacks 0A97
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def coefficientScalar (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (e : End (ringedSiteDualityUnit.{c, v, r, w} J R)) (X : D.{c, v, r, w} J R) : X ⟶ X :=
  (M.closed.monoidal.rightUnitor X).inv ≫
    M.closed.tensor.map (Prod.mkHom (𝟙 X) (M.unitIso.hom ≫ e ≫ M.unitIso.inv)) ≫
      (M.closed.monoidal.rightUnitor X).hom

section Subcategory
variable (P : ObjectProperty (D.{c, v, r, w} J R))
  (hdual : ∀ X : D.{c, v, r, w} J R, P X → P ((dual.{c, v, r, w} J R).obj (op X)))

/-- Restriction of the actual double dual to a full dual-stable subcategory.
Source: blueprint lem-coef-rational-retract-evaluation, proof paragraph 3
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def subcategoryBidual : P.FullSubcategory ⥤ P.FullSubcategory :=
  P.lift (P.ι ⋙ bidual.{c, v, r, w} J R)
    (fun X ↦ hdual _ (hdual X.obj X.property))

/-- The same evaluation map, viewed in the full subcategory.
Source: Stacks 0A97
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def subcategoryEvaluation (M : RingedSiteDualityModel.{c, v, r, w} J R) :
    𝟭 P.FullSubcategory ⟶ subcategoryBidual.{c, v, r, w} J R P hdual where
  app X := ObjectProperty.homMk ((evaluation.{c, v, r, w} J R M).app X.obj)
  naturality _ _ f := ObjectProperty.hom_ext _
    ((evaluation.{c, v, r, w} J R M).naturality f.hom)

/-- Central coefficient scalars make the actual restricted double dual linear.
Source: Stacks 0A8X, 0A97
(blueprint: lem-coef-rational-bidual-triangle-compatibility).
Proof: Step 11 of the node. Precomposition on Hom complexes is additive and commutes with the
central coefficient action. Apply this twice. The identities descend to homotopy classes and to
quasi-isomorphism fractions; sums are computed using common denominators. Restrict to the full
dual-stable subcategory, whose Hom modules and scalar action are inherited from the ambient
category. -/
theorem subcategory_linearity (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (A : Type k) [CommRing A] [Linear A (D.{c, v, r, w} J R)]
    (rho : A →+* End (ringedSiteDualityUnit.{c, v, r, w} J R))
    (hcentral : ∀ (a : A) (X : D.{c, v, r, w} J R),
      a • 𝟙 X = coefficientScalar.{c, v, r, w} J R M (rho a) X) :
    ∃ add : (subcategoryBidual.{c, v, r, w} J R P hdual).Additive,
      (fun [addInst : (subcategoryBidual.{c, v, r, w} J R P hdual).Additive] ↦
        (subcategoryBidual.{c, v, r, w} J R P hdual).Linear A) (addInst := add) := by
  sorry

/-- Descent through the raw scalar localization with precisely its induced shift and image
distinguished triangles. The structural parameters describe the triangulation supplied by
exists_triangulated_scalarLocalization, rather than additional assumptions on the site or on
objects. Linearity is supplied by subcategory_linearity.
Source: Stacks 08JC, 0A97; blueprint lem-coef-rational-retract-evaluation, paragraph 3
(blueprint: lem-coef-rational-bidual-triangle-compatibility).
Proof: Restrict the exact signed structure of compatibility to the full subcategory. Step 12
extends its functor by f tensor a ↦ F(f) tensor a, its evaluation by tensoring with 1, and its
shift comparison by tensoring with 1 and using Q's shift comparison. Balancing follows from
subcategory_linearity. Naturality holds on pure tensors and then on sums. Every localized
distinguished triangle is isomorphic to an image triangle, by the scalar-localization
triangulated lemma. Thus exactness and all three squares descend, including the connecting
square for triangles with fractional arrows. Step 13 applies triangle two-out-of-three to id and
the descended exact functor. The invertibility locus is shift-closed by compatibility and its
inverse. The inclusion equation below pins the original signed comparison, and the Q equation
pins its scalar extension at every integer shift. No individual bidual map is assumed
invertible, and no idempotent completion is taken. -/
theorem scalar_compatibility (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (A : Type k) [CommRing A] [Linear A (D.{c, v, r, w} J R)]
    [P.IsTriangulated] [(shiftFunctor P.FullSubcategory (1 : ℤ)).Linear A] (s : A)
    [(subcategoryBidual.{c, v, r, w} J R P hdual).Additive]
    [(subcategoryBidual.{c, v, r, w} J R P hdual).Linear A]
    [HasZeroObject (ScalarLocalization A P.FullSubcategory s)]
    [HasShift (ScalarLocalization A P.FullSubcategory s) ℤ]
    [∀ n : ℤ, (shiftFunctor (ScalarLocalization A P.FullSubcategory s) n).Additive]
    [(ScalarLocalization.localization A P.FullSubcategory s).CommShift ℤ]
    [Pretriangulated (ScalarLocalization A P.FullSubcategory s)]
    [IsTriangulated (ScalarLocalization A P.FullSubcategory s)]
    [(ScalarLocalization.localization A P.FullSubcategory s).IsTriangulated]
    (hshift : shiftFunctor (ScalarLocalization A P.FullSubcategory s) (1 : ℤ) =
      ScalarLocalization.map A P.FullSubcategory s (shiftFunctor P.FullSubcategory (1 : ℤ)))
    (hQ : ∀ X : P.FullSubcategory,
      HEq (((ScalarLocalization.localization A P.FullSubcategory s).commShiftIso (1 : ℤ)).hom.app X)
        (𝟙 ((ScalarLocalization.localization A P.FullSubcategory s).obj (X⟦(1 : ℤ)⟧))))
    (htriangles : ∀ T : Triangle (ScalarLocalization A P.FullSubcategory s),
      T ∈ distTriang _ ↔ ∃ T' : Triangle P.FullSubcategory,
        T' ∈ distTriang _ ∧
          Nonempty (T ≅
            (ScalarLocalization.localization A P.FullSubcategory s).mapTriangle.obj T')) :
    ∃ subShift : (subcategoryBidual.{c, v, r, w} J R P hdual).CommShift ℤ,
      (fun [subShiftInst : (subcategoryBidual.{c, v, r, w} J R P hdual).CommShift ℤ] ↦
        (∀ X : P.FullSubcategory,
          P.ι.map (((subcategoryBidual.{c, v, r, w} J R P hdual).commShiftIso (1 : ℤ)).hom.app X) ≫
            (P.ι.commShiftIso (1 : ℤ)).hom.app
              ((subcategoryBidual.{c, v, r, w} J R P hdual).obj X) =
            (bidual.{c, v, r, w} J R).map ((P.ι.commShiftIso (1 : ℤ)).hom.app X) ≫
              signedShift.{c, v, r, w} J R X.obj) ∧
        TriangleCompatibility (subcategoryBidual.{c, v, r, w} J R P hdual)
          (subcategoryEvaluation.{c, v, r, w} J R P hdual M) ∧
        ScalarCompatibility (subcategoryBidual.{c, v, r, w} J R P hdual)
          (subcategoryEvaluation.{c, v, r, w} J R P hdual M) A s)
        (subShiftInst := subShift) := by
  sorry


end Subcategory
end Site
end CategoryTheory.CoefficientBidual
