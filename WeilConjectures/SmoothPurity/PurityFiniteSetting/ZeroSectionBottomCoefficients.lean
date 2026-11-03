/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityVectorBundle.PurityVectorBundleZeroSection
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleFiniteTypeFrames
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteZerothHypercohomologyOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.ProEtaleFiniteProjectiveDualizable
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.CategoryTheory.Integral.IntegralResidueTensorPresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Sites.Spaces
public import WeilConjectures.Algebra.Homology.Ringed.RingedSiteFiniteRetractDualExact
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenExtensionProducts
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafBaseChangeMates
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafClosedLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleZariskiComparison
public import WeilConjectures.CategoryTheory.DerivedInternalHomSectionsModel.DerivedInternalHomSectionsModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FormalClosedSupportGeneralField
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothDivisorNativeBottom
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ZeroSectionCoefficientSupport
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ZeroSectionFiniteNativeBound
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ZeroSectionIntegralLimit
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ZeroSectionScalarComparison

/-!
# Bottom-degree zero-section support with native coefficients

Source: latest blueprint, part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/thm-pur-localized-top-chern.proof.md,
Step 3, universal case
(blueprint: lem-pur-zero-section-bottom-coefficients).

For an open U, the free module on its representable is extension by zero of the
coefficient unit from U. Thus maps from its closed direct image are precisely
Hom(z_U* Lambda_U, Lambda_VU(r)[2r]), by open restriction and closed base change.
This presentation retains the restriction maps without choosing local resolutions.
The comparison below is H^0 of the actual closed-support adjunct.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures.PurityFiniteSetting

/-- Zariski opens as objects of the small pro-etale site, with their actual inclusions.
Source: blueprint Step 3, open restriction
(blueprint: lem-pur-zero-section-bottom-coefficients). -/
def zeroBottomOpens (B : Scheme.{u}) : B.Opens ⥤ B.ProEt where
  obj U := Scheme.ProEt.mk U.ι
  map f := ⟨Over.homMk (B.homOfLE f.le) (by simp), trivial, trivial⟩
  map_id U := by
    apply (Scheme.ProEt.forget B).map_injective
    apply Over.OverMorphism.ext
    exact (B.restrictFunctor ⋙ Over.forget B).map_id U
  map_comp f g := by
    apply (Scheme.ProEt.forget B).map_injective
    apply Over.OverMorphism.ext
    exact (B.restrictFunctor ⋙ Over.forget B).map_comp f g

set_option maxHeartbeats 1000000 in
-- The free/sheafification composite elaborates large internal-module equivalences.
/-- The sheafified free module on each representable, in the existing internal-module
category. On a Zariski open U this is u_! Lambda_U. Its maps are the canonical
extension-by-zero maps for inclusions, so precomposition is supported restriction.
Source: blueprint Step 3, adjunction and restriction
(blueprint: lem-pur-zero-section-bottom-coefficients). -/
def zeroBottomFree
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (B : Scheme.{u}) :
    B.ProEt ⥤ supportModules Λ B :=
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology B) (condensedRingObj Λ B)
  uliftYoneda.{u + 1} ⋙
    PresheafOfModules.free.{u + 1, u, u + 1} (R.obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
    PresheafOfModules.sheafification.{u + 1, u, u + 1, u + 1}
      (R := (sheafCompose (Scheme.ProEt.topology B)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (𝟙 _) ⋙
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology B) (condensedRingObj Λ B)).inverse

/-- The shifted root-normalized coefficient line; the signed powers are the recorded
Tate-twist construction, applied to the concrete root-tower first line.
Source: sk-def-sp-tate-twist and the coefficient conventions
(blueprint: lem-pur-zero-section-bottom-coefficients). -/
abbrev zeroBottomInput (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) (X : Scheme.{u}) (r : ℕ) :
    c.derived P.coefficients.l X :=
  nativeZeroInput P c X r

variable {P : PurityFiniteSetting.{u}} {B : Scheme.{u}}
  {hB : B ⟶ Spec (.of P.field.k)}
  [IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB] {r : ℕ}

/-- The actual derived support object, using the canonical open complement of z.
Source: blueprint Step 3 and sk-lem-formal-closed-support
(blueprint: lem-pur-zero-section-bottom-coefficients). -/
abbrev zeroBottomSupport {P : PurityFiniteSetting.{u}} {B : Scheme.{u}}
    {hB : B ⟶ Spec (.of P.field.k)}
    [IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB] {r : ℕ}
    (V : PurityVectorBundle P B hB r) (c : PurityTransport.Coefficient P.coefficients.l) :
    c.derived P.coefficients.l B :=
  nativeZeroSupport V c

/-- The canonical bottom map: take the closed-support adjunct and apply H^0,
normalizing H^0 of a module in degree zero by the standard single-object isomorphism.
Its codomain is Hom(u_! Lambda_U,H^0 K), canonically Gamma(U,H^0 K).
Source: blueprint Step 3, displayed bottom-degree identification
(blueprint: lem-pur-zero-section-bottom-coefficients). -/
def zeroBottomMap {P : PurityFiniteSetting.{u}} {B : Scheme.{u}}
    {hB : B ⟶ Spec (.of P.field.k)}
    [IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB] {r : ℕ}
    (V : PurityVectorBundle P B hB r) (c : PurityTransport.Coefficient P.coefficients.l)
    (U : B.Opens) :
    (((lowerStar (c.obj P.coefficients.l) V.zeroSection).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj
        ((zeroBottomFree (c.obj P.coefficients.l) B).obj ((zeroBottomOpens B).obj U)))) ⟶
      zeroBottomInput P c V.E r) →
      ((zeroBottomFree (c.obj P.coefficients.l) B).obj ((zeroBottomOpens B).obj U) ⟶
        (DerivedCategory.homologyFunctor (supportModules (c.obj P.coefficients.l) B) 0).obj
          (zeroBottomSupport V c)) :=
  fun f ↦
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app _ ≫
      (DerivedCategory.homologyFunctor _ 0).map
        ((closedSupportDerivedAdjunction _ V.zeroSection
          V.zeroSection.openComplement.ι
          V.zeroSection.range_eq_compl_range_openComplement_ι).homEquiv _ _ f)

/-- The existing section-module equivalence, restricted to the Zariski opens.
Its values are the actual sections, rather than a choice of abstract isomorphic groups.
Source: blueprint Step 3, Gamma(U,H^0 K)
(blueprint: lem-pur-zero-section-bottom-coefficients). -/
def zeroBottomSections
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (B : Scheme.{u}) (M : supportModules Λ B) :=
  (zeroBottomOpens B).op ⋙
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology B) (condensedRingObj Λ B)).functor.obj M).val.presheaf ⋙
      forget Ab

set_option maxHeartbeats 1000000 in
-- The two adjunctions elaborate large section-module equivalence expressions.
/-- Evaluate a map out of the free module at its identity generator, using the
canonical sheafification adjunction and the section-module equivalence.
Source: blueprint Step 3, unit/internal-Hom interpretation of sections
(blueprint: lem-pur-zero-section-bottom-coefficients). -/
def zeroBottomEvaluate
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (B : Scheme.{u}) (M : supportModules Λ B)
    (U : B.Opens) :
    ((zeroBottomFree Λ B).obj ((zeroBottomOpens B).obj U) ⟶ M) →
      (zeroBottomSections Λ B M).obj (op U) := by
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology B) (condensedRingObj Λ B)
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology B) (condensedRingObj Λ B)
  let S := (sheafCompose (Scheme.ProEt.topology B)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  intro f
  let h := e.counitIso.inv.app _ ≫ e.functor.map f
  let g := (PresheafOfModules.sheafificationAdjunction (R := S) (𝟙 _)).homEquiv _ _ h
  exact (PresheafOfModules.freeHomEquiv g).app
    (op ((zeroBottomOpens B).obj U)) (ULift.up (𝟙 _))

/-- The native-coefficient presentations permitted by the fixed purity conventions.
An algebra embedding expresses a finite extension of the fixed F inside the standard
coefficient closure; the finite case is exactly the quotient A_n, up to presentation.
Source: def-pur-conventions and the native coefficient list in Step 3
(blueprint: lem-pur-zero-section-bottom-coefficients). -/
def zeroBottomAllowed (P : PurityFiniteSetting.{u}) :
    PurityTransport.Coefficient P.coefficients.l → Prop
  | .finite A _ _ _ => Nonempty (A ≃+* P.Ring)
  | .integers => Nonempty (P.extension →ₐ[ℚ_[P.coefficients.l]] ℚ_[P.coefficients.l])
  | .rationals => Nonempty (P.extension →ₐ[ℚ_[P.coefficients.l]] ℚ_[P.coefficients.l])
  | .integral E => Nonempty (P.extension →ₐ[ℚ_[P.coefficients.l]] E.1)
  | .rational E => Nonempty (P.extension →ₐ[ℚ_[P.coefficients.l]] E.1)
  | .closure => True

/-- Extension by zero from U, followed by exact closed direct image, in the ordinary
unbounded derived category. It represents the local supported Hom source.
Source: Step 3, open restriction and closed base change
(blueprint: lem-pur-zero-section-bottom-coefficients). -/
def zeroBottomSource (V : PurityVectorBundle P B hB r)
    (c : PurityTransport.Coefficient P.coefficients.l) :=
  zeroBottomOpens B ⋙ zeroBottomFree (c.obj P.coefficients.l) B ⋙
    DerivedCategory.singleFunctor _ 0 ⋙
      (lowerStar (c.obj P.coefficients.l) V.zeroSection).mapDerivedCategory

/-- The supported Hom presheaf, before sheafification. Its arrows are restrictions
by precomposition with actual extension-by-zero inclusions.
Source: Step 3, the displayed local supported Hom groups
(blueprint: lem-pur-zero-section-bottom-coefficients). -/
def zeroBottomHom (V : PurityVectorBundle P B hB r)
    (c : PurityTransport.Coefficient P.coefficients.l) :=
  (zeroBottomSource V c).op ⋙ yoneda.obj (zeroBottomInput P c V.E r)

/-- The canonical bottom comparison to actual sections of H^0 of the support object.
Source: Step 3, adjunction followed by bottom cohomology and unit evaluation
(blueprint: lem-pur-zero-section-bottom-coefficients). -/
def zeroBottomComparison (V : PurityVectorBundle P B hB r)
    (c : PurityTransport.Coefficient P.coefficients.l) (U : B.Opens) :=
  zeroBottomEvaluate (c.obj P.coefficients.l) B
    ((DerivedCategory.homologyFunctor _ 0).obj (zeroBottomSupport V c)) U ∘
      zeroBottomMap V c U

private theorem zeroBottomMap_bijective (V : PurityVectorBundle P B hB r)
    (c : PurityTransport.Coefficient P.coefficients.l)
    (hK : (zeroBottomSupport V c).IsGE 0) (U : B.Opens) :
    Function.Bijective (zeroBottomMap V c U) := by
  let := hK
  let A := (zeroBottomFree (c.obj P.coefficients.l) B).obj ((zeroBottomOpens B).obj U)
  let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app A
  have h := DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE
    (X := (DerivedCategory.singleFunctor _ 0).obj A) (Y := zeroBottomSupport V c) 0
  let adj := closedSupportDerivedAdjunction (c.obj P.coefficients.l) V.zeroSection
    V.zeroSection.openComplement.ι V.zeroSection.range_eq_compl_range_openComplement_ι
  exact ((Iso.homCongr e (Iso.refl _)).bijective.comp h).comp
    (adj.homEquiv _ _).bijective

private theorem zeroBottomEvaluate_bijective
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (B : Scheme.{u}) (M : supportModules Λ B)
    (U : B.Opens) : Function.Bijective (zeroBottomEvaluate Λ B M U) := by
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology B) (condensedRingObj Λ B)
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology B) (condensedRingObj Λ B)
  let S := (sheafCompose (Scheme.ProEt.topology B)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let a := PresheafOfModules.sheafificationAdjunction (R := S) (𝟙 _)
  let T := (PresheafOfModules.free S.obj).obj
    (uliftYoneda.{u + 1}.obj ((zeroBottomOpens B).obj U))
  let b := e.symm.toAdjunction.homEquiv
    ((PresheafOfModules.sheafification (R := S) (𝟙 _)).obj T) M
  exact uliftYonedaEquiv.bijective.comp
    (PresheafOfModules.freeHomEquiv.bijective.comp
      ((a.homEquiv _ _).bijective.comp b.bijective))

private theorem zeroBottomMap_naturality (V : PurityVectorBundle P B hB r)
    (c : PurityTransport.Coefficient P.coefficients.l)
    (U W : B.Opens) (f : U ⟶ W) (a : (zeroBottomHom V c).obj (op W)) :
    zeroBottomMap V c U ((zeroBottomHom V c).map f.op a) =
      (zeroBottomFree (c.obj P.coefficients.l) B).map ((zeroBottomOpens B).map f) ≫
        zeroBottomMap V c W a := by
  let g := (zeroBottomFree (c.obj P.coefficients.l) B).map ((zeroBottomOpens B).map f)
  let H := DerivedCategory.homologyFunctor (supportModules (c.obj P.coefficients.l) B) 0
  let S := DerivedCategory.singleFunctor (supportModules (c.obj P.coefficients.l) B) 0
  let L := (lowerStar (c.obj P.coefficients.l) V.zeroSection).mapDerivedCategory
  let adj := closedSupportDerivedAdjunction (c.obj P.coefficients.l) V.zeroSection
    V.zeroSection.openComplement.ι V.zeroSection.range_eq_compl_range_openComplement_ι
  let e := DerivedCategory.singleFunctorCompHomologyFunctorIso
    (supportModules (c.obj P.coefficients.l) B) 0
  change (L.obj (S.obj ((zeroBottomFree (c.obj P.coefficients.l) B).obj
    ((zeroBottomOpens B).obj W))) ⟶ zeroBottomInput P c V.E r) at a
  change e.inv.app _ ≫ H.map (adj.homEquiv _ _ (L.map (S.map g) ≫ a)) =
    g ≫ e.inv.app _ ≫ H.map (adj.homEquiv _ _ a)
  have h := adj.homEquiv_naturality_left (S.map g) a
  have he := e.inv.naturality g
  change g ≫ e.inv.app _ = e.inv.app _ ≫ H.map (S.map g) at he
  calc
    _ = e.inv.app _ ≫ H.map (S.map g ≫ adj.homEquiv _ _ a) :=
      congrArg (fun k => e.inv.app _ ≫ H.map k) h
    _ = (e.inv.app _ ≫ H.map (S.map g)) ≫ H.map (adj.homEquiv _ _ a) := by
      rw [H.map_comp, Category.assoc]
    _ = _ := by
      convert! congrArg (fun k => k ≫ H.map (adj.homEquiv _ _ a)) he.symm using 1

private theorem zeroBottomEvaluate_naturality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (B : Scheme.{u}) (M : supportModules Λ B)
    (U W : B.Opens) (f : U ⟶ W)
    (a : (zeroBottomFree Λ B).obj ((zeroBottomOpens B).obj W) ⟶ M) :
    zeroBottomEvaluate Λ B M U
      ((zeroBottomFree Λ B).map ((zeroBottomOpens B).map f) ≫ a) =
      (zeroBottomSections Λ B M).map f.op (zeroBottomEvaluate Λ B M W a) := by
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology B) (condensedRingObj Λ B)
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology B) (condensedRingObj Λ B)
  let S := (sheafCompose (Scheme.ProEt.topology B)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let adj := ((PresheafOfModules.freeAdjunction S.obj).comp
    (PresheafOfModules.sheafificationAdjunction (R := S) (𝟙 _))).comp
      e.symm.toAdjunction
  let F := (PresheafOfModules.free S.obj ⋙
    PresheafOfModules.sheafification (R := S) (𝟙 _)) ⋙ e.inverse
  let g := (zeroBottomOpens B).map f
  change (F.obj (uliftYoneda.{u + 1}.obj ((zeroBottomOpens B).obj W)) ⟶ M) at a
  change uliftYonedaEquiv.{u + 1} (adj.homEquiv _ _
    (F.map (uliftYoneda.{u + 1}.map g) ≫ a)) =
    (e.functor.obj M).val.presheaf.map g.op
      (uliftYonedaEquiv.{u + 1} (adj.homEquiv _ _ a))
  exact (congrArg uliftYonedaEquiv.{u + 1}
    (adj.homEquiv_naturality_left (uliftYoneda.{u + 1}.map g) a)).trans
      (uliftYonedaEquiv_naturality _ g.op).symm

private def zeroBottomOpensEtale (X : Scheme.{u}) : X.Opens ⥤ X.Etale where
  obj U := Scheme.opensEtale U
  map f := MorphismProperty.Over.homMk (X.homOfLE f.le) (X.homOfLE_ι _) trivial
  map_id _ := Scheme.opensEtale_hom_ext _ _
  map_comp _ _ := Scheme.opensEtale_hom_ext _ _

private instance zeroBottomOpensEtale_flat (X : Scheme.{u}) :
    RepresentablyFlat (zeroBottomOpensEtale X) := by
  constructor
  intro A
  refine @IsCofiltered.mk _ _ ?_ ?_
  · constructor
    · intro V W
      have h : ∀ a, A.hom a ∈ V.right ⊓ W.right := fun a ↦
        ⟨Scheme.mem_of_hom_opensEtale V.hom a, Scheme.mem_of_hom_opensEtale W.hom a⟩
      exact ⟨StructuredArrow.mk (Y := V.right ⊓ W.right) (Scheme.opensEtaleLift h),
        StructuredArrow.homMk (homOfLE inf_le_left) (Scheme.opensEtale_hom_ext _ _),
        StructuredArrow.homMk (homOfLE inf_le_right) (Scheme.opensEtale_hom_ext _ _), trivial⟩
    · exact fun _ _ _ _ ↦ ⟨_, 𝟙 _, by ext; exact Subsingleton.elim _ _⟩
  · exact ⟨StructuredArrow.mk (Y := ⊤) (Scheme.opensEtaleLift (fun _ ↦ trivial))⟩

private theorem zeroBottomOpensEtale_cover (X : Scheme.{u}) :
    CoverPreserving (Opens.grothendieckTopology X) X.smallEtaleTopology
      (zeroBottomOpensEtale X) where
  cover_preserve {V S} hS := by
    let ι := Σ W : X.Opens, {g : W ⟶ V // S g}
    refine X.smallEtaleTopology.superset_covering ?_
      ((Scheme.ofArrows_mem_smallEtaleTopology_iff
        (fun i : ι ↦ (zeroBottomOpensEtale X).map i.2.1)).2 ?_)
    · exact (Sieve.generate_le_iff _ _).2
        (Presieve.ofArrows_le_iff.2 fun i ↦ Sieve.image_mem_functorPushforward _ _ i.2.2)
    · ext y
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      obtain ⟨W, g, hg, hy⟩ := hS y.1 y.2
      exact ⟨⟨W, g, hg⟩, ⟨y.1, hy⟩, Subtype.ext (X.homOfLE_apply g.le _)⟩

private instance zeroBottomOpensEtale_continuous (X : Scheme.{u}) :
    (zeroBottomOpensEtale X).IsContinuous (Opens.grothendieckTopology X)
      X.smallEtaleTopology :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    (zeroBottomOpensEtale_cover X)

private instance zeroBottomOpens_continuous (X : Scheme.{u}) :
    (zeroBottomOpens X).IsContinuous (Opens.grothendieckTopology X)
      (Scheme.ProEt.topology X) := by
  exact Functor.isContinuous_comp'
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl))
    (Opens.grothendieckTopology X) X.smallEtaleTopology (Scheme.ProEt.topology X)
    (F₁ := zeroBottomOpensEtale X) (F₂ := Scheme.toProEt X)

private theorem zeroBottomSections_isSheaf
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (B : Scheme.{u}) (M : supportModules Λ B) :
    Presheaf.IsSheaf (Opens.grothendieckTopology B) (zeroBottomSections Λ B M)  := by
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology B) (condensedRingObj Λ B)
  have hM : Presheaf.IsSheaf (Scheme.ProEt.topology B)
      ((e.functor.obj M).val.presheaf ⋙ forget Ab.{u + 1}) := by
    exact Presheaf.isSheaf_comp_of_isSheaf
      (J := Scheme.ProEt.topology B) (P := (e.functor.obj M).val.presheaf)
      (forget Ab.{u + 1}) (e.functor.obj M).isSheaf
  exact (zeroBottomOpens B).op_comp_isSheaf_of_isSheaf
    (Opens.grothendieckTopology B) (Scheme.ProEt.topology B) _ hM

/-- The bottom comparison is a natural isomorphism of Zariski presheaves whenever
its actual closed-support object is connective. Source: Step 3, bottom-degree
identification and gluing in the universal vector-bundle argument.
Proof: closed-support adjunction and the derived heart-Hom theorem give the first
bijection; free-module adjunction, sheafification and Yoneda give evaluation. Their
naturality identifies the restrictions. The sections presheaf is a sheaf because the
opens functor is continuous (factor it through the small etale site), so transport
sheafhood along the resulting natural isomorphism.
(blueprint: lem-pur-zero-bottom-connective-comparison). -/
private theorem zeroBottomComparison_of_isGE (V : PurityVectorBundle P B hB r)
    (c : PurityTransport.Coefficient P.coefficients.l)
    (hK : (zeroBottomSupport V c).IsGE 0) :
    (∀ U : B.Opens, Function.Bijective (zeroBottomComparison V c U)) ∧
    (∀ (U W : B.Opens) (f : U ⟶ W) (a : (zeroBottomHom V c).obj (op W)),
      zeroBottomComparison V c U ((zeroBottomHom V c).map f.op a) =
        (zeroBottomSections (c.obj P.coefficients.l) B
          ((DerivedCategory.homologyFunctor _ 0).obj (zeroBottomSupport V c))).map f.op
            (zeroBottomComparison V c W a)) ∧
    Presheaf.IsSheaf (Opens.grothendieckTopology B) (zeroBottomHom V c) := by
  have hbij (U : B.Opens) : Function.Bijective (zeroBottomComparison V c U) :=
    (zeroBottomEvaluate_bijective _ _ _ U).comp (zeroBottomMap_bijective V c hK U)
  have hnat (U W : B.Opens) (f : U ⟶ W) (a : (zeroBottomHom V c).obj (op W)) :
      zeroBottomComparison V c U ((zeroBottomHom V c).map f.op a) =
        (zeroBottomSections (c.obj P.coefficients.l) B
          ((DerivedCategory.homologyFunctor _ 0).obj (zeroBottomSupport V c))).map f.op
            (zeroBottomComparison V c W a) := by
    dsimp only [zeroBottomComparison, Function.comp_apply]
    rw [zeroBottomMap_naturality]
    exact zeroBottomEvaluate_naturality _ _ _ U W f _
  let η : zeroBottomHom V c ⟶ zeroBottomSections (c.obj P.coefficients.l) B
      ((DerivedCategory.homologyFunctor _ 0).obj (zeroBottomSupport V c)) :=
    { app := fun U ↦ TypeCat.ofHom (zeroBottomComparison V c U.unop)
      naturality := by
        intro U W f
        ext a
        exact hnat W.unop U.unop f.unop a }
  have (U : B.Opensᵒᵖ) : IsIso (η.app U) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (hbij U.unop)
  have : IsIso η := NatIso.isIso_of_isIso_app η
  exact ⟨hbij, hnat, (Presheaf.isSheaf_of_iso_iff (asIso η)).2
    (zeroBottomSections_isSheaf _ _ _)⟩

/-- Bottom-degree supported classes for every native coefficient in the purity setting.
Source: latest blueprint, part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/thm-pur-localized-top-chern.proof.md,
Step 3, universal case,
with the native coefficient refinement in lem-pur-zero-section-bottom-coefficients
(blueprint: lem-pur-zero-section-bottom-coefficients).

Proof: Restrict the kernel defining closed support to a Zariski open. Exact open
restriction has exact extension by zero as left adjoint, hence preserves K-injectives;
this identifies the actual derived support objects and their cohomology on all opens.
For finite coefficients, trivialize V and apply affine-space zero-section purity;
its support-object isomorphism gives vanishing in all negative degrees. Vanishing
of cohomology sheaves is local, so it descends to B. For integral coefficients the
continuous coefficient unit is the derived limit of its genuine finite quotients:
the quotient tower is surjective, and the root-normalized invertible line commutes
with the sequential derived limit. Closed support, being a right adjoint, preserves
this limit. Exact scalar restriction identifies this supported tower with the same
finite support objects in the fixed integral module category, including the units
in the fiber formula. Exact countable products on the pro-etale site and the Roos
triangle imply that the derived limit of this connective tower is connective; no
Mittag-Leffler claim about its supported cohomology is needed. For the fraction
field and coefficient closure, scalar extension commutes with the open direct image
on the shifted invertible coefficient line and with its unit. The fiber description
of closed support therefore identifies scalar extension of the actual support
objects. These scalar extensions are exact: inversion of ell is flat, and the
closure is a filtered colimit of finite free field extensions. Thus they preserve
the lower bound. The same argument applies to every finite extension of F.

For every U, adjunction and open localization identify the displayed Hom group with
Hom(Lambda_U,K|U). The sheafified free representable used here is precisely extension
by zero of this unit. Since K is connective, the bottom-degree theorem for the left
exact sections functor identifies this group with Gamma(U,H^0 K). Its comparison
is obtained by applying H^0 to the closed-support adjunct and evaluating at the
identity generator, exactly zeroBottomComparison. All the adjunctions, restriction
maps and truncations are natural for successive open inclusions, proving the
stated equality. Sections of H^0 K glue uniquely, and these natural bijections
transfer sheafhood to the supported Hom presheaf. In rank zero z is an isomorphism
and this is the usual unit/sections identification. On the empty base both sides
are zero. No generator or invertible Thom arrow is selected. -/
theorem zeroSectionBottomCoefficients (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) (hB : B ⟶ Spec (.of P.field.k))
    [IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB]
    (r : ℕ) (V : PurityVectorBundle P B hB r)
    (c : PurityTransport.Coefficient P.coefficients.l) (hc : zeroBottomAllowed P c) :
    (zeroBottomSupport V c).IsGE 0 ∧
    (∀ U : B.Opens, Function.Bijective (zeroBottomComparison V c U)) ∧
    (∀ (U W : B.Opens) (f : U ⟶ W) (a : (zeroBottomHom V c).obj (op W)),
      zeroBottomComparison V c U ((zeroBottomHom V c).map f.op a) =
        (zeroBottomSections (c.obj P.coefficients.l) B
          ((DerivedCategory.homologyFunctor _ 0).obj (zeroBottomSupport V c))).map f.op
            (zeroBottomComparison V c W a)) ∧
    Presheaf.IsSheaf (Opens.grothendieckTopology B)
      (zeroBottomHom V c) := by
  have _hAllowed := hc
  cases r with
  | zero =>
      have hK : (zeroBottomSupport V c).IsGE 0 := by
        simpa using (nativeZeroSupport_isGE_neg V c)
      exact ⟨hK, zeroBottomComparison_of_isGE V c hK⟩
  | succ r =>
      have hK : (zeroBottomSupport V c).IsGE 0 := by
        exact nativeZeroSupport_isGE_of_comparisons V
          (nativeZeroSupport_finite_bound V) (nativeZeroSupport_integral_limit V)
          (nativeZeroSupport_scalar_bound V) c
      exact ⟨hK, zeroBottomComparison_of_isGE V c hK⟩

end WeilConjectures.PurityFiniteSetting
