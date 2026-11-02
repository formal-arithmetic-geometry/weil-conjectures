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
def zeroBottomInput (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) (X : Scheme.{u}) (r : ℕ) :
    c.derived P.coefficients.l X :=
  ((DerivedCategory.singleFunctor _ 0).obj
    (spInternalSignedTwist X (condensedRingObj (c.obj P.coefficients.l) X)
      (c.firstLine P.coefficients.l X) (r : ℤ))) ⟦2 * (r : ℤ)⟧

variable {P : PurityFiniteSetting.{u}} {B : Scheme.{u}}
  {hB : B ⟶ Spec (.of P.field.k)}
  [IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB] {r : ℕ}

/-- The actual derived support object, using the canonical open complement of z.
Source: blueprint Step 3 and sk-lem-formal-closed-support
(blueprint: lem-pur-zero-section-bottom-coefficients). -/
def zeroBottomSupport {P : PurityFiniteSetting.{u}} {B : Scheme.{u}}
    {hB : B ⟶ Spec (.of P.field.k)}
    [IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB] {r : ℕ}
    (V : PurityVectorBundle P B hB r) (c : PurityTransport.Coefficient P.coefficients.l) :
    c.derived P.coefficients.l B :=
  letI := (V.zeroSection_spec).2.1
  (closedSupport (c.obj P.coefficients.l) V.zeroSection
    V.zeroSection.openComplement.ι).rightDerivedFunctor.obj (zeroBottomInput P c V.E r)

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

end WeilConjectures.PurityFiniteSetting
