/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.CategoryTheory.CochainCoefficientUniverseTransport
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestrictionSupplement
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage

/-! # Scheme-test restriction of quasi-coherent modules on a fibred fppf site

Source: Stacks Project, stacks-sheaves.tex, Tags 06WI, 06WK and 06WH; descent.tex,
Tags 03DX(1), 03LC(1) and 06VE(1),(3),(4),(7)
(blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction).

The coefficient lift is the existing sectionwise `ULift` construction. It allows
Zariski modules to have the same size as modules on the total site, while retaining
independent universes for schemes, site objects and site morphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w m

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped ChangeOfRings

namespace CategoryTheory

/-- The ordinary Zariski structure sheaf in the ambient coefficient universe.
Only its section carriers are lifted, by the canonical ring equivalence.
Source: Stacks 03DX (blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
abbrev schemeTestStructureSheaf (T : Scheme.{u}) :
    Sheaf (Opens.grothendieckTopology T) CommRingCat.{max u m} :=
  SheafOfModules.CochainUniverseTransport.ring.{u, u, u, u, m} T.sheaf

/-- The ring-valued ordinary structure sheaf in the common universe.
Source: Stacks 03DX (blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
abbrev schemeTestModuleRings (T : Scheme.{u}) :=
  (sheafCompose (Opens.grothendieckTopology T) (forget₂ CommRingCat RingCat)).obj
    (schemeTestStructureSheaf.{u, m} T)

/-- Zariski module sheaves, retaining arbitrary ambient-size carriers.
Source: Stacks 03DX (blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
abbrev SchemeTestModules (T : Scheme.{u}) :=
  SheafOfModules.{max u m} (schemeTestModuleRings.{u, m} T)

/-- The existing sectionwise coefficient lift on ordinary scheme modules.
Source: Stacks 03DA, 03DX
(blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
def schemeTestModuleLift (T : Scheme.{u}) :
    T.Modules ⥤ SchemeTestModules.{u, m} T :=
  SheafOfModules.CochainUniverseTransport.functor.{u, u, u, u, m} T.sheaf

/-- Pullback of regular functions, transported sectionwise by `ULift`.
Source: Stacks 0095, 03LC
(blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
def schemeTestRingMap {T' T : Scheme.{u}} (a : T' ⟶ T) :
    schemeTestModuleRings.{u, m} T ⟶
      ((TopologicalSpace.Opens.map a.base).sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology T) (Opens.grothendieckTopology T')).obj
          (schemeTestModuleRings.{u, m} T') :=
  ⟨Functor.whiskerRight a.c
    (SheafOfModules.CochainUniverseTransport.ringFunctor.{u, u, m} ⋙
      forget₂ CommRingCat RingCat)⟩

/-- The existing universe-general existence theorem supplies the canonical tensor adjoint.
Source: Stacks 03D7 (blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
instance schemeTestPullbackExists {T' T : Scheme.{u}} (a : T' ⟶ T) :
    (SheafOfModules.pushforward.{max u m} (schemeTestRingMap.{u, m} a)).IsRightAdjoint :=
  SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{u, u, m} _

/-- The usual tensor pullback on the transported ordinary structure sheaves.
Mathlib constructs it by module-presheaf pullback and sheafification, hence by
extension of scalars after inverse image, with its canonical adjunction unit.
Source: Stacks 0095--0096, 03LC
(blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
def schemeTestPullback {T' T : Scheme.{u}} (a : T' ⟶ T) :
    SchemeTestModules.{u, m} T ⥤ SchemeTestModules.{u, m} T' :=
  SheafOfModules.pullback (schemeTestRingMap.{u, m} a)

/-- Canonical identity tensor pullback.
Source: Stacks 0097 (blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
def schemeTestPullbackId (T : Scheme.{u}) :
    schemeTestPullback.{u, m} (𝟙 T) ≅ 𝟭 (SchemeTestModules.{u, m} T) :=
  SheafOfModules.pullbackId (schemeTestModuleRings.{u, m} T)

/-- Canonical composition tensor pullback.
Source: Stacks 0097 (blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
def schemeTestPullbackComp {T'' T' T : Scheme.{u}} (a : T'' ⟶ T') (b : T' ⟶ T) :
    schemeTestPullback.{u, m} b ⋙ schemeTestPullback.{u, m} a ≅
      schemeTestPullback.{u, m} (a ≫ b) :=
  SheafOfModules.pullbackComp (schemeTestRingMap.{u, m} b) (schemeTestRingMap.{u, m} a)

/-- The normalized pullback of a global section: the tensor-adjunction unit,
followed by restriction from the inverse image of the whole space to the whole space.
Source: Stacks 0096, 03LC
(blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
def schemeTestPullSection {T' T : Scheme.{u}} (a : T' ⟶ T)
    (M : SchemeTestModules.{u, m} T) (s : M.val.obj (op ⊤)) :
    ((schemeTestPullback.{u, m} a).obj M).val.obj (op ⊤) :=
  ((schemeTestPullback.{u, m} a).obj M).val.map
    (homOfLE (show (⊤ : T'.Opens) ≤ a ⁻¹ᵁ (⊤ : T.Opens) by simp)).op
    (((SheafOfModules.pullbackPushforwardAdjunction (schemeTestRingMap.{u, m} a)).unit.app
      M).val.app (op ⊤) s)

/-- The whole-space section of the recorded tensor pullback, with its recorded unit.
Source: Stacks 0095--0096
(blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
def schemeTensorPullbackGlobalSection {T' T : Scheme.{u}} (a : T' ⟶ T)
    (M : T.Modules) (s : M.val.obj (op ⊤)) :
    ((Scheme.Modules.tensorPullback a).obj M).val.obj (op ⊤) :=
  ((Scheme.Modules.tensorPullback a).obj M).val.map
    (homOfLE (show (⊤ : T'.Opens) ≤ a ⁻¹ᵁ (⊤ : T.Opens) by simp)).op
    (Scheme.Modules.tensorPullbackSection a M ⊤ s)

/-- The existing local-presentation predicate, with the original total site and rings.
Source: Stacks 06WI (blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
abbrev ModuliQCoh {S : Scheme.{u}} (C : BasedCategory.{v, w} (Over S))
    (hC : IsFibredInGroupoids C) :=
  (SheafOfModules.isQuasicoherent (moduliModuleRings C hC)).FullSubcategory

/-- The ordinary scheme underlying a test object.
Source: Stacks 06WK (blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
abbrev schemeTestBase {S : Scheme.{u}} (C : BasedCategory.{v, w} (Over S)) (x : C.obj) :=
  (moduliSchemeForget C).obj x

/-- Slice sheafification for ordinary tests in the same coefficient universe.
Source: Stacks 03DX (blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
instance schemeTestSliceHasWeakSheafify (T : Scheme.{u}) (U : T.Opens)
    [EssentiallySmall.{m} (Over U)] :
    HasWeakSheafify ((Opens.grothendieckTopology T).over U) AddCommGrpCat.{m} :=
  letI : HasSheafify ((Opens.grothendieckTopology T).over U) AddCommGrpCat.{m} :=
    SheafOfModules.hasSheafify_coefficientUniverse
  HasSheafify.isRightAdjoint

/-- The local-bijection criterion for ordinary tests in the ambient universe.
Source: Stacks 03DX (blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
instance schemeTestSliceWEqualsLocallyBijective (T : Scheme.{u}) (U : T.Opens)
    [EssentiallySmall.{m} (Over U)] :
    ((Opens.grothendieckTopology T).over U).WEqualsLocallyBijective
      AddCommGrpCat.{m} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

/-- Sheafification on the total site in a universe containing its objects and arrows.
Source: Stacks 03DA (blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
instance moduliTestHasWeakSheafify {S : Scheme.{u}} (C : BasedCategory.{v, w} (Over S))
    [EssentiallySmall.{m} C.obj] :
    HasWeakSheafify (moduliFppfTopology C) AddCommGrpCat.{m} :=
  letI : HasSheafify (moduliFppfTopology C) AddCommGrpCat.{m} :=
    SheafOfModules.hasSheafify_coefficientUniverse
  HasSheafify.isRightAdjoint

/-- The local-bijection criterion on the total site.
Source: Stacks 03DA (blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
instance moduliTestWEqualsLocallyBijective {S : Scheme.{u}}
    (C : BasedCategory.{v, w} (Over S)) [EssentiallySmall.{m} C.obj] :
    (moduliFppfTopology C).WEqualsLocallyBijective AddCommGrpCat.{m} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

/-- Sheafification on the ordinary Zariski site in the ambient universe.
Source: Stacks 03DA (blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
instance schemeTestHasWeakSheafify (T : Scheme.{u}) [EssentiallySmall.{m} T.Opens] :
    HasWeakSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{m} :=
  letI : HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{m} :=
    SheafOfModules.hasSheafify_coefficientUniverse
  HasSheafify.isRightAdjoint

/-- The local-bijection criterion on the ordinary Zariski site.
Source: Stacks 03DA (blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
instance schemeTestWEqualsLocallyBijective (T : Scheme.{u}) [EssentiallySmall.{m} T.Opens] :
    (Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{m} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

/-- Ordinary quasi-coherent modules, using the existing local-presentation predicate.
Source: Stacks 03DX (blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
abbrev SchemeTestQCoh (T : Scheme.{u}) :=
  (SheafOfModules.isQuasicoherent (schemeTestModuleRings.{u, m} T)).FullSubcategory

/-- Restriction in the associated big-site sheaf: pull back a section and use the
canonical tensor compositor. The equality is exactly the triangle in the slice.
Source: Stacks 03DX, 03LC
(blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
def schemeTestSliceTransition {S : Scheme.{u}} (C : BasedCategory.{v, w} (Over S))
    (x : C.obj) (M : SchemeTestModules.{u, m} (schemeTestBase C x))
    {z y : Over x} (b : z ⟶ y)
    (s : ((schemeTestPullback ((moduliSchemeForget C).map y.hom)).obj M).val.obj (op ⊤)) :
    ((schemeTestPullback ((moduliSchemeForget C).map z.hom)).obj M).val.obj (op ⊤) :=
  (eqToHom (congrArg (fun a ↦ (schemeTestPullback a).obj M)
    (((moduliSchemeForget C).map_comp b.left y.hom).symm.trans
      (congrArg ((moduliSchemeForget C).map) (Over.w b))))).val.app (op ⊤)
    (((schemeTestPullbackComp ((moduliSchemeForget C).map b.left)
      ((moduliSchemeForget C).map y.hom)).hom.app M).val.app (op ⊤)
        (schemeTestPullSection ((moduliSchemeForget C).map b.left)
          ((schemeTestPullback ((moduliSchemeForget C).map y.hom)).obj M) s))

/-- Witnesses for the simultaneous scheme-test comparison. The section equation fixes
all arrow comparisons as the actual restriction-induced tensor maps; in particular
no arbitrary cartesian action is supplied as a hypothesis.
Source: Stacks 06WK, 03DX and 06VE
(blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
structure ModuliSchemeRestriction {S : Scheme.{u}}
    (C : BasedCategory.{v, w} (Over S)) (hC : IsFibredInGroupoids C) where
  /-- The ambient-universe pullback agrees with the dependency's tensor pullback. -/
  tensorPullback_agreement {T' T : Scheme.{u}} (a : T' ⟶ T) :
    schemeTestModuleLift.{u, max (u + 1) v w} T ⋙ schemeTestPullback a ≅
      Scheme.Modules.tensorPullback a ⋙ schemeTestModuleLift.{u, max (u + 1) v w} T'
  /-- The agreement preserves the specified tensor unit 1 tensor s, not just adjunctions. -/
  tensorPullback_agreement_sections {T' T : Scheme.{u}} (a : T' ⟶ T)
      (M : T.Modules) (s : M.val.obj (op ⊤)) :
    ((tensorPullback_agreement a).hom.app M).val.app (op ⊤)
      (schemeTestPullSection a ((schemeTestModuleLift T).obj M) (ULift.up s)) =
        ULift.up (schemeTensorPullbackGlobalSection a M s)
  /-- Restriction to the ordinary Zariski module on each test scheme. -/
  restriction (x : C.obj) : ModuliQCoh C hC ⥤
    SchemeTestModules.{u, max (u + 1) v w} (schemeTestBase C x)
  /-- The ordinary modules are quasi-coherent. -/
  quasicoherent (x : C.obj) (F : ModuliQCoh C hC) :
    SheafOfModules.IsQuasicoherent.{max (u + 1) v w, u, u} ((restriction x).obj F)
  /-- Evaluation is the global-section comparison, with additive structure. -/
  sections (x : C.obj) (F : ModuliQCoh C hC) :
    F.obj.val.obj (op x) ≃+ ((restriction x).obj F).val.obj (op ⊤)
  /-- The comparison also respects its actual structural scalars. -/
  sections_smul (x : C.obj) (F : ModuliQCoh C hC)
      (r : (moduliModuleRings C hC).obj.obj (op x)) (s : F.obj.val.obj (op x)) :
    sections x F (r • s) = r • sections x F s
  /-- Naturality for every module morphism. -/
  sections_naturality {F G : ModuliQCoh C hC} (f : F ⟶ G) (x : C.obj)
      (s : F.obj.val.obj (op x)) :
    sections x G (f.hom.val.app (op x) s) =
      ((restriction x).map f).val.app (op ⊤) (sections x F s)
  /-- Tensor base change along every arrow, without flatness. -/
  comparison {y x : C.obj} (a : y ⟶ x) (F : ModuliQCoh C hC) :
    (schemeTestPullback ((moduliSchemeForget C).map a)).obj ((restriction x).obj F) ≅
      (restriction y).obj F
  /-- Canonical normalization: pull back a section and then apply the comparison. -/
  comparison_sections {y x : C.obj} (a : y ⟶ x) (F : ModuliQCoh C hC)
      (s : F.obj.val.obj (op x)) :
    (comparison a F).hom.val.app (op ⊤)
      (schemeTestPullSection ((moduliSchemeForget C).map a)
        ((restriction x).obj F) (sections x F s)) =
      sections y F (F.obj.val.map a.op s)
  /-- Naturality of the canonical tensor comparisons in F. -/
  comparison_naturality {y x : C.obj} (a : y ⟶ x)
      {F G : ModuliQCoh C hC} (f : F ⟶ G) :
    (schemeTestPullback ((moduliSchemeForget C).map a)).map ((restriction x).map f) ≫
      (comparison a G).hom = (comparison a F).hom ≫ (restriction y).map f
  /-- Identity compatibility includes the actual tensor-pullback unitor. -/
  comparison_id (x : C.obj) (F : ModuliQCoh C hC) :
    (comparison (𝟙 x) F).hom =
      eqToHom (congrArg (fun a ↦ (schemeTestPullback a).obj ((restriction x).obj F))
        ((moduliSchemeForget C).map_id x)) ≫
      (schemeTestPullbackId (schemeTestBase C x)).hom.app ((restriction x).obj F)
  /-- Composition compatibility includes the actual tensor-pullback compositor. -/
  comparison_comp {z y x : C.obj} (b : z ⟶ y) (a : y ⟶ x) (F : ModuliQCoh C hC) :
    (comparison (b ≫ a) F).hom =
      eqToHom (congrArg (fun a ↦ (schemeTestPullback a).obj ((restriction x).obj F))
        ((moduliSchemeForget C).map_comp b a)) ≫
      (schemeTestPullbackComp ((moduliSchemeForget C).map b)
        ((moduliSchemeForget C).map a)).inv.app ((restriction x).obj F) ≫
      (schemeTestPullback ((moduliSchemeForget C).map b)).map (comparison a F).hom ≫
      (comparison b F).hom
  /-- The associated-sheaf comparison is defined on all ordinary quasi-coherent modules. -/
  realization (x : C.obj) :
    SchemeTestQCoh.{u, max (u + 1) v w} (schemeTestBase C x) ⥤
      SheafOfModules.{max (u + 1) v w} ((moduliModuleRings C hC).over x)
  /-- Its value at every object of the slice is the full pullback-section formula. -/
  realization_sections (x : C.obj)
      (M : SchemeTestQCoh.{u, max (u + 1) v w} (schemeTestBase C x)) (z : Over x) :
    ((realization x).obj M).val.obj (op z) ≃+
      ((schemeTestPullback ((moduliSchemeForget C).map z.hom)).obj M.obj).val.obj (op ⊤)
  /-- The formula is linear in the actual regular functions on the test scheme. -/
  realization_smul (x : C.obj)
      (M : SchemeTestQCoh.{u, max (u + 1) v w} (schemeTestBase C x)) (z : Over x)
      (r : ((moduliModuleRings C hC).over x).obj.obj (op z))
      (s : ((realization x).obj M).val.obj (op z)) :
    realization_sections x M z (r • s) = r • realization_sections x M z s
  /-- All slice arrows act by pullback of sections and the canonical tensor compositor. -/
  realization_restriction (x : C.obj)
      (M : SchemeTestQCoh.{u, max (u + 1) v w} (schemeTestBase C x))
      {z y : Over x} (b : z ⟶ y) (s : ((realization x).obj M).val.obj (op y)) :
    realization_sections x M z (((realization x).obj M).val.map b.op s) =
      schemeTestSliceTransition C x M.obj b (realization_sections x M y s)
  /-- On module maps the formula is the ordinary tensor pullback of that map. -/
  realization_naturality (x : C.obj)
      {M N : SchemeTestQCoh.{u, max (u + 1) v w} (schemeTestBase C x)} (f : M ⟶ N)
      (z : Over x) (s : ((realization x).obj M).val.obj (op z)) :
    realization_sections x N z (((realization x).map f).val.app (op z) s) =
      ((schemeTestPullback ((moduliSchemeForget C).map z.hom)).map f.hom).val.app
        (op ⊤) (realization_sections x M z s)
  /-- Full faithfulness, including comparison to any other ordinary realization. -/
  realization_fullyFaithful (x : C.obj) : (realization x).FullyFaithful
  /-- The slice restriction is the associated big-site sheaf of F_x. -/
  realization_counit (x : C.obj) (F : ModuliQCoh C hC) :
    (realization x).obj ⟨(restriction x).obj F, quasicoherent x F⟩ ≅ F.obj.over x
  /-- The counit gives exactly the section coordinates of the arrow comparison. -/
  realization_counit_sections (x : C.obj) (F : ModuliQCoh C hC) (z : Over x)
      (s : ((realization x).obj ⟨(restriction x).obj F, quasicoherent x F⟩).val.obj (op z)) :
    realization_sections x ⟨(restriction x).obj F, quasicoherent x F⟩ z s =
      (comparison z.hom F).inv.val.app (op ⊤)
        (sections z.left F ((realization_counit x F).hom.val.app (op z) s))
  /-- Local sheaf surjections are exactly the maps surjective on every Zariski test. -/
  surjective_iff {F G : ModuliQCoh C hC} (f : F ⟶ G) :
    Presheaf.IsLocallySurjective (moduliFppfTopology C)
      ((SheafOfModules.toSheaf (moduliModuleRings C hC)).map f.hom).hom ↔
        ∀ x : C.obj, Epi ((restriction x).map f)
  /-- The structure module is quasi-coherent, so it belongs to the domain. -/
  unit_quasicoherent : (SheafOfModules.unit (moduliModuleRings C hC)).IsQuasicoherent
  /-- Identification with the ordinary structure module. -/
  unit_comparison (x : C.obj) :
    (restriction x).obj ⟨SheafOfModules.unit (moduliModuleRings C hC),
      unit_quasicoherent⟩ ≅ SheafOfModules.unit
        (schemeTestModuleRings.{u, max (u + 1) v w} (schemeTestBase C x))
  /-- This identification is the identity in regular-function coordinates. -/
  unit_sections (x : C.obj) (r : (moduliModuleRings C hC).obj.obj (op x)) :
    (unit_comparison x).hom.val.app (op ⊤)
      (sections x ⟨SheafOfModules.unit (moduliModuleRings C hC), unit_quasicoherent⟩ r) = r
  /-- Tensor products remain quasi-coherent. -/
  tensor_quasicoherent (F G : ModuliQCoh C hC) :
    ((SheafOfModules.siteSheafTensorRight G.obj).obj F.obj).IsQuasicoherent
  /-- Identification with the ordinary sheaf tensor product on each scheme. -/
  tensor_comparison (x : C.obj) (F G : ModuliQCoh C hC) :
    (restriction x).obj
      ⟨(SheafOfModules.siteSheafTensorRight G.obj).obj F.obj, tensor_quasicoherent F G⟩ ≅
        (SheafOfModules.siteSheafTensorRight ((restriction x).obj G)).obj
          ((restriction x).obj F)
  /-- The tensor comparison is fixed on local pure tensors, naturally in both factors. -/
  tensor_sections (x : C.obj) (F G : ModuliQCoh C hC)
      (s : F.obj.val.obj (op x)) (t : G.obj.val.obj (op x)) :
    (tensor_comparison x F G).hom.val.app (op ⊤)
      (sections x ⟨(SheafOfModules.siteSheafTensorRight G.obj).obj F.obj,
        tensor_quasicoherent F G⟩ (SheafOfModules.siteSheafTensorTmul F.obj G.obj (op x) s t)) =
      SheafOfModules.siteSheafTensorTmul ((restriction x).obj F) ((restriction x).obj G)
        (op ⊤) (sections x F s) (sections x G t)

/-- The structural ring comparison of a based functor. It is obtained solely from
its equality over Sch/S, so its components are the identity on regular functions.
Source: Stacks 06TW (blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
def moduliPrecompositionStructureIso {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C)
    [a.toFunctor.IsContinuous (moduliFppfTopology D) (moduliFppfTopology C)] :
    moduliStructureSheaf D hD ≅
      (a.toFunctor.sheafPushforwardContinuous CommRingCat
        (moduliFppfTopology D) (moduliFppfTopology C)).obj (moduliStructureSheaf C hC) :=
  let e : moduliSchemeForget D = a.toFunctor ⋙ moduliSchemeForget C := by
    dsimp only [moduliSchemeForget]
    rw [← Functor.assoc, a.w]
  let i := eqToIso (congrArg (fun B : D.obj ⥤ Scheme.{u} ↦
    B.op ⋙ Scheme.Γ ⋙
      SheafOfModules.CochainUniverseTransport.ringFunctor.{u, max (u + 1) v w, 0}) e)
  (fullyFaithfulSheafToPresheaf (moduliFppfTopology D)
    CommRingCat.{max (u + 1) v w}).preimageIso i

/-- Forget commutativity in the canonical structural comparison.
Source: Stacks 06TW (blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
def moduliPrecompositionRingIso {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C)
    [a.toFunctor.IsContinuous (moduliFppfTopology D) (moduliFppfTopology C)] :
    moduliModuleRings D hD ≅
      (a.toFunctor.sheafPushforwardContinuous RingCat
        (moduliFppfTopology D) (moduliFppfTopology C)).obj (moduliModuleRings C hC) :=
  (sheafCompose (moduliFppfTopology D)
    (forget₂ CommRingCat.{max (u + 1) v w} RingCat.{max (u + 1) v w})).mapIso
    (moduliPrecompositionStructureIso hD hC a)

/-- Precomposition on module sheaves, including the prescribed structural scalar map.
The underlying sections and restriction maps are literally those of M after a.
Source: Stacks 06WE (blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
def moduliModulePrecomposition {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C)
    [a.toFunctor.IsContinuous (moduliFppfTopology D) (moduliFppfTopology C)] :
    SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC) ⥤
      SheafOfModules.{max (u + 1) v w} (moduliModuleRings D hD) :=
  SheafOfModules.pushforward (moduliPrecompositionRingIso hD hC a).hom

/-- Module inverse image before extending scalars: its ring is a^-1 O_C itself.
Source: Stacks 06WE (blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
def moduliRawPrecomposition {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hC : IsFibredInGroupoids C)
    (a : BasedFunctor D C)
    [a.toFunctor.IsContinuous (moduliFppfTopology D) (moduliFppfTopology C)] :=
  SheafOfModules.pushforward.{max (u + 1) v w} (F := a.toFunctor)
    (J := moduliFppfTopology D) (K := moduliFppfTopology C)
    (R := moduliModuleRings C hC) (𝟙 _)

/-- The actual tensor formula O_D tensor_(a^-1 O_C) a^-1 M, with sheafification.
The structural arrow is the inverse of the canonical equality over Sch/S.
Source: Stacks 06WE (blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
def moduliTensorPrecomposition {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C)
    [a.toFunctor.IsContinuous (moduliFppfTopology D) (moduliFppfTopology C)]
    (M : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC)) :
    SheafOfModules.{max (u + 1) v w} (moduliModuleRings D hD) :=
  SheafOfModules.changeOfRingsOfUniverses.{v, w, max (u + 1) v w, max (u + 1) v w}
    (moduliPrecompositionStructureIso hD hC a).inv
    ((moduliRawPrecomposition hC a).obj M)

/-- The local tensor r tensor m in the actual scalar-extension sheaf.
Source: Stacks 06WE (blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
def moduliTensorPrecompositionTmul {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C)
    [a.toFunctor.IsContinuous (moduliFppfTopology D) (moduliFppfTopology C)]
    (M : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC)) (d : D.obj)
    (r : (moduliModuleRings D hD).obj.obj (op d))
    (s : M.val.obj (op (a.toFunctor.obj d))) :
    (moduliTensorPrecomposition hD hC a M).val.obj (op d) :=
  ((PresheafOfModules.sheafificationAdjunction
    (R := moduliModuleRings D hD) (𝟙 _)).unit.app
      (SheafOfModules.changeOfRingsPresheafOfUniverses.{v, w,
        max (u + 1) v w, max (u + 1) v w}
        (moduliPrecompositionStructureIso hD hC a).inv
          ((moduliRawPrecomposition hC a).obj M))).app (op d)
    (r ⊗ₜ[(moduliStructureSheaf C hC).obj.obj (op (a.toFunctor.obj d)),
      ((moduliPrecompositionStructureIso hD hC a).inv.hom.app (op d)).hom] s)

/-- The geometric and quasi-coherent properties of the explicitly defined precomposition.
A left exact left adjoint is the inverse image of a geometric morphism. Its structural
map is the preceding canonical ring isomorphism, so extension of scalars is tensor
pullback, with local formula r tensor m ↦ r m and m ↦ 1 tensor m.
Source: Stacks 06TS, 06TW, 06WE, 06WH
(blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction). -/
structure ModuliQuasicoherentPrecomposition {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) where
  /-- Precomposition sends sheaves to sheaves. -/
  continuous : a.toFunctor.IsContinuous (moduliFppfTopology D) (moduliFppfTopology C)
  /-- On sets it has a right adjoint, in the geometric inverse-image direction. -/
  inverseImageLeftAdjoint :
    (@Functor.sheafPushforwardContinuous _ _ _ _ a.toFunctor (Type (max (u + 1) v w))
      _ (moduliFppfTopology D) (moduliFppfTopology C) continuous).IsLeftAdjoint
  /-- This inverse image is left exact. -/
  inverseImageLeftExact : PreservesFiniteLimits
    (@Functor.sheafPushforwardContinuous _ _ _ _ a.toFunctor (Type (max (u + 1) v w))
      _ (moduliFppfTopology D) (moduliFppfTopology C) continuous)
  /-- Tensor pullback is canonically isomorphic to literal precomposition on all modules. -/
  tensor_comparison (M : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC)) :
    @moduliTensorPrecomposition S D C hD hC a continuous M ≅
      (@moduliModulePrecomposition S D C hD hC a continuous).obj M
  /-- The tensor comparison is the canonical multiplication map, on every local tensor. -/
  tensor_sections (M : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC))
      (d : D.obj) (r : (moduliModuleRings D hD).obj.obj (op d))
      (s : M.val.obj (op (a.toFunctor.obj d))) :
    (tensor_comparison M).hom.val.app (op d)
      (@moduliTensorPrecompositionTmul S D C hD hC a continuous M d r s) =
        ((@moduliPrecompositionRingIso S D C hD hC a continuous).hom.hom.app (op d)) r • s
  /-- This identification commutes with every module morphism. -/
  tensor_naturality
      {M N : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC)} (f : M ⟶ N) :
    SheafOfModules.changeOfRingsHomOfUniverses.{v, w,
      max (u + 1) v w, max (u + 1) v w}
      (@moduliPrecompositionStructureIso S D C hD hC a continuous).inv
      ((@moduliRawPrecomposition S D C hC a continuous).obj M)
      ((@moduliRawPrecomposition S D C hC a continuous).map f) ≫
        (tensor_comparison N).hom =
      (tensor_comparison M).hom ≫
        (@moduliModulePrecomposition S D C hD hC a continuous).map f
  /-- Local presentations are preserved. -/
  quasicoherent (F : ModuliQCoh C hC) :
    ((@moduliModulePrecomposition S D C hD hC a continuous).obj F.obj).IsQuasicoherent

/-- Scheme-test restriction, canonical tensor base change, full faithfulness,
structure and tensor comparisons, detection of sheaf surjections, and preservation
of quasi-coherence by arbitrary based functors.

Source: Stacks Project, stacks-sheaves.tex, Tags 06WI, 06WK, 06WH; descent.tex,
Tags 03DX(1), 03LC(1), 06VE(1),(3),(4),(7)
(blueprint: lem-sfb-stack-quasi-coherent-scheme-restriction).

Proof:
1. For x over T, the functor C/x to Sch/T is essentially surjective by existence
of cartesian lifts. Unique factorization makes it fully faithful. The fppf covers
and regular-function rings agree, giving an equivalence of ringed sites. Restriction
preserves local free presentations: a presentation cover of z becomes the same cover
with its arrows composed to x. This uses def-sfb-stable-pointed-moduli-groupoids,
lem-sfb-fibred-fppf-ringed-inverse-image, def-trf-space-quasi-coherent-module and
def-pur-localized-ringed-site.
2. Apply lem-sfb-scheme-big-fppf-quasicoherent-equivalence to this restriction. Its
inverse gives F_x, and its counit gives the associated-sheaf formula on every test,
including the global-section formula at the terminal test. Full faithfulness gives
the unique ordinary module map attached to every slice map and the unique compatible
isomorphism from any other realization. All section formulas transport along the
canonical ULift equivalences; the ordinary tensor adjunction gives the agreement
with def-pc-module-pullback and its section-normalized unit.
3. Relocalize from C/x to C/y along an arrow y to x over u. The same equivalence,
with its base-restriction comparison, identifies the two sheaves attached to u^*F_x
and F_y. Full faithfulness gives their canonical isomorphism. On sections it is the
restriction map of F. Identity and composite restrictions coincide, so faithfulness
gives precisely the tensor unitor and compositor equations; the same argument gives
naturality in F. This uses def-pur-localized-ringed-site and the base-restriction
clause of lem-sfb-scheme-big-fppf-quasicoherent-equivalence.
4. The structure sheaf is identified objectwise. By
lem-sfb-localized-site-tensor-restriction, restriction of F tensor G is the tensor
of the restrictions. The tensor clause of the scheme equivalence then identifies
it with the associated sheaf of F_x tensor G_x. Local presentations on every slice
are presentations on C, so the tensor is quasi-coherent. On pure tensors the
comparison has the displayed formula, which also fixes its naturality.
5. A locally surjective map remains so on each slice. The ordinary cokernel Q_x is
quasi-coherent by lem-weil-pbc-quasi-coherent-module-cokernel-image. The associated
sheaf functor preserves ambient cokernels by the scheme equivalence, hence sends Q_x
to zero. Its full faithfulness gives Q_x zero, so the ordinary map is surjective.
Conversely, zero ordinary cokernels give zero slice cokernels. Local lifts at each
terminal test then give an fppf lifting cover in C. This uses only right exactness,
not left exactness of passage from ordinary to big-site modules.
6. For a based functor, lem-sfb-fibred-fppf-ringed-inverse-image identifies geometric
inverse image with precomposition and the structural ring with the unchanged rings
of regular functions. Extension of scalars is therefore canonically precomposition;
on local tensors the map is r tensor m to r m, inverse m to 1 tensor m. To check
quasi-coherence, over d the scheme-test module is F_(a(d)); its arrow comparisons
are those already constructed, so the slice criterion gives local free presentations
on D. No algebraicity, finiteness, quasi-compactness or geometric flatness is used. -/
theorem exists_moduliSchemeRestriction {S : Scheme.{u}}
    (C : BasedCategory.{v, w} (Over S)) (hC : IsFibredInGroupoids C) :
    Nonempty (ModuliSchemeRestriction C hC) ∧
      ∀ (D : BasedCategory.{v, w} (Over S)) (hD : IsFibredInGroupoids D)
        (a : BasedFunctor D C), Nonempty (ModuliQuasicoherentPrecomposition hD hC a) := by
  sorry

end CategoryTheory
