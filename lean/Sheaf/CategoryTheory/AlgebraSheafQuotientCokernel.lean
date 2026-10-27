module

public import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.RingedSiteIdeal
public import Sheaf.Paper.IdealModuleQuotients
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-! # Algebra-sheaf quotients and module cokernels

Source: Stacks Project, Modules, Tag 01AH(2) and the cokernel construction preceding
Tag 01AG; Sheaves, Tags 0087 and 0089
(blueprint: lem-weil-pbc-ringed-space-algebra-quotient-cokernel).

The quotient presheaf, ring sheafification, and projection are the canonical constructions
from `RingedSiteIdeal.ringQuotient` and `RingedSiteIdeal.ringProjection`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace CategoryTheory

variable {X : Type u} [TopologicalSpace X]
    {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    (B : Under O) (I : RingedSiteIdeal B.right)

/-- The quotient algebra sheaf Q, with structure map q composed with sigma_B.
Source: Stacks, Sheaves, Tag 0087; Modules, Tag 01AH(2)
(blueprint: lem-weil-pbc-ringed-space-algebra-quotient-cokernel). -/
def algebraSheafQuotient : Under O :=
  Under.mk (B.hom ≫ RingedSiteIdeal.ringProjection I)

/-- The quotient projection as an algebra-sheaf morphism.
Source: Stacks, Sheaves, Tag 0087; Modules, Tag 01AH(2)
(blueprint: lem-weil-pbc-ringed-space-algebra-quotient-cokernel). -/
def algebraSheafQuotientMap : B ⟶ algebraSheafQuotient B I :=
  Under.homMk (RingedSiteIdeal.ringProjection I) rfl

/-- The ideal inclusion regarded as a morphism of O-module sheaves.
Source: Stacks, Modules, cokernel construction preceding Tag 01AG
(blueprint: lem-weil-pbc-ringed-space-algebra-quotient-cokernel). -/
def algebraSheafIdealInclusion :
    (SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat)).map
        B.hom)).obj I.module ⟶ commAlgebraSheafModule O B :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat)).map
      B.hom)).map I.inclusion

private lemma quotient_locallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (RingedSiteIdeal.ringProjection I).hom := by
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (RingedSiteIdeal.ringQuotientPresheafProjection I) :=
    Presheaf.isLocallySurjective_of_surjective _ _
      (fun _ ↦ Ideal.Quotient.mk_surjective)
  change Presheaf.IsLocallySurjective _
    (RingedSiteIdeal.ringQuotientPresheafProjection I ≫ toSheafify _ _)
  infer_instance

private lemma quotient_algebra_lift (H : Under O) (χ : B ⟶ H)
    (hχ : ∀ (U : Opens X) (a : I.sections U), χ.right.hom.app (op U) a.val = 0) :
    ∃! χbar : algebraSheafQuotient B I ⟶ H,
      algebraSheafQuotientMap B I ≫ χbar = χ := by
  let ψ : RingedSiteIdeal.ringQuotientPresheaf I ⟶ H.right.obj :=
    { app := fun W ↦ CommRingCat.ofHom
        (Ideal.Quotient.lift (I.sections W.unop) (χ.right.hom.app W).hom
          (fun a ha ↦ hχ W.unop ⟨a, ha⟩))
      naturality := by
        intro W V f
        apply CommRingCat.hom_ext
        apply Ideal.Quotient.ringHom_ext
        ext a
        exact congrArg (fun k ↦ k a) (χ.right.hom.naturality f) }
  have hp : RingedSiteIdeal.ringQuotientPresheafProjection I ≫ ψ = χ.right.hom := by
    ext W a
    rfl
  let φ : RingedSiteIdeal.ringQuotient I ⟶ H.right :=
    ⟨sheafifyLift (Opens.grothendieckTopology X) ψ H.right.property⟩
  have hφ : RingedSiteIdeal.ringProjection I ≫ φ = χ.right := by
    apply Sheaf.hom_ext
    change (RingedSiteIdeal.ringQuotientPresheafProjection I ≫ toSheafify _ _) ≫
      sheafifyLift _ ψ _ = _
    rw [Category.assoc, toSheafify_sheafifyLift, hp]
  let χbar : algebraSheafQuotient B I ⟶ H :=
    Under.homMk φ (by
      change (B.hom ≫ RingedSiteIdeal.ringProjection I) ≫ φ = H.hom
      rw [Category.assoc, hφ, Under.w χ])
  have hbar : algebraSheafQuotientMap B I ≫ χbar = χ := by
    apply Under.UnderMorphism.ext
    exact hφ
  refine ⟨χbar, hbar, ?_⟩
  intro v hv
  apply Under.UnderMorphism.ext
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Opens.grothendieckTopology X) _ _ H.right.property
  ext W a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact congrArg (fun k ↦ k.right.hom.app W b) (hv.trans hbar.symm)

private def quotientModulePresheaf : PresheafOfModules.{u} (siteModuleRings O).obj :=
  (PresheafOfModules.restrictScalars
    (Functor.whiskerRight
      (B.hom.hom ≫ RingedSiteIdeal.ringQuotientPresheafProjection I)
      (forget₂ CommRingCat RingCat))).obj
    (PresheafOfModules.unit
      (RingedSiteIdeal.ringQuotientPresheaf I ⋙ forget₂ CommRingCat RingCat))

private def quotientModuleUnit : quotientModulePresheaf B I ⟶
    (commAlgebraSheafModule O (algebraSheafQuotient B I)).val :=
  PresheafOfModules.homMk
    (Functor.whiskerRight (toSheafify (Opens.grothendieckTopology X)
      (RingedSiteIdeal.ringQuotientPresheaf I))
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) (by
      intro W r a
      change (RingedSiteIdeal.ringQuotientPresheaf I).obj W at a
      change (toSheafify (Opens.grothendieckTopology X)
        (RingedSiteIdeal.ringQuotientPresheaf I)).app W
        ((RingedSiteIdeal.ringQuotientPresheafProjection I).app W
          (B.hom.hom.app W r) * a) = _
      exact map_mul ((toSheafify (Opens.grothendieckTopology X)
        (RingedSiteIdeal.ringQuotientPresheaf I)).app W).hom _ _)

private def quotientModuleProjection : (commAlgebraSheafModule O B).val ⟶
    quotientModulePresheaf B I :=
  PresheafOfModules.homMk
    (Functor.whiskerRight (RingedSiteIdeal.ringQuotientPresheafProjection I)
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) (by
      intro W r a
      exact map_mul (Ideal.Quotient.mk (I.sections W.unop)) _ _)

private lemma quotientModule_factor :
    quotientModuleProjection B I ≫ quotientModuleUnit B I =
      ((commAlgebraSheafModuleFunctor O).map (algebraSheafQuotientMap B I)).val := by
  ext W a
  rfl

private lemma quotientModuleUnit_surjective :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
      (quotientModuleUnit B I) where
  imageSieve_mem s := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    (toSheafify (Opens.grothendieckTopology X) (RingedSiteIdeal.ringQuotientPresheaf I)) s

private lemma quotientModuleUnit_injective :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X)
      (quotientModuleUnit B I) where
  equalizerSieve_mem a b h := Presheaf.equalizerSieve_mem
    (Opens.grothendieckTopology X)
    (toSheafify (Opens.grothendieckTopology X) (RingedSiteIdeal.ringQuotientPresheaf I))
    a b h

-- Descend the sectionwise additive quotient map along the locally bijective unit.
-- Mathlib also proves linearity locally, so no choice of module structure is needed.
private lemma quotient_module_lift
    (N : SheafOfModules.{u} (siteModuleRings O)) (f : commAlgebraSheafModule O B ⟶ N)
    (hf : algebraSheafIdealInclusion B I ≫ f = 0) :
    ∃! l : commAlgebraSheafModule O (algebraSheafQuotient B I) ⟶ N,
      (commAlgebraSheafModuleFunctor O).map (algebraSheafQuotientMap B I) ≫ l = f := by
  let := quotientModuleUnit_surjective B I
  let := quotientModuleUnit_injective B I
  have hzero (W : (Opens X)ᵒᵖ) (a : B.right.obj.obj W) (ha : a ∈ I.sections W.unop) :
      f.val.app W a = 0 := by
    exact congrArg (fun k ↦ k.val.app W ⟨a, ha⟩) hf
  let ψapp (W : (Opens X)ᵒᵖ) :
      (RingedSiteIdeal.ringQuotientPresheaf I).obj W →+ N.val.obj W :=
    QuotientAddGroup.lift (I.sections W.unop).toAddSubgroup
      (f.val.app W).hom.toAddMonoidHom (hzero W)
  let ψ : quotientModulePresheaf B I ⟶ N.val :=
    PresheafOfModules.homMk
      { app := fun W ↦ AddCommGrpCat.ofHom (ψapp W)
        naturality := by
          intro W V g
          ext a
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
          exact PresheafOfModules.naturality_apply f.val g a }
      (by
        intro W r a
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact (f.val.app W).hom.map_smul r a)
  have hp : quotientModuleProjection B I ≫ ψ = f.val := by
    ext W a
    rfl
  let e := PresheafOfModules.homEquivOfIsLocallyBijective
    (quotientModuleUnit B I) N.isSheaf
  let l : commAlgebraSheafModule O (algebraSheafQuotient B I) ⟶ N := ⟨e.symm ψ⟩
  have hl : (commAlgebraSheafModuleFunctor O).map (algebraSheafQuotientMap B I) ≫ l =
      f := by
    apply SheafOfModules.hom_ext
    rw [SheafOfModules.comp_val, ← quotientModule_factor B I, Category.assoc]
    exact congrArg (fun k ↦ quotientModuleProjection B I ≫ k) (e.apply_symm_apply ψ)
      |>.trans hp
  refine ⟨l, hl, ?_⟩
  intro m hm
  apply SheafOfModules.hom_ext
  apply e.injective
  apply PresheafOfModules.hom_ext
  intro W
  ext a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact congrArg (fun k ↦ k.val.app W a) (hm.trans hl.symm)

/-- The ring-sheaf quotient is the module cokernel, with normalized projection; it is
locally surjective and has the algebra quotient universal property.
Source: Stacks, Modules, Tag 01AH(2) and construction preceding Tag 01AG;
Sheaves, Tags 0087 and 0089
(blueprint: lem-weil-pbc-ringed-space-algebra-quotient-cokernel).

Proof:
1. The landed `RingedSiteIdeal.ringQuotientPresheaf`, `ringQuotient`, and `ringProjection`
   provide the sectionwise quotient, its sheafification, and the specified projection.
   Composing sigma_B with `ringProjection I` makes Q an O-algebra and the projection an
   algebra morphism. Restricting scalars makes I an O-submodule.
2. Ring sheafification has underlying set and abelian-group sheafification (the
   ring-sheafification-space-underlying-abelian node, via sheafifyComposeIso).
   Identify its unit with the standard set-sheafification unit by the two universal
   properties. Local representatives and local equality transfer across this unit-preserving
   isomorphism (site-sheafification-sections-local, Tags 00WB and 00WK).
   Every quotient class lifts to B, so `ringProjection I` is locally surjective. If q(b)=0,
   locally b lies in I; glue these lifts in the subsheaf I to obtain b in I on the whole open,
   including the empty open. Conversely b in I maps to zero.
3. Given an O-linear map killing I, lift a Q-section locally to B and apply the map.
   Differences on overlaps lie in I, so the images glue uniquely. Refining two choices
   proves independence; restricting proves naturality. Common refinements prove additivity
   and O-linearity. This gives the module cokernel property for this very q.
4. The two cokernel properties give h and its inverse, normalized by c followed by h = q.
   Uniqueness in each cokernel property makes both composites identities.
5. An algebra map chi killing I factors sectionwise through the quotient rings, then
   uniquely through the canonical ring sheafification. The composite structure map makes
   the result O-linear as an algebra map. Sectionwise surjectivity of the quotient
   projection and sheafification uniqueness give uniqueness among algebra maps. -/
theorem algebraSheafQuotient_cokernel :
    (∃ h : cokernel (algebraSheafIdealInclusion B I) ≅
        commAlgebraSheafModule O (algebraSheafQuotient B I),
      cokernel.π (algebraSheafIdealInclusion B I) ≫ h.hom =
        (commAlgebraSheafModuleFunctor O).map (algebraSheafQuotientMap B I)) ∧
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (RingedSiteIdeal.ringProjection I).hom ∧
    (∀ (H : Under O) (χ : B ⟶ H),
      (∀ (U : Opens X) (a : I.sections U), χ.right.hom.app (op U) a.val = 0) →
      ∃! χbar : algebraSheafQuotient B I ⟶ H, algebraSheafQuotientMap B I ≫ χbar = χ) := by
  refine ⟨?_, quotient_locallySurjective B I, quotient_algebra_lift B I⟩
  let q := (commAlgebraSheafModuleFunctor O).map (algebraSheafQuotientMap B I)
  have hq : algebraSheafIdealInclusion B I ≫ q = 0 := by
    ext W a
    change (toSheafify (Opens.grothendieckTopology X)
      (RingedSiteIdeal.ringQuotientPresheaf I)).app W
      (Ideal.Quotient.mk (I.sections W.unop) a.val) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr a.property, map_zero]
  let hQ : IsColimit (CokernelCofork.ofπ q hq) :=
    CokernelCofork.IsColimit.ofπ q hq
      (fun f hf ↦ (quotient_module_lift B I _ f hf).choose)
      (fun f hf ↦ (quotient_module_lift B I _ f hf).choose_spec.1)
      (fun f hf m hm ↦ (quotient_module_lift B I _ f hf).choose_spec.2 m hm)
  refine ⟨(cokernelIsCokernel (algebraSheafIdealInclusion B I)).coconePointUniqueUpToIso hQ,
    ?_⟩
  exact (cokernelIsCokernel (algebraSheafIdealInclusion B I)).comp_coconePointUniqueUpToIso_hom
    hQ WalkingParallelPair.one

end CategoryTheory
