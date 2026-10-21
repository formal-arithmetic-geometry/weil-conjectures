/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Sheaf.CategoryTheory.ConstantRingModuleSheaves
public import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Sheaf.CategoryTheory.SiteDerivedConstantModuleFunctor
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-! # Exact étale module stalks and constant complexes

Source: Stacks Project, Modules on Sites, Tags 03EI and 04EQ; Étale Cohomology,
Tag 03PT; Homology, Tag 010N.
(blueprint: lem-sfb-etale-stalk-constant-complex-exactness).

The stalk is the recorded pointed-neighbourhood colimit after restricting sectionwise
along the constant-ring unit. Thus its A-action is the germ action, not an extra choice.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]

/-- The existing constant ring sheaf.
Source: Stacks 03EI (blueprint: lem-sfb-etale-stalk-constant-complex-exactness). -/
abbrev etaleConstantComplexRing : Sheaf T.smallEtaleTopology RingCat.{u + 1} :=
  (constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of A)

/-- The recorded category of genuine modules over the constant ring sheaf.
Source: Stacks 03DA (blueprint: lem-sfb-etale-stalk-constant-complex-exactness). -/
abbrev etaleConstantComplexModules :=
  ringedSiteModules.{u + 1} (etaleConstantComplexRing T A)

/-- The existing constant module presheaf followed by module sheafification.
Source: Stacks 03EI (blueprint: lem-sfb-etale-stalk-constant-complex-exactness). -/
abbrev etaleConstantComplexFunctor :
    ModuleCat.{u + 1} A ⥤ etaleConstantComplexModules T A :=
  siteConstantModuleFunctorGeneral T.smallEtaleTopology A

variable {T} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- Take the pointed-neighbourhood colimit of sectionwise A-modules, with scalars
restricted along A → A_T(U). Its underlying colimit is `pointedEtaleStalk` of the
restricted sheaf, and its germs are `pointedEtaleGerm`.
Source: Stacks 04EQ and 03PT
(blueprint: lem-sfb-etale-stalk-constant-complex-exactness). -/
def etaleConstantModuleStalkFunctor (t : Spec (.of Ω) ⟶ T) :
    etaleConstantComplexModules T A ⥤ ModuleCat.{u + 1} A :=
  constantRingModuleRestriction T.smallEtaleTopology A ⋙ (pointSmallEtale t).sheafFiber

private theorem moduleLimitsSmall : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} A) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

attribute [local instance] moduleLimitsSmall

private theorem moduleAB5Small : AB5OfSize.{u, u} (ModuleCat.{u + 1} A) :=
  AB5OfSize_of_univLE (ModuleCat.{u + 1} A)

attribute [local instance] moduleAB5Small

private theorem moduleForgetFilteredSmall :
    PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} A)) :=
  preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u}
    (CategoryTheory.forget (ModuleCat.{u + 1} A))

attribute [local instance] moduleForgetFilteredSmall

private theorem moduleSheafFiberAdditive (t : Spec (.of Ω) ⟶ T) :
    ((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).Additive := by
  apply leftExactFunctor_le_additiveFunctor _ _
  rw [leftExactFunctor_iff]
  infer_instance

attribute [local instance] moduleSheafFiberAdditive

/-- The constant-module functor is additive.
Source: Stacks 03EI (blueprint: lem-sfb-etale-stalk-constant-complex-exactness).
Proof: addition of linear maps is sectionwise on constant presheaves. Module
sheafification has the underlying additive sheafification and preserves these sums. -/
theorem etaleConstantComplexFunctor_additive :
    (etaleConstantComplexFunctor T A).Additive := by
  exact (siteConstantModuleFunctorGeneral_exact T.smallEtaleTopology A).1

attribute [instance] etaleConstantComplexFunctor_additive

/-- The module stalk functor is additive.
Source: Stacks 04EQ (blueprint: lem-sfb-etale-stalk-constant-complex-exactness).
Proof: scalar restriction retains the underlying additive maps; germs of sums are
sums of germs in the filtered module colimit. The colimit injections jointly detect
this identity. -/
theorem etaleConstantModuleStalkFunctor_additive (t : Spec (.of Ω) ⟶ T) :
    (etaleConstantModuleStalkFunctor A t).Additive := by
  obtain ⟨⟨e, he, ha, _⟩, _⟩ := constant_ring_module_sheaves.{u + 1, u} T.smallEtaleTopology A
  have : (constantRingModuleRestriction T.smallEtaleTopology A).Additive := by
    rw [← he]
    exact ha
  unfold etaleConstantModuleStalkFunctor
  infer_instance

attribute [instance] etaleConstantModuleStalkFunctor_additive

/-- Both functors are exact on their abelian module categories.
Source: Stacks 03EI, 03DA, 04EQ and Homology 010N
(blueprint: lem-sfb-etale-stalk-constant-complex-exactness).
Proof: constant module presheaves preserve short exact sequences sectionwise.
Module sheafification has exact underlying abelian sheafification. The faithful
module-to-abelian forgetful functor preserves kernels and cokernels, so reflects
short exactness. This proves constant-module exactness. For the stalk, forgetting
scalars and taking the exact geometric abelian stalk gives a short exact sequence
of groups. Its maps are A-linear for the constant-germ action, and their kernels,
images and surjectivity do not change upon forgetting scalars. Thus the module
stalk is exact. An additive functor preserving short exact sequences preserves
kernels and cokernels by the two image sequences, hence finite limits and colimits. -/
theorem etale_stalk_constant_exact (t : Spec (.of Ω) ⟶ T) :
    PreservesFiniteLimits (etaleConstantComplexFunctor T A) ∧
    PreservesFiniteColimits (etaleConstantComplexFunctor T A) ∧
    PreservesFiniteLimits (etaleConstantModuleStalkFunctor A t) ∧
    PreservesFiniteColimits (etaleConstantModuleStalkFunctor A t) := by
  obtain ⟨⟨e, he, _⟩, _⟩ := constant_ring_module_sheaves.{u + 1, u} T.smallEtaleTopology A
  have : (constantRingModuleRestriction T.smallEtaleTopology A).IsEquivalence := by
    rw [← he]
    infer_instance
  have hc := (siteConstantModuleFunctorGeneral_exact T.smallEtaleTopology A).2
  refine ⟨hc.1, hc.2, ?_, ?_⟩
  · exact comp_preservesFiniteLimits (constantRingModuleRestriction T.smallEtaleTopology A)
      ((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A))
  · have : PreservesFiniteColimits
        ((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)) := inferInstance
    exact comp_preservesFiniteColimits (constantRingModuleRestriction T.smallEtaleTopology A)
      ((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A))

/-- Natural linear cohomology comparisons in every integer degree.
Source: Stacks Homology 010N
(blueprint: lem-sfb-etale-stalk-constant-complex-exactness).
Proof: exactness identifies the kernels of mapped differentials and images of
preceding differentials with the images of the original cycles and boundaries.
Their quotients give the displayed isomorphisms. The kernel and cokernel universal
properties give naturality for complex maps. All constructions are in the module
categories, so the comparisons are A-linear and A_T-linear respectively. Only
adjacent differentials enter, so no bound on the complexes is needed. -/
theorem etale_stalk_constant_cohomology (t : Spec (.of Ω) ⟶ T) (n : ℤ) :
    Nonempty (((etaleConstantModuleStalkFunctor A t).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} A) (.up ℤ) n) ≅
        (HomologicalComplex.homologyFunctor (etaleConstantComplexModules T A) (.up ℤ) n ⋙
          etaleConstantModuleStalkFunctor A t)) ∧
    Nonempty (((etaleConstantComplexFunctor T A).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.homologyFunctor (etaleConstantComplexModules T A) (.up ℤ) n) ≅
        (HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} A) (.up ℤ) n ⋙
          etaleConstantComplexFunctor T A)) := by
  obtain ⟨hc₁, hc₂, hs₁, hs₂⟩ := etale_stalk_constant_exact A t
  exact ⟨⟨Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor _ (.up ℤ) n)
    (ShortComplex.homologyFunctorIso (etaleConstantModuleStalkFunctor A t))⟩,
    ⟨Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor _ (.up ℤ) n)
      (ShortComplex.homologyFunctorIso (etaleConstantComplexFunctor T A))⟩⟩

/-- Both termwise functors preserve acyclicity and quasi-isomorphisms, unboundedly.
Source: Stacks Homology 010N
(blueprint: lem-sfb-etale-stalk-constant-complex-exactness).
Proof: the natural cohomology comparisons identify the homology of each mapped
complex with the image of its original homology. Additive functors send zero
objects to zero objects, which proves preservation of acyclicity. Naturality
conjugates the homology map of a mapped quasi-isomorphism to the functor's image
of an invertible homology map. That image is invertible in every degree. -/
theorem etale_stalk_constant_preserves (t : Spec (.of Ω) ⟶ T) :
    (∀ C : CochainComplex (etaleConstantComplexModules T A) ℤ,
      C.Acyclic →
        (((etaleConstantModuleStalkFunctor A t).mapHomologicalComplex (.up ℤ)).obj C).Acyclic) ∧
    (∀ E : CochainComplex (ModuleCat.{u + 1} A) ℤ,
      E.Acyclic →
        (((etaleConstantComplexFunctor T A).mapHomologicalComplex (.up ℤ)).obj E).Acyclic) ∧
    (∀ {C D : CochainComplex (etaleConstantComplexModules T A) ℤ} (f : C ⟶ D),
      QuasiIso f → QuasiIso
        (((etaleConstantModuleStalkFunctor A t).mapHomologicalComplex (.up ℤ)).map f)) ∧
    (∀ {E F : CochainComplex (ModuleCat.{u + 1} A) ℤ} (f : E ⟶ F),
      QuasiIso f → QuasiIso
        (((etaleConstantComplexFunctor T A).mapHomologicalComplex (.up ℤ)).map f)) := by
  obtain ⟨hc₁, hc₂, hs₁, hs₂⟩ := etale_stalk_constant_exact A t
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C h n
    exact (h n).map (etaleConstantModuleStalkFunctor A t)
  · intro E h n
    exact (h n).map (etaleConstantComplexFunctor T A)
  · intro C D f hf
    let := hf
    infer_instance
  · intro E F f hf
    let := hf
    infer_instance

variable (T)

-- The module-sheafification unit, viewed as a map of fixed-ring presheaves.
set_option backward.isDefEq.respectTransparency false in
private def constantModuleUnit (M : ModuleCat.{u + 1} A) :
    (Functor.const T.Etaleᵒᵖ).obj M ⟶
      ((constantRingModuleRestriction T.smallEtaleTopology A).obj
        ((etaleConstantComplexFunctor T A).obj M)).obj where
  app X := ((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of A)))).unit.app
        ((siteConstantModulePresheafGeneral (C := T.Etale) A).obj M)).app X
  naturality X Y f := by
    ext x
    exact PresheafOfModules.naturality_apply
      ((PresheafOfModules.sheafificationAdjunction.{u + 1}
        (toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of A)))).unit.app
            ((siteConstantModulePresheafGeneral (C := T.Etale) A).obj M)) f x

set_option backward.isDefEq.respectTransparency false in
private theorem constantModuleUnit_locallyInjective (M : ModuleCat.{u + 1} A) :
    Presheaf.IsLocallyInjective T.smallEtaleTopology (constantModuleUnit T A M) where
  equalizerSieve_mem x y h := Presheaf.equalizerSieve_mem T.smallEtaleTopology
    (toSheafify T.smallEtaleTopology
      ((siteConstantModulePresheafGeneral (C := T.Etale) A).obj M).presheaf) x y h

attribute [local instance] constantModuleUnit_locallyInjective

set_option backward.isDefEq.respectTransparency false in
private theorem constantModuleUnit_locallySurjective (M : ModuleCat.{u + 1} A) :
    Presheaf.IsLocallySurjective T.smallEtaleTopology (constantModuleUnit T A M) where
  imageSieve_mem x := Presheaf.imageSieve_mem T.smallEtaleTopology
    (toSheafify T.smallEtaleTopology
      ((siteConstantModulePresheafGeneral (C := T.Etale) A).obj M).presheaf) x

attribute [local instance] constantModuleUnit_locallySurjective

-- A locally bijective constant-section map becomes an isomorphism on fibres.
private def constantSectionStalkIso (t : Spec (.of Ω) ⟶ T)
    (M : ModuleCat.{u + 1} A) (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (φ : (Functor.const T.Etaleᵒᵖ).obj M ⟶ N.obj)
    [Presheaf.IsLocallyInjective T.smallEtaleTopology φ]
    [Presheaf.IsLocallySurjective T.smallEtaleTopology φ] :
    M ≅ (pointSmallEtale t).sheafFiber.obj N := by
  have : IsIso ((pointSmallEtale t).presheafFiber.map φ) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (pointSmallEtale t).toPresheafFiber_map_bijective φ
  exact ((pointSmallEtale t).presheafFiberConstIso M).symm ≪≫
    asIso ((pointSmallEtale t).presheafFiber.map φ)

private theorem constantSectionStalkIso_hom (t : Spec (.of Ω) ⟶ T)
    (M : ModuleCat.{u + 1} A) (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (φ : (Functor.const T.Etaleᵒᵖ).obj M ⟶ N.obj)
    [Presheaf.IsLocallyInjective T.smallEtaleTopology φ]
    [Presheaf.IsLocallySurjective T.smallEtaleTopology φ] :
    (constantSectionStalkIso T A t M N φ).hom =
      φ.app (op (Etale.mk (𝟙 T))) ≫
        (pointSmallEtale t).toPresheafFiber (Etale.mk (𝟙 T))
          (Over.homMk t (Category.comp_id t)) N.obj := by
  have h := (pointSmallEtale t).toPresheafFiber_presheafFiberConstIso_hom M
    (Etale.mk (𝟙 T)) (Over.homMk t (Category.comp_id t))
  have hi : ((pointSmallEtale t).presheafFiberConstIso M).inv =
      (pointSmallEtale t).toPresheafFiber (Etale.mk (𝟙 T))
        (Over.homMk t (Category.comp_id t)) ((Functor.const T.Etaleᵒᵖ).obj M) := by
    rw [← cancel_mono ((pointSmallEtale t).presheafFiberConstIso M).hom,
      Iso.inv_hom_id, h]
  change ((pointSmallEtale t).presheafFiberConstIso M).inv ≫
    (pointSmallEtale t).presheafFiber.map φ = _
  rw [hi, (pointSmallEtale t).toPresheafFiber_naturality]

set_option backward.isDefEq.respectTransparency false in
private def constantModuleStalkIso (t : Spec (.of Ω) ⟶ T) :
    𝟭 (ModuleCat.{u + 1} A) ≅
      etaleConstantComplexFunctor T A ⋙ etaleConstantModuleStalkFunctor A t :=
  NatIso.ofComponents (fun M ↦ constantSectionStalkIso T A t M _
    (constantModuleUnit T A M)) (by
      intro M N f
      simp only [constantSectionStalkIso_hom, Functor.id_map, Category.assoc]
      change f ≫ _ ≫ _ = _ ≫ _ ≫ (pointSmallEtale t).presheafFiber.map
        (((constantRingModuleRestriction T.smallEtaleTopology A).map
          ((etaleConstantComplexFunctor T A).map f)).hom)
      rw [(pointSmallEtale t).toPresheafFiber_naturality]
      have hunit : f ≫ (constantModuleUnit T A N).app (op (Etale.mk (𝟙 T))) =
          (constantModuleUnit T A M).app (op (Etale.mk (𝟙 T))) ≫
            (((constantRingModuleRestriction T.smallEtaleTopology A).map
              ((etaleConstantComplexFunctor T A).map f)).hom.app
                (op (Etale.mk (𝟙 T)))) := by
        ext x
        exact congrArg (fun g ↦ g.app (op (Etale.mk (𝟙 T))) x)
          (toSheafify_naturality T.smallEtaleTopology
            ((PresheafOfModules.toPresheaf _).map
              ((siteConstantModulePresheafGeneral (C := T.Etale) A).map f)))
      rw [← Category.assoc, hunit, Category.assoc])

set_option backward.isDefEq.respectTransparency false in
private def regularModuleUnit :
    (Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A) ⟶
      ((constantRingModuleRestriction T.smallEtaleTopology A).obj
        (SheafOfModules.unit (etaleConstantComplexRing T A))).obj where
  app X := ModuleCat.ofHom
    (Y := ((constantRingModuleRestriction T.smallEtaleTopology A).obj
      (SheafOfModules.unit (etaleConstantComplexRing T A))).obj.obj X)
    { toFun := (toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of A))).app X
      map_add' := fun x y ↦ map_add _ x y
      map_smul' := by
        intro a x
        change ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of A))).app X) (a * x) =
            _ * _
        exact map_mul _ a x }
  naturality X Y f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun g ↦ g x)
      ((toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of A))).naturality f)

set_option backward.isDefEq.respectTransparency false in
private theorem regularModuleUnit_locallyInjective :
    Presheaf.IsLocallyInjective T.smallEtaleTopology (regularModuleUnit T A) where
  equalizerSieve_mem x y h := Presheaf.equalizerSieve_mem T.smallEtaleTopology
    (toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of A))) x y h

attribute [local instance] regularModuleUnit_locallyInjective

set_option backward.isDefEq.respectTransparency false in
private theorem regularModuleUnit_locallySurjective :
    Presheaf.IsLocallySurjective T.smallEtaleTopology (regularModuleUnit T A) where
  imageSieve_mem x := Presheaf.imageSieve_mem T.smallEtaleTopology
    (toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of A))) x

attribute [local instance] regularModuleUnit_locallySurjective

variable {T}

/-- The natural chain retraction is normalized by constant germs; the stalk of A_T
is A with its ordinary scalar action.
Source: Stacks 03PT (2), 03EI and 04EQ
(blueprint: lem-sfb-etale-stalk-constant-complex-exactness).
Proof: the underlying abelian constant-germ map is invertible by 03PT. Linearity
of the module-sheafification unit gives η(am)=aη(m), and functoriality of that unit
gives naturality in all module maps. Apply this to each differential: the degreewise
constant-germ maps commute with the differential, hence define a chain isomorphism.
The inverses commute with differentials by multiplying the same identities by the
component inverses. Apply module naturality to every component of a complex map to
obtain chain naturality. For the regular module A_T, the ring sheafification unit
is multiplicative and sends 1 to 1; its germ identifies the scalar action with the
ordinary action of A on itself. No step uses finiteness or bounds. -/
theorem etale_stalk_constant_complex_retraction (t : Spec (.of Ω) ⟶ T) :
    (∃ η : 𝟭 (CochainComplex (ModuleCat.{u + 1} A) ℤ) ≅
        (etaleConstantComplexFunctor T A).mapHomologicalComplex (.up ℤ) ⋙
          (etaleConstantModuleStalkFunctor A t).mapHomologicalComplex (.up ℤ),
      ∀ (E : CochainComplex (ModuleCat.{u + 1} A) ℤ) (n : ℤ) (e : E.X n),
        ((η.hom.app E).f n) e =
          (pointedEtaleGerm
            ((constantRingModuleRestriction T.smallEtaleTopology A).obj
              ((etaleConstantComplexFunctor T A).obj (E.X n))) t
            (Etale.mk (𝟙 T)) (Over.homMk t (Category.comp_id t)))
              ((toSheafify T.smallEtaleTopology
                ((siteConstantModulePresheafGeneral (C := T.Etale) A).obj
                  (E.X n)).presheaf).app (op (Etale.mk (𝟙 T))) e)) ∧
    (∃ ε : ModuleCat.of A A ≅ (etaleConstantModuleStalkFunctor A t).obj
        (SheafOfModules.unit (etaleConstantComplexRing T A)),
      ∀ a : A, ε.hom a =
        (pointedEtaleGerm
          ((constantRingModuleRestriction T.smallEtaleTopology A).obj
            (SheafOfModules.unit (etaleConstantComplexRing T A))) t
          (Etale.mk (𝟙 T)) (Over.homMk t (Category.comp_id t)))
            ((toSheafify T.smallEtaleTopology
              ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of A))).app
                (op (Etale.mk (𝟙 T))) a)) := by
  refine ⟨⟨(Functor.mapHomologicalComplexIdIso (ModuleCat.{u + 1} A) (.up ℤ)).symm ≪≫
    NatIso.mapHomologicalComplex (constantModuleStalkIso T A t) (.up ℤ), ?_⟩, ?_⟩
  · intro E n e
    change ((constantModuleStalkIso T A t).hom.app (E.X n)) e = _
    rw [show (constantModuleStalkIso T A t).hom.app (E.X n) = _ from
      constantSectionStalkIso_hom T A t (E.X n) _ (constantModuleUnit T A (E.X n))]
    rfl
  · refine ⟨constantSectionStalkIso T A t (ModuleCat.of A A) _
      (regularModuleUnit T A), ?_⟩
    intro a
    rw [constantSectionStalkIso_hom]
    rfl

end AlgebraicGeometry.Scheme
