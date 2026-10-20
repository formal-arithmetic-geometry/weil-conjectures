/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.RingTheory.ModuleLocalizationFilteredColimit
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.RingTheory.Localization.Module
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.Localization
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Localization and geometric inverse image

Source: Stacks Project, Modules on Sites, Tags 03EL, 03CZ and 03D2; the localization
universal property and its identity/composition normalization
(blueprint: lem-weil-pbc-localization-inverse-image-coherence).

## Main statements

- `existsUnique_localizationInverseImage`: the unit-normalized module natural isomorphism.
- `existsUnique_localizationInverseImageRing`: the normalized ring-sheaf isomorphism.
- `localizationInverseImage_fraction`: normalization on all generalized fractions.
- `localizationInverseImage_comp`, `_id`, `_coefficient`: module coherence equations.
- `localizationComparisonDerived`: canonical descent to ordinary unbounded derived categories.

## Proof dependencies

1. Identify the tensor localization with sheafified fractions using
   `lem-pc-sites-module-sheafification-tensor`, `lem-weil-pbc-localization-tensor`,
   `lem-pc-sites-sheafification-underlying-sets` and
   `def-weil-presheaf-modules-sheafification`. The identification takes units to units.
2. The ring mapping property follows objectwise from
   `lem-weil-pbc-localization-away-universal-property`, then from sheafification.
3. Extend a module map by sending m/t^n to the inverse t-action applied n times to its
   image, using `def-weil-pbc-module-localization`; sheafify and use uniqueness.
4. `lem-weil-pbc-adjunction-lifts-group-ring-objects` and
   `lem-weil-pbc-sheaf-algebraic-structures-objects` transport the ring initial property.
5. `lem-weil-pbc-geometric-module-transport` transports the module initial property.
6. The same unit characterization proves naturality and the generalized fraction formula.
7. Kernels of inverse image are finite limits, and its adjunction preserves cokernels;
   use `lem-weil-pbc-module-sheaves-colimits-forgetful` and
   `lem-weil-pbc-left-adjoint-preserves-colimits`.
8. For scalar localization combine `lem-weil-pbc-localization-module-exact`,
   `lem-weil-pbc-ringed-site-module-sheafification-exact` and
   `lem-weil-pbc-ringed-topoi-module-adjunction` to obtain kernels and cokernels.
9. `def-weil-pbc-composite-adjunction` and `lem-weil-pbc-conjugate-iso-unit-equation`
   identify the composite inverse image. Both comparison routes extend the same unit,
   so uniqueness proves the composition and identity equations.
10. Extend a specified ring isomorphism using the localization mapping property; its
    module reinterpretation preserves units, so the same uniqueness proves the square.
11. `lem-weil-pbc-exact-functor-derived-factorization`,
    `lem-weil-pbc-exact-functor-derived-functor` and
    `lem-weil-pbc-localization-universal-property` descend the termwise comparison,
    units and equations on every unbounded complex.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u uC vC uD vD uF vF uA uB uE vA vB vE wA wB wE

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The existing module category of a commutative ring sheaf.
Source: Stacks, Tag 03D2
(blueprint: lem-weil-pbc-localization-inverse-image-coherence). -/
abbrev inverseLocalizationModules
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) :=
  ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

/-- Scalar localization is the existing sheaf tensor product with the localized ring.
The order of factors is `M ⊗ R[1/t]`, the symmetric form of `R[1/t] ⊗ M`.
Source: Stacks, Tags 03EK and 00DK
(blueprint: lem-weil-pbc-localization-inverse-image-coherence). -/
abbrev scalarLocalization
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) (t : (R.obj ⋙ forget CommRingCat.{u}).sections) :
    inverseLocalizationModules R ⥤ inverseLocalizationModules R :=
  SheafOfModules.siteSheafTensorRight (A := R) (ringedSectionLocalizationOfUniverses R t)

/-- The localization unit is uniquely specified by `m ↦ m ⊗ 1` on every section.
Source: Stacks, Tags 03EK and 00DK
(blueprint: lem-weil-pbc-localization-inverse-image-coherence).
Proof: the pure-tensor map is linear and compatible with restriction because the
localization restrictions preserve one. Compose with the module sheafification unit.
Naturality follows on pure tensors. Every section of the source has the specified image,
so componentwise extensionality proves uniqueness. -/
theorem existsUnique_scalarLocalizationUnit
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) (t : (R.obj ⋙ forget CommRingCat.{u}).sections) :
    ∃! η : 𝟭 (inverseLocalizationModules R) ⟶ scalarLocalization R t,
      ∀ (M : inverseLocalizationModules R) (U : Cᵒᵖ) (m : M.val.obj U),
        (η.app M).val.app U m =
          SheafOfModules.siteSheafTensorTmul M (ringedSectionLocalizationOfUniverses R t) U m
            ((ringedSectionLocalizationUnitOfUniverses R t).val.app U (1 : R.obj.obj U)) := by
  let N := ringedSectionLocalizationOfUniverses R t
  let j := ringedSectionLocalizationUnitOfUniverses R t
  let p (M : inverseLocalizationModules R) : M.val ⟶
      SheafOfModules.siteTensorPresheaf M.val N.val :=
    { app := fun U ↦ by
        change ModuleCat.of (R.obj.obj U) (M.val.obj U) ⟶ ModuleCat.of (R.obj.obj U)
          (TensorProduct (R.obj.obj U) (M.val.obj U) (N.val.obj U))
        exact ModuleCat.ofHom (R := R.obj.obj U)
          { toFun := fun m ↦ m ⊗ₜ[R.obj.obj U] (j.val.app U (1 : R.obj.obj U))
            map_add' := by intros; exact TensorProduct.add_tmul _ _ _
            map_smul' := by intros; exact TensorProduct.smul_tmul' _ _ _ }
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        ext m
        change M.val.map f m ⊗ₜ[R.obj.obj V] j.val.app V (1 : R.obj.obj V) =
          M.val.map f m ⊗ₜ[R.obj.obj V] N.val.map f (j.val.app U (1 : R.obj.obj U))
        congr 1
        rw [← PresheafOfModules.naturality_apply j.val f]
        change j.val.app V (1 : R.obj.obj V) =
          j.val.app V (R.obj.map f (1 : R.obj.obj U))
        rw [(R.obj.map f).hom.map_one] }
  let η : 𝟭 (inverseLocalizationModules R) ⟶ scalarLocalization R t :=
    { app := fun M ↦ ⟨p M ≫
        (PresheafOfModules.sheafificationAdjunction
          (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).unit.app
          (SheafOfModules.siteTensorPresheaf M.val N.val)⟩
      naturality := by
        intro M M' f
        apply SheafOfModules.hom_ext
        change f.val ≫ p M' ≫ _ = (p M ≫ _) ≫ _
        rw [← Category.assoc]
        have hp : f.val ≫ p M' = p M ≫ SheafOfModules.siteTensorHom f.val N.val := by
          ext U m
          rfl
        rw [hp, Category.assoc]
        exact congrArg (fun g ↦ p M ≫ g)
          ((PresheafOfModules.sheafificationAdjunction
          (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).unit.naturality
            (SheafOfModules.siteTensorHom f.val N.val)) }
  refine ⟨η, ?_, ?_⟩
  · intro M U m
    rfl
  · intro θ hθ
    apply NatTrans.ext
    funext M
    apply SheafOfModules.hom_ext
    ext U m
    exact hθ M U m

/-- The actual localization unit, chosen from its unique sectionwise specification.
Source: Stacks, Tags 03EK and 00DK
(blueprint: lem-weil-pbc-localization-inverse-image-coherence). -/
def scalarLocalizationUnit
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) (t : (R.obj ⋙ forget CommRingCat.{u}).sections) :
    𝟭 (inverseLocalizationModules R) ⟶ scalarLocalization R t :=
  Classical.choose (existsUnique_scalarLocalizationUnit R t)

/-- The underlying set sheaf of a module sheaf.
Source: Stacks, Tag 03D2
(blueprint: lem-weil-pbc-localization-inverse-image-coherence). -/
abbrev localizationModuleSets
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) :=
  SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
    sheafCompose J (forget AddCommGrpCat.{u})

/-- Transport of a global section, tested on all generalized elements. This expresses
`t' = f⁻¹t` without a point or a presentation of the geometric morphism by a site functor.
Source: Stacks, Tag 00YV
(blueprint: lem-weil-pbc-localization-inverse-image-coherence). -/
def IsInverseImageSection
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {K : GrothendieckTopology D}
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify K CommRingCat.{u}]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (a : SheafOfModules.AlgebraicInverseImage L R S)
    (t : (R.obj ⋙ forget CommRingCat.{u}).sections)
    (s : (S.obj ⋙ forget CommRingCat.{u}).sections) : Prop :=
  ∀ (T : Sheaf J (Type u))
    (r : T ⟶ (sheafCompose J (forget CommRingCat.{u})).obj R),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), r.hom.app U x = t.val U) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      a.ringUnderlying.hom.hom.app V ((L.map r).hom.app V x) = s.val V

private def unliftSetSheafIso
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C} :
    sheafCompose J uliftFunctor.{u, u} ≅ 𝟭 (Sheaf J (Type u)) :=
  NatIso.ofComponents (fun T ↦
    { hom := ⟨{ app := fun _ ↦ ↾ULift.down }⟩
      inv := ⟨{ app := fun _ ↦ ↾ULift.up }⟩ })
    (by intro T T' f; rfl)

private def inverseImageUniverses
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (a : SheafOfModules.AlgebraicInverseImage L R S) :
    SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, u, u} L R S := by
  let eJ := unliftSetSheafIso (J := J)
  let eK := unliftSetSheafIso (J := K)
  let rR := (sheafCompose J (forget CommRingCat.{u})).obj R
  let rS := (sheafCompose K (forget CommRingCat.{u})).obj S
  let mR := SheafOfModules.toSheaf.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose J (forget AddCommGrpCat.{u})
  let mS := SheafOfModules.toSheaf.{u}
    ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
      sheafCompose K (forget AddCommGrpCat.{u})
  refine
    { ringUnderlying := L.mapIso (eJ.app rR) ≪≫ a.ringUnderlying ≪≫ (eK.app rS).symm
      modules := a.modules
      moduleUnderlying :=
        Functor.isoWhiskerLeft a.modules (Functor.isoWhiskerLeft mS eK) ≪≫
          a.moduleUnderlying ≪≫
            Functor.isoWhiskerRight (Functor.isoWhiskerLeft mR eJ.symm) L
      ringAdd := ?_
      ringMul := ?_
      ringZero := ?_
      ringOne := ?_
      moduleAdd := ?_
      moduleZero := ?_
      moduleSMul := ?_ }
  · intro T x y z h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringAdd T (x ≫ eJ.hom.app rR) (y ≫ eJ.hom.app rR)
        (z ≫ eJ.hom.app rR) h W q
  · intro T x y z h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringMul T (x ≫ eJ.hom.app rR) (y ≫ eJ.hom.app rR)
        (z ≫ eJ.hom.app rR) h W q
  · intro T x h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringZero T (x ≫ eJ.hom.app rR) h W q
  · intro T x h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringOne T (x ≫ eJ.hom.app rR) h W q
  · intro M T x y z h W q
    have h' := a.moduleAdd M T (x ≫ eJ.hom.app (mR.obj M))
      (y ≫ eJ.hom.app (mR.obj M)) (z ≫ eJ.hom.app (mR.obj M)) h W q
    simp only [Functor.map_comp] at h'
    convert h' using 1
    all_goals rfl
  · intro M T x h W q
    have h' := a.moduleZero M T (x ≫ eJ.hom.app (mR.obj M)) h W q
    simp only [Functor.map_comp] at h'
    convert h' using 1
    all_goals rfl
  · intro M T r x z h W q
    have h' := a.moduleSMul M T (r ≫ eJ.hom.app rR) (x ≫ eJ.hom.app (mR.obj M))
      (z ≫ eJ.hom.app (mR.obj M)) h W q
    simp only [Functor.map_comp] at h'
    convert h' using 1
    all_goals rfl

open MonoidalCategory in
private theorem scalarLocalization_exact
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) (t : (R.obj ⋙ forget CommRingCat.{u}).sections) :
    (scalarLocalization R t).Additive ∧ PreservesFiniteLimits (scalarLocalization R t) ∧
      PreservesFiniteColimits (scalarLocalization R t) := by
  let O := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let P := ringedSectionLocalizationPresheafOfUniverses R t
  let F := PresheafOfModules.sheafification (R := O) (𝟙 O.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (R := O) (𝟙 O.obj)
  let I := SheafOfModules.forget O ⋙ PresheafOfModules.restrictScalars (𝟙 O.obj)
  have hP : PreservesFiniteLimits (tensorRight P) := by
    constructor
    intro K _ _
    have (U : Cᵒᵖ) : Module.Flat (R.obj.obj U) (P.obj U) :=
      IsLocalization.flat (ringedSectionLocalizationCarrierOfUniverses R t U)
        (Submonoid.powers (t.val U : R.obj.obj U))
    exact ⟨⟨fun hc ↦ ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _
      (fun U ↦ isLimitOfPreserves
        (tensorRight (show ModuleCat (R.obj.obj U) from P.obj U))
        (isLimitOfPreserves (PresheafOfModules.evaluation O.obj U) hc))⟩⟩⟩
  have : PreservesLimitsOfSize.{0, 0} I := adj.rightAdjoint_preservesLimits
  have : PreservesFiniteLimits I := inferInstance
  have : F.Monoidal := inferInstance
  let e : tensorRight (F.obj P) ≅ I ⋙ tensorRight P ⋙ F :=
    Functor.isoWhiskerRight (asIso adj.counit).symm (tensorRight (F.obj P)) ≪≫
      Functor.isoWhiskerLeft I (Functor.Monoidal.commTensorRight F P)
  have : PreservesFiniteLimits (I ⋙ tensorRight P ⋙ F) :=
    comp_preservesFiniteLimits I (tensorRight P ⋙ F)
  have : PreservesFiniteLimits (tensorRight (F.obj P)) :=
    preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteLimits (tensorRight (ringedSectionLocalizationOfUniverses R t)) :=
    inferInstanceAs (PreservesFiniteLimits (tensorRight (F.obj P)))
  let e' := (SheafOfModules.siteSheafTensorRightIso R
    (ringedSectionLocalizationOfUniverses R t)).symm
  have : PreservesFiniteLimits (scalarLocalization R t) :=
    preservesFiniteLimits_of_natIso e'
  have : PreservesFiniteColimits (scalarLocalization R t) :=
    preservesFiniteColimits_of_natIso e'
  exact ⟨Functor.additive_of_iso e', inferInstance, inferInstance⟩

/-- Exactness of both functors, including additivity. No flat coefficient map and no
bound on a complex is assumed.
Source: Stacks, Tags 04JC, 03EI and 00CS
(blueprint: lem-weil-pbc-localization-inverse-image-coherence).
Proof: the inverse image transports addition and zero and preserves kernels by finite
limits; its module adjunction preserves cokernels. For localization use the sheafified
fraction model of the tensor product. Ordinary module localization preserves kernels,
module sheafification is exact, and extension of scalars preserves cokernels as a left
adjoint. Thus both additive functors preserve finite limits and finite colimits. -/
theorem localization_inverseImage_exact
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {K : GrothendieckTopology D}
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify K CommRingCat.{u}]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (_adj : L ⊣ V)
    [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (a : SheafOfModules.AlgebraicInverseImage L R S)
    (t : (R.obj ⋙ forget CommRingCat.{u}).sections)
    (s : (S.obj ⋙ forget CommRingCat.{u}).sections) :
    a.modules.Additive ∧ PreservesFiniteLimits a.modules ∧
      PreservesFiniteColimits a.modules ∧
      (scalarLocalization R t).Additive ∧ PreservesFiniteLimits (scalarLocalization R t) ∧
      PreservesFiniteColimits (scalarLocalization R t) ∧
      (scalarLocalization S s).Additive ∧ PreservesFiniteLimits (scalarLocalization S s) ∧
      PreservesFiniteColimits (scalarLocalization S s) := by
  let f : GeometricMorphism (Sheaf K (Type u)) (Sheaf J (Type u)) :=
    ⟨L, V, _adj, inferInstance⟩
  have hi := ((GeometricMorphism.geometric_inverse_image_exact J K f).2.2 R).2 S
    (inverseImageUniverses a)
  have he : exactFunctor _ _ a.modules := hi.1
  obtain ⟨hR, hlR, hcR⟩ := scalarLocalization_exact R t
  obtain ⟨hS, hlS, hcS⟩ := scalarLocalization_exact S s
  exact ⟨(rightExactFunctor_le_additiveFunctor _ _) _ he.2, he.1, he.2,
    hR, hlR, hcR, hS, hlS, hcS⟩

-- The regular-module colimit model, with independent site and coefficient universes.
namespace LocalizationSequence

set_option linter.unusedSectionVars false

open Opposite

private theorem scalar_localization_colimit {R : Type u} [CommRing R] (s : R) :
    let D := Functor.ofSequence (X := fun _ : ℕ ↦ ModuleCat.of R R)
      (fun _ ↦ ModuleCat.ofHom (LinearMap.lsmul R R s))
    ∃ e : colimit D ≅ ModuleCat.of R (Localization.Away s),
      ∀ (m : ℕ) (a : R), e.hom ((colimit.ι D m) a) =
        algebraMap R _ a * IsLocalization.Away.invSelf s ^ m := by
  dsimp only
  obtain ⟨κ, hκ⟩ := ModuleCat.localization_away_colimit s R
  let e := IsLocalizedModule.iso (Submonoid.powers s)
    (Algebra.linearMap R (Localization.Away s))
  have he (a : R) (n : ℕ) :
      e (LocalizedModule.mk (S := Submonoid.powers s) a ⟨s ^ n, ⟨n, rfl⟩⟩) =
        algebraMap R _ a * IsLocalization.Away.invSelf s ^ n := by
    apply (IsLocalization.Away.algebraMap_pow_isUnit
      (S := Localization.Away s) s n).mul_left_cancel
    calc
      _ = e ((s ^ n) • LocalizedModule.mk (S := Submonoid.powers s)
          a ⟨s ^ n, ⟨n, rfl⟩⟩) := by rw [map_smul, Algebra.smul_def, map_pow]
      _ = algebraMap R _ a := by
        rw [LocalizedModule.smul'_mk, ← Submonoid.smul_def (⟨s ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers s),
          LocalizedModule.mk_cancel]
        exact IsLocalizedModule.iso_mk_one _ _ a
      _ = _ := by rw [mul_left_comm, ← mul_pow,
        IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  refine ⟨(κ.trans e).toModuleIso, ?_⟩
  intro n a
  change e (κ ((colimit.ι (Functor.ofSequence (X := fun _ : ℕ ↦
    ModuleCat.of R R) (fun _ ↦ ModuleCat.ofHom (LinearMap.lsmul R R s))) n) a)) = _
  rw [hκ, he]

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
variable {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (O : Sheaf J CommRingCat.{u})

private def regularScalar
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    End (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  (SheafOfModules.unitHomEquiv _).symm ⟨s.val, s.property⟩

private abbrev sectionValue
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) : O.obj.obj X := s.val X

private abbrev localizationInv
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) :
    ringedSectionLocalizationCarrierOfUniverses O s X :=
  IsLocalization.Away.invSelf (R := O.obj.obj X) (sectionValue O s X)

private theorem localization_map_inv
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y : Cᵒᵖ} (g : X ⟶ Y) :
    ringedSectionLocalizationMapOfUniverses O s g
      (localizationInv O s X) =
        localizationInv O s Y := by
  apply (IsLocalization.Away.algebraMap_isUnit
    (R := O.obj.obj Y) (S := ringedSectionLocalizationCarrierOfUniverses O s Y)
      (sectionValue O s Y)).mul_left_cancel
  have hc (a : O.obj.obj X) :
      ringedSectionLocalizationMapOfUniverses O s g (algebraMap _ _ a) =
        algebraMap _ _ (O.obj.map g a) := by
    exact IsLocalization.Away.lift_eq _ _ a
  calc
    _ = ringedSectionLocalizationMapOfUniverses O s g
        (algebraMap _ _ (sectionValue O s X) * localizationInv O s X) := by
      rw [map_mul, hc, show O.obj.map g (sectionValue O s X) =
          sectionValue O s Y from s.property g]
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf, map_one]
    _ = _ := (IsLocalization.Away.mul_invSelf (sectionValue O s Y)).symm

private def fractionMap
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    PresheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj ⟶
      ringedSectionLocalizationPresheafOfUniverses O s :=
  (ringedSectionLocalizationPresheafOfUniverses O s).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun X ↦ localizationInv O s X ^ n)
      (fun {_ _} g ↦ by
        change ringedSectionLocalizationMapOfUniverses O s g _ = _
        rw [map_pow, localization_map_inv]))

private theorem fractionMap_apply
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ)
    (X : Cᵒᵖ) (a : O.obj.obj X) :
    (fractionMap O s n).app X a =
      algebraMap (O.obj.obj X) (ringedSectionLocalizationCarrierOfUniverses O s X) a *
        localizationInv O s X ^ n := by
  change a • localizationInv O s X ^ n = _
  exact Algebra.smul_def a _

private theorem scalar_apply
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) (a : O.obj.obj X) :
    (regularScalar O s).val.app X a = a * sectionValue O s X := by
  change a • sectionValue O s X = _
  rfl

private theorem fractionMap_step
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    (regularScalar O s).val ≫ fractionMap O s (n + 1) = fractionMap O s n := by
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change O.obj.obj X at a
  change (fractionMap O s (n + 1)).app X ((regularScalar O s).val.app X a) =
    (fractionMap O s n).app X a
  rw [fractionMap_apply, scalar_apply, fractionMap_apply, map_mul, pow_succ]
  calc
    _ = (algebraMap _ _ a * localizationInv O s X ^ n) *
        (algebraMap _ _ (sectionValue O s X) * localizationInv O s X) := by ring
    _ = _ := by rw [IsLocalization.Away.mul_invSelf, mul_one]

private def localizationPresheafCocone
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    Cocone (Functor.ofSequence (X := fun _ : ℕ ↦
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
        (fun _ ↦ regularScalar O s) ⋙ SheafOfModules.forget _) where
  pt := ringedSectionLocalizationPresheafOfUniverses O s
  ι := NatTrans.ofSequence (fun n ↦ fractionMap O s n) (by
    intro n
    change ((SheafOfModules.forget _).map
      ((Functor.ofSequence (fun _ ↦ regularScalar O s)).map _)) ≫ _ = _ ≫ 𝟙 _
    rw [Functor.ofSequence_map_homOfLE_succ, Category.comp_id]
    exact fractionMap_step O s n)

private def localizationPresheafCoconeIsColimit
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    IsColimit (localizationPresheafCocone O s) := by
  apply PresheafOfModules.evaluationJointlyReflectsColimits
  intro X
  let R := O.obj.obj X
  let D := Functor.ofSequence (X := fun _ : ℕ ↦ ModuleCat.of R R)
    (fun _ ↦ ModuleCat.ofHom (LinearMap.lsmul R R (sectionValue O s X)))
  let c := (PresheafOfModules.evaluation _ X).mapCocone
    (localizationPresheafCocone O s)
  let F := (Functor.ofSequence (fun _ ↦ regularScalar O s) ⋙
    SheafOfModules.forget _) ⋙ PresheafOfModules.evaluation _ X
  let t : D ⟶ F := NatTrans.ofSequence (fun _ ↦ 𝟙 (ModuleCat.of R R)) (by
    intro n
    simp only [F, D, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change O.obj.obj X at a
    change (sectionValue O s X) * a = (regularScalar O s).val.app X a
    rw [scalar_apply, mul_comm])
  let et : D ≅ F := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro i j f; exact t.naturality f)
  let e := Classical.choose (scalar_localization_colimit (sectionValue O s X))
  have he := Classical.choose_spec (scalar_localization_colimit (sectionValue O s X))
  change ∀ (m : ℕ) (a : R), e.hom ((colimit.ι D m) a) =
    algebraMap R (Localization.Away (sectionValue O s X)) a *
      IsLocalization.Away.invSelf (sectionValue O s X) ^ m at he
  clear_value e
  apply (IsColimit.precomposeHomEquiv et c).toFun
  apply IsColimit.ofIsoColimit (colimit.isColimit D)
  refine Cocone.ext e ?_
  intro m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  dsimp only [et, c, Cocone.precompose, localizationPresheafCocone,
    Functor.mapCocone, NatIso.ofComponents, NatTrans.ofSequence] at *
  change e.hom ((colimit.ι D m) a) = (fractionMap O s m).app X a
  rw [he, fractionMap_apply]

private def localizationSheafMap
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) ⟶
      ringedSectionLocalizationOfUniverses O s :=
  (SheafOfModules.fullyFaithfulForget _).preimage
    (fractionMap O s n ≫
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).unit.app _)

private theorem localizationSheafMap_step
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    regularScalar O s ≫ localizationSheafMap O s (n + 1) =
      localizationSheafMap O s n := by
  apply SheafOfModules.hom_ext
  change (regularScalar O s).val ≫ (fractionMap O s (n + 1) ≫ _) = _
  rw [← Category.assoc, fractionMap_step]
  rfl

private def localizationSheafCocone
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    Cocone (Functor.ofSequence (X := fun _ : ℕ ↦
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
        (fun _ ↦ regularScalar O s)) where
  pt := ringedSectionLocalizationOfUniverses O s
  ι := NatTrans.ofSequence (fun n ↦ localizationSheafMap O s n) (by
    intro n
    rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
    change regularScalar O s ≫ _ = _ ≫ 𝟙 _
    rw [Category.comp_id]
    exact localizationSheafMap_step O s n)

private def localizationSheafCoconeIsColimit
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    IsColimit (localizationSheafCocone O s) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)
  let hc := localizationPresheafCoconeIsColimit O s
  clear_value hc
  let U := SheafOfModules.forget ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  refine { desc := fun t ↦ (adj.homEquiv _ _).symm (hc.desc (U.mapCocone t))
           fac := ?_
           uniq := ?_ }
  · intro t n
    apply U.map_injective
    change (fractionMap O s n ≫ adj.unit.app _) ≫
      U.map ((adj.homEquiv _ _).symm (hc.desc (U.mapCocone t))) = _
    rw [Category.assoc]
    erw [← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]
    exact hc.fac (U.mapCocone t) n
  · intro t m hm
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    apply hc.hom_ext
    intro n
    rw [hc.fac]
    change fractionMap O s n ≫ (adj.homEquiv _ _ m) = _
    rw [Adjunction.homEquiv_unit, ← Category.assoc]
    exact congrArg (fun f ↦ U.map f) (hm n)

private theorem localizationSheafMap_zero
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    localizationSheafMap O s 0 = ringedSectionLocalizationUnitOfUniverses O s := by
  unfold localizationSheafMap ringedSectionLocalizationUnitOfUniverses
  congr 2

end LocalizationSequence

section ScalarMaps

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
variable {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

private def localizationScalar (R : Sheaf J CommRingCat.{u})
    (t : (R.obj ⋙ forget CommRingCat.{u}).sections) (M : inverseLocalizationModules R) :
    M ⟶ M :=
  ⟨{ app := fun U ↦ ModuleCat.ofHom (LinearMap.lsmul (R.obj.obj U) (M.val.obj U) (t.val U))
     naturality := by
       intro U V f
       ext m
       change (t.val V : R.obj.obj V) • M.val.map f m =
         M.val.map f ((t.val U : R.obj.obj U) • m)
       rw [M.val.map_smul]
       have ht : R.obj.map f (t.val U) = t.val V := t.property f
       change (t.val V : R.obj.obj V) • _ = R.obj.map f (t.val U) • _
       rw [ht] }⟩

private theorem localizationSets_preserves_sequence (R : Sheaf J CommRingCat.{u}) :
    PreservesColimitsOfShape ℕ (localizationModuleSets R) := by
  let O := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  have : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{u} C).inverse.op) (Type u) :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{u} _ _
  have : HasSheafify J (Type u) := hasSheafifyEssentiallySmallSite J _
  have : PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} O) := by
    constructor
    intro T _
    exact ((moduleSheaves_colimits_forgetful O).2.2.2.2.2 T).2.1
  have : PreservesColimitsOfShape ℕ (SheafOfModules.toSheaf.{u} O) :=
    (preservesColimitsOfSize_shrink (SheafOfModules.toSheaf.{u} O)).preservesColimitsOfShape
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  have : J.PreservesSheafification (forget AddCommGrpCat.{u}) := inferInstance
  have : PreservesColimitsOfShape ℕ (sheafCompose J (forget AddCommGrpCat.{u})) := by
    rw [(sheafificationAdjunction J AddCommGrpCat.{u}).preservesColimitsOfShape_iff]
    exact preservesColimitsOfShape_of_natIso
      (sheafComposeNatIso J (forget AddCommGrpCat.{u})
        (sheafificationAdjunction J AddCommGrpCat.{u}) (sheafificationAdjunction J (Type u)))
  exact comp_preservesColimitsOfShape _ _

end ScalarMaps

private theorem inverseImage_preserves_sequence
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify K CommRingCat.{u}]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {V : Sheaf K (Type u) ⥤ Sheaf J (Type u)} (adj : L ⊣ V)
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (a : SheafOfModules.AlgebraicInverseImage L R S) :
    PreservesColimitsOfShape ℕ a.modules := by
  have : PreservesColimitsOfShape ℕ L := adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have := localizationSets_preserves_sequence R
  have := localizationSets_preserves_sequence S
  have : PreservesColimitsOfShape ℕ (a.modules ⋙ localizationModuleSets S) :=
    preservesColimitsOfShape_of_natIso a.moduleUnderlying.symm
  have : ReflectsColimitsOfShape ℕ (localizationModuleSets S) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves a.modules (localizationModuleSets S)

private theorem inverseImage_scalar
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify K CommRingCat.{u}]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (a : SheafOfModules.AlgebraicInverseImage L R S)
    (t : (R.obj ⋙ forget CommRingCat.{u}).sections)
    (s : (S.obj ⋙ forget CommRingCat.{u}).sections) (hs : IsInverseImageSection a t s)
    (M : inverseLocalizationModules R) :
    a.modules.map (localizationScalar R t M) = localizationScalar S s (a.modules.obj M) := by
  let T := (localizationModuleSets R).obj M
  let r : T ⟶ (sheafCompose J (forget CommRingCat.{u})).obj R :=
    ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ t.val U)
       naturality := by
         intro U V f
         ext x
         exact (t.property f).symm }⟩
  have h := a.moduleSMul M T r (𝟙 T)
    ((localizationModuleSets R).map (localizationScalar R t M)) (by intro U x; rfl)
  apply (localizationModuleSets S).map_injective
  apply (cancel_epi (a.moduleUnderlying.inv.app M)).1
  ext W x
  have hn := congrArg (fun f ↦ f.hom.app W x)
    (a.moduleUnderlying.inv.naturality (localizationScalar R t M))
  change (a.moduleUnderlying.inv.app M).hom.app W
      ((L.map ((localizationModuleSets R).map (localizationScalar R t M))).hom.app W x) =
    (a.modules.map (localizationScalar R t M)).val.app W
      ((a.moduleUnderlying.inv.app M).hom.app W x) at hn
  change (a.modules.map (localizationScalar R t M)).val.app W
      ((a.moduleUnderlying.inv.app M).hom.app W x) = _
  rw [← hn]
  have hh := h W x
  dsimp only [id_eq] at hh
  rw [hs T r (by intro U x; rfl) W x, L.map_id] at hh
  exact hh

namespace LocalizationSequence

open MonoidalCategory
set_option linter.unusedSectionVars false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
variable {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (R : Sheaf J CommRingCat.{u}) (t : (R.obj ⋙ forget CommRingCat.{u}).sections)

private def tensorModelIso (M : inverseLocalizationModules R) :
    (PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).obj
        (M.val ⊗ ringedSectionLocalizationPresheafOfUniverses R t) ≅
      (scalarLocalization R t).obj M := by
  let O := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let P := ringedSectionLocalizationPresheafOfUniverses R t
  let F := PresheafOfModules.sheafification (R := O) (𝟙 O.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (R := O) (𝟙 O.obj)
  let W := J.W.inverseImage (PresheafOfModules.toPresheaf.{u} O.obj)
  have hη : W (adj.unit.app P) := by
    change J.W ((PresheafOfModules.toPresheaf O.obj).map (adj.unit.app P))
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact J.W_toSheafify P.presheaf
  have hk : W (M.val ◁ adj.unit.app P) := W.whiskerLeft_mem M.val _ hη
  dsimp only [W] at hk
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (R := O) (𝟙 O.obj)] at hk
  have : IsIso (F.map (M.val ◁ adj.unit.app P)) := hk
  exact asIso (F.map (M.val ◁ adj.unit.app P)) ≪≫
    F.mapIso ((SheafOfModules.siteTensorRightIso R (F.obj P).val).app M.val).symm

private theorem tensorModelIso_tmul (M : inverseLocalizationModules R)
    (U : Cᵒᵖ) (m : M.val.obj U)
    (p : ringedSectionLocalizationCarrierOfUniverses R t U) :
    (tensorModelIso R t M).hom.val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
          (M.val ⊗ ringedSectionLocalizationPresheafOfUniverses R t)).app U
            (m ⊗ₜ[R.obj.obj U] p)) =
      SheafOfModules.siteSheafTensorTmul M (ringedSectionLocalizationOfUniverses R t) U m
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
          (ringedSectionLocalizationPresheafOfUniverses R t)).app U p) := by
  let O := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let F := PresheafOfModules.sheafification (R := O) (𝟙 O.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (R := O) (𝟙 O.obj)
  let P := ringedSectionLocalizationPresheafOfUniverses R t
  let k := (M.val ◁ adj.unit.app P) ≫
    ((SheafOfModules.siteTensorRightIso R (F.obj P).val).app M.val).inv
  have hn := congrArg (fun f ↦ f.app U (m ⊗ₜ[R.obj.obj U] p)) (adj.unit.naturality k).symm
  change (F.map k).val.app U ((adj.unit.app (M.val ⊗ P)).app U
    (m ⊗ₜ[R.obj.obj U] p)) = _ at hn
  apply (show (tensorModelIso R t M).hom = F.map k by
    simp only [tensorModelIso, k, F.map_comp, Iso.trans_hom, asIso_hom,
      Functor.mapIso_hom, Iso.symm_hom]
    rfl) ▸ hn

private def modulePresheafCocone (M : inverseLocalizationModules R) :
    Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ M)
      (fun _ ↦ localizationScalar R t M) ⋙ SheafOfModules.forget _) := by
  let X := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let D := Functor.ofSequence (X := fun _ : ℕ ↦ M) (fun _ ↦ localizationScalar R t M)
  let E := Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ regularScalar R t)
  let F := tensorLeft M.val
  let ε : D ⋙ SheafOfModules.forget _ ≅
      (E ⋙ SheafOfModules.forget _) ⋙ F := by
    let τ : D ⋙ SheafOfModules.forget _ ⟶
        (E ⋙ SheafOfModules.forget _) ⋙ F :=
      NatTrans.ofSequence (fun _ ↦ (ρ_ M.val).inv) (by
        intro n
        simp only [D, E, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ]
        ext U m
        change (sectionValue R t U • m) ⊗ₜ[R.obj.obj U] (1 : R.obj.obj U) =
          m ⊗ₜ[R.obj.obj U] ((regularScalar R t).val.app U (1 : R.obj.obj U))
        rw [scalar_apply, one_mul]
        simpa only [smul_eq_mul, mul_one] using
          (TensorProduct.smul_tmul (R := R.obj.obj U) (sectionValue R t U) m
            (1 : R.obj.obj U)))
    exact NatIso.ofComponents (fun _ ↦ (ρ_ M.val).symm) (fun f ↦ τ.naturality f)
  exact (Cocone.precompose ε.hom).obj (F.mapCocone (localizationPresheafCocone R t))

private def modulePresheafCoconeIsColimit (M : inverseLocalizationModules R) :
    IsColimit (modulePresheafCocone R t M) := by
  have : PreservesColimitsOfSize.{u, u} (tensorLeft M.val) := by
    change PreservesColimitsOfSize.{u, u} (tensorLeft
      (show PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat) from M.val))
    infer_instance
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft M.val) :=
    preservesColimitsOfSize_shrink (tensorLeft M.val)
  unfold modulePresheafCocone
  exact (IsColimit.precomposeHomEquiv _ _).symm
    (isColimitOfPreserves _ (localizationPresheafCoconeIsColimit R t))

private theorem modulePresheafCocone_zero (M : inverseLocalizationModules R)
    (U : Cᵒᵖ) (m : M.val.obj U) :
    ((modulePresheafCocone R t M).ι.app 0).app U m =
      m ⊗ₜ[R.obj.obj U]
        (1 : ringedSectionLocalizationCarrierOfUniverses R t U) := by
  change m ⊗ₜ[R.obj.obj U] ((fractionMap R t 0).app U (1 : R.obj.obj U)) = _
  congr 1
  rw [fractionMap_apply]
  simp

end LocalizationSequence

namespace LocalizationSequence

set_option linter.unusedSectionVars false
variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
variable {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (R : Sheaf J CommRingCat.{u}) (t : (R.obj ⋙ forget CommRingCat.{u}).sections)

private def moduleSheafCocone (M : inverseLocalizationModules R) :
    Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ M)
      (fun _ ↦ localizationScalar R t M)) := by
  let c := modulePresheafCocone R t M
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  exact
    { pt := (scalarLocalization R t).obj M
      ι :=
        { app := fun n ↦
            (show M ⟶ (PresheafOfModules.sheafification
              (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).obj c.pt from
              ⟨c.ι.app n ≫ adj.unit.app c.pt⟩) ≫ (tensorModelIso R t M).hom
          naturality := by
            intro n k f
            apply SheafOfModules.hom_ext
            change
              ((Functor.ofSequence (X := fun _ : ℕ ↦ M)
                (fun _ ↦ localizationScalar R t M)).map f).val ≫
                  ((c.ι.app k ≫ adj.unit.app c.pt) ≫ (tensorModelIso R t M).hom.val) =
                (c.ι.app n ≫ adj.unit.app c.pt) ≫ (tensorModelIso R t M).hom.val
            rw [← Category.assoc, ← Category.assoc]
            exact congrArg (fun h ↦ (h ≫ adj.unit.app c.pt) ≫
              (tensorModelIso R t M).hom.val) (c.w f) } }

private def moduleSheafCoconeIsColimit (M : inverseLocalizationModules R) :
    IsColimit (moduleSheafCocone R t M) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let c := modulePresheafCocone R t M
  let hc := modulePresheafCoconeIsColimit R t M
  let U := SheafOfModules.forget ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let e := tensorModelIso R t M
  let F := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  refine
    { desc := fun d ↦ e.inv ≫ (adj.homEquiv _ _).symm (hc.desc (U.mapCocone d))
      fac := ?_
      uniq := ?_ }
  · intro d n
    change ((show M ⟶ F.obj c.pt from ⟨c.ι.app n ≫ adj.unit.app c.pt⟩) ≫ e.hom) ≫
      (e.inv ≫ _) = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    apply U.map_injective
    change (c.ι.app n ≫ adj.unit.app c.pt) ≫
      U.map ((adj.homEquiv _ _).symm (hc.desc (U.mapCocone d))) = _
    rw [Category.assoc]
    erw [← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]
    exact hc.fac (U.mapCocone d) n
  · intro d f hf
    apply (cancel_epi e.hom).1
    simp only [Iso.hom_inv_id_assoc]
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    apply hc.hom_ext
    intro n
    rw [hc.fac]
    change c.ι.app n ≫ adj.homEquiv _ _ (e.hom ≫ f) = _
    rw [Adjunction.homEquiv_unit, ← Category.assoc]
    have hh := congrArg (fun g ↦ U.map g) (hf n)
    change ((c.ι.app n ≫ adj.unit.app c.pt) ≫ e.hom.val) ≫ f.val = _ at hh
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact congrArg (fun g ↦ g.app X m) hh

private theorem moduleSheafCocone_zero (M : inverseLocalizationModules R) :
    (moduleSheafCocone R t M).ι.app 0 = (scalarLocalizationUnit R t).app M := by
  apply SheafOfModules.hom_ext
  ext U m
  change (tensorModelIso R t M).hom.val.app U
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
      (modulePresheafCocone R t M).pt).app U
        (((modulePresheafCocone R t M).ι.app 0).app U m)) = _
  rw [modulePresheafCocone_zero]
  refine (tensorModelIso_tmul R t M U m 1).trans ?_
  convert (Classical.choose_spec (existsUnique_scalarLocalizationUnit R t)).1 M U m |>.symm
    using 1
  · congr 1
    change _ = ((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
        (ringedSectionLocalizationPresheafOfUniverses R t)).app U
          ((1 : R.obj.obj U) • (1 : ringedSectionLocalizationCarrierOfUniverses R t U))
    rw [one_smul]
  · rfl

private theorem scalar_naturality {M N : inverseLocalizationModules R} (f : M ⟶ N) :
    localizationScalar R t M ≫ f = f ≫ localizationScalar R t N := by
  ext U m
  exact (f.val.app U).hom.map_smul (sectionValue R t U) m

private theorem colimit_hom_ext_zero
    {M N : inverseLocalizationModules R}
    (c : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ M)
      (fun _ ↦ localizationScalar R t M))) (hc : IsColimit c)
    [Mono (localizationScalar R t N)] (f g : c.pt ⟶ N)
    (h : c.ι.app 0 ≫ f = c.ι.app 0 ≫ g) : f = g := by
  apply hc.hom_ext
  intro n
  induction n with
  | zero => exact h
  | succ n ih =>
      apply (cancel_mono (localizationScalar R t N)).1
      have hw := c.w (homOfLE (Nat.le_succ n))
      simp only [Functor.ofSequence_map_homOfLE_succ] at hw
      calc
        _ = localizationScalar R t M ≫ (c.ι.app (n + 1) ≫ f) :=
          (scalar_naturality R t (c.ι.app (n + 1) ≫ f)).symm
        _ = c.ι.app n ≫ f := by rw [← Category.assoc, hw]
        _ = c.ι.app n ≫ g := ih
        _ = localizationScalar R t M ≫ (c.ι.app (n + 1) ≫ g) := by
          rw [← Category.assoc, hw]
        _ = _ := scalar_naturality R t (c.ι.app (n + 1) ≫ g)

private theorem colimit_scalar_isIso
    {M : inverseLocalizationModules R}
    (c : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ M)
      (fun _ ↦ localizationScalar R t M))) (hc : IsColimit c) :
    IsIso (localizationScalar R t c.pt) := by
  let d : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ M)
      (fun _ ↦ localizationScalar R t M)) :=
    { pt := c.pt
      ι := NatTrans.ofSequence (fun n ↦ c.ι.app (n + 1)) (by
        intro n
        simp only [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
        have h := c.w (homOfLE (Nat.le_succ (n + 1)))
        rw [Functor.ofSequence_map_homOfLE_succ] at h
        exact h.trans (Category.comp_id _).symm) }
  have hstep (n : ℕ) : localizationScalar R t M ≫ c.ι.app (n + 1) = c.ι.app n := by
    have h := c.w (homOfLE (Nat.le_succ n))
    rw [Functor.ofSequence_map_homOfLE_succ] at h
    exact h
  refine ⟨⟨hc.desc d, ?_, ?_⟩⟩
  · apply hc.hom_ext
    intro n
    calc
      _ = (c.ι.app n ≫ localizationScalar R t c.pt) ≫ hc.desc d :=
        (Category.assoc _ _ _).symm
      _ = (localizationScalar R t M ≫ c.ι.app n) ≫ hc.desc d := by
        rw [scalar_naturality R t (show M ⟶ c.pt from c.ι.app n)]
      _ = localizationScalar R t M ≫ c.ι.app (n + 1) := by
        rw [Category.assoc, hc.fac]; rfl
      _ = c.ι.app n ≫ 𝟙 _ := (hstep n).trans (Category.comp_id _).symm
  · apply hc.hom_ext
    intro n
    calc
      _ = c.ι.app (n + 1) ≫ localizationScalar R t c.pt := by
        rw [← Category.assoc, hc.fac]; rfl
      _ = localizationScalar R t M ≫ c.ι.app (n + 1) :=
        (scalar_naturality R t (show M ⟶ c.pt from c.ι.app (n + 1))).symm
      _ = c.ι.app n ≫ 𝟙 _ := (hstep n).trans (Category.comp_id _).symm

end LocalizationSequence

namespace LocalizationSequence

set_option linter.unusedSectionVars false
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify K CommRingCat.{u}]
variable [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
variable {V : Sheaf K (Type u) ⥤ Sheaf J (Type u)} (adj : L ⊣ V)
variable {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
variable (a : SheafOfModules.AlgebraicInverseImage L R S)
variable (t : (R.obj ⋙ forget CommRingCat.{u}).sections)
variable (s : (S.obj ⋙ forget CommRingCat.{u}).sections) (hs : IsInverseImageSection a t s)

private def imageCocone (M : inverseLocalizationModules R) :
    Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ a.modules.obj M)
      (fun _ ↦ localizationScalar S s (a.modules.obj M))) := by
  let T := Functor.ofSequence (X := fun _ : ℕ ↦ a.modules.obj M)
    (fun _ ↦ localizationScalar S s (a.modules.obj M))
  let D := Functor.ofSequence (X := fun _ : ℕ ↦ M) (fun _ ↦ localizationScalar R t M)
  let τ : T ⟶ D ⋙ a.modules := NatTrans.ofSequence (fun _ ↦ 𝟙 _) (by
    intro n
    simpa only [T, D, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ,
      Category.id_comp, Category.comp_id] using (inverseImage_scalar a t s hs M).symm)
  let e : T ≅ D ⋙ a.modules :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ τ.naturality f)
  exact (Cocone.precompose e.hom).obj (a.modules.mapCocone (moduleSheafCocone R t M))

private def imageCoconeIsColimit (M : inverseLocalizationModules R) :
    IsColimit (imageCocone a t s hs M) := by
  have := inverseImage_preserves_sequence adj a
  unfold imageCocone
  exact (IsColimit.precomposeHomEquiv _ _).symm
    (isColimitOfPreserves _ (moduleSheafCoconeIsColimit R t M))

private theorem imageCocone_zero (M : inverseLocalizationModules R) :
    (imageCocone a t s hs M).ι.app 0 = a.modules.map ((scalarLocalizationUnit R t).app M) := by
  change (𝟙 _) ≫ a.modules.map ((moduleSheafCocone R t M).ι.app 0) = _
  rw [Category.id_comp, moduleSheafCocone_zero]

private def comparison (M : inverseLocalizationModules R) :
    a.modules.obj ((scalarLocalization R t).obj M) ≅
      (scalarLocalization S s).obj (a.modules.obj M) :=
  (imageCoconeIsColimit adj a t s hs M).coconePointUniqueUpToIso
    (moduleSheafCoconeIsColimit S s (a.modules.obj M))

private theorem comparison_unit (M : inverseLocalizationModules R) :
    a.modules.map ((scalarLocalizationUnit R t).app M) ≫ (comparison adj a t s hs M).hom =
      (scalarLocalizationUnit S s).app (a.modules.obj M) := by
  rw [← imageCocone_zero a t s hs M, comparison,
    IsColimit.comp_coconePointUniqueUpToIso_hom, moduleSheafCocone_zero]

private theorem comparison_naturality {M N : inverseLocalizationModules R} (f : M ⟶ N) :
    a.modules.map ((scalarLocalization R t).map f) ≫ (comparison adj a t s hs N).hom =
      (comparison adj a t s hs M).hom ≫ (scalarLocalization S s).map (a.modules.map f) := by
  have : IsIso (localizationScalar S s ((scalarLocalization S s).obj (a.modules.obj N))) :=
    colimit_scalar_isIso S s (moduleSheafCocone S s (a.modules.obj N))
      (moduleSheafCoconeIsColimit S s (a.modules.obj N))
  apply colimit_hom_ext_zero S s (imageCocone a t s hs M)
    (imageCoconeIsColimit adj a t s hs M)
  rw [imageCocone_zero]
  calc
    _ = a.modules.map (((scalarLocalizationUnit R t).app M) ≫
        (scalarLocalization R t).map f) ≫ (comparison adj a t s hs N).hom := by
      simp only [Functor.map_comp, Category.assoc]
    _ = a.modules.map (f ≫ (scalarLocalizationUnit R t).app N) ≫
        (comparison adj a t s hs N).hom := by
      rw [← (scalarLocalizationUnit R t).naturality f]
      rfl
    _ = a.modules.map f ≫ (scalarLocalizationUnit S s).app (a.modules.obj N) := by
      rw [Functor.map_comp, Category.assoc, comparison_unit]
    _ = (scalarLocalizationUnit S s).app (a.modules.obj M) ≫
        (scalarLocalization S s).map (a.modules.map f) :=
      (scalarLocalizationUnit S s).naturality (a.modules.map f)
    _ = _ := by rw [← comparison_unit adj a t s hs M, Category.assoc]

end LocalizationSequence

/-- The canonical comparison is uniquely characterized by preservation of the unit.
Source: Stacks, Tags 03EL and 03CZ
(blueprint: lem-weil-pbc-localization-inverse-image-coherence).
Proof: the tensor localization is the sheafification of module fractions, with unit
`m ↦ m/1`. For any module on which the section is invertible, a map extends uniquely by
`m/tⁿ ↦ t⁻ⁿh(m)`. The geometric module adjunction transports this initial property to
the inverse image, since its scalar-action comparison transports invertibility of t.
The two initial objects therefore have unique mutually inverse unit-preserving maps.
Uniqueness proves naturality in M and uniqueness of the natural isomorphism. Maps
between the localized modules are automatically linear over the localized ring,
because they commute with the inverse of multiplication by the scalar section. -/
theorem existsUnique_localizationInverseImage
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {K : GrothendieckTopology D}
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify K CommRingCat.{u}]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (_adj : L ⊣ V)
    [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (a : SheafOfModules.AlgebraicInverseImage L R S)
    (t : (R.obj ⋙ forget CommRingCat.{u}).sections)
    (s : (S.obj ⋙ forget CommRingCat.{u}).sections) (_hs : IsInverseImageSection a t s) :
    ∃! β : scalarLocalization R t ⋙ a.modules ≅ a.modules ⋙ scalarLocalization S s,
      Functor.whiskerRight (scalarLocalizationUnit R t) a.modules ≫ β.hom =
        Functor.whiskerLeft a.modules (scalarLocalizationUnit S s) := by
  let β : scalarLocalization R t ⋙ a.modules ≅ a.modules ⋙ scalarLocalization S s :=
    NatIso.ofComponents (LocalizationSequence.comparison _adj a t s _hs)
      (fun f ↦ LocalizationSequence.comparison_naturality _adj a t s _hs f)
  refine ⟨β, ?_, ?_⟩
  · apply NatTrans.ext
    funext M
    exact LocalizationSequence.comparison_unit _adj a t s _hs M
  · intro γ hγ
    apply Iso.ext
    apply NatTrans.ext
    funext M
    have : IsIso (localizationScalar S s ((scalarLocalization S s).obj (a.modules.obj M))) :=
      LocalizationSequence.colimit_scalar_isIso S s
        (LocalizationSequence.moduleSheafCocone S s (a.modules.obj M))
        (LocalizationSequence.moduleSheafCoconeIsColimit S s (a.modules.obj M))
    change γ.hom.app M = (LocalizationSequence.comparison _adj a t s _hs M).hom
    apply LocalizationSequence.colimit_hom_ext_zero S s
      (N := (scalarLocalization S s).obj (a.modules.obj M))
      (LocalizationSequence.imageCocone a t s _hs M)
      (LocalizationSequence.imageCoconeIsColimit _adj a t s _hs M)
    rw [LocalizationSequence.imageCocone_zero]
    exact (congr_app hγ M).trans
      (LocalizationSequence.comparison_unit _adj a t s _hs M).symm

-- Ring morphisms are transported directly using the specified graph equations.
namespace LocalizationRings

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency.types false

open MonoidalCategory CartesianMonoidalCategory

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]

private abbrev sets (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (forget CommRingCat.{u})).obj R

private def constMap (R : Sheaf J CommRingCat.{u})
    (t : (R.obj ⋙ forget CommRingCat.{u}).sections) (T : Sheaf J (Type u)) : T ⟶ sets R :=
  ⟨{ app := fun U ↦ ↾(fun _ ↦ t.val U)
     naturality := by intro U V f; ext x; exact (t.property f).symm }⟩

private def addMap (R : Sheaf J CommRingCat.{u}) : sets R ⊗ sets R ⟶ sets R :=
  ⟨{ app := fun U ↦ ↾(fun x ↦ @Add.add (R.obj.obj U) inferInstance x.1 x.2)
     naturality := by intro U V f; ext x; exact ((R.obj.map f).hom.map_add _ _).symm }⟩

private def mulMap (R : Sheaf J CommRingCat.{u}) : sets R ⊗ sets R ⟶ sets R :=
  ⟨{ app := fun U ↦ ↾(fun x ↦ @Mul.mul (R.obj.obj U) inferInstance x.1 x.2)
     naturality := by intro U V f; ext x; exact ((R.obj.map f).hom.map_mul _ _).symm }⟩

variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)} [PreservesFiniteLimits L]
variable {R Q : Sheaf J CommRingCat.{u}} {S A : Sheaf K CommRingCat.{u}}
variable (a : SheafOfModules.AlgebraicInverseImage L R S)
variable (b : SheafOfModules.AlgebraicInverseImage L Q A) (f : R ⟶ Q)

private def transportSets : sets S ⟶ sets A :=
  a.ringUnderlying.inv ≫ L.map ((sheafCompose J (forget CommRingCat.{u})).map f) ≫
    b.ringUnderlying.hom

private theorem transportSets_apply (T : Sheaf J (Type u)) (r : T ⟶ sets R)
    (W : Dᵒᵖ) (x : (L.obj T).obj.obj W) :
    (transportSets a b f).hom.app W
      (a.ringUnderlying.hom.hom.app W ((L.map r).hom.app W x)) =
    b.ringUnderlying.hom.hom.app W
      ((L.map (r ≫ (sheafCompose J (forget CommRingCat.{u})).map f)).hom.app W x) := by
  have h : a.ringUnderlying.hom ≫ transportSets a b f =
      L.map ((sheafCompose J (forget CommRingCat.{u})).map f) ≫ b.ringUnderlying.hom := by
    simp only [transportSets, Iso.hom_inv_id_assoc]
  have hh := congrArg (fun g ↦ g.hom.app W x) (congrArg (fun g ↦ L.map r ≫ g) h)
  change (transportSets a b f).hom.app W
    (a.ringUnderlying.hom.hom.app W ((L.map r).hom.app W x)) =
      b.ringUnderlying.hom.hom.app W
        ((L.map r ≫ L.map ((sheafCompose J (forget CommRingCat.{u})).map f)).hom.app W x) at hh
  simpa only [Functor.map_comp] using hh

private theorem transportSets_add (W : Dᵒᵖ) (x y : S.obj.obj W) :
    @id (A.obj.obj W) ((transportSets a b f).hom.app W (x + y)) =
      @id (A.obj.obj W) ((transportSets a b f).hom.app W x) +
        @id (A.obj.obj W) ((transportSets a b f).hom.app W y) := by
  let X := sets R
  let p := inv (CartesianMonoidalCategory.prodComparison L X X)
  let z := p.hom.app W (a.ringUnderlying.inv.hom.app W x,
    a.ringUnderlying.inv.hom.app W y)
  have h₁ : (L.map (fst X X)).hom.app W z = a.ringUnderlying.inv.hom.app W x :=
    congrArg (fun g ↦ g.hom.app W
      (a.ringUnderlying.inv.hom.app W x, a.ringUnderlying.inv.hom.app W y))
      (inv_prodComparison_map_fst L X X)
  have h₂ : (L.map (snd X X)).hom.app W z = a.ringUnderlying.inv.hom.app W y :=
    congrArg (fun g ↦ g.hom.app W
      (a.ringUnderlying.inv.hom.app W x, a.ringUnderlying.inv.hom.app W y))
      (inv_prodComparison_map_snd L X X)
  have hi (r : S.obj.obj W) :
      a.ringUnderlying.hom.hom.app W (a.ringUnderlying.inv.hom.app W r) = r :=
    congrArg (fun g ↦ g.hom.app W r) a.ringUnderlying.inv_hom_id
  have ha := a.ringAdd (X ⊗ X) (fst X X) (snd X X) (addMap R) (fun _ _ ↦ rfl) W z
  rw [h₁, h₂, hi, hi] at ha
  dsimp only [id] at ha ⊢
  rw [← ha, transportSets_apply]
  have hb := b.ringAdd (X ⊗ X)
    (fst X X ≫ (sheafCompose J (forget CommRingCat.{u})).map f)
    (snd X X ≫ (sheafCompose J (forget CommRingCat.{u})).map f)
    (addMap R ≫ (sheafCompose J (forget CommRingCat.{u})).map f)
    (fun U z ↦ (f.hom.app U).hom.map_add z.1 z.2) W z
  dsimp only [id] at hb
  rw [hb, ← transportSets_apply a b f, ← transportSets_apply a b f,
    h₁, h₂, hi, hi]

private theorem transportSets_mul (W : Dᵒᵖ) (x y : S.obj.obj W) :
    @id (A.obj.obj W) ((transportSets a b f).hom.app W (x * y)) =
      @id (A.obj.obj W) ((transportSets a b f).hom.app W x) *
        @id (A.obj.obj W) ((transportSets a b f).hom.app W y) := by
  let X := sets R
  let p := inv (CartesianMonoidalCategory.prodComparison L X X)
  let z := p.hom.app W (a.ringUnderlying.inv.hom.app W x,
    a.ringUnderlying.inv.hom.app W y)
  have h₁ : (L.map (fst X X)).hom.app W z = a.ringUnderlying.inv.hom.app W x :=
    congrArg (fun g ↦ g.hom.app W
      (a.ringUnderlying.inv.hom.app W x, a.ringUnderlying.inv.hom.app W y))
      (inv_prodComparison_map_fst L X X)
  have h₂ : (L.map (snd X X)).hom.app W z = a.ringUnderlying.inv.hom.app W y :=
    congrArg (fun g ↦ g.hom.app W
      (a.ringUnderlying.inv.hom.app W x, a.ringUnderlying.inv.hom.app W y))
      (inv_prodComparison_map_snd L X X)
  have hi (r : S.obj.obj W) :
      a.ringUnderlying.hom.hom.app W (a.ringUnderlying.inv.hom.app W r) = r :=
    congrArg (fun g ↦ g.hom.app W r) a.ringUnderlying.inv_hom_id
  have ha := a.ringMul (X ⊗ X) (fst X X) (snd X X) (mulMap R) (fun _ _ ↦ rfl) W z
  rw [h₁, h₂, hi, hi] at ha
  dsimp only [id] at ha ⊢
  rw [← ha, transportSets_apply]
  have hb := b.ringMul (X ⊗ X)
    (fst X X ≫ (sheafCompose J (forget CommRingCat.{u})).map f)
    (snd X X ≫ (sheafCompose J (forget CommRingCat.{u})).map f)
    (mulMap R ≫ (sheafCompose J (forget CommRingCat.{u})).map f)
    (fun U z ↦ (f.hom.app U).hom.map_mul z.1 z.2) W z
  dsimp only [id] at hb
  rw [hb, ← transportSets_apply a b f, ← transportSets_apply a b f,
    h₁, h₂, hi, hi]

private theorem transportSets_one (W : Dᵒᵖ) :
    (transportSets a b f).hom.app W (1 : S.obj.obj W) = (1 : A.obj.obj W) := by
  let r : sets R ⟶ sets R :=
    ⟨{ app := fun U ↦ ↾(fun _ ↦ (1 : R.obj.obj U))
       naturality := by intro U V f; ext x; exact (map_one (R.obj.map f).hom).symm }⟩
  let z := a.ringUnderlying.inv.hom.app W (0 : S.obj.obj W)
  have ha := a.ringOne (sets R) r (fun _ _ ↦ rfl) W z
  dsimp only [id] at ha
  rw [← ha, transportSets_apply]
  exact b.ringOne (sets R) (r ≫ (sheafCompose J (forget CommRingCat.{u})).map f)
    (fun U _ ↦ map_one (f.hom.app U).hom) W z

private def transportHom : S ⟶ A :=
  ⟨{ app := fun W ↦ CommRingCat.ofHom
       { toFun := (transportSets a b f).hom.app W
         map_one' := transportSets_one a b f W
         map_mul' := transportSets_mul a b f W
         map_zero' := by
           have h := transportSets_add a b f W 0 0
           simp only [add_zero, id_eq] at h
           exact (add_left_cancel ((add_zero _).trans h)).symm
         map_add' := transportSets_add a b f W }
     naturality := by
       intro U V g
       ext x
       exact ConcreteCategory.congr_hom ((transportSets a b f).hom.naturality g) x }⟩

end LocalizationRings

namespace LocalizationRings

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
variable {J : GrothendieckTopology C} [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (R : Sheaf J CommRingCat.{u})
variable (t : (R.obj ⋙ forget CommRingCat.{u}).sections)

private theorem unit_isUnit (U : Cᵒᵖ) :
    IsUnit ((ringedLocalizationRingUnitOfUniverses R t).hom.app U (t.val U)) := by
  exact (IsLocalization.Away.algebraMap_isUnit (R := R.obj.obj U)
    (S := ringedSectionLocalizationCarrierOfUniverses R t U) (t.val U)).map
      ((toSheafify J (ringedLocalizationRingPresheafOfUniverses R t)).app U).hom

private theorem hom_ext {A : Sheaf J CommRingCat.{u}}
    (f g : ringedLocalizationRingOfUniverses R t ⟶ A)
    (h : ringedLocalizationRingUnitOfUniverses R t ≫ f =
      ringedLocalizationRingUnitOfUniverses R t ≫ g) : f = g := by
  apply ((sheafificationAdjunction J CommRingCat.{u}).homEquiv _ _).injective
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (R := R.obj.obj U)
    (S := ringedSectionLocalizationCarrierOfUniverses R t U)
    (Submonoid.powers (show R.obj.obj U from t.val U))
  ext r
  exact congrArg (fun k ↦ k.hom.app U r) h

private def lift {A : Sheaf J CommRingCat.{u}} (c : R ⟶ A)
    (hu : ∀ U, IsUnit (c.hom.app U (t.val U))) :
    ringedLocalizationRingOfUniverses R t ⟶ A := by
  let f : ringedLocalizationRingPresheafOfUniverses R t ⟶ A.obj :=
    { app := fun U ↦ CommRingCat.ofHom (IsLocalization.Away.lift (R := R.obj.obj U)
        (S := ringedSectionLocalizationCarrierOfUniverses R t U)
        (g := (c.hom.app U).hom) (t.val U) (hu U))
      naturality := by
        intro U V g
        apply CommRingCat.hom_ext
        apply IsLocalization.ringHom_ext (R := R.obj.obj U)
          (S := ringedSectionLocalizationCarrierOfUniverses R t U)
          (Submonoid.powers (show R.obj.obj U from t.val U))
        ext r
        change IsLocalization.Away.lift (R := R.obj.obj V)
            (S := ringedSectionLocalizationCarrierOfUniverses R t V)
            (g := (c.hom.app V).hom) (t.val V) (hu V)
            ((ringedSectionLocalizationMapOfUniverses R t g)
              (algebraMap _ (ringedSectionLocalizationCarrierOfUniverses R t U) r)) =
          A.obj.map g (IsLocalization.Away.lift (R := R.obj.obj U)
            (S := ringedSectionLocalizationCarrierOfUniverses R t U)
            (g := (c.hom.app U).hom) (t.val U) (hu U)
            (algebraMap _ (ringedSectionLocalizationCarrierOfUniverses R t U) r))
        simp only [ringedSectionLocalizationMapOfUniverses, IsLocalization.Away.lift_eq,
          RingHom.comp_apply]
        exact congrArg (fun k ↦ k r) (c.hom.naturality g) }
  exact ((sheafificationAdjunction J CommRingCat.{u}).homEquiv _ _).symm f

private theorem lift_unit {A : Sheaf J CommRingCat.{u}} (c : R ⟶ A)
    (hu : ∀ U, IsUnit (c.hom.app U (t.val U))) :
    ringedLocalizationRingUnitOfUniverses R t ≫ lift R t c hu = c := by
  apply Sheaf.hom_ext
  change ringedLocalizationRingPresheafUnitOfUniverses R t ≫
    (sheafificationAdjunction J CommRingCat.{u}).homEquiv _ _ (lift R t c hu) = _
  unfold lift
  rw [Equiv.apply_symm_apply]
  ext U r
  exact IsLocalization.Away.lift_eq (R := R.obj.obj U)
    (S := ringedSectionLocalizationCarrierOfUniverses R t U)
    (g := (c.hom.app U).hom) (t.val U) (hu U) r

end LocalizationRings

namespace LocalizationRings

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
variable {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (R : Sheaf J CommRingCat.{u})
variable (t : (R.obj ⋙ forget CommRingCat.{u}).sections)

private abbrev sequence :=
  Functor.ofSequence (X := fun _ : ℕ ↦
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (fun _ ↦ LocalizationSequence.regularScalar R t) ⋙ localizationModuleSets R

private def scalar : sets R ⟶ sets R :=
  (localizationModuleSets R).map (LocalizationSequence.regularScalar R t)

private def moduleIso := Classical.choose (ringedLocalizationRing_moduleComparisonOfUniverses R t)

private def cocone : Cocone (sequence R t) := by
  let c := (localizationModuleSets R).mapCocone (LocalizationSequence.localizationSheafCocone R t)
  let e := (localizationModuleSets R).mapIso (moduleIso R t).symm
  exact c.extend e.hom

private def isColimit : IsColimit (cocone R t) := by
  have := localizationSets_preserves_sequence R
  exact IsColimit.extendIso _ (isColimitOfPreserves (localizationModuleSets R)
    (LocalizationSequence.localizationSheafCoconeIsColimit R t))

private theorem cocone_zero : (cocone R t).ι.app 0 =
    (sheafCompose J (forget CommRingCat.{u})).map (ringedLocalizationRingUnitOfUniverses R t) := by
  apply (cancel_mono ((localizationModuleSets R).map (moduleIso R t).hom)).1
  change ((localizationModuleSets R).map
      (LocalizationSequence.localizationSheafMap R t 0) ≫
        (localizationModuleSets R).map (moduleIso R t).inv) ≫
          (localizationModuleSets R).map (moduleIso R t).hom = _
  rw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id,
    Category.comp_id, LocalizationSequence.localizationSheafMap_zero]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro r
  change R.obj.obj U at r
  have h := Classical.choose_spec (ringedLocalizationRing_moduleComparisonOfUniverses R t)
    U (algebraMap (R.obj.obj U) (ringedSectionLocalizationCarrierOfUniverses R t U) r)
  change _ = (moduleIso R t).hom.val.app U
    ((toSheafify J (ringedLocalizationRingPresheafOfUniverses R t)).app U
      (algebraMap (R.obj.obj U) (ringedSectionLocalizationCarrierOfUniverses R t U) r))
  change _ =
    (Classical.choose (ringedLocalizationRing_moduleComparisonOfUniverses R t)).hom.val.app U
    ((toSheafify J (ringedLocalizationRingPresheafOfUniverses R t)).app U
      (algebraMap (R.obj.obj U) (ringedSectionLocalizationCarrierOfUniverses R t U) r))
  rw [h]
  change ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
      (ringedSectionLocalizationPresheafOfUniverses R t)).app U
    (r • (1 : ringedSectionLocalizationCarrierOfUniverses R t U)) = _
  rw [Algebra.smul_def, mul_one]

private theorem cocone_mul (n : ℕ) (U : Cᵒᵖ) (r : R.obj.obj U) :
    ((cocone R t).ι.app n).hom.app U (r * LocalizationSequence.sectionValue R t U) =
      (show (ringedLocalizationRingOfUniverses R t).obj.obj U from
        ((cocone R t).ι.app n).hom.app U r) *
        (ringedLocalizationRingUnitOfUniverses R t).hom.app U (t.val U) := by
  change (moduleIso R t).inv.val.app U
      ((LocalizationSequence.localizationSheafMap R t n).val.app U
        (r * LocalizationSequence.sectionValue R t U)) = _
  rw [mul_comm r]
  calc
    _ = LocalizationSequence.sectionValue R t U •
        (moduleIso R t).inv.val.app U
          ((LocalizationSequence.localizationSheafMap R t n).val.app U r) := by
      exact (congrArg (fun x ↦ (moduleIso R t).inv.val.app U x)
        (((LocalizationSequence.localizationSheafMap R t n).val.app U).hom.map_smul
          (LocalizationSequence.sectionValue R t U) r)).trans
            (((moduleIso R t).inv.val.app U).hom.map_smul _ _)
    _ = _ := by
      change @Mul.mul ((ringedLocalizationRingOfUniverses R t).obj.obj U) _
        ((ringedLocalizationRingUnitOfUniverses R t).hom.app U (t.val U))
        ((moduleIso R t).inv.val.app U
          ((LocalizationSequence.localizationSheafMap R t n).val.app U r)) =
        @Mul.mul ((ringedLocalizationRingOfUniverses R t).obj.obj U) _
          ((moduleIso R t).inv.val.app U
            ((LocalizationSequence.localizationSheafMap R t n).val.app U r))
          ((ringedLocalizationRingUnitOfUniverses R t).hom.app U (t.val U))
      exact mul_comm _ _

end LocalizationRings

namespace LocalizationRings

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify K CommRingCat.{u}]
variable [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)} [PreservesFiniteLimits L]
variable {V : Sheaf K (Type u) ⥤ Sheaf J (Type u)} (adj : L ⊣ V)
variable {R : Sheaf J CommRingCat.{u}} {S A : Sheaf K CommRingCat.{u}}
variable (a : SheafOfModules.AlgebraicInverseImage L R S)
variable (t : (R.obj ⋙ forget CommRingCat.{u}).sections)
variable (s : (S.obj ⋙ forget CommRingCat.{u}).sections) (hs : IsInverseImageSection a t s)
variable (b : SheafOfModules.AlgebraicInverseImage L (ringedLocalizationRingOfUniverses R t) A)

private def sectionMap {E : Type uF} [Category.{vF} E] {H : GrothendieckTopology E}
    {B Q : Sheaf H CommRingCat.{u}} (c : B ⟶ Q)
    (x : (B.obj ⋙ forget CommRingCat.{u}).sections) :
    (Q.obj ⋙ forget CommRingCat.{u}).sections :=
  ⟨fun U ↦ c.hom.app U (x.val U), by
    intro U V g
    have h := congrArg (fun k ↦ k (x.val U)) (c.hom.naturality g)
    exact h.symm.trans (congrArg (c.hom.app V) (x.property g))⟩

include hs in
private theorem image_unit_isUnit (W : Dᵒᵖ) :
    IsUnit ((transportHom a b (ringedLocalizationRingUnitOfUniverses R t)).hom.app W
      (s.val W)) := by
  let Q := ringedLocalizationRingOfUniverses R t
  let j := ringedLocalizationRingUnitOfUniverses R t
  let qsec := sectionMap j t
  have hu (U : Cᵒᵖ) : IsUnit (LocalizationSequence.sectionValue Q qsec U) := unit_isUnit R t U
  choose v hv using fun U ↦ (hu U).exists_right_inv
  let vsec : (Q.obj ⋙ forget CommRingCat.{u}).sections :=
    ⟨v, by
      intro U V g
      apply (hu V).mul_left_cancel
      have hq := qsec.property g
      change Q.obj.map g (LocalizationSequence.sectionValue Q qsec U) =
        LocalizationSequence.sectionValue Q qsec V at hq
      calc
        LocalizationSequence.sectionValue Q qsec V * Q.obj.map g (v U) =
            Q.obj.map g (LocalizationSequence.sectionValue Q qsec U * v U) := by
          rw [(Q.obj.map g).hom.map_mul, hq]
        _ = 1 := by rw [hv, map_one]
        _ = LocalizationSequence.sectionValue Q qsec V * v V := (hv V).symm⟩
  let p := constMap Q qsec (sets R)
  let q := constMap Q vsec (sets R)
  let one : sets R ⟶ sets Q :=
    ⟨{ app := fun U ↦ ↾(fun _ ↦ (1 : Q.obj.obj U))
       naturality := by intro U V g; ext x; exact (map_one (Q.obj.map g).hom).symm }⟩
  let z := a.ringUnderlying.inv.hom.app W (0 : S.obj.obj W)
  have hp := b.ringMul (sets R) p q one (fun U _ ↦ (hv U).symm) W z
  have h1 := b.ringOne (sets R) one (fun _ _ ↦ rfl) W z
  have hc := transportSets_apply a b j (sets R) (constMap R t (sets R)) W z
  rw [hs (sets R) (constMap R t (sets R)) (fun _ _ ↦ rfl) W z] at hc
  refine IsUnit.of_mul_eq_one (b.ringUnderlying.hom.hom.app W ((L.map q).hom.app W z)) ?_
  change @Mul.mul (A.obj.obj W) _
    ((transportSets a b j).hom.app W (s.val W))
    (b.ringUnderlying.hom.hom.app W ((L.map q).hom.app W z)) = 1
  rw [hc]
  change @Mul.mul (A.obj.obj W) _
    (b.ringUnderlying.hom.hom.app W ((L.map p).hom.app W z))
    (b.ringUnderlying.hom.hom.app W ((L.map q).hom.app W z)) = 1
  exact hp.symm.trans h1

include hs in
private theorem scalar_image :
    L.map (scalar R t) ≫ a.ringUnderlying.hom = a.ringUnderlying.hom ≫ scalar S s := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply ConcreteCategory.hom_ext
  intro x
  have h := a.ringMul (sets R) (𝟙 _) (constMap R t (sets R)) (scalar R t)
    (fun U r ↦ LocalizationSequence.scalar_apply R t U r) W x
  dsimp only [id] at h
  rw [hs (sets R) (constMap R t (sets R)) (fun _ _ ↦ rfl) W x] at h
  rw [Functor.map_id] at h
  change a.ringUnderlying.hom.hom.app W ((L.map (scalar R t)).hom.app W x) =
    @Mul.mul (S.obj.obj W) _ (a.ringUnderlying.hom.hom.app W x)
      (LocalizationSequence.sectionValue S s W) at h
  change a.ringUnderlying.hom.hom.app W ((L.map (scalar R t)).hom.app W x) =
    @Mul.mul (S.obj.obj W) _ (a.ringUnderlying.hom.hom.app W x)
      (LocalizationSequence.sectionValue S s W)
  exact h

private def imageDiagramIso : sequence S s ≅ sequence R t ⋙ L := by
  let τ : sequence R t ⋙ L ⟶ sequence S s :=
    NatTrans.ofSequence (fun _ ↦ a.ringUnderlying.hom) (by
      intro n
      simpa only [sequence, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ, scalar]
        using scalar_image a t s hs)
  exact (NatIso.ofComponents (fun _ ↦ a.ringUnderlying) (fun f ↦ τ.naturality f)).symm

private def imageCocone : Cocone (sequence S s) where
  pt := sets A
  ι :=
    { app := fun n ↦ a.ringUnderlying.inv ≫ L.map ((cocone R t).ι.app n) ≫
        b.ringUnderlying.hom
      naturality := by
        intro n m f
        let c := ((Cocone.precompose (imageDiagramIso a t s hs).hom).obj
          (L.mapCocone (cocone R t))).extend b.ringUnderlying.hom
        exact (c.w f).trans (Category.comp_id _).symm }

private def imageIsColimit : IsColimit (imageCocone a t s hs b) := by
  have : PreservesColimitsOfShape ℕ L := adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  exact IsColimit.extendIso b.ringUnderlying.hom
    ((IsColimit.precomposeHomEquiv (imageDiagramIso a t s hs)
      (L.mapCocone (cocone R t))).symm
        (isColimitOfPreserves L (isColimit R t)))

private theorem imageCocone_zero : (imageCocone a t s hs b).ι.app 0 =
    (sheafCompose K (forget CommRingCat.{u})).map
      (transportHom a b (ringedLocalizationRingUnitOfUniverses R t)) := by
  change (a.ringUnderlying.inv ≫ L.map ((cocone R t).ι.app 0)) ≫
    b.ringUnderlying.hom = _
  rw [cocone_zero]
  rfl

private theorem imageCocone_mul (n : ℕ) (W : Dᵒᵖ) (y : S.obj.obj W) :
    ((imageCocone a t s hs b).ι.app n).hom.app W (y * LocalizationSequence.sectionValue S s W) =
      (show A.obj.obj W from ((imageCocone a t s hs b).ι.app n).hom.app W y) *
        (transportHom a b (ringedLocalizationRingUnitOfUniverses R t)).hom.app W (s.val W) := by
  let Q := ringedLocalizationRingOfUniverses R t
  let j := ringedLocalizationRingUnitOfUniverses R t
  let p := constMap R t (sets R) ≫ (sheafCompose J (forget CommRingCat.{u})).map j
  let q := (cocone R t).ι.app n
  let x := a.ringUnderlying.inv.hom.app W y
  have hi : a.ringUnderlying.hom.hom.app W x = y :=
    congrArg (fun g ↦ g.hom.app W y) a.ringUnderlying.inv_hom_id
  have h := b.ringMul (sets R) q p (scalar R t ≫ q)
    (fun U r ↦ cocone_mul R t n U r) W x
  have hp := transportSets_apply a b j (sets R) (constMap R t (sets R)) W x
  rw [hs (sets R) (constMap R t (sets R)) (fun _ _ ↦ rfl) W x] at hp
  have hm := congrArg (fun g ↦ g.hom.app W x) (scalar_image a t s hs)
  change a.ringUnderlying.hom.hom.app W ((L.map (scalar R t)).hom.app W x) =
    @Mul.mul (S.obj.obj W) _ (a.ringUnderlying.hom.hom.app W x)
      (LocalizationSequence.sectionValue S s W) at hm
  rw [hi] at hm
  have hm' : (L.map (scalar R t)).hom.app W x =
      a.ringUnderlying.inv.hom.app W (y * LocalizationSequence.sectionValue S s W) := by
    have hh := congrArg (fun z ↦ a.ringUnderlying.inv.hom.app W z) hm
    have hi' := congrArg (fun g ↦ g.hom.app W ((L.map (scalar R t)).hom.app W x))
      a.ringUnderlying.hom_inv_id
    exact hi'.symm.trans hh
  rw [Functor.map_comp] at h
  change b.ringUnderlying.hom.hom.app W
      ((L.map q).hom.app W ((L.map (scalar R t)).hom.app W x)) = _ at h
  rw [hm', ← hp] at h
  exact h

end LocalizationRings

/-- The ring comparison, as a ring-structure-preserving identification of underlying
inverse images, is the unique one preserving the localization unit.
Source: Stacks, Tags 00YV and 00CP
(blueprint: lem-weil-pbc-localization-inverse-image-coherence).
Proof: maps from the localization of R are precisely maps from R inverting t, first
objectwise and then by sheafification. The ring-object adjunction preserves the equations
expressing an inverse. Thus the inverse image of the localization has the same initial
property as the localization of the inverse-image ring. The two universal maps are inverse;
their restrictions to R give the displayed equation and uniqueness. This works for the
zero ring and nilpotent t as well. -/
theorem existsUnique_localizationInverseImageRing
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {K : GrothendieckTopology D}
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify K CommRingCat.{u}]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (_adj : L ⊣ V)
    [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (a : SheafOfModules.AlgebraicInverseImage L R S)
    (t : (R.obj ⋙ forget CommRingCat.{u}).sections)
    (s : (S.obj ⋙ forget CommRingCat.{u}).sections) (_hs : IsInverseImageSection a t s)
    (A : Sheaf K CommRingCat.{u})
    (b : SheafOfModules.AlgebraicInverseImage L (ringedLocalizationRingOfUniverses R t) A) :
    ∃! α : A ≅ ringedLocalizationRingOfUniverses S s,
      L.map ((sheafCompose J (forget CommRingCat.{u})).map
          (ringedLocalizationRingUnitOfUniverses R t)) ≫
          b.ringUnderlying.hom ≫ (sheafCompose K (forget CommRingCat.{u})).map α.hom =
        a.ringUnderlying.hom ≫
          (sheafCompose K (forget CommRingCat.{u})).map
            (ringedLocalizationRingUnitOfUniverses S s) := by
  set_option backward.isDefEq.respectTransparency.types false in
    let c := LocalizationRings.transportHom a b (ringedLocalizationRingUnitOfUniverses R t)
    have hu : ∀ W, IsUnit (c.hom.app W (s.val W)) :=
      LocalizationRings.image_unit_isUnit a t s _hs b
    let f := LocalizationRings.lift S s c hu
    have hf : ringedLocalizationRingUnitOfUniverses S s ≫ f = c :=
      LocalizationRings.lift_unit S s c hu
    let d := LocalizationRings.cocone S s
    let e := LocalizationRings.imageCocone a t s _hs b
    have hd := LocalizationRings.isColimit S s
    have he := LocalizationRings.imageIsColimit _adj a t s _hs b
    let F := sheafCompose K (forget CommRingCat.{u})
    have hstep (n : ℕ) (W : Dᵒᵖ) (r : S.obj.obj W) :
        (d.ι.app (n + 1)).hom.app W (r * LocalizationSequence.sectionValue S s W) =
          (d.ι.app n).hom.app W r := by
      have h := congrArg (fun g ↦ g.hom.app W r) (d.w (homOfLE (Nat.le_succ n)))
      simp only [LocalizationRings.sequence, Functor.comp_map,
        Functor.ofSequence_map_homOfLE_succ] at h
      change (d.ι.app (n + 1)).hom.app W
        ((LocalizationSequence.regularScalar S s).val.app W r) =
          (d.ι.app n).hom.app W r at h
      rw [LocalizationSequence.scalar_apply] at h
      exact h
    have hstep' (n : ℕ) (W : Dᵒᵖ) (r : S.obj.obj W) :
        (e.ι.app (n + 1)).hom.app W (r * LocalizationSequence.sectionValue S s W) =
          (e.ι.app n).hom.app W r := by
      have h := congrArg (fun g ↦ g.hom.app W r) (e.w (homOfLE (Nat.le_succ n)))
      simp only [LocalizationRings.sequence, Functor.comp_map,
        Functor.ofSequence_map_homOfLE_succ] at h
      change (e.ι.app (n + 1)).hom.app W
        ((LocalizationSequence.regularScalar S s).val.app W r) =
          (e.ι.app n).hom.app W r at h
      rw [LocalizationSequence.scalar_apply] at h
      exact h
    have hall (n : ℕ) : d.ι.app n ≫ F.map f = e.ι.app n := by
      induction n with
      | zero =>
          change (LocalizationRings.cocone S s).ι.app 0 ≫ F.map f =
            (LocalizationRings.imageCocone a t s _hs b).ι.app 0
          rw [LocalizationRings.cocone_zero, LocalizationRings.imageCocone_zero,
            ← F.map_comp, hf]
      | succ n ih =>
          apply Sheaf.hom_ext
          apply NatTrans.ext
          funext W
          apply ConcreteCategory.hom_ext
          intro r
          change S.obj.obj W at r
          apply (hu W).mul_right_cancel
          change f.hom.app W ((d.ι.app (n + 1)).hom.app W r) * c.hom.app W (s.val W) = _
          have hfW := congrArg (fun g ↦ g.hom.app W (s.val W)) hf
          change f.hom.app W
            ((ringedLocalizationRingUnitOfUniverses S s).hom.app W (s.val W)) =
              c.hom.app W (s.val W) at hfW
          have ihn := congrArg (fun g ↦ g.hom.app W r) ih
          change f.hom.app W ((d.ι.app n).hom.app W r) =
            (e.ι.app n).hom.app W r at ihn
          calc
            _ = f.hom.app W ((show (ringedLocalizationRingOfUniverses S s).obj.obj W from
                  (d.ι.app (n + 1)).hom.app W r) *
                (ringedLocalizationRingUnitOfUniverses S s).hom.app W (s.val W)) := by
              rw [(f.hom.app W).hom.map_mul, hfW]
            _ = f.hom.app W ((d.ι.app (n + 1)).hom.app W
                (r * LocalizationSequence.sectionValue S s W)) := by
              rw [LocalizationRings.cocone_mul]
            _ = f.hom.app W ((d.ι.app n).hom.app W r) := by rw [hstep]
            _ = (e.ι.app n).hom.app W r := ihn
            _ = (e.ι.app (n + 1)).hom.app W
                (r * LocalizationSequence.sectionValue S s W) := (hstep' n W r).symm
            _ = _ := LocalizationRings.imageCocone_mul a t s _hs b (n + 1) W r
    have heq : F.map f = (hd.coconePointUniqueUpToIso he).hom := by
      apply hd.hom_ext
      intro n
      rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
      exact hall n
    have : IsIso (F.map f) := by rw [heq]; infer_instance
    have : IsIso f := isIso_of_reflects_iso f F
    let α := (asIso f).symm
    have hα : c ≫ α.hom = ringedLocalizationRingUnitOfUniverses S s := by
      rw [← hf, Category.assoc]
      change _ ≫ (f ≫ inv f) = _
      rw [IsIso.hom_inv_id, Category.comp_id]
    have hc : a.ringUnderlying.hom ≫ F.map c =
        L.map ((sheafCompose J (forget CommRingCat.{u})).map
          (ringedLocalizationRingUnitOfUniverses R t)) ≫ b.ringUnderlying.hom := by
      change a.ringUnderlying.hom ≫
        (a.ringUnderlying.inv ≫ _ ≫ b.ringUnderlying.hom) = _
      rw [Iso.hom_inv_id_assoc]
    refine ⟨α, ?_, ?_⟩
    · change L.map ((sheafCompose J (forget CommRingCat.{u})).map
        (ringedLocalizationRingUnitOfUniverses R t)) ≫ b.ringUnderlying.hom ≫ F.map α.hom =
          a.ringUnderlying.hom ≫ F.map (ringedLocalizationRingUnitOfUniverses S s)
      rw [← Category.assoc, ← hc, Category.assoc, ← F.map_comp, hα]
    · intro γ hγ
      change L.map ((sheafCompose J (forget CommRingCat.{u})).map
        (ringedLocalizationRingUnitOfUniverses R t)) ≫ b.ringUnderlying.hom ≫ F.map γ.hom =
          a.ringUnderlying.hom ≫ F.map (ringedLocalizationRingUnitOfUniverses S s) at hγ
      have hg : c ≫ γ.hom = ringedLocalizationRingUnitOfUniverses S s := by
        apply F.map_injective
        apply (cancel_epi a.ringUnderlying.hom).1
        simpa only [Functor.map_comp, ← Category.assoc, hc] using hγ
      apply Iso.ext
      apply (cancel_epi f).1
      change f ≫ γ.hom = f ≫ inv f
      rw [IsIso.hom_inv_id]
      apply LocalizationRings.hom_ext S s
      rw [← Category.assoc, hf, hg, Category.comp_id]

/-- The comparison transports every generalized fraction representative. The equation
`tⁿ q = η(m)` characterizes `q = m/tⁿ` uniquely in a localized module, so this formula
also applies to representatives on sheafified representables, without enough points.
Source: Stacks, Tags 03D2 and 00DK
(blueprint: lem-weil-pbc-localization-inverse-image-coherence).
Proof: apply inverse image to the displayed scalar-action equation. Transport the action
using the algebraic inverse-image graph equations and use the unit normalization of β.
The resulting equation is exactly the target fraction relation, and invertibility of s
makes its solution unique. This keeps the denominator exponent, including exponent zero. -/
theorem localizationInverseImage_fraction
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {K : GrothendieckTopology D}
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify K CommRingCat.{u}]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (_adj : L ⊣ V)
    [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (a : SheafOfModules.AlgebraicInverseImage L R S)
    (t : (R.obj ⋙ forget CommRingCat.{u}).sections)
    (s : (S.obj ⋙ forget CommRingCat.{u}).sections) (_hs : IsInverseImageSection a t s)
    (β : scalarLocalization R t ⋙ a.modules ≅ a.modules ⋙ scalarLocalization S s)
    (_hβ : Functor.whiskerRight (scalarLocalizationUnit R t) a.modules ≫ β.hom =
      Functor.whiskerLeft a.modules (scalarLocalizationUnit S s))
    (M : inverseLocalizationModules R) (T : Sheaf J (Type u))
    (m : T ⟶ (localizationModuleSets R).obj M)
    (q : T ⟶ (localizationModuleSets R).obj ((scalarLocalization R t).obj M))
    (n : ℕ)
    (_hq : ∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (t.val U : R.obj.obj U) ^ n •
        @id (((scalarLocalization R t).obj M).val.obj U) (q.hom.app U x) =
        ((scalarLocalizationUnit R t).app M).val.app U (m.hom.app U x)) :
    ∀ (W : Dᵒᵖ) (x : (L.obj T).obj.obj W),
      (s.val W) ^ n • ((β.hom.app M).val.app W
        (((a.moduleUnderlying.inv.app ((scalarLocalization R t).obj M)).hom.app W)
          ((L.map q).hom.app W x))) =
      ((scalarLocalizationUnit S s).app (a.modules.obj M)).val.app W
        (((a.moduleUnderlying.inv.app M).hom.app W) ((L.map m).hom.app W x)) := by
  let ρ : ℕ → (T ⟶ (sheafCompose J (forget CommRingCat.{u})).obj R) := fun k ↦
    ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ (t.val U : R.obj.obj U) ^ k)
       naturality := by
         intro U V f
         ext x
         change (t.val V : R.obj.obj V) ^ k = R.obj.map f ((t.val U) ^ k)
         rw [map_pow]
         exact congrArg (fun z : R.obj.obj V ↦ z ^ k) (t.property f).symm }⟩
  have hρ : ∀ k (W : Dᵒᵖ) (x : (L.obj T).obj.obj W),
      a.ringUnderlying.hom.hom.app W ((L.map (ρ k)).hom.app W x) =
        (s.val W : S.obj.obj W) ^ k := by
    intro k
    induction k with
    | zero =>
        intro W x
        simpa only [id_eq, pow_zero] using
          a.ringOne T (ρ 0) (by intro U x; exact pow_zero _) W x 
    | succ k hk =>
        intro W x
        have hp := a.ringMul T (ρ k) (ρ 1) (ρ (k + 1))
          (by
            intro U x
            change (t.val U : R.obj.obj U) ^ (k + 1) =
              (t.val U : R.obj.obj U) ^ k * (t.val U : R.obj.obj U) ^ 1
            rw [pow_succ, pow_one]) W x
        dsimp only [id_eq] at hp
        rw [hp, hk, _hs T (ρ 1) (by intro U x; exact pow_one (t.val U : R.obj.obj U)) W x, pow_succ]
  let z : T ⟶ (localizationModuleSets R).obj ((scalarLocalization R t).obj M) :=
    m ≫ (localizationModuleSets R).map ((scalarLocalizationUnit R t).app M)
  have hz : ∀ U (x : T.obj.obj U),
      @id (((scalarLocalization R t).obj M).val.obj U) (z.hom.app U x) =
        @id (R.obj.obj U) ((ρ n).hom.app U x) •
          @id (((scalarLocalization R t).obj M).val.obj U) (q.hom.app U x) := by
    intro U x
    exact (_hq U x).symm
  have ht := a.moduleSMul ((scalarLocalization R t).obj M) T (ρ n) q z hz
  intro W x
  have he := ht W x
  dsimp only [id_eq] at he
  rw [hρ] at he
  have hβ := congr_app _hβ M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hβ
  have hnat := a.moduleUnderlying.inv.naturality ((scalarLocalizationUnit R t).app M)
  have hnat' := congrArg (fun f ↦ f.hom.app W ((L.map m).hom.app W x)) hnat
  change (a.moduleUnderlying.inv.app ((scalarLocalization R t).obj M)).hom.app W
      ((L.map ((localizationModuleSets R).map ((scalarLocalizationUnit R t).app M))).hom.app
        W ((L.map m).hom.app W x)) =
    (a.modules.map ((scalarLocalizationUnit R t).app M)).val.app W
      ((a.moduleUnderlying.inv.app M).hom.app W ((L.map m).hom.app W x)) at hnat'
  have hz' : (L.map z).hom.app W x =
      (L.map ((localizationModuleSets R).map ((scalarLocalizationUnit R t).app M))).hom.app
        W ((L.map m).hom.app W x) := by
    rw [show z = m ≫ (localizationModuleSets R).map
      ((scalarLocalizationUnit R t).app M) from rfl, L.map_comp]
    rfl
  rw [← (β.hom.app M).val.app W |>.hom.map_smul, ← he, hz', hnat']
  exact congrArg (fun f ↦ f.val.app W
    ((a.moduleUnderlying.inv.app M).hom.app W ((L.map m).hom.app W x))) hβ

/-- The composition equation, with the canonical module inverse-image composition
identification inserted on both sides. It holds for any presentation of that canonical
identification, since it is natural at the localization unit.
Source: Stacks, Tags 03CB, 03CC and the uniqueness argument of Tags 03D2 and 00CP
(blueprint: lem-weil-pbc-localization-inverse-image-coherence).
Proof: precompose both transformations with the image of the localization unit.
Use first the unit equation for β, then the one for γ, and naturality of κ at the unit.
Both composites become the target localization unit. The transported localization
initial property gives equality on each module, hence equality of transformations. -/
theorem localizationInverseImage_comp
    {C : Type uC} {D : Type uD} {E : Type uF}
    [Category.{vC} C] [Category.{vD} D] [Category.{vF} E]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D] [EssentiallySmall.{u} E]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {K : GrothendieckTopology D}
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify K CommRingCat.{u}]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {H : GrothendieckTopology E}
    [HasSheafify H AddCommGrpCat.{u}] [H.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify H CommRingCat.{u}]
    [H.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (_adj : L ⊣ V)
    (L' : Sheaf K (Type u) ⥤ Sheaf H (Type u))
    (V' : Sheaf H (Type u) ⥤ Sheaf K (Type u)) (_adj' : L' ⊣ V')
    [PreservesFiniteLimits L] [PreservesFiniteLimits L']
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (A : Sheaf H CommRingCat.{u})
    (a : SheafOfModules.AlgebraicInverseImage L R S)
    (b : SheafOfModules.AlgebraicInverseImage L' S A)
    (c : SheafOfModules.AlgebraicInverseImage (L ⋙ L') R A)
    (κ : c.modules ≅ a.modules ⋙ b.modules)
    (t : (R.obj ⋙ forget CommRingCat.{u}).sections)
    (s : (S.obj ⋙ forget CommRingCat.{u}).sections)
    (r : (A.obj ⋙ forget CommRingCat.{u}).sections)
    (_hs : IsInverseImageSection a t s) (_hr : IsInverseImageSection b s r)
    (_hc : IsInverseImageSection c t r)
    (β : scalarLocalization R t ⋙ a.modules ≅ a.modules ⋙ scalarLocalization S s)
    (γ : scalarLocalization S s ⋙ b.modules ≅ b.modules ⋙ scalarLocalization A r)
    (δ : scalarLocalization R t ⋙ c.modules ≅ c.modules ⋙ scalarLocalization A r)
    (_hβ : Functor.whiskerRight (scalarLocalizationUnit R t) a.modules ≫ β.hom =
      Functor.whiskerLeft a.modules (scalarLocalizationUnit S s))
    (_hγ : Functor.whiskerRight (scalarLocalizationUnit S s) b.modules ≫ γ.hom =
      Functor.whiskerLeft b.modules (scalarLocalizationUnit A r))
    (_hδ : Functor.whiskerRight (scalarLocalizationUnit R t) c.modules ≫ δ.hom =
      Functor.whiskerLeft c.modules (scalarLocalizationUnit A r)) :
    δ.hom ≫ Functor.whiskerRight κ.hom (scalarLocalization A r) =
      Functor.whiskerLeft (scalarLocalization R t) κ.hom ≫
        Functor.whiskerRight β.hom b.modules ≫ Functor.whiskerLeft a.modules γ.hom := by
  let ζ : scalarLocalization R t ⋙ c.modules ≅ c.modules ⋙ scalarLocalization A r :=
    Functor.isoWhiskerLeft (scalarLocalization R t) κ ≪≫
      Functor.isoWhiskerRight β b.modules ≪≫ Functor.isoWhiskerLeft a.modules γ ≪≫
        (Functor.isoWhiskerRight κ (scalarLocalization A r)).symm
  have hζ : Functor.whiskerRight (scalarLocalizationUnit R t) c.modules ≫ ζ.hom =
      Functor.whiskerLeft c.modules (scalarLocalizationUnit A r) := by
    apply NatTrans.ext
    funext M
    have hβ := congr_app _hβ M
    have hγ := congr_app _hγ (a.modules.obj M)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app] at hβ hγ
    dsimp [ζ]
    rw [← Category.assoc, κ.hom.naturality, Category.assoc]
    simp only [Functor.comp_map]
    rw [← b.modules.map_comp_assoc, hβ, reassoc_of% hγ]
    rw [← (scalarLocalizationUnit A r).naturality]
    simp
  have he : δ = ζ :=
    (existsUnique_localizationInverseImage (L ⋙ L') (V' ⋙ V) (_adj.comp _adj')
      R A c t r _hc).unique _hδ hζ
  rw [he]
  dsimp [ζ]
  apply NatTrans.ext
  funext M
  simp [← Functor.map_comp]

/-- The identity inverse-image comparison is the identity under its canonical
identification. The equation is an equality of natural transformations.
Source: Stacks, Tags 03D2 and 00CP, unit-preserving uniqueness
(blueprint: lem-weil-pbc-localization-inverse-image-coherence).
Proof: the identity and β both extend the same localization unit. Naturality of κ
inserts the identity inverse-image identifications. Uniqueness gives the equation. -/
theorem localizationInverseImage_id
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u})
    (a : SheafOfModules.AlgebraicInverseImage (𝟭 (Sheaf J (Type u))) R R)
    (κ : a.modules ≅ 𝟭 (inverseLocalizationModules R))
    (t : (R.obj ⋙ forget CommRingCat.{u}).sections)
    (_ht : IsInverseImageSection a t t)
    (β : scalarLocalization R t ⋙ a.modules ≅ a.modules ⋙ scalarLocalization R t)
    (_hβ : Functor.whiskerRight (scalarLocalizationUnit R t) a.modules ≫ β.hom =
      Functor.whiskerLeft a.modules (scalarLocalizationUnit R t)) :
    β.hom ≫ Functor.whiskerRight κ.hom (scalarLocalization R t) =
      Functor.whiskerLeft (scalarLocalization R t) κ.hom := by
  let ζ : scalarLocalization R t ⋙ a.modules ≅ a.modules ⋙ scalarLocalization R t :=
    Functor.isoWhiskerLeft (scalarLocalization R t) κ ≪≫
      (Functor.isoWhiskerRight κ (scalarLocalization R t)).symm
  have hζ : Functor.whiskerRight (scalarLocalizationUnit R t) a.modules ≫ ζ.hom =
      Functor.whiskerLeft a.modules (scalarLocalizationUnit R t) := by
    apply NatTrans.ext
    funext M
    dsimp [ζ]
    rw [← Category.assoc, κ.hom.naturality]
    simp only [Functor.id_map]
    rw [Category.assoc, ← (scalarLocalizationUnit R t).naturality]
    simp
  have he : β = ζ :=
    (existsUnique_localizationInverseImage (𝟭 _) (𝟭 _) Adjunction.id
      R R a t t _ht).unique _hβ hζ
  rw [he]
  dsimp [ζ]
  apply NatTrans.ext
  funext M
  simp [← Functor.map_comp]

/-- Descent of the module comparison through ordinary unbounded derived localization.
The two outer isomorphisms are the canonical termwise composition comparisons.
Source: Stacks, Tag 015F and categorical localization of natural transformations
(blueprint: lem-weil-pbc-localization-inverse-image-coherence). -/
def localizationComparisonDerived
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (P : A ⥤ A) (Q : B ⥤ B) (I : A ⥤ B)
    [P.Additive] [Q.Additive] [I.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (β : P ⋙ I ≅ I ⋙ Q) :
    P.mapDerivedCategory ⋙ I.mapDerivedCategory ≅
      I.mapDerivedCategory ⋙ Q.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso P I).symm ≪≫
    Functor.mapDerivedCategoryNatIso β ≪≫ Functor.mapDerivedCategoryCompIso I Q

/-- Derived comparisons obey composition as equations of natural transformations, with
both the inverse-image and termwise-derived composition isomorphisms inserted.
Source: Stacks, Tag 015F and categorical localization of natural transformations
(blueprint: lem-weil-pbc-localization-inverse-image-coherence).
Proof: the module composition equation holds degreewise on every unbounded complex.
Descent preserves whiskering and vertical composition. Precomposition with the derived
localization is faithful on natural transformations, so the descended equation holds.
The canonical derived composition comparisons insert exactly the factors shown below. -/
theorem localizationComparisonDerived_comp
    {A : Type uA} {B : Type uB} {C : Type uE}
    [Category.{vA} A] [Category.{vB} B] [Category.{vE} C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wE} C]
    (P : A ⥤ A) (Q : B ⥤ B) (T : C ⥤ C) (I : A ⥤ B) (G : B ⥤ C)
    [P.Additive] [Q.Additive] [T.Additive] [I.Additive] [G.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (β : P ⋙ I ≅ I ⋙ Q) (γ : Q ⋙ G ≅ G ⋙ T)
    (δ : P ⋙ (I ⋙ G) ≅ (I ⋙ G) ⋙ T)
    (_hδ : δ.hom = Functor.whiskerRight β.hom G ≫ Functor.whiskerLeft I γ.hom) :
    (localizationComparisonDerived P T (I ⋙ G) δ).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryCompIso I G).hom
          T.mapDerivedCategory =
      Functor.whiskerLeft P.mapDerivedCategory
          (Functor.mapDerivedCategoryCompIso I G).hom ≫
        Functor.whiskerRight (localizationComparisonDerived P Q I β).hom
          G.mapDerivedCategory ≫
        Functor.whiskerLeft I.mapDerivedCategory (localizationComparisonDerived Q T G γ).hom := by
  have hδ' : δ = Functor.isoWhiskerRight β G ≪≫ Functor.isoWhiskerLeft I γ :=
    Iso.ext _hδ
  rw [hδ']
  simp only [localizationComparisonDerived, Iso.trans_hom, Iso.symm_hom,
    Functor.mapDerivedCategoryNatIso_trans, Category.assoc]
  erw [← Functor.mapDerivedCategoryCompIso_assoc I G T,
    reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft I γ)]
  have hc : (Functor.mapDerivedCategoryCompIso I (Q ⋙ G)).hom =
      (Functor.mapDerivedCategoryCompIso (I ⋙ Q) G).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryCompIso I Q).hom
          G.mapDerivedCategory ≫
        Functor.whiskerLeft I.mapDerivedCategory (Functor.mapDerivedCategoryCompIso Q G).inv := by
    rw [← cancel_mono (Functor.whiskerLeft I.mapDerivedCategory
      (Functor.mapDerivedCategoryCompIso Q G).hom)]
    simp only [Category.assoc, ← Functor.whiskerLeft_comp, Iso.inv_hom_id]
    erw [Functor.whiskerLeft_id, Category.comp_id]
    exact Functor.mapDerivedCategoryCompIso_assoc I Q G
  rw [hc]
  simp only [Category.assoc]
  erw [reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerRight β G)]
  simp only [Functor.whiskerRight_comp, Functor.whiskerLeft_comp, Category.assoc]
  have hp : (Functor.mapDerivedCategoryCompIso P (I ⋙ G)).inv ≫
      (Functor.mapDerivedCategoryCompIso (P ⋙ I) G).hom =
        Functor.whiskerLeft P.mapDerivedCategory (Functor.mapDerivedCategoryCompIso I G).hom ≫
          Functor.whiskerRight (Functor.mapDerivedCategoryCompIso P I).inv
            G.mapDerivedCategory := by
    rw [← cancel_epi (Functor.mapDerivedCategoryCompIso P (I ⋙ G)).hom,
      ← cancel_mono (Functor.whiskerRight (Functor.mapDerivedCategoryCompIso P I).hom
        G.mapDerivedCategory)]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    simp only [Category.assoc, ← Functor.whiskerRight_comp, Iso.inv_hom_id]
    erw [Functor.whiskerRight_id, Category.comp_id]
    exact (Functor.mapDerivedCategoryCompIso_assoc P I G).symm
  rw [reassoc_of% hp]

/-- The identity comparison also descends with the canonical derived identity
identification, as an equation of natural transformations.
Source: Stacks, Tag 015F and categorical localization of natural transformations
(blueprint: lem-weil-pbc-localization-inverse-image-coherence).
Proof: apply the degreewise identity equation to complexes. The factorization
isomorphisms identify the induced identity functor with the derived identity, and
faithfulness of precomposition with localization gives the displayed equation. -/
theorem localizationComparisonDerived_id
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (P : A ⥤ A) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (β : P ⋙ 𝟭 A ≅ 𝟭 A ⋙ P) (_hβ : β.hom = 𝟙 P) :
    (localizationComparisonDerived P P (𝟭 A) β).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryIdIso A).hom P.mapDerivedCategory =
      Functor.whiskerLeft P.mapDerivedCategory (Functor.mapDerivedCategoryIdIso A).hom := by
  have he : β = Iso.refl P := Iso.ext _hβ
  rw [he]
  dsimp [localizationComparisonDerived]
  rw [Functor.mapDerivedCategoryNatIso_refl (F := P)]
  erw [Category.id_comp, Category.assoc,
    Functor.mapDerivedCategoryCompIso_id_comp, Category.comp_id]
  rw [← cancel_epi (Functor.mapDerivedCategoryCompIso P (𝟭 A)).hom]
  erw [Iso.hom_inv_id, Functor.mapDerivedCategoryCompIso_comp_id]
  rfl

/-- Compatibility with a specified identification of the inverse-image coefficient ring.
The presentation `b` is reinterpretation along `e`; its underlying inverse image is the
identity and its ring identification is exactly the specified ring isomorphism.
Source: Stacks, Tags 00CP, 03D2 and 03CZ
(blueprint: lem-weil-pbc-localization-inverse-image-coherence).
Proof: reinterpret S-modules along e⁻¹. This preserves the underlying abelian sheaf,
the localization units and the invertible action of the scalar section. Extend e to
the localized rings by the unique localization lift, sending x/sⁿ to e(x)/e(s)ⁿ.
The two module comparisons in the equation extend the same unit, so the initial
property proves the commuting square. Reinterpretation is exact since kernels and
cokernels have unchanged underlying abelian sheaves. Its derived square is the
specialization of localizationComparisonDerived_comp to this exact reinterpretation. -/
theorem localizationInverseImage_coefficient
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify K CommRingCat.{u}]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (_adj : L ⊣ V)
    [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{u}) (S A : Sheaf K CommRingCat.{u}) (e : S ≅ A)
    (a : SheafOfModules.AlgebraicInverseImage L R S)
    (b : SheafOfModules.AlgebraicInverseImage (𝟭 (Sheaf K (Type u))) S A)
    (_hb : b.ringUnderlying = (sheafCompose K (forget CommRingCat.{u})).mapIso e)
    (c : SheafOfModules.AlgebraicInverseImage L R A)
    (κ : c.modules ≅ a.modules ⋙ b.modules)
    (t : (R.obj ⋙ forget CommRingCat.{u}).sections)
    (s : (S.obj ⋙ forget CommRingCat.{u}).sections)
    (r : (A.obj ⋙ forget CommRingCat.{u}).sections)
    (_hs : IsInverseImageSection a t s) (_hr : IsInverseImageSection b s r)
    (_hc : IsInverseImageSection c t r)
    (β : scalarLocalization R t ⋙ a.modules ≅ a.modules ⋙ scalarLocalization S s)
    (γ : scalarLocalization S s ⋙ b.modules ≅ b.modules ⋙ scalarLocalization A r)
    (δ : scalarLocalization R t ⋙ c.modules ≅ c.modules ⋙ scalarLocalization A r)
    (_hβ : Functor.whiskerRight (scalarLocalizationUnit R t) a.modules ≫ β.hom =
      Functor.whiskerLeft a.modules (scalarLocalizationUnit S s))
    (_hγ : Functor.whiskerRight (scalarLocalizationUnit S s) b.modules ≫ γ.hom =
      Functor.whiskerLeft b.modules (scalarLocalizationUnit A r))
    (_hδ : Functor.whiskerRight (scalarLocalizationUnit R t) c.modules ≫ δ.hom =
      Functor.whiskerLeft c.modules (scalarLocalizationUnit A r)) :
    δ.hom ≫ Functor.whiskerRight κ.hom (scalarLocalization A r) =
      Functor.whiskerLeft (scalarLocalization R t) κ.hom ≫
        Functor.whiskerRight β.hom b.modules ≫ Functor.whiskerLeft a.modules γ.hom := by
  exact localizationInverseImage_comp L V _adj (𝟭 _) (𝟭 _) (Adjunction.id)
    R S A a b c κ t s r _hs _hr _hc β γ δ _hβ _hγ _hδ

private def derivedLocalizationMap
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (τ : F ⟶ G) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ))
      DerivedCategory.Q)

@[reassoc] private lemma derivedLocalizationMap_fac
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (τ : F ⟶ G) (K : CochainComplex A ℤ) :
    (derivedLocalizationMap τ).app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategoryFactors.hom.app K =
    F.mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K) := by
  simp only [derivedLocalizationMap, Localization.liftNatTrans_app]
  change (F.mapDerivedCategoryFactors.hom.app K ≫ _ ≫
    G.mapDerivedCategoryFactors.inv.app K) ≫ _ = _
  simp

private lemma derivedLocalizationMap_right
    {A : Type uA} {B : Type uB} {C : Type uE}
    [Category.{vA} A] [Category.{vB} B] [Category.{vE} C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wE} C]
    {F F' : A ⥤ B} (G : B ⥤ C) [F.Additive] [F'.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (τ : F ⟶ F') :
    derivedLocalizationMap (Functor.whiskerRight τ G) ≫
      (Functor.mapDerivedCategoryCompIso F' G).hom =
    (Functor.mapDerivedCategoryCompIso F G).hom ≫
      Functor.whiskerRight (derivedLocalizationMap τ) G.mapDerivedCategory := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) (fun K ↦ ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  rw [← cancel_mono (G.mapDerivedCategory.map (F'.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F'.mapHomologicalComplex (.up ℤ)).obj K)),
    Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors,
    derivedLocalizationMap_fac, Category.assoc, ← Functor.map_comp_assoc,
    derivedLocalizationMap_fac, Functor.map_comp_assoc,
    Functor.mapDerivedCategoryFactors_hom_naturality,
    Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  congr 2

private lemma derivedLocalizationMap_left
    {A : Type uA} {B : Type uB} {C : Type uE}
    [Category.{vA} A] [Category.{vB} B] [Category.{vE} C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wE} C]
    (F : A ⥤ B) {G G' : B ⥤ C} [F.Additive] [G.Additive] [G'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] (τ : G ⟶ G') :
    derivedLocalizationMap (Functor.whiskerLeft F τ) ≫
      (Functor.mapDerivedCategoryCompIso F G').hom =
    (Functor.mapDerivedCategoryCompIso F G).hom ≫
      Functor.whiskerLeft F.mapDerivedCategory (derivedLocalizationMap τ) := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) (fun K ↦ ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← cancel_mono (G'.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G'.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K)),
    Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors,
    derivedLocalizationMap_fac, Category.assoc,
    ← reassoc_of% ((derivedLocalizationMap τ).naturality
      (F.mapDerivedCategoryFactors.hom.app K)), derivedLocalizationMap_fac,
    Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  congr 2

/-- Descent of a localization unit to the ordinary unbounded derived category, using
its actual termwise chain map and the localization universal property.
Source: Stacks, Tag 015F
(blueprint: lem-weil-pbc-localization-inverse-image-coherence). -/
def localizationUnitDerived
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (P : A ⥤ A) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P] (η : 𝟭 A ⟶ P) :
    𝟭 (DerivedCategory A) ⟶ P.mapDerivedCategory :=
  (Functor.mapDerivedCategoryIdIso A).inv ≫
    Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
      ((𝟭 A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (P.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (𝟭 A).mapDerivedCategory P.mapDerivedCategory
      (Functor.whiskerRight (NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ))
        DerivedCategory.Q)

/-- The same unit normalization holds after termwise passage to unbounded derived
categories. In the application P and Q are the two actual scalar-localization functors,
and I is the exact inverse image; their exactness is supplied above.
Source: Stacks, Tag 015F
(blueprint: lem-weil-pbc-localization-inverse-image-coherence).
Proof: naturality gives the chain map in every degree. The module unit equation holds
on each component of each complex. The localization universal property descends it,
and its faithfulness on natural transformations proves the displayed equality. -/
theorem localizationComparisonDerived_unit
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (P : A ⥤ A) (Q : B ⥤ B) (I : A ⥤ B)
    [P.Additive] [Q.Additive] [I.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (η : 𝟭 A ⟶ P) (ε : 𝟭 B ⟶ Q) (β : P ⋙ I ≅ I ⋙ Q)
    (_hβ : Functor.whiskerRight η I ≫ β.hom = Functor.whiskerLeft I ε) :
    Functor.whiskerRight (localizationUnitDerived P η) I.mapDerivedCategory ≫
        (localizationComparisonDerived P Q I β).hom =
      Functor.whiskerLeft I.mapDerivedCategory (localizationUnitDerived Q ε) := by
  have h : derivedLocalizationMap (Functor.whiskerRight η I) ≫
      derivedLocalizationMap β.hom = derivedLocalizationMap (Functor.whiskerLeft I ε) := by
    rw [← _hβ]
    simp only [derivedLocalizationMap, NatTrans.mapHomologicalComplex_comp,
      Functor.whiskerRight_comp, Localization.comp_liftNatTrans]
    rfl
  change (Functor.whiskerRight ((Functor.mapDerivedCategoryIdIso A).inv ≫
    derivedLocalizationMap η) I.mapDerivedCategory) ≫ _ =
    Functor.whiskerLeft I.mapDerivedCategory
      ((Functor.mapDerivedCategoryIdIso B).inv ≫ derivedLocalizationMap ε)
  have hr : Functor.whiskerRight (derivedLocalizationMap η) I.mapDerivedCategory ≫
      (Functor.mapDerivedCategoryCompIso P I).inv =
      (Functor.mapDerivedCategoryCompIso (𝟭 A) I).inv ≫
        derivedLocalizationMap (Functor.whiskerRight η I) := by
    rw [← cancel_epi (Functor.mapDerivedCategoryCompIso (𝟭 A) I).hom]
    rw [← Category.assoc, ← derivedLocalizationMap_right I η]
    simp
  have huA : (Functor.mapDerivedCategoryCompIso (𝟭 A) I).inv =
      Functor.whiskerRight (Functor.mapDerivedCategoryIdIso A).hom I.mapDerivedCategory := by
    rw [← cancel_epi (Functor.mapDerivedCategoryCompIso (𝟭 A) I).hom,
      Iso.hom_inv_id]
    exact (Functor.mapDerivedCategoryCompIso_id_comp I).symm
  have huB : (Functor.mapDerivedCategoryCompIso I (𝟭 B)).hom =
      Functor.whiskerLeft I.mapDerivedCategory (Functor.mapDerivedCategoryIdIso B).inv := by
    rw [← cancel_mono (Functor.whiskerLeft I.mapDerivedCategory
      (Functor.mapDerivedCategoryIdIso B).hom)]
    rw [Functor.mapDerivedCategoryCompIso_comp_id, ← Functor.whiskerLeft_comp,
      Iso.inv_hom_id]
    rfl
  change Functor.whiskerRight _ _ ≫
    ((Functor.mapDerivedCategoryCompIso P I).inv ≫
      derivedLocalizationMap β.hom ≫ (Functor.mapDerivedCategoryCompIso I Q).hom) = _
  simp only [Functor.whiskerRight_comp, Functor.whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% hr, huA]
  simp only [← Category.assoc, ← Functor.whiskerRight_comp, Iso.inv_hom_id]
  erw [Functor.whiskerRight_id, Category.id_comp]
  rw [Category.assoc, reassoc_of% h, derivedLocalizationMap_left I ε, huB]

/-- Maps of localized module sheaves are already linear over the localized ring if
linear over the original ring. This supplies the localized-scalar linearity of β
and of the ring-identification comparison, with no extra choice of a module map.
Source: Stacks, Tags 00CM, 00CP and 03CZ
(blueprint: lem-weil-pbc-localization-inverse-image-coherence).
Proof: an R-linear map commutes with multiplication by t and hence with its inverse.
It therefore commutes with every local scalar r/tⁿ. These scalars generate the
sheafified localized ring locally, so the sheaf condition gives linearity on the
localized ring. The underlying map fixes the lift uniquely. -/
theorem localization_restrictScalars_fullyFaithful
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) (t : (R.obj ⋙ forget CommRingCat.{u}).sections)
    (M N : inverseLocalizationModules (ringedLocalizationRingOfUniverses R t))
    (h : (SheafOfModules.restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map
            (ringedLocalizationRingUnitOfUniverses R t))).obj M ⟶
        (SheafOfModules.restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map
            (ringedLocalizationRingUnitOfUniverses R t))).obj N) :
    ∃! h' : M ⟶ N, (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map
        (ringedLocalizationRingUnitOfUniverses R t))).map h' = h := by
  let P := ringedLocalizationRingPresheafOfUniverses R t
  let B := ringedLocalizationRingOfUniverses R t
  let α : (P ⋙ forget₂ CommRingCat RingCat) ⟶
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj :=
    Functor.whiskerRight (toSheafify J P) (forget₂ CommRingCat RingCat)
  let M₀ := (PresheafOfModules.restrictScalars α).obj M.val
  let N₀ := (PresheafOfModules.restrictScalars α).obj N.val
  let g : M₀ ⟶ N₀ :=
    { app := fun U ↦ by
        letI : Algebra (R.obj.obj U) (P.obj U) :=
          inferInstanceAs (Algebra (R.obj.obj U)
            (ringedSectionLocalizationCarrierOfUniverses R t U))
        letI : IsLocalization (R := R.obj.obj U)
            (Submonoid.powers (t.val U : R.obj.obj U)) (P.obj U) :=
          inferInstanceAs (IsLocalization (R := R.obj.obj U)
            (Submonoid.powers (t.val U : R.obj.obj U))
            (ringedSectionLocalizationCarrierOfUniverses R t U))
        letI : Module (R.obj.obj U) (M₀.obj U) :=
          Module.compHom (M₀.obj U) (algebraMap (R.obj.obj U) (P.obj U))
        letI : Module (R.obj.obj U) (N₀.obj U) :=
          Module.compHom (N₀.obj U) (algebraMap (R.obj.obj U) (P.obj U))
        letI : IsScalarTower (R.obj.obj U) (P.obj U) (M₀.obj U) :=
          { smul_assoc := fun r p m ↦ by
              rw [Algebra.smul_def]
              change (algebraMap (R.obj.obj U) (P.obj U) r * p) • m =
                algebraMap (R.obj.obj U) (P.obj U) r • (p • m)
              exact mul_smul _ _ _ }
        letI : IsScalarTower (R.obj.obj U) (P.obj U) (N₀.obj U) :=
          { smul_assoc := fun r p m ↦ by
              rw [Algebra.smul_def]
              change (algebraMap (R.obj.obj U) (P.obj U) r * p) • m =
                algebraMap (R.obj.obj U) (P.obj U) r • (p • m)
              exact mul_smul _ _ _ }
        let f : M₀.obj U →ₗ[R.obj.obj U] N₀.obj U :=
          { toFun := h.val.app U
            map_add' := (h.val.app U).hom.map_add
            map_smul' := (h.val.app U).hom.map_smul }
        exact ModuleCat.ofHom (X := M₀.obj U) (Y := N₀.obj U)
          (f.extendScalarsOfIsLocalization (R := R.obj.obj U)
            (Submonoid.powers (t.val U : R.obj.obj U)) (P.obj U))
      naturality := by
        intro U V f
        ext m
        exact PresheafOfModules.naturality_apply h.val f m }
  have hα : Presheaf.IsLocallySurjective J α := by
    obtain ⟨e, he⟩ := ringedLocalizationRing_moduleComparisonOfUniverses R t
    let Q := ringedSectionLocalizationPresheafOfUniverses R t
    let η := (PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app Q
    let z := (PresheafOfModules.toPresheaf _).map η
    have hz : Presheaf.IsLocallySurjective J z := by
      dsimp only [z, η]
      rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
      exact (J.W_toSheafify Q.presheaf).isLocallySurjective
    constructor
    intro U x
    have hc := Presheaf.imageSieve_mem J z (e.hom.val.app _ x)
    apply J.superset_covering _ hc
    rintro V f ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply Function.LeftInverse.injective
      (g := e.inv.val.app (Opposite.op V))
      (f := e.hom.val.app (Opposite.op V)) ?_ ?_
    · intro m
      exact DFunLike.congr_fun
        (congrArg (fun k ↦ (k.val.app (Opposite.op V)).hom) e.hom_inv_id) m
    · change e.hom.val.app _ ((toSheafify J P).app _ y) = _
      rw [he]
      exact hy.trans (PresheafOfModules.naturality_apply e.hom.val f.op x).symm
  let e := PresheafOfModules.restrictHomEquivOfIsLocallySurjective
    (M₁ := M.val) α N.isSheaf
  let h' : M ⟶ N := ⟨e.symm g⟩
  refine ⟨h', ?_, ?_⟩
  · apply SheafOfModules.hom_ext
    ext U m
    have he := congrArg (fun f ↦ f.app U m) (e.apply_symm_apply g)
    exact he
  · intro k hk
    apply SheafOfModules.hom_ext
    ext U m
    have he := congrArg (fun f ↦ f.val.app U m) hk
    exact he.trans (by
      have he' := congrArg (fun f ↦ f.app U m) (e.apply_symm_apply g)
      exact he'.symm)

end CategoryTheory

