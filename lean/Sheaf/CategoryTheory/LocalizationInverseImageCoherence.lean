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
import Mathlib.RingTheory.Localization.Module
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.Localization
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Sheaf.CategoryTheory.GeometricModuleTransport
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor

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
  sorry

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
  sorry

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

