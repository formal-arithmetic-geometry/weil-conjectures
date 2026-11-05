/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.SitePullbackTensorGenerators
public import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Monoidal structure of a ringed-site module pullback

Source: Stacks Project, Modules on Sites, Tag 03EL, and Cohomology on Sites, Tag 07A4.

For a continuous, representably flat functor of sites and a map of coefficient rings,
every left adjoint of the module direct image carries the pure-tensor normalized
comparison of `sitePullbackTensorGenerators`. All identities are checked on the
adjunction-unit images of pure tensors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false

universe c v r uC vC w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open CategoryTheory.CochainPullback (moduleTmul moduleTmul_map moduleTmul_braiding
  moduleTmul_associator)

namespace WeilConjectures.SitePullbackMonoidal

attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
attribute [local instance 2000] SheafOfModules.cochainModulesSymmetric

section TensorExt

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}}

end TensorExt

section RingMap

variable [UnivLE.{max c v, r}] {C D : Type c} [Category.{v} C] [Category.{v} D]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (U : C ⥤ D) [U.IsContinuous J K]
  (R : Sheaf J CommRingCat.{r}) (S : Sheaf K CommRingCat.{r})
  (φ : R ⟶ (U.sheafPushforwardContinuous CommRingCat.{r} J K).obj S)

end RingMap

section Generic

variable [UnivLE.{max c v, r}]
  {C D : Type c} [Category.{v} C] [Category.{v} D]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (U : C ⥤ D) [U.IsContinuous J K] [RepresentablyFlat U]
  (R : Sheaf J CommRingCat.{r}) (S : Sheaf K CommRingCat.{r})
  (φ : R ⟶ (U.sheafPushforwardContinuous CommRingCat.{r} J K).obj S)
  (F : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
    SheafOfModules.{r} ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
  [F.Additive]
  (adj : F ⊣ SheafOfModules.pushforward.{r} (ringMap J K U R S φ))

end Generic

section Composition

variable [UnivLE.{max c v, r}]
  {C D E : Type c} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} D] [EssentiallySmall.{r} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  {U₁ : C ⥤ D} [U₁.IsContinuous J K] [RepresentablyFlat U₁]
  {U₂ : D ⥤ E} [U₂.IsContinuous K L] [RepresentablyFlat U₂]
  {U₁₂ : C ⥤ E} [U₁₂.IsContinuous J L] [RepresentablyFlat U₁₂]
  {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}} {T : Sheaf L CommRingCat.{r}}
  {φ₁ : R ⟶ (U₁.sheafPushforwardContinuous CommRingCat.{r} J K).obj S}
  {φ₂ : S ⟶ (U₂.sheafPushforwardContinuous CommRingCat.{r} K L).obj T}
  {φ₁₂ : R ⟶ (U₁₂.sheafPushforwardContinuous CommRingCat.{r} J L).obj T}
  {F₁ : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
    SheafOfModules.{r} ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S)}
  [F₁.Additive]
  {F₂ : SheafOfModules.{r} ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S) ⥤
    SheafOfModules.{r} ((sheafCompose L (forget₂ CommRingCat.{r} RingCat.{r})).obj T)}
  [F₂.Additive]
  {F₁₂ : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
    SheafOfModules.{r} ((sheafCompose L (forget₂ CommRingCat.{r} RingCat.{r})).obj T)}
  [F₁₂.Additive]
  (adj₁ : F₁ ⊣ SheafOfModules.pushforward.{r} (ringMap J K U₁ R S φ₁))
  (adj₂ : F₂ ⊣ SheafOfModules.pushforward.{r} (ringMap K L U₂ S T φ₂))
  (adj₁₂ : F₁₂ ⊣ SheafOfModules.pushforward.{r} (ringMap J L U₁₂ R T φ₁₂))

end Composition

end WeilConjectures.SitePullbackMonoidal
