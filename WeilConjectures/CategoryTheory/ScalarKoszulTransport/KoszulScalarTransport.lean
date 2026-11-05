/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Strict.StrictScalarKoszulInstances
import all WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement

/-! # KoszulScalarTransport for strict Koszul comparison

Source: Stacks Project, Tags 0A0E and 0913.
(blueprint: lem-f5-koszul-scalar-transport).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FlatScalarKoszul

variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}
variable {R B : Sheaf J CommRingCat.{u}}

open MonoidalCategory
open scoped CategoryTheory.Prod

attribute [local irreducible] homComplexFunctor
  SheafOfModules.tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction
  Localization.Monoidal.tensorBifunctor

attribute [local instance] gradedTensorCache gradedGoodTensorLeftCache
  gradedGoodTensorRightCache gradedFourCache tensorPreservesEmptyLeftCache
  tensorPreservesEmptyRightCache cachedModuleMonoidal cachedModuleSymmetric
  cachedModulePreadditive cachedModuleClosed cachedComplexMonoidal
  cachedComplexBraided cachedComplexClosed

namespace ScalarKoszulTransport

universe v u₁ w₁ u₂ w₂ u' w w'

section DoubleComparison

variable {E : Type u₁} [Category.{w₁} E] [Preadditive E] [HasZeroObject E]
variable {E' : Type u₂} [Category.{w₂} E'] [Preadditive E'] [HasZeroObject E']
variable (P : E ⥤ E') [P.Additive] {X : E} {Y : E'}

end DoubleComparison

section FactorComparison

variable {C D : Type v} [SmallCategory C] [SmallCategory D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {R : Sheaf J CommRingCat.{v}} {S : Sheaf K CommRingCat.{v}}
variable (P : Modules R ⥤ Modules S) [P.Additive]
variable (s : (R.obj ⋙ forget CommRingCat).sections)
variable (t : (S.obj ⋙ forget CommRingCat).sections)

end FactorComparison

section TensorDiagrams

variable {E : Type u₁} [Category.{w₁} E]
variable {E' : Type u₂} [Category.{w₂} E']
variable {P : E ⥤ E'} {T : E ⥤ E ⥤ E} {T' : E' ⥤ E' ⥤ E'}
variable {R : E} {S : E'} {ρ : ∀ N : E, (T.obj N).obj R ≅ N}
variable {ρ' : ∀ N : E', (T'.obj N).obj S ≅ N}

end TensorDiagrams

section KoszulInduction

variable {C D : Type v} [SmallCategory C] [SmallCategory D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

end KoszulInduction

end ScalarKoszulTransport

end CategoryTheory.FlatScalarKoszul
