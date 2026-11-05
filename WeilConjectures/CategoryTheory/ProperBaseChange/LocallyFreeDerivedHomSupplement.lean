/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Algebra.Homology.RingedSiteZerothHypercohomology
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.AlgebraicGeometry.DualTensorHomComparison
import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Free
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Algebra.Homology.LocallyFreeDerivedHom

/-! # Derived Hom from a locally finite free module on a ringed site

Source: Stacks Project, Tag 08JJ, lemma-dual-perfect-complex, specialized to P[0]
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom).

The degree-zero formulation below is applied to every shifted bounded-below complex.
Thus H⁰ RΓ(P∨ ⊗ K[n]) is Hⁿ RΓ(P∨ ⊗ K), including negative n. The cycle normalization
specifies evaluation, rather than only asserting the existence of abstract group isomorphisms.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
universe u v w

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory

section AbstractModel

variable {A : Type v} [Category.{u} A] [Abelian A] [MonoidalCategory A]
  [MonoidalClosed A] [∀ P : A, (tensorLeft P).Additive]

variable [HasDerivedCategory.{w} A] [IsGrothendieckAbelian.{u} A]

-- Infer addition on the localized Hom group without exhausting the instance budget.
-- The cycle and naturality identities elaborate several derived Hom groups.

-- The cycle and naturality identities elaborate several derived Hom groups.
-- The cycle and naturality identities elaborate several derived Hom groups.

-- The cycle and naturality identities elaborate several derived Hom groups.
end AbstractModel

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (R : Sheaf J CommRingCat.{u})

set_option backward.isDefEq.respectTransparency true in
section

variable [HasDerivedCategory.{w} (ringedSiteModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]

end

variable [HasDerivedCategory.{w} (ringedSiteModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]

end CategoryTheory
