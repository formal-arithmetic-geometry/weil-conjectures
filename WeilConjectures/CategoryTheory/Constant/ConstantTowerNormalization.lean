/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafHom
public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.Algebra.Homology.ProperBaseChange.DiagramKFlatReplacements
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Category.ULift

/-!
# The representative normalization of the derived constant-tower comparison

Source: Stacks Project, Derived Categories, Tag 06XN, `lemma-find-existence-computes`
(dual), and the completed-pullback constant-tower subargument, Step 4
(blueprint: lem-cbc-derived-constant-tower-normalization).

The auxiliary maps below merely spell out the canonical localization identifications.
Strict towers are indexed by `ℕᵒᵖ`, with level `n` representing the paper's level `n + 1`.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section

set_option autoImplicit false

universe uA vA uB vB wA wB wTA wTB u

open CategoryTheory CategoryTheory.Limits

-- Avoid expanding covering multicospans when forgetting commutative ring structures.
attribute [local instance 11000] hasSheafCompose_of_preservesLimitsOfSize

-- A full, essentially surjective functor is initial: every comma object maps
-- to a fixed lift of the target, giving a zigzag between any two objects.

-- The induced functor on structured arrows is also full and essentially
-- surjective, so restricting the defining limit cone preserves its limit.

-- Transport the defining limit cone through an equivalence of structured
-- arrow categories and the prescribed isomorphism of diagram functors.

-- Computation on a resolving class is invariant under the chosen universal pair.

-- The inverse of Mathlib's transpose on complexes of functors.

namespace CategoryTheory.Functor

section Identifications

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
  (E : A ⥤ B) [E.Additive]

end Identifications

end CategoryTheory.Functor

namespace CategoryTheory.RingedToposMorphism

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {T : GrothendieckTopology C} {T' : GrothendieckTopology D}
  (R : Sheaf T CommRingCat.{u}) (S : Sheaf T' CommRingCat.{u})
  [HasDerivedCategory.{wA}
    (ringedSiteModules.{u, u, u, u} ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R))]
  [HasDerivedCategory.{wB}
    (ringedSiteModules.{u, u, u, u} ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S))]
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u}
    ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R))]
  [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u}
    ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S))]

end CategoryTheory.RingedToposMorphism
