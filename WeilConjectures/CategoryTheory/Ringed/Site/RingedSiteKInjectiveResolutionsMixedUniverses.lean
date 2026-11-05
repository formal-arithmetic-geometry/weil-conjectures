/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.Ring.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-! # K-injective resolutions with independent site universes

Source: Stacks Project, Section 07A5 and Theorem 079P
(blueprint: prop-pur-kinjective-resolutions-exist).
The ring universe is r, while module sections live in max c v r.
The free lifted Yoneda sheaves are precisely the sheafifications of the localized
rank-one extension presheaves. Their use preserves the generator in the source statement.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r s

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Forgetting commutativity preserves the sheaf condition, independently of the
size of the site. This supplies the underlying ring sheaf used in Mod(O).
Source: Stacks, Modules on Sites 03D7, and Sites 00VR
(blueprint: prop-pur-kinjective-resolutions-exist).
Proof: a compatible family of ring maps has the same underlying functions as a
compatible family of commutative-ring maps when its test ring is commutative. For
an arbitrary test ring, glue the images of its elements in the commutative sheaf;
uniqueness and restriction test the ring laws locally. Thus the glued function
is a ring map. Equivalently, the fully faithful inclusion of commutative rings
preserves every existing limit, including the limits of covering diagrams. -/
@[instance] theorem hasSheafCompose_commRingToRing {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) := by
  let F := forget₂ CommRingCat.{r} RingCat.{r}
  let G := forget RingCat.{r}
  have : PreservesLimitsOfSize.{v, max c v} F := by
    constructor
    intro K _
    constructor
    intro D
    constructor
    intro t ht
    have : PreservesLimit D (forget CommRingCat.{r}) :=
      CommRingCat.adj.rightAdjoint_preservesLimits.preservesLimitsOfShape.preservesLimit
    have htypes := isLimitOfPreserves (forget CommRingCat.{r}) ht
    have : HasLimit (D ⋙ forget CommRingCat.{r}) := ⟨⟨_, htypes⟩⟩
    have : Small.{r} (D ⋙ forget CommRingCat.{r}).sections :=
      (Types.hasLimit_iff_small_sections _).mp inferInstance
    have : Small.{r} ((D ⋙ F) ⋙ G).sections := ‹_›
    have : HasLimit (D ⋙ F) := inferInstance
    have : PreservesLimit (D ⋙ F) G :=
      preservesLimit_of_preserves_limit_cone (RingCat.limitConeIsLimit _)
        (Types.Small.limitConeIsLimit _)
    have : ReflectsLimit (D ⋙ F) G := reflectsLimit_of_reflectsIsomorphisms (D ⋙ F) G
    exact ⟨isLimitOfReflects G htypes⟩
  exact hasSheafCompose_of_preservesLimitsOfSize J

end CategoryTheory

namespace PresheafOfModules

end PresheafOfModules

namespace SheafOfModules

end SheafOfModules
