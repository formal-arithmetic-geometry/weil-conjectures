/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Constant scalar restriction and geometric module adjunctions

Source: Stacks Project, Sites, Tag 00YV (6), and Categories, Tag 0B65;
normalized constant-scalar comparison (blueprint: lem-sfb-constant-scalar-geometric-adjunctions).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- The induced geometric adjunction on fixed-ring module sheaves. The direct-image
comparison and generalized-element equation specify the transported addition and every
scalar endomorphism. The inverse image is its specified left adjoint; hence uniqueness
of left adjoints identifies it with the induced geometric inverse image.
Source: Stacks Project, Sites, Tag 00YV (6), proof by scalar endomorphisms
(blueprint: lem-sfb-constant-scalar-geometric-adjunctions). -/
structure FixedScalarGeometricAdjunction
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (B : Type u) [CommRing B]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (a : L ⊣ V) (hL : PreservesFiniteLimits L) where
  /-- Induced inverse image of fixed-scalar module sheaves. -/
  inverse : Sheaf J (ModuleCat.{u} B) ⥤ Sheaf K (ModuleCat.{u} B)
  /-- Induced direct image of fixed-scalar module sheaves. -/
  direct : Sheaf K (ModuleCat.{u} B) ⥤ Sheaf J (ModuleCat.{u} B)
  /-- The specified module adjunction. -/
  adj : inverse ⊣ direct
  /-- Identification with the given direct image on underlying sheaves. -/
  underlying : direct ⋙ sheafCompose J (forget (ModuleCat.{u} B)) ≅
    sheafCompose K (forget (ModuleCat.{u} B)) ⋙ V
  /-- The direct-image action and addition under the given sheaf adjunction.
  This also determines zero and negation by the abelian group laws. -/
  linear : ∀ (N : Sheaf K (ModuleCat.{u} B)) (T : Sheaf J (Type u)) (b : B)
    (x y z : T ⟶ (sheafCompose J (forget (ModuleCat.{u} B))).obj (direct.obj N)),
    (∀ (U : Cᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Add.add ((direct.obj N).obj.obj U) inferInstance
        (@SMul.smul B ((direct.obj N).obj.obj U) inferInstance b (x.hom.app U t))
        (y.hom.app U t)) →
    ∀ (U : Dᵒᵖ) (t : (L.obj T).obj.obj U),
      ((a.homEquiv T _).symm (z ≫ underlying.hom.app N)).hom.app U t =
        @Add.add (N.obj.obj U) inferInstance
          (@SMul.smul B (N.obj.obj U) inferInstance b
            (((a.homEquiv T _).symm (x ≫ underlying.hom.app N)).hom.app U t))
          (((a.homEquiv T _).symm (y ≫ underlying.hom.app N)).hom.app U t)

end CategoryTheory
