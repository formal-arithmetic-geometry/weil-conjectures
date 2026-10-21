/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.CategoryTheory.ConstantRingModuleSheaves
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

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


/-- Constant scalar restriction identifies geometric module adjunctions and their
specified further left adjoints, in particular open extension by zero.

Source: Stacks Project, Sites, Tag 00YV (6), and Categories, Tag 0B65
(blueprint: lem-sfb-constant-scalar-geometric-adjunctions).

Proof plan:
1. Normalization on constant scalar summands says that the ringed direct-image
   action of a scalar is the direct image of that scalar endomorphism. Thus its
   fixed-scalar action equals the induced one. The common underlying additive
   direct-image map is a linear identity, natural in the module, giving beta.
2. Use constant_ring_module_sheaves (lem-cbc-constant-ring-module-sheaves): scalar
   restriction is an equivalence, with inverse extending the action and retaining
   all additive maps. Transport the ringed Hom adjunction through these equivalences
   and beta to an adjunction with the specified fixed-scalar direct image.
3. Apply unit-compatible uniqueness of left adjoints
   (lem-weil-pbc-conjugate-iso-unit-equation) to obtain alpha, the mate of beta.
4. Expand each Hom adjunction as the unit followed by the right image of the map.
   Naturality of beta and the mate unit equation give the Hom equation. Take the
   identity for the unit and the ringed counit for the counit equation; injectivity
   of the fixed-scalar Hom bijection gives the latter equality.
5. For the supplied further left adjoints, transport their Hom bijections using
   alpha and the same scalar equivalences. Uniqueness of left adjoints gives kappa.
   Its Hom equation specializes at identities to the open unit equation and at the
   ringed open counit to the open counit equation.
6. This applies to every localized site: overFunctor evaluates on V/U as evaluation
   on V. The constant-sheaf restriction comparison
   (lem-weil-pbc-site-constant-restriction) identifies the localized constant units.
   Restricting the action before or after scalar restriction therefore gives the
   same action and maps, also under relocalization. The further-left-adjoint clause
   only uses the supplied adjunctions, so does not require a subterminal object.
No points, nonzero-ring, finite-coefficient or scheme hypothesis is used. -/
theorem constant_scalar_geometric_adjunctions
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (B : Type u) [CommRing B]
    (r : RingedToposMorphism
      ((constantSheaf K RingCat.{u}).obj (RingCat.of B))
      ((constantSheaf J RingCat.{u}).obj (RingCat.of B)))
    (hb : IsIso r.ringMap)
    (e₁ : r.inverse.obj ((constantSheaf J (Type u)).obj PUnit.{u + 1}) ≅
      (constantSheaf K (Type u)).obj PUnit.{u + 1})
    (hn : ∀ b : B,
      r.inverse.map ((constantSheaf J (Type u)).map
        (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ b)) ≫
        (constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of B)) ≫
        r.ringMap =
      e₁.hom ≫ (constantSheaf K (Type u)).map
        (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ b)) ≫
        (constantCommuteCompose K (forget RingCat.{u})).inv.app (RingCat.of B))
    (LR : ringedSiteModules.{u}
        ((constantSheaf J RingCat.{u}).obj (RingCat.of B)) ⥤
      ringedSiteModules.{u} ((constantSheaf K RingCat.{u}).obj (RingCat.of B)))
    (aR : LR ⊣ r.modules)
    (q : FixedScalarGeometricAdjunction J K B r.inverse r.direct r.adj r.leftExact) :
    ∃ (β : r.modules ⋙ constantRingModuleRestriction J B ≅
        constantRingModuleRestriction K B ⋙ q.direct)
      (α : LR ⋙ constantRingModuleRestriction K B ≅
        constantRingModuleRestriction J B ⋙ q.inverse),
      (∀ N,
        (sheafCompose J (forget (ModuleCat.{u} B))).map (β.hom.app N) ≫
          q.underlying.hom.app ((constantRingModuleRestriction K B).obj N) =
            r.underlying.hom.app N) ∧
      (∀ M N (f : LR.obj M ⟶ N),
        q.adj.homEquiv _ _ (α.inv.app M ≫ (constantRingModuleRestriction K B).map f) =
          (constantRingModuleRestriction J B).map (aR.homEquiv M N f) ≫ β.hom.app N) ∧
      (∀ M,
        (constantRingModuleRestriction J B).map (aR.unit.app M) ≫
          β.hom.app (LR.obj M) ≫ q.direct.map (α.hom.app M) =
            q.adj.unit.app ((constantRingModuleRestriction J B).obj M)) ∧
      (∀ N,
        (constantRingModuleRestriction K B).map (aR.counit.app N) =
          α.hom.app (r.modules.obj N) ≫ q.inverse.map (β.hom.app N) ≫
            q.adj.counit.app ((constantRingModuleRestriction K B).obj N)) ∧
      (∀ (ER : ringedSiteModules.{u}
          ((constantSheaf K RingCat.{u}).obj (RingCat.of B)) ⥤
        ringedSiteModules.{u} ((constantSheaf J RingCat.{u}).obj (RingCat.of B)))
        (aER : ER ⊣ LR)
        (EB : Sheaf K (ModuleCat.{u} B) ⥤ Sheaf J (ModuleCat.{u} B))
        (aEB : EB ⊣ q.inverse),
        ∃ κ : ER ⋙ constantRingModuleRestriction J B ≅
            constantRingModuleRestriction K B ⋙ EB,
          (∀ N M (f : ER.obj N ⟶ M),
            aEB.homEquiv _ _ (κ.inv.app N ≫ (constantRingModuleRestriction J B).map f) =
              (constantRingModuleRestriction K B).map (aER.homEquiv N M f) ≫ α.hom.app M) ∧
          (∀ N,
            (constantRingModuleRestriction K B).map (aER.unit.app N) ≫
              α.hom.app (ER.obj N) ≫ q.inverse.map (κ.hom.app N) =
                aEB.unit.app ((constantRingModuleRestriction K B).obj N)) ∧
          (∀ M,
            (constantRingModuleRestriction J B).map (aER.counit.app M) =
              κ.hom.app (LR.obj M) ≫ EB.map (α.hom.app M) ≫
                aEB.counit.app ((constantRingModuleRestriction J B).obj M))) := by
  sorry

end CategoryTheory
