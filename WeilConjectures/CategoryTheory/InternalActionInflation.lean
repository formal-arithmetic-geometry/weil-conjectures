/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSiteBasic
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Trivial actions, restriction of actions, and underlying exactness

Source: paragraph (3) of the direct-image stability proof, internal-action input.
The following declarations are extracted unchanged from the two action theorem modules.
(blueprint: def-sfb-internal-action-inflation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.InternalActionSite

variable {C : Type u} [SmallCategory C]
  {K L : Cᵒᵖ ⥤ GrpCat.{u}} {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- Naturality of an action precomposed with a natural homomorphism of group presheaves.
Source: paragraph (3), categorical input, restriction of actions
(blueprint: def-sfb-internal-action-inflation).
Proof: apply naturality of the original action to θ_X(l). Naturality of θ identifies
its restriction with θ_Y of the restricted section. Substitute this equality in the
resulting action on the restricted module section. -/
theorem restrictLinearAction_naturality (θ : L ⟶ K) {M : PresheafOfModules.{u} R}
    (a : LinearAction K M) {X Y : Cᵒᵖ} (f : X ⟶ Y) (l : L.obj X) (m : M.obj X) :
    M.map f (a.act X (θ.app X l) m) =
      a.act Y (θ.app Y (L.map f l)) (M.map f m) := by
  rw [a.naturality]
  have h := congrArg (fun f ↦ f l) (θ.naturality f).symm
  change K.map f (θ.app X l) = θ.app Y (L.map f l) at h
  rw [h]

/-- Restrict the sectionwise action along a natural group homomorphism.
Source: paragraph (3), categorical input, restriction of actions
(blueprint: def-sfb-internal-action-inflation). -/
def restrictLinearAction (θ : L ⟶ K) {M : PresheafOfModules.{u} R}
    (a : LinearAction K M) : LinearAction L M where
  act X := (a.act X).comp (θ.app X).hom
  naturality f l m := restrictLinearAction_naturality θ a f l m

/-- Inflation has exactly the old module and maps, and action θ(l) on each section.
Source: paragraph (3), categorical input, restriction of actions
(blueprint: def-sfb-internal-action-inflation). -/
def inflateSheaf (J : GrothendieckTopology C) (S : Sheaf J RingCat.{u})
    (θ : L ⟶ K) : EquivariantSheaf (K := K) J S ⥤ EquivariantSheaf (K := L) J S where
  obj M := ⟨⟨M.obj.val, restrictLinearAction θ M.obj.action⟩, M.property⟩
  map f := ⟨⟨f.hom.val, fun X l m => f.hom.property X (θ.app X l) m⟩⟩

/-- The forgetful functor creates the displayed kernel and cokernel, is exact,
and detects exactness and zero objects. Kernel evaluation is sectionwise; the
cokernel comparison is with module sheafification of the presheaf cokernel.
Source: paragraph (3), categorical input, underlying exactness
(blueprint: def-sfb-internal-action-inflation). -/
structure ActionForgetExact (J : GrothendieckTopology C) (S : Sheaf J RingCat.{u})
    (K : Cᵒᵖ ⥤ GrpCat.{u}) : Prop where
  /-- Addition of maps remains sectionwise addition. -/
  [additive : (forgetSheaf (K := K) J S).Additive]
  /-- The underlying functor is left exact. -/
  finiteLimits : PreservesFiniteLimits (forgetSheaf (K := K) J S)
  /-- The underlying functor is right exact. -/
  finiteColimits : PreservesFiniteColimits (forgetSheaf (K := K) J S)
  /-- Exactness can be tested after forgetting the action. -/
  exact_iff (T : ShortComplex (EquivariantSheaf (K := K) J S)) :
    T.Exact ↔ (T.map (forgetSheaf (K := K) J S)).Exact
  /-- The zero object is detected on the underlying sheaf. -/
  zero_iff (M : EquivariantSheaf (K := K) J S) :
    IsZero M ↔ IsZero ((forgetSheaf J S).obj M)
  /-- Every ordinary module kernel lifts with its induced action. -/
  createsKernels (M N : EquivariantSheaf (K := K) J S) (f : M ⟶ N) :
    Nonempty (CreatesLimit (parallelPair f 0) (forgetSheaf J S))
  /-- Every ordinary module cokernel lifts with its induced action. -/
  createsCokernels (M N : EquivariantSheaf (K := K) J S) (f : M ⟶ N) :
    Nonempty (CreatesColimit (parallelPair f 0) (forgetSheaf J S))
  /-- Evaluating the underlying kernel gives the kernel on sections. -/
  sectionwiseKernel (M N : EquivariantSheaf (K := K) J S) (f : M ⟶ N) (X : Cᵒᵖ) :
    PreservesLimit (parallelPair ((forgetSheaf J S).map f) 0)
      (SheafOfModules.evaluation S X)
  /-- The underlying cokernel is module sheafification of the sectionwise quotient. -/
  sheafifiedCokernel (M N : EquivariantSheaf (K := K) J S) (f : M ⟶ N) :
    Nonempty (cokernel ((forgetSheaf J S).map f) ≅
      (PresheafOfModules.sheafification (𝟙 S.obj)).obj
        (cokernel ((SheafOfModules.forget S).map ((forgetSheaf J S).map f))))

variable {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})

/-- Give an existing module sheaf the trivial sectionwise action.
Source: trivial action in paragraph (3)
(blueprint: def-sfb-internal-action-inflation). -/
def trivialSheafAction (P : Cᵒᵖ ⥤ GrpCat.{u}) :
    ringedSiteModules.{u} R ⥤ EquivariantSheaf (K := P) J R where
  obj M := ⟨⟨M.val, ⟨fun _ ↦ 1, fun _ _ _ ↦ rfl⟩⟩, M.isSheaf⟩
  map f := ObjectProperty.homMk ⟨f.val, fun _ _ _ ↦ rfl⟩

end CategoryTheory.InternalActionSite
