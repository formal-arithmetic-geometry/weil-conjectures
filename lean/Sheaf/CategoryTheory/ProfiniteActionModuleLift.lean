/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q90
-/
module

public import Sheaf.CategoryTheory.ProfiniteActionCechRecovery
public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.CategoryTheory.SheafificationTensorLocalIso

/-! # Linear profinite-action descent

Source: current blueprint, direct-image stability, paragraph (3), auxiliary
profinite-action infrastructure, extracted presentation steps 11 and 12
(blueprint: lem-sfb-profinite-action-module-lift).

The data below are a specification, never a choice from an existence theorem.
Injective section maps with the specified exact images express the subsets Q.
Their semilinearity fixes inherited operations, including the scalar inclusion.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open Profinite.CondensedAction.CoherentPresentation
open Profinite.CondensedAction.YonedaFreeEvaluation
open Profinite.CondensedAction.CechRecovery

namespace Profinite.CondensedAction.LinearDescent

variable (J : Type u) [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
  [CompactSpace J] [T2Space J] [TotallyDisconnectedSpace J]
  (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

/-- Section modules on the action site, using the recorded general ringed-site category.
Source: paragraph (3), module lift (blueprint: lem-sfb-profinite-action-module-lift). -/
abbrev SiteModules (A : Sheaf (coverage J).toGrothendieck CommRingCat.{u + 1}) :=
  ringedSiteModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)

set_option genSizeOf false in
set_option genInjectivity false in
/-- The linear descent data, with every construction normalized by `LiftProperties`.
No data are obtained from the theorem asserting their existence.
Source: paragraph (3), extracted steps 11 and 12
(blueprint: lem-sfb-profinite-action-module-lift). -/
structure LiftData where
  /-- The coefficient ring sheaf R_J. -/
  ring : Sheaf (coverage J).toGrothendieck CommRingCat.{u + 1}
  /-- Inclusion of Q_R(T) into the original section ring. -/
  ringSection (T : Space J) : ring.obj.obj (op T) →+*
    (coefficient R).obj.obj (op ((underlying J).obj T))
  /-- Evaluation of free coefficient sections at (1,s). -/
  freeRing (S : Base.{u}) : ring.obj.obj (op ((freeParameter J).obj S)) ≃+*
    (coefficient R).obj.obj (op (parameter S))
  /-- The functor Phi_R. -/
  phi : ActionModule R J ⥤ SiteModules J ring
  /-- Inclusion of Q_N(T), with inherited addition and pointwise scalars. -/
  moduleSection (N : ActionModule R J) (T : Space J) :
    (phi.obj N).val.obj (op T) →ₛₗ[ringSection T]
      sectionModule R N.module ((underlying J).obj T)
  /-- The reverse functor G_R. -/
  free : SiteModules J ring ⥤ ActionModule R J
  /-- The original groups M(H(S)), before changing scalars by freeRing. -/
  freeSections (M : SiteModules J ring) (S : Base.{u}) :
    sectionModule R (free.obj M).module (parameter S) ≃+
      M.val.obj (op ((freeParameter J).obj S))
  /-- The linear Cech descent isomorphism. -/
  unit : 𝟭 (SiteModules J ring) ≅ free ⋙ phi
  /-- The linear free-evaluation isomorphism. -/
  counit : phi ⋙ free ≅ 𝟭 (ActionModule R J)
  /-- Evaluation on free module sections, with the specified section-ring change. -/
  evaluation (N : ActionModule R J) (S : Base.{u}) :
    (phi.obj N).val.obj (op ((freeParameter J).obj S)) ≃+
      sectionModule R N.module (parameter S)

/-- All equations fixing the lift: exact Q images, original restrictions and maps,
free evaluation, coefficient change, and the two linear recovery isomorphisms.
Source: paragraph (3), extracted steps 11 and 12
(blueprint: lem-sfb-profinite-action-module-lift). -/
structure LiftProperties (D : LiftData J R) : Prop where
  /-- Q_R is a subset, not a quotient or an arbitrary coefficient identification. -/
  ring_injective (T : Space J) : Function.Injective (D.ringSection T)
  /-- Its image is the universal-parameter equation for trivial coefficient action. -/
  ring_image (T : Space J) (a : (coefficient R).obj.obj (op ((underlying J).obj T))) :
    (∃ b, D.ringSection T b = a) ↔
      (coefficient R).obj.map (actionMap J T).down.op a =
        (coefficient R).obj.map (secondProjection J T).down.op a
  /-- Restrictions are inherited from the original coefficient sheaf. -/
  ring_restriction {T V : Space J} (f : T ⟶ V) (a : D.ring.obj.obj (op V)) :
    D.ringSection T (D.ring.obj.map f.op a) =
      (coefficient R).obj.map ((underlying J).map f).op (D.ringSection V a)
  /-- Free coefficient evaluation is restriction to (1,s). -/
  freeRing_eq (S : Base.{u}) (a : D.ring.obj.obj (op ((freeParameter J).obj S))) :
    D.freeRing S a = (coefficient R).obj.map (unitParameter S).op
      (D.ringSection ((freeParameter J).obj S) a)
  /-- Its inverse pulls back along the projection J times S to S. -/
  freeRing_inverse (S : Base.{u}) (a : (coefficient R).obj.obj (op (parameter S))) :
    D.ringSection ((freeParameter J).obj S) ((D.freeRing S).symm a) =
      (coefficient R).obj.map
        (CompHausLike.ofHom _ ⟨Prod.snd, continuous_snd⟩ :
          Profinite.of (J × parameter S) ⟶ parameter S).op a
  /-- Free coefficient evaluation is natural in all profinite parameters. -/
  freeRing_natural {S V : Base.{u}} (f : S ⟶ V)
      (a : D.ring.obj.obj (op ((freeParameter J).obj V))) :
    D.freeRing S (D.ring.obj.map ((freeParameter J).map f).op a) =
      (coefficient R).obj.map f.down.op (D.freeRing V a)
  /-- Every family right translation is the identity on free coefficients. -/
  freeRing_translation (S : Base.{u}) (g : C(parameter S, J))
      (a : D.ring.obj.obj (op ((freeParameter J).obj S))) :
    D.freeRing S (D.ring.obj.map (freeRightTranslation J S g).op a) = D.freeRing S a
  /-- The module sections are actual subsets of the original section modules. -/
  section_injective (N : ActionModule R J) (T : Space J) :
    Function.Injective (D.moduleSection N T)
  /-- Their image is precisely Q_N, with the universal continuous group parameter. -/
  section_image (N : ActionModule R J) (T : Space J)
      (x : sectionModule R N.module ((underlying J).obj T)) :
    (∃ y, D.moduleSection N T y = x) ↔
      (N.module.X.obj.map (actionMap J T).down.op).hom x =
        N.act (parameter (productParameter J T)) (groupProjection J T).down
          ((N.module.X.obj.map (secondProjection J T).down.op).hom x)
  /-- Restrictions are the original semilinear restrictions, restricted to Q. -/
  section_restriction (N : ActionModule R J) {T V : Space J} (f : T ⟶ V)
      (x : (D.phi.obj N).val.obj (op V)) :
    D.moduleSection N T ((D.phi.obj N).val.map f.op x) =
      (N.module.X.obj.map ((underlying J).map f).op).hom (D.moduleSection N V x)
  /-- An equivariant linear map acts by its original component restricted to Q. -/
  phi_maps {N N' : ActionModule R J} (v : N ⟶ N') (T : Space J)
      (x : (D.phi.obj N).val.obj (op T)) :
    D.moduleSection N' T ((D.phi.map v).val.app (op T) x) =
      (v.val.hom.hom.app (op ((underlying J).obj T))).hom (D.moduleSection N T x)
  /-- Phi_R preserves sums of maps. -/
  phi_additive : D.phi.Additive
  /-- G_R preserves sums of maps. -/
  free_additive : D.free.Additive
  /-- The R(S)-module structure is exactly scalar restriction through e_R inverse. -/
  free_scalar (M : SiteModules J D.ring) (S : Base.{u})
      (a : (coefficient R).obj.obj (op (parameter S)))
      (x : sectionModule R (D.free.obj M).module (parameter S)) :
    D.freeSections M S (a • x) = (D.freeRing S).symm a • D.freeSections M S x
  /-- The reconstructed underlying restrictions are M(H(f)). -/
  free_restriction (M : SiteModules J D.ring) {S V : Base.{u}} (f : S ⟶ V)
      (x : sectionModule R (D.free.obj M).module (parameter V)) :
    D.freeSections M S (((D.free.obj M).module.X.obj.map f.down.op).hom x) =
      M.val.map ((freeParameter J).map f).op (D.freeSections M V x)
  /-- The reconstructed linear action is exactly M(r_g). -/
  free_action (M : SiteModules J D.ring) (S : Base.{u}) (g : C(parameter S, J))
      (x : sectionModule R (D.free.obj M).module (parameter S)) :
    D.freeSections M S ((D.free.obj M).act (parameter S) g x) =
      M.val.map (freeRightTranslation J S g).op (D.freeSections M S x)
  /-- The reconstructed morphisms are the original components at H(S). -/
  free_maps {M M' : SiteModules J D.ring} (v : M ⟶ M') (S : Base.{u})
      (x : sectionModule R (D.free.obj M).module (parameter S)) :
    D.freeSections M' S (((D.free.map v).val.hom.hom.app (op (parameter S))).hom x) =
      v.val.app (op ((freeParameter J).obj S)) (D.freeSections M S x)
  /-- The linear unit is the actual Cech pullback M(a_T), over the scalar inclusion. -/
  unit_eq (M : SiteModules J D.ring) (T : Space J) (x : M.val.obj (op T)) :
    D.freeSections M (base J T)
        (D.moduleSection (D.free.obj M) T ((D.unit.hom.app M).val.app (op T) x)) =
      M.val.map (actionCover J T).op x
  /-- Free evaluation is restriction to (1,s) on the original module. -/
  evaluation_eq (N : ActionModule R J) (S : Base.{u})
      (x : (D.phi.obj N).val.obj (op ((freeParameter J).obj S))) :
    D.evaluation N S x = (N.module.X.obj.map (unitParameter S).op).hom
      (D.moduleSection N ((freeParameter J).obj S) x)
  /-- In particular free evaluation is R(S)-linear under e_R. -/
  evaluation_scalar (N : ActionModule R J) (S : Base.{u})
      (a : D.ring.obj.obj (op ((freeParameter J).obj S)))
      (x : (D.phi.obj N).val.obj (op ((freeParameter J).obj S))) :
    D.evaluation N S (a • x) = D.freeRing S a • D.evaluation N S x
  /-- The natural equivariant linear counit is precisely free evaluation. -/
  counit_eq (N : ActionModule R J) (S : Base.{u})
      (x : sectionModule R (D.free.obj (D.phi.obj N)).module (parameter S)) :
    ((D.counit.hom.app N).val.hom.hom.app (op (parameter S))).hom x =
      D.evaluation N S (D.freeSections (D.phi.obj N) S x)

/-- The specified linear lift exists for every commutative condensed ring.
Source: current blueprint, direct-image stability, paragraph (3), auxiliary infrastructure
(blueprint: lem-sfb-profinite-action-module-lift).
Proof:
1. Use the size convention and sk-def-sfb-sheaf-tensor together with
   det-def-sfb-sheaf-tensor-local-iso to apply the recorded internal/section-module
   equivalence on the profinite site, with unchanged section groups and restrictions.
2. Q_R is the equalizer subring of R(alpha) and R(pi). Equivariant Yoneda descent
   proves it is a sheaf. Restriction at (1,s) is a ring equivalence on H(S), with
   inverse projection pullback; projection commutes with H(f) and every r_g.
3. For Q_N, additivity of restrictions and linearity of the action give closure
   under sums and negatives. Semilinearity and R(alpha)a=R(pi)a give scalar closure.
   Yoneda descent supplies the sheaf condition. Restrict equivariant maps to Q;
   the component formulas show identities, composition, zero and sums are preserved.
4. Set G_R(M)(S)=M(H(S)), with scalar a acting by e_R inverse(a). The module-sheaf
   restriction law gives semilinearity along H(f) and linearity along r_g, since
   free coefficients are unchanged by r_g. Free restriction proves sheaf descent,
   the action laws and naturality. The internal/section-module equivalence reconstructs
   the internal module. Component maps give the additive reverse functor.
5. Cech recovery identifies M(T) with Q_G(T) by M(a_T). Its scalar map is the
   inclusion Q_R(T) into R(T), because a_T after (1,t) is the identity. Thus the
   identification and its inverse are linear. This supplies the natural linear unit.
6. Restriction at (1,s) preserves addition and sends projection-pullback(a) times x
   to a times its evaluation. Yoneda free evaluation makes it bijective. Cech
   recovery gives naturality, equivariance and the natural linear counit. All
   naturality equations are the identical section equations of the set-level maps.
-/
theorem profiniteAction_module_lift :
    ∃ D : LiftData J R, LiftProperties J R D := by
  sorry

end Profinite.CondensedAction.LinearDescent
