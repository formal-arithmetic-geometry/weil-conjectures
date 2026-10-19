/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Pullback
import Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable
import Sheaf.CategoryTheory.Sites.LocalizedSetPullbackComparison
import Sheaf.CategoryTheory.Sites.LocalizedCommRingPullbackComparison
import Sheaf.CategoryTheory.Sites.LocalizedModulePullbackComparison

/-!
# Localization of ringed-site morphisms without extra covering axioms

Source: Stacks Project, Modules on Sites, Tag 04J0; Sites, Tag 03CF
(blueprint: lem-weil-pbc-localize-ringed-site-morphism).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {D C : Type u} [SmallCategory D] [SmallCategory C]
  {K : GrothendieckTopology D} {J : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous K J]
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf J CommRingCat.{u}}
  (a : R ⟶ (u.sheafPushforwardContinuous CommRingCat.{u} K J).obj S)

/-- The structural map on the slice, obtained by restricting every component of a.
Source: Stacks Tag 04J0 (blueprint: lem-weil-pbc-localize-ringed-site-morphism). -/
def localizedRingedSiteMap (V : D)
    [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))] :
    R.over V ⟶ ((Over.post (X := V) u).sheafPushforwardContinuous CommRingCat.{u}
      (K.over V) (J.over (u.obj V))).obj (S.over (u.obj V)) :=
  ⟨{ app T := a.hom.app (op T.unop.left)
     naturality _T _T' f := a.hom.naturality ((Over.forget V).op.map f) }⟩

/-- The same structural map on underlying ring sheaves; no scalar map is chosen.
Source: Stacks Tag 04J0 (blueprint: lem-weil-pbc-localize-ringed-site-morphism). -/
abbrev ringedSiteModuleMap :
    (sheafCompose K (forget₂ CommRingCat RingCat)).obj R ⟶
      (u.sheafPushforwardContinuous RingCat.{u} K J).obj
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) :=
  (sheafCompose K (forget₂ CommRingCat RingCat)).map a

-- Keep the original existential witness names in the unchanged statement.
set_option linter.unusedVariables false in
set_option maxHeartbeats 800000 in
-- The statement expands the set, ring and module comparison squares.
/-- The slice inverse image and restricted structural map give the canonical module square.
Source: Stacks Tags 04J0 and 03CF
(blueprint: lem-weil-pbc-localize-ringed-site-morphism).

Proof:
1. Identify sheaves on the slice with objects over the sheafified representable.
The inverse image takes the sheafified representable of V to that of u(V), by the
sheaf adjunction and Yoneda. Finite-limit preservation gives the induced geometric
morphism of slices and the inverse-image comparison.
2. Apply the comparison to R and then restrict its structural map. Adjunction gives
localizedRingedSiteMap: at T -> V its component is exactly a at T.
3. The induced module direct images both evaluate G at u(T), with the same scalar
action, so their comparison is identity on every section. Tensor pullback and the
module adjunction give the inverse-image module comparison. The inverse-adjunct
identity follows on a generator r tensor x, where both sides give r times h(x).
No closure under arbitrarily repeated covering indices is required. -/
theorem localize_ringed_site_morphism_general
    [PreservesFiniteLimits (u.sheafPullback (Type u) K J)] (V : D) :
    ∃ hc : (Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V)),
      ∃ hl : PreservesFiniteLimits
        ((Over.post (X := V) u).sheafPullback (Type u) (K.over V) (J.over (u.obj V))),
        ∃ es : K.overPullback (Type u) V ⋙
            (Over.post (X := V) u).sheafPullback (Type u) (K.over V) (J.over (u.obj V)) ≅
            u.sheafPullback (Type u) K J ⋙ J.overPullback (Type u) (u.obj V),
          ∃ er : K.overPullback CommRingCat.{u} V ⋙
              (Over.post (X := V) u).sheafPullback CommRingCat.{u}
                (K.over V) (J.over (u.obj V)) ≅
              u.sheafPullback CommRingCat.{u} K J ⋙
                J.overPullback CommRingCat.{u} (u.obj V),
            ((Over.post (X := V) u).sheafAdjunctionContinuous CommRingCat.{u}
              (K.over V) (J.over (u.obj V))).homEquiv (R.over V) (S.over (u.obj V))
                (er.hom.app R ≫ (J.overPullback CommRingCat.{u} (u.obj V)).map
                  (((u.sheafAdjunctionContinuous CommRingCat.{u} K J).homEquiv R S).symm a)) =
              localizedRingedSiteMap u a V ∧
            ∃ (lambda : overFunctor ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) V ⋙
                pullback (ringedSiteModuleMap (Over.post (X := V) u)
                  (localizedRingedSiteMap u a V)) ≅
                pullback (ringedSiteModuleMap u a) ⋙
                  overFunctor ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (u.obj V))
              (beta : pushforward (ringedSiteModuleMap u a) ⋙
                  overFunctor ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) V ≅
                overFunctor ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (u.obj V) ⋙
                  pushforward (ringedSiteModuleMap (Over.post (X := V) u)
                    (localizedRingedSiteMap u a V))),
              (∀ (G : SheafOfModules.{u}
                  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
                (T : Over V) (x : G.val.obj (op (u.obj T.left))),
                (beta.hom.app G).val.app (op T) x = x) ∧
              ∀ (A : SheafOfModules.{u}
                  ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))
                (B : SheafOfModules.{u}
                  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
                (h : A ⟶ (pushforward (ringedSiteModuleMap u a)).obj B),
                lambda.hom.app A ≫
                    (overFunctor ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
                      (u.obj V)).map
                        (((pullbackPushforwardAdjunction (ringedSiteModuleMap u a)).homEquiv
                          A B).symm h) =
                  ((pullbackPushforwardAdjunction
                    (ringedSiteModuleMap (Over.post (X := V) u)
                      (localizedRingedSiteMap u a V))).homEquiv _ _).symm
                    ((overFunctor ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) V).map
                      h ≫ beta.hom.app B) := by
  let hc := overPost_isContinuous K J u V
  let hl := sliceSetPullback_preservesFiniteLimits (K := K) (J := J) u V
  let := sliceSetPullbackMap_isIso (K := K) (J := J) u V
  let es := asIso (sliceSetPullbackMap (K := K) (J := J) u V)
  let := sliceCommRingPullbackMap_isIso (K := K) (J := J) u V
  let er := asIso (sliceCommRingPullbackMap (K := K) (J := J) u V)
  let := sliceModulePullbackMap_isIso u a V
  let lambda := asIso (sliceModulePullbackMap u (ringedSiteModuleMap u a) V)
  let beta := sliceModulePushforwardIso u (ringedSiteModuleMap u a) V
  refine ⟨hc, hl, es, er, ?_, lambda, beta, ?_, ?_⟩
  · exact sliceCommRingPullbackMap_adjunct u V a
  · intro G T x
    rfl
  · intro A B h
    exact sliceModulePullbackMap_adjunct u (ringedSiteModuleMap u a) V A B h

end SheafOfModules
