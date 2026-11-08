/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import Submission.WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Generic constructibility and base change of a direct image

The property appearing in Deligne's generic constructibility theorem
(`thm-fin-deligne-generic-open`): over a subset `U` of the base `S`, the derived direct image
of a sheaf `F` along a morphism `j : X ⟶ Y` of `S`-schemes is bounded constructible, and its
formation commutes with every base change from a noetherian scheme
(`AlgebraicGeometry.Etale.HasConstructibleDirectImageBaseChangeOn`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Over a subset `U` of `S`, the derived direct image of the sheaf `F` along `j : X ⟶ Y`, for
`Y` over `S` via `fY`, is bounded constructible and its formation commutes with every base
change from a noetherian scheme: for every noetherian `T`, every `t : T ⟶ S` with image in `U`
and all cartesian squares

```
  X_T --g'--> X
   |          |
  j_T         j
   ↓          ↓
  Y_T --g---> Y
   |          |
  f_T         fY
   ↓          ↓
   T ---t---> S
```

the direct image `Rj_{T,*}(g'^* F)` is bounded constructible and the derived base change map
`g^* Rj_* F ⟶ Rj_{T,*} g'^* F` is an isomorphism. -/
def HasConstructibleDirectImageBaseChangeOn {S X Y : Scheme.{u}} (fY : Y ⟶ S) (j : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : Set S) : Prop :=
  ∀ (T : Scheme.{u}) [IsNoetherian T] (t : T ⟶ S), Set.range t ⊆ U →
    ∀ (YT XT : Scheme.{u}) (g : YT ⟶ Y) (fT : YT ⟶ T) (g' : XT ⟶ X) (jT : XT ⟶ YT),
      IsPullback g fT fY t → ∀ sq : IsPullback g' jT j g,
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) YT
          ((R((jT)_*[ModuleCat.{u + 1} Λ])).obj ((L((g')^*[ModuleCat.{u + 1} Λ])).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ∧
        IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))

variable {Λ}

end Etale

end AlgebraicGeometry
