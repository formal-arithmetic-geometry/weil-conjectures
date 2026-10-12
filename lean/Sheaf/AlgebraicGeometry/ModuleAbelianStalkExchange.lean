/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import Sheaf.AlgebraicGeometry.DerivedExchangeTermwise
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic
import Sheaf.AlgebraicGeometry.ModuleAbelianInverseImageComparison
import Sheaf.Paper.HigherDirectImageSheafifiedPresheaf
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Module and abelian stalk exchange comparison

Source: Stacks Project, Tags 03FD, 0736 and 07A7.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

/-- Forgetting module coefficients commutes with the stalk of the derived exchange.
This comparison concerns an arbitrary cartesian square and an arbitrary geometric
point of its lower-left scheme; it does not identify either side with total-space
cohomology and requires no strict-local hypothesis.

Source: Stacks Project, Tag 03FD (module/abelian acyclic comparison), together
with the termwise mate construction of Tag 0736 and Remark 07A7.
(blueprint: lem-weil-pbc-module-abelian-stalk-exchange)

Proof: resolve F by a bounded below complex of injective module sheaves I.
The underlying abelian terms are acyclic for evaluation on every etale object,
by Tag 03FD. They are therefore acyclic for direct image, whose higher derived
images are the sheafifications of these objectwise cohomology groups. Forgetting
coefficients is exact and commutes with inverse image and with stalks (the
filtered colimit is computed on underlying groups). The acyclic-resolution
comparison thus identifies the source homology stalk with the abelian source.
Choose an injective module replacement J of g'^* I. The same argument for J,
and exactness of inverse image, gives the target comparison. To compare maps,
forget the termwise exchange followed by f'_* of I → J. Underived inverse image
and direct image comparisons preserve units, the square isomorphism and
counits, so this is the abelian termwise mate. Comparing the underlying acyclic
complexes to injective abelian resolutions gives the abelian derived exchange;
homotopy uniqueness shows the comparisons commute with this map. Take degree q
homology and the exact stalk. No claim that forgetting preserves injectives is
used. -/
theorem Etale.exists_addEquiv_module_abelian_stalk_exchange
    (Λ : Type (u + 1)) [CommRing Λ]
    {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y')
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    let G := (sheafCompose _
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let S := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((R+((f)_*[AddCommGrpCat.{u + 1}]) ⋙
        D+((g)^*[AddCommGrpCat.{u + 1}])).obj K)
    let T := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙
        R+((f')_*[AddCommGrpCat.{u + 1}])).obj K)
    let e := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K)
    ∃ (b₁ : (((pointSmallEtale t).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeSourceFunctor Λ g f q).obj F)) ≃+
        (((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj S))
      (b₂ : (((pointSmallEtale t).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeTargetFunctor Λ g' f' q).obj F)) ≃+
        (((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj T)),
      ∀ x, b₂ ((((pointSmallEtale t).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).map
          (Etale.baseChangeHomologyMap Λ sq q F)).hom x) =
        ((((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).map e).hom (b₁ x)) := by
  sorry

end AlgebraicGeometry
