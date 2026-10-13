/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Compatibility of the pullback stalk comparison with change of lift

Source: Stacks Project, Tag 03QW, equation 59.56.0.1 and Remark 59.56.6,
and Tag 03Q1, Lemma 59.36.2(3).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

/-- The canonical pullback stalk comparison commutes with endomorphisms that change
represented lifts by the same endomorphism of the geometric point.

Source: Stacks Project, Tag 03QW, equation 59.56.0.1 and Remark 59.56.6;
Tag 03Q1, Lemma 59.36.2(3).
(blueprint: lem-sc-pullback-stalk-germ-action)

Proof: Precomposing every pointed lift with tau defines endomorphisms of the two
point fibre functors, because tau fixes s and hence t. Their maps on stalk colimits
send the germ of z at x to the germ of z at tau followed by x. The two supplied
endomorphisms equal these maps, since every stalk element is a represented germ.
The base-change identification of fibre functors is natural for these endomorphisms:
the lift (x,s) into a fibre product is carried to (tau followed by x,s), since
tau followed by s equals s. The sheaf pullback/stalk comparison is the mate of the
corresponding identification of skyscraper pushforwards. Naturality of mates gives
the commuting square on stalks; composing with the equality s followed by f = t
preserves that square. This proves the stated equality. The proof needs neither
invertibility of tau nor any Galois or field-equivalence hypothesis. -/
theorem exists_etale_pullback_stalk_germ_action
    {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (t : Spec (.of Ω) ⟶ Y) (hst : s ≫ f = t)
    (M : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ∃ j : (pointSmallEtale s).sheafFiber.obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj M) ≅
      (pointSmallEtale t).sheafFiber.obj M,
    ∀ (τ : Spec (.of Ω) ⟶ Spec (.of Ω)) (_hτs : τ ≫ s = s)
    (a : ((pointSmallEtale s).sheafFiber.obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj M)) ⟶
      ((pointSmallEtale s).sheafFiber.obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj M)))
    (b : (pointSmallEtale t).sheafFiber.obj M ⟶
      (pointSmallEtale t).sheafFiber.obj M)
    (ha : ∀ (U : X.Etale) (x x' : (pointSmallEtale s).fiber.obj U)
      (_hx : x'.left = τ ≫ x.left)
      (z : ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj M).obj.obj (op U)),
      a ((pointSmallEtale s).toPresheafFiber U x
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj M).obj z) =
      (pointSmallEtale s).toPresheafFiber U x'
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj M).obj z)
    (hb : ∀ (U : Y.Etale) (x x' : (pointSmallEtale t).fiber.obj U)
      (_hx : x'.left = τ ≫ x.left) (z : M.obj.obj (op U)),
      b ((pointSmallEtale t).toPresheafFiber U x M.obj z) =
      (pointSmallEtale t).toPresheafFiber U x' M.obj z),
    j.hom ≫ b = a ≫ j.hom := by sorry

end AlgebraicGeometry.Scheme
