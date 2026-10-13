/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackComposition

/-! # Localization of the canonical homotopy pullback square

Source: Stacks Project, Tags 0D5S and 0DVC.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry
noncomputable section

/-- The canonical pullback square, descended termwise to homotopy categories.
Its composition comparisons are conjugate to the recorded pushforward comparisons.
Source: Stacks Project, Tag 0D5S.
(blueprint: lem-pc-homotopy-pullback-square-localization). -/
def moduleHomotopyPullbackSquare
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g)
    [(Scheme.Modules.tensorPullback f).Additive]
    [(Scheme.Modules.tensorPullback f').Additive]
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback p).Additive] :
    (Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ) ⋙
        (Scheme.Modules.tensorPullback f').mapHomotopyCategory (.up ℤ) ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ) ⋙
        (Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ) := by
  let adj := fun {A B : Scheme.{u}} (k : A ⟶ B) ↦
    Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)
  let c := fun {A B C : Scheme.{u}} (k : A ⟶ B) (l : B ⟶ C) ↦
    (conjugateIsoEquiv (adj (k ≫ l)) ((adj l).comp (adj k))).symm
      (Scheme.Modules.pushforwardComp k l).symm
  let t := c f' g ≪≫
    eqToIso (congrArg Scheme.Modules.tensorPullback h.symm) ≪≫ (c p f).symm
  exact (Functor.mapHomotopyCategoryCompIso t (.up ℤ)).hom ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl
      (Scheme.Modules.tensorPullback f ⋙ Scheme.Modules.tensorPullback p)) (.up ℤ)).inv

/-- Localization carries the canonical pullback square to the pinned derived square,
including the left-derived counits and any map out of the ordinary pullback.
There are no pushforward units, derived adjunctions or acyclicity hypotheses here.
Source: Stacks Project, Tag 0D5S, compatibility of composite derived pullbacks;
Tag 0DVC, compatibility with localization.
(blueprint: lem-pc-homotopy-pullback-square-localization).

Proof: The defining left-derived lift factorization for c(f',g) identifies its
composite with the counit for f' g with Lf'(delta_g) followed by delta_f' and
localization of the ordinary composition comparison. Apply the same factorization
to c(p,f), and cancel its invertible component to express its inverse followed by
Lp(delta_f) and delta_p. Transport the composite counit across p f = f' g;
equality elimination identifies both transports. Compose the two factorizations:
the ordinary comparisons combine into moduleHomotopyPullbackSquare. Finally use
naturality of delta_p at a and functoriality of Qh to move the localized a to the
right. This is an identity of natural transformations, so it applies to arbitrary
M, K and a, including zero complexes and identity squares. -/
theorem homotopyPullbackSquare_localization
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g)
    [(Scheme.Modules.tensorPullback f).Additive]
    [(Scheme.Modules.tensorPullback f').Additive]
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback p).Additive]
    (M : HomotopyCategory S.Modules (.up ℤ))
    (K : HomotopyCategory X.Modules (.up ℤ))
    (a : ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ)).obj M ⟶ K) :
    let ε := @Classical.choose _ _ (Classical.choose_spec
      exists_derivedPullbackComposition.{u, w})
    let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
    (c f' g).hom.app (DerivedCategory.Qh.obj M) ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj (DerivedCategory.Qh.obj M)) h.symm) ≫
      (c p f).inv.app (DerivedCategory.Qh.obj M) ≫
      (derivedPullback p).map ((ε f).app M ≫ DerivedCategory.Qh.map a) ≫
      (ε p).app K =
    (derivedPullback f').map ((ε g).app M) ≫
      (ε f').app
        (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj M) ≫
      DerivedCategory.Qh.map ((moduleHomotopyPullbackSquare f f' g p h).app M ≫
        ((Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ)).map a) := by sorry

end
end AlgebraicGeometry
