/-
Copyright (c) 2026 SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.CategoryTheory.ColimitSites
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Injective systems on a filtered colimit of sites

Source: Stacks Project, Sites, Lemma 0EXZ (lemma-colim-sites-injective).
(blueprint: lem-weil-pbc-colimit-of-sites-injective-system)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A compatible system of abelian sheaves on the sites in a filtered diagram embeds
into a compatible system of injective sheaves.

The maps in the system are written in transposed form, using the right adjoints
`sheafPushforwardContinuous`; the transpose is under `sheafAdjunctionContinuous`.
The comparison isomorphisms in the cocycle are those supplied by
`sheafPushforwardContinuousComp'` and `F.map_comp`.
Source: Stacks Project, Sites, Lemma 0EXZ.
(blueprint: lem-weil-pbc-colimit-of-sites-injective-system)

Proof: choose an injective embedding at each index and take the product of all
pushforwards of these embeddings. Exactness of inverse image and the adjoint
criterion make every factor injective, and products of injectives are injective.
The transition maps are induced by composition of arrows; the comparison
isomorphisms give the cocycle, and the identity component gives monomorphisms.

Step 1 (lem-weil-pbc-site-sheaves-enough-injectives): for each `j`, choose an
injective object `A j` and a monomorphism `Fs j ⟶ A j`.
Step 2 (lem-sp-right-adjoint-preserves-injectives and
lem-weil-pbc-product-injectives): for each arrow `b : k ⟶ j`, the exact inverse
image and its right adjoint make the pushed-forward factor injective; their
product is therefore injective.
Step 3 (lem-weil-pbc-colimit-of-sites and
def-weil-pbc-sites-and-cohomology): define each transition map componentwise by
composition of arrows and the inverse-image/pushforward adjunction; the
comparison isomorphism supplied by `F.map_comp` gives its cocycle.
Step 4 (lem-weil-pbc-colimit-of-sites): adjunction naturality makes the chosen
monomorphisms compatible, and the identity-arrow component proves each `γ j`
is mono.
-/
theorem exists_compatible_injective_system
    (J : Type u) [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Cat.{u, u}) (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos] [∀ j, (P j).IsStableUnderComposition]
    [∀ j, (P j).IsStableUnderBaseChange] [∀ j, (P j).HasPullbacks]
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k
        ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j)
      (R : Presieve X), R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck
        (P k).toGrothendieck]
    [∀ (j k : J) (a : j ⟶ k),
      PreservesFiniteLimits
        (Functor.sheafPullbackConstruction.sheafPullback (F.map a).toFunctor
          (Type u) (P j).toGrothendieck (P k).toGrothendieck)]
    [∀ (j k : J) (a : j ⟶ k),
      PreservesFiniteColimits
        (Functor.sheafPullbackConstruction.sheafPullback (F.map a).toFunctor
          (Type u) (P j).toGrothendieck (P k).toGrothendieck)]
    (Fs : ∀ j : J, Sheaf (P j).toGrothendieck AddCommGrpCat.{u})
    (φ : ∀ {j k : J} (a : j ⟶ k),
      Fs j ⟶ ((F.map a).toFunctor.sheafPushforwardContinuous
        AddCommGrpCat.{u} (P j).toGrothendieck (P k).toGrothendieck).obj (Fs k))
    (hφ : ∀ {j k l : J} (a : j ⟶ k) (b : k ⟶ l),
      φ (a ≫ b) = φ a ≫
        ((F.map a).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
          (P j).toGrothendieck (P k).toGrothendieck).map (φ b) ≫
        (Functor.sheafPushforwardContinuousComp'
          (eqToIso (congrArg Cat.Hom.toFunctor (F.map_comp a b).symm)) AddCommGrpCat.{u}
          (P j).toGrothendieck (P k).toGrothendieck (P l).toGrothendieck).hom.app (Fs l)) :
    ∃ (Gs : ∀ j : J, Sheaf (P j).toGrothendieck AddCommGrpCat.{u})
      (ψ : ∀ {j k : J} (a : j ⟶ k),
        Gs j ⟶ ((F.map a).toFunctor.sheafPushforwardContinuous
          AddCommGrpCat.{u} (P j).toGrothendieck (P k).toGrothendieck).obj (Gs k))
      (γ : ∀ j : J, Fs j ⟶ Gs j),
      (∀ j : J, Injective (Gs j)) ∧
      (∀ j : J, Mono (γ j)) ∧
      (∀ {j k l : J} (a : j ⟶ k) (b : k ⟶ l),
        ψ (a ≫ b) = ψ a ≫
          ((F.map a).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
            (P j).toGrothendieck (P k).toGrothendieck).map (ψ b) ≫
          (Functor.sheafPushforwardContinuousComp'
            (eqToIso (congrArg Cat.Hom.toFunctor (F.map_comp a b).symm)) AddCommGrpCat.{u}
            (P j).toGrothendieck (P k).toGrothendieck (P l).toGrothendieck).hom.app (Gs l)) ∧
      (∀ {j k : J} (a : j ⟶ k),
        φ a ≫
            ((F.map a).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
              (P j).toGrothendieck (P k).toGrothendieck).map (γ k) =
          γ j ≫ ψ a) := by
  sorry

end CategoryTheory
