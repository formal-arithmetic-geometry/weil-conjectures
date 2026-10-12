/-
Copyright (c) 2026 SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.CategoryTheory.ColimitSites
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.CategoryTheory.ColimitSystemProductTransitions
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
  classical
  have _ := hfinite
  let A := fun j ↦ Injective.under (Fs j)
  let ι := fun j ↦ Injective.ι (Fs j)
  let R := fun {j k : J} (a : j ⟶ k) ↦
    (F.map a).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
      (P j).toGrothendieck (P k).toGrothendieck
  let E := fun j ↦ Functor.sheafPushforwardContinuousId'
    (eqToIso (congrArg Cat.Hom.toFunctor (F.map_id j)))
    AddCommGrpCat.{u} (P j).toGrothendieck
  let B := fun j ↦ ∏ᶜ fun t : Σ k : J, j ⟶ k ↦ (R t.2).obj (A t.1)
  let Gs := fun j ↦ A j ⨯ B j
  let γ := fun j ↦ prod.lift
    ((𝟙 (Fs j) - (φ (𝟙 j) ≫ (E j).hom.app (Fs j) : Fs j ⟶ Fs j)) ≫ ι j)
    (Pi.lift fun t : Σ k : J, j ⟶ k ↦ φ t.2 ≫ (R t.2).map (ι t.1))
  obtain ⟨ψ, hψ, hγ⟩ := exists_colimitSystem_product_transitions
    F (fun j ↦ (P j).toGrothendieck) Fs φ hφ A ι
  refine ⟨Gs, ψ, γ, ?_, ?_, hψ, hγ⟩
  · intro j
    have factors_injective (t : Σ k : J, j ⟶ k) : Injective ((R t.2).obj (A t.1)) := by
      obtain ⟨_, hlim, _⟩ := sitePullback_abelian_exact
        (P j) (P t.1) (F.map t.2).toFunctor
        (hcover j t.1 t.2) (hpullback j t.1 t.2)
      let := hlim
      let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (F.map t.2).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck (P t.1).toGrothendieck
      let := adj.preservesInjectiveObjects_of_preservesFiniteLimits
      exact Functor.injective_obj (R t.2) (A t.1)
    let := factors_injective
    dsimp [Gs, B]
    infer_instance
  · intro j
    let r : Gs j ⟶ A j := prod.fst +
      prod.snd ≫ Pi.π (fun t : Σ k : J, j ⟶ k ↦ (R t.2).obj (A t.1)) ⟨j, 𝟙 j⟩ ≫
        (E j).hom.app (A j)
    have hr : γ j ≫ r = ι j := by
      dsimp only [γ, r, Gs, B, A, R, ι]
      rw [Preadditive.comp_add]
      have hf : γ j ≫ (prod.fst : Gs j ⟶ A j) =
          (𝟙 (Fs j) - (φ (𝟙 j) ≫ (E j).hom.app (Fs j) : Fs j ⟶ Fs j)) ≫ ι j := by
        exact prod.lift_fst _ _
      change γ j ≫ (prod.fst : Gs j ⟶ A j) +
        (γ j ≫ prod.snd ≫ Pi.π _ ⟨j, 𝟙 j⟩ ≫
          (E j).hom.app (A j) : Fs j ⟶ A j) = ι j
      rw [hf]
      dsimp only [γ]
      rw [prod.lift_snd_assoc, Pi.lift_π_assoc]
      rw [Category.assoc, (E j).hom.naturality (ι j)]
      simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc, Functor.id_map]
      abel
    have : Mono (ι j) := inferInstance
    exact mono_of_mono_fac hr

end CategoryTheory
