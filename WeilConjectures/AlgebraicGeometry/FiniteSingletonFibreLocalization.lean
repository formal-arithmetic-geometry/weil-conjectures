/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-!
# Neighbourhoods and module stalks at a singleton finite fibre

Source: Stacks Project, More on Morphisms, Tag 05B8,
`lemma-finite-morphism-single-point-in-fibre`, assertions (1) and (4).
(blueprint: lem-trf-finite-singleton-fibre-localization).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A singleton finite fibre has cofinal inverse-image neighbourhoods, and the canonical
pushforward germ map is an isomorphism linear over the target local ring via `π.stalkMap z`.
The underlying map is Mathlib's `stalkPushforward`, not an unspecified isomorphism.
Source: Stacks Project, More on Morphisms, Tag 05B8,
`lemma-finite-morphism-single-point-in-fibre`, assertions (1) and (4).
(blueprint: lem-trf-finite-singleton-fibre-localization).

Proof:
1. By lem-weil-pbc-finite-iff-integral-lft and pqf-lem-integral-univclosed, π is
   integral and closed. For an open U containing z, remove the closed image of Z \ U.
   Its complement V contains π z because the fibre is {z}, and π⁻¹V is contained in U.
2. Use the alternative proof at the end of Stacks Tag 05B8: represent a source
   stalk element by a section on U and restrict it to π⁻¹V as in step 1. Its
   pushforward germ maps to the original germ, proving surjectivity. For injectivity,
   two source germs agree on some W. Choose Q with π⁻¹Q contained in W and intersect
   Q with both target neighbourhoods. The two pushforward sections agree there,
   so their germs agree. Thus the canonical stalkPushforward is an isomorphism.
3. Represent a target-ring scalar and a pushforward-module element by sections on
   a common target neighbourhood. Apply germ_smul on the pushforward, the canonical
   stalkPushforward germ formula, and germ_smul on the source. The ring germ formula
   Scheme.Hom.germ_stalkMap_apply identifies the scalar with its image under
   π.stalkMap z, proving precisely the displayed scalar compatibility. -/
theorem finite_singleton_fibre_neighbourhoods_and_module_stalk
    {Z Y : Scheme.{u}} (π : Z ⟶ Y) [IsFinite π] (z : Z)
    (_hfibre : π ⁻¹' ({π z} : Set Y) = ({z} : Set Z)) :
    (∀ U : Z.Opens, z ∈ U → ∃ V : Y.Opens, π z ∈ V ∧ π ⁻¹ᵁ V ≤ U) ∧
    (∀ G : Z.Modules, G.IsQuasicoherent →
      IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} π.base G.presheaf z) ∧
      ∀ (r : Y.presheaf.stalk (π z))
        (m : (RingedSpace.moduleStalkFunctor Y.toRingedSpace (π z)).obj
          ((pushforward π).obj G)),
        TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} π.base G.presheaf z (r • m) =
          (π.stalkMap z).hom r •
            (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} π.base G.presheaf z m :
              (RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj G)) := by
  have hnbhd : ∀ U : Z.Opens, z ∈ U →
      ∃ V : Y.Opens, π z ∈ V ∧ π ⁻¹ᵁ V ≤ U := by
    intro U hzU
    let V : Y.Opens := ⟨(π '' (U : Set Z)ᶜ)ᶜ,
      (π.isClosedMap _ U.isOpen.isClosed_compl).isOpen_compl⟩
    refine ⟨V, ?_, ?_⟩
    · rintro ⟨w, hw, heq⟩
      have hwz : w = z := by
        have : w ∈ π ⁻¹' ({π z} : Set Y) := heq
        rw [_hfibre] at this
        exact this
      exact hw (hwz ▸ hzU)
    · intro w hw
      by_contra hwU
      exact hw ⟨w, hwU, rfl⟩
  refine ⟨hnbhd, fun G _hqc ↦ ⟨?_, ?_⟩⟩
  · let F := (TopCat.Presheaf.pushforward Ab π.base).obj G.presheaf
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · intro a b hab
      obtain ⟨U, hzU, s, rfl⟩ := F.exists_germ_eq a
      obtain ⟨V, hzV, t, rfl⟩ := F.exists_germ_eq b
      change TopCat.Presheaf.stalkPushforward Ab π.base G.presheaf z
          (F.germ U (π z) hzU s) =
        TopCat.Presheaf.stalkPushforward Ab π.base G.presheaf z
          (F.germ V (π z) hzV t) at hab
      dsimp only [F] at hab
      erw [TopCat.Presheaf.stalkPushforward_germ_apply,
        TopCat.Presheaf.stalkPushforward_germ_apply] at hab
      obtain ⟨W, hzW, iU, iV, heq⟩ := G.presheaf.germ_eq z hzU hzV s t hab
      obtain ⟨Q, hzQ, hQ⟩ := hnbhd W hzW
      let R := Q ⊓ U ⊓ V
      have hzR : π z ∈ R := ⟨⟨hzQ, hzU⟩, hzV⟩
      let jU : R ⟶ U := homOfLE (inf_le_left.trans inf_le_right)
      let jV : R ⟶ V := homOfLE inf_le_right
      let k : π ⁻¹ᵁ R ⟶ W := homOfLE
        ((show π ⁻¹ᵁ R ≤ π ⁻¹ᵁ Q from fun _ hw ↦ hw.1.1).trans hQ)
      have heq' : F.map jU.op s = F.map jV.op t := by
        change G.presheaf.map ((TopologicalSpace.Opens.map π.base).map jU).op s =
          G.presheaf.map ((TopologicalSpace.Opens.map π.base).map jV).op t
        have hU : iU.op ≫ k.op = ((TopologicalSpace.Opens.map π.base).map jU).op :=
          Subsingleton.elim _ _
        have hV : iV.op ≫ k.op = ((TopologicalSpace.Opens.map π.base).map jV).op :=
          Subsingleton.elim _ _
        simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, hU, hV] using
          congrArg (G.presheaf.map k.op) heq
      rw [← F.germ_res_apply jU (π z) hzR s,
        ← F.germ_res_apply jV (π z) hzR t, heq']
    · intro m
      obtain ⟨U, hzU, s, rfl⟩ := G.presheaf.exists_germ_eq m
      obtain ⟨V, hzV, hV⟩ := hnbhd U hzU
      refine ⟨F.germ V (π z) hzV (G.presheaf.map (homOfLE hV).op s), ?_⟩
      dsimp only [F]
      erw [TopCat.Presheaf.stalkPushforward_germ_apply]
      exact G.presheaf.germ_res_apply (homOfLE hV) z hzV s
  · intro r m
    obtain ⟨U, hzU, r, rfl⟩ := Y.presheaf.exists_germ_eq r
    obtain ⟨V, hVU, hzV, m, rfl⟩ :=
      ((pushforward π).obj G).presheaf.exists_le_germ_eq m hzU
    rw [← Y.presheaf.germ_res_apply (homOfLE hVU) (π z) hzV r]
    erw [← PresheafOfModules.germ_smul ((pushforward π).obj G).val]
    erw [TopCat.Presheaf.stalkPushforward_germ_apply,
      TopCat.Presheaf.stalkPushforward_germ_apply]
    change TopCat.Presheaf.germ G.val.presheaf (π ⁻¹ᵁ V) z hzV
        ((π.app V).hom (Y.presheaf.map (homOfLE hVU).op r) •
          (show G.presheaf.obj (Opposite.op (π ⁻¹ᵁ V)) from m)) = _
    erw [PresheafOfModules.germ_smul G.val]
    rw [Scheme.Hom.germ_stalkMap_apply]
    rfl

end AlgebraicGeometry.Scheme.Modules
