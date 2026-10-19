/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafOperations

import Sheaf.AlgebraicGeometry.ProEtaleRingSheafClosedLocalization
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafBaseChangeMates
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful

/-!
# Open–closed localization with arbitrary ring-sheaf coefficients

Source: blueprint `det-sf-open-closed-sequence-ring-sheaf`, clauses (1)–(4);
Stacks Project, Tags 09AA, 09BM, 09BN, 09AH, 09AG, 03D3, 03DI and 03DJ
(blueprint: det-sf-open-closed-sequence-ring-sheaf).

A ring sheaf is a monoid object in abelian sheaves, without a commutativity assumption.
Its modules are the existing `Mod` objects, as in `closed_inverseImage_preserves_limits`.
The helpers specialize the published module-object functors and adjunctions to these
coefficients. Base-change coefficient transport uses the specified composition isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

set_option maxHeartbeats 400000 in
-- Comparing transported module structures needs additional elaboration heartbeats.
set_option linter.unusedVariables false in
/-- The open–closed sequence over an arbitrary ring sheaf, and canonical base change.
The square restriction comparisons are normalized on underlying sheaves. The open
comparison is characterized by its transpose of the open unit; the closed comparison
by its transpose of the closed counit. The final two equations identify both sequence
arrows, rather than merely identifying its three terms.

Source: blueprint `det-sf-open-closed-sequence-ring-sheaf`, clauses (1)–(4);
Stacks, Tags 09AA, 09BM, 09BN, 09AH, 09AG, 03D3, 03DI, 03DJ, 03CB and 03CC
(blueprint: det-sf-open-closed-sequence-ring-sheaf).

Proof:
1. Apply inverse image to the ring operations and module actions. Direct image is
   evaluation on fibre products with its scalar action through the ring unit. Identify
   the open site with the localized site by lem-weil-proetale-weakly-etale-localization.
   The sheafification of def-weil-extension-by-zero-presheaf is the open extension.
   Forgetting actions preserves and reflects kernels, cokernels and isomorphisms by
   lem-weil-pbc-module-sheaves-colimits-forgetful, so exactness can be checked there.
2. The abelian inverse/direct-image Hom bijection restricts to linear maps: naturality
   of its unit on the action map identifies the two linearity equations, in both
   directions. This is the displayed lifted adjunction, including its actual maps.
3. Apply lem-weil-pbc-proetale-ringed-open-closed with the constant integer ring sheaf
   to obtain the abelian localization statements. Every abelian sheaf has its canonical
   integer action. The open unit and closed counit are the actual adjunction maps:
   use the localization sequence on j_!N and i_*G and their triangle identities.
4. The extension-presheaf Hom bijection and module sheafification give the open module
   adjunction. Its carrier is the abelian extension by zero, so it is exact and its
   unit is invertible. Inverse image is exact on carriers by
   lem-weil-pbc-site-pullback-abelian-exact, hence on these module categories.
5. Reflect the abelian closed counit, exactness and vanishing through the forgetful
   functor. The resulting counit–unit sequence is short exact. It also shows that open
   and closed restriction jointly detect zero objects and isomorphisms, by applying
   exact restriction to kernels and cokernels.
6. Base change preserves open and closed immersions and quasi-compactness of j, by
   lem-weil-pbc-open-immersion-base-change, lem-weil-pbc-closed-immersion-base-change
   and lem-pc-quasi-compact-base-change. The pulled-back immersions are complementary.
   The adjunction-compatible composition comparison of
   lem-weil-pbc-site-morphism-composition respects actions and gives delta and gamma.
7. Sectionwise j^*g_* = g_U* j'^* yields open base change by the composite adjunction
   Hom bijections. Its inverse is exactly the transpose of the pulled-back open unit
   written below; naturality gives inverse isomorphisms.
8. Define closed base change as the transpose of gamma followed by the pulled-back
   closed counit. Its open restriction has zero source and target. Its closed
   restriction is invertible by the counit equation and invertible closed counits.
   Joint detection from step 5 proves it is invertible for arbitrary g.
9. Under the same adjunction Hom bijections, the two open sequence maps have the same
   transpose by the triangle identities and step 7. For the closed maps, the counit
   equation of step 8 and the closed triangle identity give the same transpose gamma.
   These are the last two equations. Exactness of g^* therefore carries the entire
   short exact sequence to that for g^*M, with the specified arrows.
-/
theorem proEtale_openClosed_sequence_ring_sheaf
    {X Z U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [QuasiCompact j] (_hU : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    PreservesFiniteLimits (ringSheafInverseImage j B) ∧
    PreservesFiniteColimits (ringSheafInverseImage j B) ∧
    PreservesFiniteLimits (ringSheafOpenExtension j B) ∧
    PreservesFiniteColimits (ringSheafOpenExtension j B) ∧
    (∀ N, IsIso ((ringSheafOpenAdjunction j B).unit.app N)) ∧
    PreservesFiniteLimits (ringSheafDirectImage i B) ∧
    PreservesFiniteColimits (ringSheafDirectImage i B) ∧
    (∀ G, IsIso ((ringSheafAdjunction i B).counit.app G)) ∧
    (∀ G, IsZero ((ringSheafInverseImage j B).obj ((ringSheafDirectImage i B).obj G))) ∧
    (∀ M, Mono ((ringSheafOpenAdjunction j B).counit.app M) ∧
      Epi ((ringSheafAdjunction i B).unit.app M) ∧
      (ComposableArrows.mk₂ ((ringSheafOpenAdjunction j B).counit.app M)
        ((ringSheafAdjunction i B).unit.app M)).Exact) ∧
    (∀ {X' : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X'] (g : X' ⟶ X),
      Exists fun [hu : IsMonHom (ringSheafSquareCoefficient g j B)] ↦
      Exists fun [hz : IsMonHom (ringSheafSquareCoefficient g i B)] ↦
      ∃ delta : ringSheafInverseImage g B ⋙
            ringSheafInverseImage (pullback.fst g j) ((upperStar Ab.{u + 1} g).obj B) ≅
          ringSheafInverseImage j B ⋙ ringSheafSquarePullback g j B,
      ∃ gamma : ringSheafInverseImage g B ⋙
            ringSheafInverseImage (pullback.fst g i) ((upperStar Ab.{u + 1} g).obj B) ≅
          ringSheafInverseImage i B ⋙ ringSheafSquarePullback g i B,
        (∀ M, (delta.hom.app M).hom = (ringSheafSquareComparison g j).hom.app M.X) ∧
        (∀ M, (gamma.hom.app M).hom = (ringSheafSquareComparison g i).hom.app M.X) ∧
        (∀ M, Mono ((ringSheafOpenAdjunction (pullback.fst g j)
              ((upperStar Ab.{u + 1} g).obj B)).counit.app
                ((ringSheafInverseImage g B).obj M)) ∧
          Epi ((ringSheafAdjunction (pullback.fst g i)
              ((upperStar Ab.{u + 1} g).obj B)).unit.app
                ((ringSheafInverseImage g B).obj M)) ∧
          (ComposableArrows.mk₂
            ((ringSheafOpenAdjunction (pullback.fst g j)
              ((upperStar Ab.{u + 1} g).obj B)).counit.app
                ((ringSheafInverseImage g B).obj M))
            ((ringSheafAdjunction (pullback.fst g i)
              ((upperStar Ab.{u + 1} g).obj B)).unit.app
                ((ringSheafInverseImage g B).obj M))).Exact) ∧
        ∃ alpha : ringSheafOpenExtension j B ⋙ ringSheafInverseImage g B ≅
            ringSheafSquarePullback g j B ⋙
              ringSheafOpenExtension (pullback.fst g j) ((upperStar Ab.{u + 1} g).obj B),
        ∃ beta : ringSheafDirectImage i B ⋙ ringSheafInverseImage g B ≅
            ringSheafSquarePullback g i B ⋙
              ringSheafDirectImage (pullback.fst g i) ((upperStar Ab.{u + 1} g).obj B),
          (∀ N, (ringSheafOpenAdjunction (pullback.fst g j)
                ((upperStar Ab.{u + 1} g).obj B)).homEquiv _ _ (alpha.inv.app N) =
            (ringSheafSquarePullback g j B).map ((ringSheafOpenAdjunction j B).unit.app N) ≫
              delta.inv.app ((ringSheafOpenExtension j B).obj N)) ∧
          (∀ G, ((ringSheafAdjunction (pullback.fst g i)
                ((upperStar Ab.{u + 1} g).obj B)).homEquiv _ _).symm (beta.hom.app G) =
            gamma.hom.app ((ringSheafDirectImage i B).obj G) ≫
              (ringSheafSquarePullback g i B).map ((ringSheafAdjunction i B).counit.app G)) ∧
          (∀ M, (ringSheafInverseImage g B).map ((ringSheafOpenAdjunction j B).counit.app M) =
            alpha.hom.app ((ringSheafInverseImage j B).obj M) ≫
              (ringSheafOpenExtension (pullback.fst g j)
                ((upperStar Ab.{u + 1} g).obj B)).map (delta.inv.app M) ≫
              (ringSheafOpenAdjunction (pullback.fst g j)
                ((upperStar Ab.{u + 1} g).obj B)).counit.app
                  ((ringSheafInverseImage g B).obj M)) ∧
          (∀ M, (ringSheafInverseImage g B).map ((ringSheafAdjunction i B).unit.app M) ≫
              beta.hom.app ((ringSheafInverseImage i B).obj M) =
            (ringSheafAdjunction (pullback.fst g i)
                ((upperStar Ab.{u + 1} g).obj B)).unit.app
                  ((ringSheafInverseImage g B).obj M) ≫
              (ringSheafDirectImage (pullback.fst g i)
                ((upperStar Ab.{u + 1} g).obj B)).map (gamma.hom.app M))) := by
  obtain ⟨hcol, hc, hz, hs⟩ := ringSheaf_closed_localization i j _hU B
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_, ?_, hcol, hc, hz, hs, ?_⟩
  · have : (ringSheafOpenExtension j B).IsLeftAdjoint :=
      (ringSheafOpenAdjunction j B).isLeftAdjoint
    infer_instance
  · intro N
    have h : IsIso ((Mod.forget _).map ((ringSheafOpenAdjunction j B).unit.app N)) := by
      change IsIso (((ringSheafOpenAdjunction j B).unit.app N).hom)
      simp only [ringSheafOpenAdjunction, Adjunction.mapModLeftAdjunction,
        Adjunction.mkOfHomEquiv_unit_app]
      change IsIso ((openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).homEquiv _ _
        (𝟙 ((openImmersionLowerShriek Ab.{u + 1} j).obj N.X)))
      rw [Adjunction.homEquiv_id]
      have := Adjunction.unit_isIso_of_L_fully_faithful
        (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j)
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  · have : (ringSheafDirectImage i B).IsRightAdjoint :=
      (ringSheafAdjunction i B).isRightAdjoint
    infer_instance
  · intro X' _ _ g
    obtain ⟨hu, hz', delta, gamma, hd, hg, alpha, beta, ha, hb⟩ :=
      ringSheaf_baseChange_mates i j _hU B g
    have := hu
    have := hz'
    have hU' : Set.range (pullback.fst g j) = (Set.range (pullback.fst g i))ᶜ := by
      rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst, _hU]
      rfl
    have hs' := (ringSheaf_closed_localization (pullback.fst g i)
      (pullback.fst g j) hU' ((upperStar Ab.{u + 1} g).obj B)).2.2.2
    refine ⟨hu, hz', delta, gamma, hd, hg, ?_, alpha, beta, ha, hb, ?_, ?_⟩
    · intro M
      exact hs' ((ringSheafInverseImage g B).obj M)
    · intro M
      let adj' := ringSheafOpenAdjunction (pullback.fst g j)
        ((upperStar Ab.{u + 1} g).obj B)
      apply (cancel_epi (alpha.inv.app ((ringSheafInverseImage j B).obj M))).1
      simp only [Iso.inv_hom_id_app_assoc]
      apply (adj'.homEquiv _ _).injective
      rw [adj'.homEquiv_naturality_right, ha]
      rw [adj'.homEquiv_naturality_left]
      dsimp only [adj']
      simp only [Adjunction.homEquiv_unit]
      rw [← Category.assoc, ← Functor.comp_map]
      rw [Category.assoc]
      have hd := delta.inv.naturality
        ((ringSheafOpenAdjunction j B).counit.app M)
      simp only [Functor.comp_obj] at hd ⊢
      rw [← hd]
      simp only [Functor.comp_map]
      change (ringSheafSquarePullback g j B).map
          ((ringSheafOpenAdjunction j B).unit.app ((ringSheafInverseImage j B).obj M)) ≫
          (ringSheafSquarePullback g j B).map
            ((ringSheafInverseImage j B).map
              ((ringSheafOpenAdjunction j B).counit.app M)) ≫ delta.inv.app M = _
      rw [← Category.assoc, ← Functor.map_comp,
        (ringSheafOpenAdjunction j B).right_triangle_components]
      simp only [Category.assoc, Adjunction.right_triangle_components, Category.comp_id]
      apply Mod.Hom.ext
      simp only [Functor.id_obj, Functor.comp_obj, Functor.comp_map,
        Functor.mapMod_map, Mod.id_hom', Mod.comp_hom',
        Mod.comap_map_hom, Mod.homMk_hom]
      rw [(upperStar Ab.{u + 1} (pullback.snd g j)).map_id]
      exact Category.id_comp ((delta.inv.app M).hom)
    · intro M
      let adj' := ringSheafAdjunction (pullback.fst g i)
        ((upperStar Ab.{u + 1} g).obj B)
      apply (adj'.homEquiv _ _).symm.injective
      rw [adj'.homEquiv_naturality_left_symm]
      dsimp only [adj']
      simp only [Functor.comp_obj, Functor.id_obj] at hb ⊢
      rw [hb ((ringSheafInverseImage i B).obj M)]
      change _ = (adj'.homEquiv _ _).symm ((adj'.homEquiv _ _) (gamma.hom.app M))
      rw [Equiv.symm_apply_apply]
      rw [← Category.assoc, ← Functor.comp_map]
      rw [gamma.hom.naturality]
      change gamma.hom.app M ≫
          (ringSheafSquarePullback g i B).map
            ((ringSheafInverseImage i B).map ((ringSheafAdjunction i B).unit.app M)) ≫
          (ringSheafSquarePullback g i B).map
            ((ringSheafAdjunction i B).counit.app ((ringSheafInverseImage i B).obj M)) = _
      rw [← (ringSheafSquarePullback g i B).map_comp,
        (ringSheafAdjunction i B).left_triangle_components M]
      apply Mod.Hom.ext
      simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map,
        Functor.mapMod_map, Mod.id_hom', Mod.comp_hom',
        Mod.comap_map_hom, Mod.homMk_hom]
      rw [(upperStar Ab.{u + 1} (pullback.snd g i)).map_id]
      exact Category.comp_id ((gamma.hom.app M).hom)

end AlgebraicGeometry.ProEtale
