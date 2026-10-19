/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NC, U9
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom

/-!
# The equalizer internal hom for the relative monoidal tensor

Source: Weil conjectures blueprint, main-20261015, sec-proetale-coefficients,
unit sk-prop-sfb-module-category, definition def-sfb-modobj-internal-hom
(blueprint: def-sfb-modobj-internal-hom).

The object and functor are the existing `CategoryTheory.Mod.ihom'`. Its equalizer uses
`homModPre` and `homModB`, with the action through the target given by `homAct`.
The statement below identifies this specified functor as a right adjoint for the
monoidal tensor of `CategoryTheory.Mod.monoidalCategory`, with the factor order of the
blueprint. The existing `ihom'Adjunction` instead uses `Mod.tensorLeft`, the separately
constructed coequalizer functor computing tensoring on the right.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Mod

open MonoidalCategory Limits MonObj in
section

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]

/-- The quotient map defining the relative tensor product is linear in its first factor. -/
private noncomputable def equalizerAdjTensorπ (M N : Mod C R) :
    (Mod.tensorRight R N.X).obj M ⟶ M ⊗ N :=
  homMk (M := (Mod.tensorRight R N.X).obj M) (N := M ⊗ N) (tensorObjπ M N) (by
    change ((α_ R M.X N.X).inv ≫ γ[R,M.X] ▷ N.X) ≫ tensorObjπ M N =
      R ◁ tensorObjπ M N ≫ γ[R,(M ⊗ N).X]
    simpa only [Category.assoc] using (whiskerLeft_tensorπ_smul M N).symm)

/-- The relative tensor product is a cofork of the two action maps on module objects. -/
private noncomputable def equalizerAdjTensorCofork (M N : Mod C R) :
    Cofork ((tensorRightMap R γ[R,N.X]).app M)
      ((tensorRightRightAct R N.X).app M) :=
  Cofork.ofπ (equalizerAdjTensorπ M N) (by
    apply Mod.hom_ext
    change M.X ◁ γ[R,N.X] ≫ tensorObjπ M N =
      ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X) ≫ tensorObjπ M N
    rw [Category.assoc, tensorObjπ_condition]
    simp only [Category.assoc, Iso.inv_hom_id_assoc])

/-- The tensor cofork is a coequalizer, as can be checked after forgetting the module action. -/
private noncomputable def isColimitEqualizerAdjTensorCofork (M N : Mod C R) :
    IsColimit (equalizerAdjTensorCofork M N) := by
  apply isColimitOfIsColimitCoforkMap (forget R)
  change IsColimit (Cofork.ofπ (tensorObjπ M N) _ :
    Cofork (M.X ◁ γ[R,N.X]) ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X))
  refine Cofork.IsColimit.mk _
    (fun s ↦ coequalizer.desc (f := rightAct M ▷ N.X)
      (g := (α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X]) s.π ?_) ?_ ?_
  · have h := s.condition
    change M.X ◁ γ[R,N.X] ≫ s.π =
      ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X) ≫ s.π at h
    rw [← cancel_epi (α_ M.X R N.X).inv]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h.symm
  · intro s
    exact coequalizer.π_desc _ _
  · intro s m hm
    apply coequalizer.hom_ext (f := rightAct M ▷ N.X)
      (g := (α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X])
    exact hm.trans (coequalizer.π_desc _ _).symm

/-- The previously constructed coequalizer tensor functor agrees with the monoidal tensor. -/
private noncomputable def equalizerAdjTensorRightIso (N : Mod C R) :
    Mod.tensorLeft N ≅ MonoidalCategory.tensorRight N :=
  NatIso.ofComponents
    (fun M ↦ by
      change colimit ((tensorLeftDiagram R N).flip.obj M) ≅ M ⊗ N
      exact HasColimit.isoOfNatIso
        (diagramIsoParallelPair ((tensorLeftDiagram R N).flip.obj M)) ≪≫
        (colimit.isColimit _).coconePointUniqueUpToIso (isColimitEqualizerAdjTensorCofork M N)) (by
    intro M M' f
    apply colimit.hom_ext
    intro j
    simp only [id_eq, Iso.trans_hom, tensorLeft, Functor.comp_map, colim_map, Category.assoc,
      ι_colimMap_assoc, HasColimit.isoOfNatIso_ι_hom_assoc]
    cases j <;> apply Mod.hom_ext <;>
      simp [equalizerAdjTensorCofork, equalizerAdjTensorπ, tensorObjπ_whiskerRight])

/-- The equalizer internal hom is right adjoint to left relative tensoring.
Source: main-20261015 blueprint, sec-proetale-coefficients,
sk-prop-sfb-module-category/def-sfb-modobj-internal-hom
(blueprint: def-sfb-modobj-internal-hom).

Here `ihom' R M` is the actual equalizer functor already constructed upstream, with
its action through the target, rather than an unspecified right adjoint.

Proof (the node's ten steps, reusing the upstream equalizer adjunction):
1. Grothendieck abelianness supplies equalizers and coequalizers; ambient closedness
   makes both tensor functors preserve colimits by
   `lem-weil-pbc-left-adjoint-preserves-colimits` and symmetry.
2. Curry the action-through-target and action-through-source composites to obtain
   the two maps, namely `homModB` and `homModPre`, in the opposite order to the display.
3. Curry evaluation followed by the target action, after moving the scalar past M,
   to obtain `homAct`; its unit and associativity follow by uncurrying.
4. Commutativity of R shows that both equalizer maps are linear for these actions.
5. Restrict the action to their equalizer; uniqueness gives the module laws.
6. The relative coequalizer universal property identifies module maps out of
   L tensor_R M with ambient maps L tensor M to N linear in both variables
   (`def-sfb-modobj-relative-tensor`, `sk-def-sfb-module-objects`).
7. Currying identifies linearity in M with factorization through the equalizer.
8. Linearity in L is precisely linearity of the transposed equalizer lift;
   the equalizer inclusion is monic, so it detects this equation.
9. Currying and uncurrying, followed by equalizer lift and coequalizer descent, give
   inverse natural Hom bijections. These are the existing `ihom'Adjunction`.
10. Compare its coequalizer tensor with the monoidal tensor by the unique isomorphism
    commuting with the quotient maps. Precompose with the descended symmetry of
    `def-sfb-modobj-symmetric-tensor` to obtain the stated factor order.
    Thus every left tensor functor has this right adjoint, proving closedness.
The module category is abelian by `lem-sfb-modobj-abelian`. -/
theorem nonempty_equalizerInternalHomAdjunction
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    (R : C) [MonObj R] [IsCommMonObj R] (M : Mod C R) :
    Nonempty (MonoidalCategory.tensorLeft M ⊣ ihom' R M) := by
  exact ⟨(ihom'Adjunction R M).ofNatIsoLeft
    (equalizerAdjTensorRightIso M ≪≫
      (BraidedCategory.tensorLeftIsoTensorRight M).symm)⟩

end

end CategoryTheory.Mod
