/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X5
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.Paper.ExtendedCechCompletionModel
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-! # Pullback of augmented extended Cech tensor actions

Source: Stacks Project, algebraization.tex, Tag 0A0G, the final pullback identity,
and sites-cohomology.tex, Tags 07A4 and 08J9.
(blueprint: lem-weil-pbc-augmented-cech-tensor-pullback).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u wX wY

open CategoryTheory CategoryTheory.Limits WeilConjectures

namespace CategoryTheory

set_option maxHeartbeats 200000 in
-- The image ideal interface elaborates several repeated underlying-sheaf functors.
/-- Derived pullback intertwines the augmented Cech tensor actions for an ideal and
its generated image. The augmentation equation is expressed using inverse tensor-Hom transposes.
No completion reflector or direct-image/completion comparison is part of this statement.

Source: Stacks Project, algebraization.tex, Tag 0A0G, final Koszul pullback identity;
sites-cohomology.tex, Tags 07A4 (derived tensor pullback) and 08J9 (tensor-Hom).
(blueprint: lem-weil-pbc-augmented-cech-tensor-pullback).

Proof: the comparison may be constructed in standard localization universes and then
transported back. The localization universal property gives equivalences from the
supplied derived categories to the standard ones, compatibly with Q. Uniqueness of
localization lifts identifies derived restrictions and the internal-Hom bifunctors
under these equivalences. Thus closed adjunctions, augmented local descriptions and
the actual units all transport. This handles the two independent derived universes.
Construct module inverse image by inverse image of sheaves followed by extension
of scalars. Its K-flat left derived functor is left adjoint to the given right derived
direct image; uniqueness of left adjoints identifies it with the supplied L. The tensor
comparison is induced by the ordinary extension-of-scalars tensor comparison.
Take the target cover given by its finite generating lists. Inverse image preserves
its effective epimorphic covering map, since it is a left exact left adjoint. Refine
the resulting source sheaf cover by representables. The image of each finite list
then consists of actual sections of RX on a source site object. These generate the
structural image ideal there; hImage identifies that least ideal with IX. Thus IX
is locally of finite type. For the supplied augmented Cech models, work locally
with their descriptions as tensor products of the complexes [R -> R[1/b]]. The unit-preserving
comparison of
existsUnique_localizationInverseImage commutes algebraic inverse image with scalar
localization. Apply ringedSliceLocalizationModel to the identity site functor and
the structural ring map to handle extension of scalars. Together these compute:
L(RY[1/b]) = RX[1/f(b)], including the localization map from the coefficient ring.
The two-term localization complexes and their finite tensor products are K-flat, so
this termwise calculation computes their derived pullback, with the total-complex
signs preserved. Thus L takes the target augmented Cech model to the source one.
These comparisons commute with restriction, with permutations and with refinement
of generating lists. The local tensor-Hom reflection property identifies the completion functor of
each supplied model with that of a canonical global model, preserving its unit.
Uniqueness of left adjoints transports the normalized augmented tensor action.
Thus it suffices to construct the comparison on canonical models, where its local
localization formulas are compatible with the gluing construction. Tensor compatibility
then gives c on every object, with naturality inherited from the tensor comparison.
If the supplied closed tensor data differ from the canonical representative models,
uniqueness of left adjoints gives tensor-action isomorphisms preserving the transposed
units. Conjugate the canonical comparison by those isomorphisms.
For each side, tensoring with the augmentation followed by the right unitor is the
inverse tensor-Hom transpose of evaluation at one followed by precomposition with
the augmentation, exactly the inverse transpose of ringedCechCompletionUnit. Tensor
compatibility with the augmentation and the tensor unitor proves the last equation.
For the empty generating list the models are the ring complexes and the augmentations
are identities. For the unit ideal the Cech models are acyclic, so the tensor actions
are zero; both cases satisfy the same augmented comparison. -/
theorem ringed_augmentedCech_tensor_pullback
    {C X : Type u} [SmallCategory C] [SmallCategory X]
    {J : GrothendieckTopology C} {K : GrothendieckTopology X}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (RY : Sheaf J CommRingCat.{u}) (RX : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{wY} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))]
    [HasDerivedCategory.{wX} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))]
    [∀ U : C, HasDerivedCategory.{wY} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (RY.over U)))]
    [∀ U : X, HasDerivedCategory.{wX} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose (K.over U) (forget₂ CommRingCat RingCat)).obj (RX.over U)))]
    (f : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (IY : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (ιY : IY ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    [Mono ιY] [IY.IsFiniteType]
    (IX : ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    (ιX : IX ⟶ SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    [Mono ιX]
    (hImage : ∀ (N : ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
      (j : N ⟶ SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)),
      Mono j →
      (∃ k : f.inverse.obj ((SheafOfModules.toSheaf
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⋙
          sheafCompose J (forget AddCommGrpCat)).obj IY) ⟶
          (SheafOfModules.toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) ⋙
            sheafCompose K (forget AddCommGrpCat)).obj N,
        (k ≫ (SheafOfModules.toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) ⋙
            sheafCompose K (forget AddCommGrpCat)).map j : _ ⟶ (sheafCompose K (forget RingCat)).obj
              ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) =
          (f.inverse.map ((SheafOfModules.toSheaf
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⋙
            sheafCompose J (forget AddCommGrpCat)).map ιY) : _ ⟶ f.inverse.obj
              ((sheafCompose J (forget RingCat)).obj
                ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))) ≫ f.ringMap) ↔
      ∃ a : IX ⟶ N, a ≫ j = ιX)
    (Rf : ringedSiteDerived.{u, wX} RX ⥤ ringedSiteDerived.{u, wY} RY)
    (ρ : f.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q.{wY} (C := ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ⟶
      DerivedCategory.Q.{wX} (C := ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) ⋙ Rf)
    (hRf : Rf.IsRightDerivedFunctor ρ
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) (ComplexShape.up ℤ)))
    (hCompute : ∀ I : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) ℤ,
      I.IsKInjective → IsIso (ρ.app I))
    (L : ringedSiteDerived.{u, wY} RY ⥤ ringedSiteDerived.{u, wX} RX)
    (a : L ⊣ Rf)
    (SY : CoefficientClosedStructure (derivedInternalHom.{u, wY} J RY))
    (SX : CoefficientClosedStructure (derivedInternalHom.{u, wX} K RX)) :
    IX.IsFiniteType ∧
    ∀ (KX : ringedSiteComplex RX) (εX : KX ⟶ ringedSiteRingComplex RX),
      HasLocalExtendedCechDescription.{u, wX} RX IX ιX KX εX →
    ∀ (KY : ringedSiteComplex RY) (εY : KY ⟶ ringedSiteRingComplex RY),
      HasLocalExtendedCechDescription.{u, wY} RY IY ιY KY εY →
    ∃ c : @MonoidalCategory.tensorRight _ _ SY.monoidal
          (DerivedCategory.Q.{wY}.obj KY) ⋙ L ≅
        L ⋙ @MonoidalCategory.tensorRight _ _ SX.monoidal
          (DerivedCategory.Q.{wX}.obj KX),
      ∀ T : ringedSiteDerived.{u, wY} RY, c.hom.app T ≫
          ((SX.adjunction (DerivedCategory.Q.{wX}.obj KX)).homEquiv (L.obj T) (L.obj T)).symm
            (ringedCechCompletionUnit.{u, wX} RX KX εX (L.obj T)) =
        L.map (((SY.adjunction (DerivedCategory.Q.{wY}.obj KY)).homEquiv T T).symm
          (ringedCechCompletionUnit.{u, wY} RY KY εY T)) := by
  sorry

end CategoryTheory
