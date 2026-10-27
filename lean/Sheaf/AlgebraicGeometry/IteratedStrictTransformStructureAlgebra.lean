/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
public import Sheaf.AlgebraicGeometry.ModuleStrictTransformKernel
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.CategoryTheory.Monoidal.Mon
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Structure algebra of an iterated strict transform

Source: Stacks Project, Divisors, Tags 080D, 080G and 080I, passage from the
module clause to the scheme clause
(blueprint: lem-trf-iterated-transform-structure-algebra).

We represent B by (X ×[S] Bl_I(S)) ×[Bl_I(S)] Bl_J(Bl_I(S)). A commutative
`MonObj` in B.Modules is a sheaf of commutative O_B-algebras: its multiplication
is O_B-bilinear and its unit is an O_B-linear map from the structure sheaf.
The unit below is required to be the actual iterated quotient alpha. The comparison
preserves multiplication on all local sections, with the ordinary multiplication
of functions on X₂ on the right.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical closed-subscheme map k₂: first base change i₁ to Bl_J, then compose
with the second strict-transform inclusion i₂. The map of pullbacks is the base
change of i₁, with identity maps on Bl_J and Bl_I.
Source: Stacks Project, Divisors, Tags 080D (2), 080G and 080I
(blueprint: lem-trf-iterated-transform-structure-algebra). -/
noncomputable def iteratedStrictTransformι {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) (J : I.blowup.IdealSheafData) :
    J.strictTransform (strictTransformMap f I.blowupMap I.support.compl) ⟶
      Limits.pullback (pullback.snd f I.blowupMap) J.blowupMap :=
  J.strictTransformι (strictTransformMap f I.blowupMap I.support.compl) ≫
    pullback.map (strictTransformMap f I.blowupMap I.support.compl) J.blowupMap
      (pullback.snd f I.blowupMap) J.blowupMap (I.strictTransformι f)
      (𝟙 J.blowup) (𝟙 I.blowup) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- The actual second module strict transform of O_X. Quasi-coherence of the first
transform is obtained from the one-step kernel theorem, not required as a hypothesis.
The definition retains both centres and applies the module strict-transform construction twice.
Source: Stacks Project, Divisors, Tags 080D (1) and 080I
(blueprint: lem-trf-iterated-transform-structure-algebra). -/
noncomputable def iteratedStrictTransformStructureModule {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) [I.toModules.IsFiniteType]
    (J : I.blowup.IdealSheafData) [J.toModules.IsFiniteType] :
    (Limits.pullback (pullback.snd f I.blowupMap) J.blowupMap).Modules :=
  letI : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  @moduleStrictTransform _ _ (pullback.snd f I.blowupMap) J inferInstance
    (moduleStrictTransform f I (SheafOfModules.unit X.ringCatSheaf))
    (moduleStrictTransform_properties f I (SheafOfModules.unit X.ringCatSheaf)).2.2.2.1

/-- Alpha: identify q*O_A with O_B by multiplication, pull back the first
structure-sheaf quotient O_A → M, and follow with the second quotient q*M → N.
Source: Stacks Project, Divisors, Tags 080D (1)--(2) and 080I, first proof paragraph
(blueprint: lem-trf-iterated-transform-structure-algebra). -/
noncomputable def iteratedStrictTransformStructureMap {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) [I.toModules.IsFiniteType]
    (J : I.blowup.IdealSheafData) [J.toModules.IsFiniteType] :
    (SheafOfModules.unit
      (Limits.pullback (pullback.snd f I.blowupMap) J.blowupMap).ringCatSheaf :
        (Limits.pullback (pullback.snd f I.blowupMap) J.blowupMap).Modules) ⟶
      iteratedStrictTransformStructureModule f I J :=
  letI : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  (@asIso _ _ _ _
    (tensorPullbackObjUnitToUnit (pullback.fst (pullback.snd f I.blowupMap) J.blowupMap))
    (tensorPullbackObjUnitToUnit_isIso
      (pullback.fst (pullback.snd f I.blowupMap) J.blowupMap)).1).inv ≫
    (tensorPullback (pullback.fst (pullback.snd f I.blowupMap) J.blowupMap)).map
      (moduleStrictTransformStructureMap f I) ≫
    @moduleStrictTransformπ _ _ (pullback.snd f I.blowupMap) J inferInstance
      (moduleStrictTransform f I (SheafOfModules.unit X.ringCatSheaf))
      (moduleStrictTransform_properties f I (SheafOfModules.unit X.ringCatSheaf)).2.2.2.1

/-- The iterated structure-sheaf transform is canonically the quotient algebra
k₂*O_X₂, and the kernel of its structure map is the defining ideal of k₂.
Source: Stacks Project, Divisors, Tags 080D (2), 080G and 080I (1) to (2)
(blueprint: lem-trf-iterated-transform-structure-algebra).

Proof:
1. Put Y = X₁ ×[Bl_I] Bl_J and j = the base change of i₁. Fibre-product pasting
   makes this the pullback of i₁ along q. Closed immersions are stable under base
   change and composition, so j and k₂ = i₂ ≫ j are closed immersions, hence affine.
2. Apply moduleStrictTransform_structureSheaf twice, to obtain quotient-compatible
   identifications M ≅ i₁*O_X₁ and L ≅ i₂*O_X₂. The kernel theorem gives
   quasi-coherence of M, L and the defining ideal K_Y. Local lifts through the
   quotient maps show that these identifications preserve products and units.
3. Affine pushforward base change identifies q*M with j*O_Y, as algebras. Its
   tensor formula a tensor c ↦ a r♯(c) takes the pulled-back first structure map
   to j♯; this step requires no flatness.
4. Let D be the inverse image of the second exceptional divisor in B. On each
   open W of B, j⁻¹(W minus D) = j⁻¹W minus j⁻¹D. Thus restriction kernels
   identify the supported-section ideal K in q*M with j*K_Y section by section.
5. The affine quasi-coherent quotient lemma identifies (j*O_Y)/(j*K_Y) with j*L,
   compatibly with the quotient. Descend the algebra comparison of step 3 through
   these ideals. Multiplication is well-defined because supported sections form
   an ideal; it sends products of local lifts to the class of their product.
6. Compose N ≅ j*L with j* of the second comparison and the composition comparison
   for pushforward. This gives theta to k₂*O_X₂, preserving multiplication and
   unit. The equations of steps 2, 3 and 5 give alpha ≫ theta = k₂♯.
7. The iterated quotient/support lemma makes alpha epic. Local lifts therefore
   show that the structure-map equation determines theta uniquely. Its
   injectivity gives ker alpha = ker k₂♯, precisely the defining ideal of k₂.
-/
theorem iteratedStrictTransform_structureAlgebra {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) [I.toModules.IsFiniteType]
    (J : I.blowup.IdealSheafData) [J.toModules.IsFiniteType] :
    IsClosedImmersion (iteratedStrictTransformι f I J) ∧
    ∃ a : MonObj (iteratedStrictTransformStructureModule f I J),
      a.one = iteratedStrictTransformStructureMap f I J ∧
      @IsCommMonObj _ _ _ _ _ a ∧
      (∃! θ : iteratedStrictTransformStructureModule f I J ≅
          (pushforward (iteratedStrictTransformι f I J)).obj
            (SheafOfModules.unit
              (J.strictTransform
                (strictTransformMap f I.blowupMap I.support.compl)).ringCatSheaf),
        iteratedStrictTransformStructureMap f I J ≫ θ.hom =
          SheafOfModules.unitToPushforwardObjUnit
            (iteratedStrictTransformι f I J).toRingCatSheafHom ∧
        ∀ (V : (Limits.pullback (pullback.snd f I.blowupMap) J.blowupMap).Opens)
          (s t : Γ(iteratedStrictTransformStructureModule f I J, V)),
          θ.hom.app V (a.mul.app V (tmulSection s t)) =
            @Mul.mul (Γ(J.strictTransform
              (strictTransformMap f I.blowupMap I.support.compl),
                (iteratedStrictTransformι f I J) ⁻¹ᵁ V)) inferInstance
                  (θ.hom.app V s) (θ.hom.app V t)) ∧
      ∀ (V : (Limits.pullback (pullback.snd f I.blowupMap) J.blowupMap).Opens)
        (s : Γ((SheafOfModules.unit
          (Limits.pullback (pullback.snd f I.blowupMap) J.blowupMap).ringCatSheaf :
            (Limits.pullback (pullback.snd f I.blowupMap) J.blowupMap).Modules), V)),
        Hom.app (iteratedStrictTransformStructureMap f I J) V s = 0 ↔
          s ∈ (iteratedStrictTransformι f I J).ker.idealOfOpens V := by
  sorry

end AlgebraicGeometry.Scheme.Modules
