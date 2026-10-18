/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.Blowup.Principalization

/-!
# The kernel and support of module strict transform

Source: Stacks Project, Divisors, Tag 080D (1)--(2) and its preceding paragraph;
Properties, Tag 07ZP; Morphisms, Tag 01R8
(blueprint: lem-trf-strict-transform-sheaf-kernel).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical quotient from the pullback to its module strict transform.
Source: Stacks Project, Divisors, Tag 080D (1)
(blueprint: lem-trf-strict-transform-sheaf-kernel). -/
noncomputable def moduleStrictTransformπ {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) [I.toModules.IsFiniteType] (F : X.Modules)
    [F.IsQuasicoherent] :
    (tensorPullback (pullback.fst f I.blowupMap)).obj F ⟶ moduleStrictTransform f I F :=
  cokernel.π (kernel.ι (moduleStrictTransformRestriction f I F))

/-- For the structure sheaf, identify its tensor pullback with the structure sheaf
of the fibre product before taking the canonical strict-transform quotient.
Source: Stacks Project, Divisors, Tag 080D (2)
(blueprint: lem-trf-strict-transform-sheaf-kernel). -/
noncomputable def moduleStrictTransformStructureMap {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) [I.toModules.IsFiniteType] :
    (SheafOfModules.unit (Limits.pullback f I.blowupMap).ringCatSheaf :
      (Limits.pullback f I.blowupMap).Modules) ⟶
      @moduleStrictTransform X S f I inferInstance (SheafOfModules.unit X.ringCatSheaf)
        (SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)) :=
  (@asIso _ _ _ _ (tensorPullbackObjUnitToUnit (pullback.fst f I.blowupMap))
    (tensorPullbackObjUnitToUnit_isIso (pullback.fst f I.blowupMap)).1).inv ≫
      @moduleStrictTransformπ X S f I inferInstance (SheafOfModules.unit X.ringCatSheaf)
        (SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf))

/-- The strict-transform quotient is surjective, with quasi-coherent kernel consisting
of sections supported on the inverse image of the centre. The quotient is quasi-coherent,
is unchanged off that inverse image, and has no remaining supported local sections.
Source: Stacks Project, Divisors, Tag 080D (1), preceding paragraph; Properties, Tag 07ZP
(blueprint: lem-trf-strict-transform-sheaf-kernel).

Proof: (1) Principalization of the blowup centre makes the exceptional divisor Cartier.
Its inverse image is locally principal, so its complement is retrocompact; the open
inclusion is quasi-compact and quasi-separated.
(2) Pullback preserves quasi-coherence. The restriction of the pullback is quasi-coherent,
and its direct image under this open inclusion is quasi-coherent by qcqs pushforward.
The quasi-coherent-kernel theorem applies to the restriction map. The cokernel-image
theorem gives quasi-coherence and surjectivity of the quotient, with sectionwise kernel
exactly this supported-section subsheaf.
(3) On the complement this kernel vanishes, so the quotient is an isomorphism there.
For a supported quotient section, cover its domain by affine opens. The affine cokernel
formula lifts each restriction to the pullback. Off the exceptional locus the lift maps
to zero, hence lies in the zero kernel there. It therefore belongs to the supported
kernel on the whole affine open. The quotient section vanishes on each such open,
and hence vanishes by the sheaf axiom. -/
theorem moduleStrictTransform_properties {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) [I.toModules.IsFiniteType] (F : X.Modules)
    [F.IsQuasicoherent] :
    Epi (moduleStrictTransformπ f I F) ∧
    (∀ (V : (Limits.pullback f I.blowupMap).Opens)
      (s : Γ((tensorPullback (pullback.fst f I.blowupMap)).obj F, V)),
      (moduleStrictTransformπ f I F).app V s = 0 ↔
        (moduleStrictTransformRestriction f I F).app V s = 0) ∧
    (moduleStrictTransformKernel f I F).IsQuasicoherent ∧
    (moduleStrictTransform f I F).IsQuasicoherent ∧
    IsIso ((restrictFunctor (moduleStrictTransformOpen f I).ι).map
      (moduleStrictTransformπ f I F)) ∧
    (∀ (V : (Limits.pullback f I.blowupMap).Opens) (s : Γ(moduleStrictTransform f I F, V)),
      ((restrictAdjunction (moduleStrictTransformOpen f I).ι).unit.app
        (moduleStrictTransform f I F)).app V s = 0 → s = 0) := by
  sorry

/-- The structure-sheaf strict transform is the structure sheaf of the scheme strict
transform, pushed forward along its closed immersion, compatibly with the quotient
from the structure sheaf of the fibre product. Its kernel is precisely the defining ideal.
Source: Stacks Project, Divisors, Tag 080D (2); Morphisms, Tag 01R8
(blueprint: lem-trf-strict-transform-sheaf-kernel).

Proof: (4) The tensor pullback of the structure sheaf is canonically the structure sheaf
of the fibre product. Its supported-section kernel is the ideal of functions vanishing
on the preserved open. The fibre-product universal property identifies this open with
the open used in the scheme strict transform. That transform is the scheme-theoretic
image of this qcqs open inclusion, hence is cut out by the kernel of restriction of
functions. The ideal/closed-subscheme correspondence identifies its ideal sheaf with
the supported-section kernel. The closed immersion gives an epimorphism to the direct
image of its structure sheaf with that same kernel. Uniqueness of cokernels supplies
the isomorphism, compatible with both quotient maps. -/
theorem moduleStrictTransform_structureSheaf {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) [I.toModules.IsFiniteType] :
    (∀ (V : (Limits.pullback f I.blowupMap).Opens)
      (s : Γ((SheafOfModules.unit (Limits.pullback f I.blowupMap).ringCatSheaf :
        (Limits.pullback f I.blowupMap).Modules), V)),
      Hom.app (moduleStrictTransformStructureMap f I) V s = 0 ↔
        s ∈ (I.strictTransformι f).ker.idealOfOpens V) ∧
    ∃ e : @moduleStrictTransform X S f I inferInstance (SheafOfModules.unit X.ringCatSheaf)
        (SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)) ≅
        (pushforward (I.strictTransformι f)).obj
          (SheafOfModules.unit (I.strictTransform f).ringCatSheaf),
      moduleStrictTransformStructureMap f I ≫ e.hom =
        SheafOfModules.unitToPushforwardObjUnit (I.strictTransformι f).toRingCatSheafHom := by
  sorry

end AlgebraicGeometry.Scheme.Modules
