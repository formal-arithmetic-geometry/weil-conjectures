/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.AlgebraicGeometry.ProEtalePairFlasque
public import Sheaf.AlgebraicGeometry.PurSupportExact
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-! # The pro-etale supported-sections cone

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
`def-pur-support-triangle` (blueprint: def-pur-support-triangle).

The three complexes, inclusion, quotient map, and negative shifted projection are fixed.
The triangle takes only the proof that its specified cone quotient is invertible.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Additivity needed to apply the supported kernel termwise. Source: the natural kernel
maps of blueprint `def-pur-support-triangle` (blueprint: def-pur-support-triangle).
Proof: compose the kernel map of a sum with the monic kernel inclusion. Naturality makes
this the sum of the two composites. Cancel the inclusion; the same argument handles zero. -/
theorem supportKernelAdditive {X U : Scheme.{u}} (j : U ⟶ X) :
    (finiteSupportedSections Λ j).Additive := by
  constructor
  intro M N f g
  let ι := finiteSupportedSectionsι Λ j
  have : Mono (ι.app N) :=
    inferInstanceAs (Mono (((evaluation _ _).obj N).map
      (kernel.ι (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit)))
  apply (cancel_mono (ι.app N)).1
  rw [Preadditive.add_comp, ι.naturality, ι.naturality, ι.naturality]
  simp

attribute [instance] supportKernelAdditive

/-- Additivity of closed inverse image of the supported kernel. Source: blueprint
`def-pur-support-triangle` (blueprint: def-pur-support-triangle).
Proof: `finiteClosedUpperShriek` is the composite of the additive supported-kernel
functor and the additive module inverse image; composition preserves sums. -/
theorem supportShriekAdditive {X Z U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X) :
    (finiteClosedUpperShriek Λ s j).Additive := by
  unfold finiteClosedUpperShriek
  infer_instance

attribute [instance] supportShriekAdditive

variable {X Z U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X)
  [IsClosedImmersion s] [IsOpenImmersion j] [QuasiCompact j]
  (hPair : IsCompl (Set.range s) (Set.range j))

/-- The actual inclusion `s_*s^!M → M`: invert the canonical supported-kernel comparison,
then apply its kernel inclusion. Source: blueprint `def-pur-support-triangle`
(blueprint: def-pur-support-triangle). -/
noncomputable def supportModelInclusion :
    finiteClosedUpperShriek Λ s j ⋙ lowerStar (ModuleCat.{u + 1} Λ) s ⟶ 𝟭 _ :=
  letI := finiteSupportedClosedComparison_isIso Λ s j hPair
  (asIso (finiteSupportedClosedComparison Λ s j)).inv ≫ finiteSupportedSectionsι Λ j

/-- The specified inclusion is killed by open restriction. Source: blueprint
`def-pur-support-triangle` (blueprint: def-pur-support-triangle).
Proof: the inclusion is the inverse-comparison map followed by the kernel inclusion
of the open unit. Its composite with that unit is zero by the kernel equation. -/
theorem supportModelInclusion_unit_zero
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    (supportModelInclusion Λ s j hPair).app M ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app M = 0 := by
  have hz : (finiteSupportedSectionsι Λ j).app M ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app M = 0 :=
    congrArg (fun α ↦ α.app M)
      (kernel.condition (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit)
  dsimp [supportModelInclusion]
  rw [Category.assoc, hz, comp_zero]

/-- The complex `C(I)=j_*j^*I`, applied termwise. Source: blueprint
`def-pur-support-triangle` (blueprint: def-pur-support-triangle). -/
noncomputable def supportCComplex
    (I : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ) :=
  ((upperStar (ModuleCat.{u + 1} Λ) j ⋙ lowerStar (ModuleCat.{u + 1} Λ) j).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I

/-- `A(I)=s_*s^!I`, `B(I)=I`, `C(I)=j_*j^*I`, with the specified inclusion and open unit.
Source: blueprint `def-pur-support-triangle` (blueprint: def-pur-support-triangle). -/
noncomputable def supportModelSequence
    (I : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ) :
    ShortComplex
      (CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ) :=
  ShortComplex.mk
    ({ f n := (supportModelInclusion Λ s j hPair).app (I.X n)
       comm' n m _ := ((supportModelInclusion Λ s j hPair).naturality (I.d n m)).symm } :
      supportedSectionsComplex Λ s j hPair I ⟶ I)
    ({ f n := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app (I.X n)
       comm' n m _ :=
         ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.naturality
           (I.d n m)).symm } : I ⟶ supportCComplex Λ j I)
    (by ext n : 1; exact supportModelInclusion_unit_zero Λ s j hPair (I.X n))

/-- The explicit cone of the inclusion. Mathlib uses `A[m+1] ⊞ B[m]`, canonically
identified with the blueprint's `B[m] ⊞ A[m+1]`; its differential is the same signed matrix.
Source: blueprint `def-pur-support-triangle` (blueprint: def-pur-support-triangle). -/
noncomputable def supportLocalizationCone
    (I : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ) :=
  CochainComplex.mappingCone (supportModelSequence Λ s j hPair I).f

/-- The cone-to-quotient map `q(b,a)=η(b)`. Source: blueprint
`def-pur-support-triangle` (blueprint: def-pur-support-triangle). -/
noncomputable def supportConeQuotient
    (I : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ) :=
  CochainComplex.mappingCone.descShortComplex (supportModelSequence Λ s j hPair I)

section GenericTriangle

universe v w
variable {C : Type v} [Category.{w} C] [Abelian C] [HasDerivedCategory C]

/-- The explicit quotient triangle of a short complex, with the cone quotient inverted.
This generic constructor keeps its three objects as parameters during triangle transport.
Source: blueprint def-pur-support-triangle, cone quotient and signed projection
(blueprint: def-pur-support-triangle). -/
noncomputable def supportSequenceTriangle (S : ShortComplex (CochainComplex C ℤ))
    (hq : IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S))) :
    Triangle (DerivedCategory C) :=
  letI := hq
  Triangle.mk (DerivedCategory.Q.map S.f) (DerivedCategory.Q.map S.g)
    (inv (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S)) ≫
      DerivedCategory.Q.map (CochainComplex.mappingCone.triangle S.f).mor₃ ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app S.X₁)

end GenericTriangle

/-- The specified triangle: its boundary is `q⁻¹` followed by the negative shifted
projection, including the canonical shift comparison for localization. No choice of
boundary occurs. Source: blueprint `def-pur-support-triangle`
(blueprint: def-pur-support-triangle). -/
noncomputable def supportModelTriangle
    (I : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ)
    (hq : IsIso (DerivedCategory.Q.map (supportConeQuotient Λ s j hPair I))) :
    Triangle (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :=
  supportSequenceTriangle (supportModelSequence Λ s j hPair I) hq

end AlgebraicGeometry.ProEtale
