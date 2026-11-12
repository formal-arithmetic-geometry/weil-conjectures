/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.CurvePunctualPart

/-!
# The largest punctual subsheaf

Let `G` be a Weil sheaf on a smooth curve `X` over `k₀` and `j : U₀ ↪ X` a dense open immersion
on which `G` is lisse. The *punctual part* of `G` is the kernel `G_p = ker(G ⟶ j_* j^* G)` of the
unit of `j^* ⊣ j_*` (`AlgebraicGeometry.WeilSheaf.punctualPart`). It is the largest subsheaf of
`G` of finite support (`AlgebraicGeometry.WeilSheaf.isGreatest_punctualPart`), the quotient
`G / G_p` has no nonzero subsheaf of finite support
(`AlgebraicGeometry.WeilSheaf.isZero_of_mono_cokernel_punctualPart`), and `G_p` does not depend
on `U₀` (`AlgebraicGeometry.WeilSheaf.punctualPart_eq`). (blueprint:
`lemma-largest-punctual-subsheaf`)

As a consequence, every Weil sheaf on a smooth curve has a maximal punctual subsheaf
(`AlgebraicGeometry.WeilSheaf.exists_mono_support_finite_cokernel`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace WeilSheaf

attribute [local instance 1000] IsSeparated.isSeparated_of_mono

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X U : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [U.Over (Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The *punctual part* `G_p = ker(G ⟶ j_* j^* G)` of a Weil sheaf `G` on a curve `X`, for an
open immersion `j : U₀ ↪ X`, as a subobject of `G`.
(blueprint: `lemma-largest-punctual-subsheaf--2`) -/
noncomputable def punctualPart (G : WeilSheaf k₀ l X) : Subobject G :=
  kernelSubobject ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).unit.app G)

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))]

/-- The quotient `G / G_p` of a Weil sheaf `G` on a smooth curve by its punctual part has no
nonzero subsheaf of finite support, for an open `j : U₀ ↪ X` on which `G` is lisse: it embeds
into the direct image `j_* j^* G` of a lisse sheaf.
(blueprint: `lemma-largest-punctual-subsheaf--4`) -/
theorem isZero_of_mono_cokernel_punctualPart {G : WeilSheaf k₀ l X}
    (hG : ((upperStar j).obj G).IsLisse) (G' : WeilSheaf k₀ l X)
    (i : G' ⟶ cokernel (punctualPart j G).arrow) [Mono i] (hG' : G'.support.Finite) :
    IsZero G' := by
  set u := (upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).unit.app G
  let e : cokernel (punctualPart j G).arrow ≅ Abelian.coimage u :=
    cokernelIsoOfEq (kernelSubobject_arrow u).symm ≪≫ cokernelEpiComp _ _
  refine IsZero.of_mono_eq_zero i ((cancel_mono (e.hom ≫ Abelian.factorThruCoimage u)).1 ?_)
  rw [zero_comp]
  exact eq_zero_of_support_finite_of_isLisse j hG hG' _

variable [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [IsDominant j]

/-- The punctual part of a Weil sheaf `G` on a smooth curve is the largest subsheaf of `G` of
finite support, for a dense open `j : U₀ ↪ X` on which `G` is lisse: it is punctual, as
`G ⟶ j_* j^* G` is an isomorphism on `U₀`, and a punctual subsheaf maps to zero in the direct
image `j_* j^* G` of a lisse sheaf. (blueprint: `lemma-largest-punctual-subsheaf--3`) -/
theorem isGreatest_punctualPart {G : WeilSheaf k₀ l X} (hG : ((upperStar j).obj G).IsLisse) :
    IsGreatest {S : Subobject G | (S : WeilSheaf k₀ l X).support.Finite} (punctualPart j G) := by
  set η := (upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).unit.app G
  refine ⟨?_, fun S hS ↦ le_kernelSubobject _ _ (eq_zero_of_support_finite_of_isLisse j hG hS _)⟩
  have : IsIso ((upperStar j).map η) := Adjunction.isIso_map_unit_app_of_isIso_counit_app _ G
  have : Mono ((upperStar j).map η) := IsIso.mono_of_iso _
  have h : (kernel η).support.Finite :=
    support_finite_of_isZero_upperStar_of_dense j j.denseRange _ <|
      (isZero_kernel_of_mono _).of_iso (PreservesKernel.iso (upperStar (k₀ := k₀) (l := l) j) _)
  rwa [← support_congr (kernelSubobjectIso η)] at h

/-- The punctual part of a Weil sheaf `G` on a smooth curve does not depend on the dense open on
which `G` is lisse: both are the largest punctual subsheaf of `G`.
(blueprint: `lemma-largest-punctual-subsheaf--5`) -/
theorem punctualPart_eq {U' : Scheme.{u}} [U'.Over (Spec (CommRingCat.of k₀))]
    (j' : U' ⟶ X) [IsOpenImmersion j'] [QuasiCompact j'] [j'.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U' ↘ Spec (CommRingCat.of k₀))] [IsDominant j'] {G : WeilSheaf k₀ l X}
    (hG : ((upperStar j).obj G).IsLisse) (hG' : ((upperStar j').obj G).IsLisse) :
    punctualPart j G = punctualPart j' G :=
  (isGreatest_punctualPart j hG).unique (isGreatest_punctualPart j' hG')

/-- **Maximal punctual subsheaves on a smooth curve** (input to
`lemma-perverse-sheaves-curve--1`): a Weil sheaf `F` on a smooth curve has a subsheaf `P` of
finite support such that `F / P` has no nonzero subsheaf of finite support, namely its punctual
part with respect to a dense open on which `F` is lisse. -/
theorem exists_mono_support_finite_cokernel [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l X) :
    ∃ (P : WeilSheaf k₀ l X) (i : P ⟶ F), Mono i ∧ P.support.Finite ∧
      ∀ (G : WeilSheaf k₀ l X) (j : G ⟶ cokernel i), Mono j → G.support.Finite → IsZero G := by
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k₀))
  have : Smooth (X ↘ Spec (CommRingCat.of k₀)) := SmoothOfRelativeDimension.smooth 1 _
  have : IsReduced X := isReduced_of_smooth (X ↘ Spec (CommRingCat.of k₀))
  obtain ⟨V, hV, hVl⟩ := exists_dense_isLisse_upperStar F
  have : IsDominant V.ι := ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩
  exact ⟨_, (punctualPart V.ι F).arrow, inferInstance, (isGreatest_punctualPart V.ι hVl).1,
    fun G j _ hG ↦ isZero_of_mono_cokernel_punctualPart V.ι hVl G j hG⟩

end WeilSheaf

end AlgebraicGeometry
