/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.DirectImageUnit

/-!
# The largest punctual subsheaf

Let `G` be a Weil sheaf on the affine line and `j : U₀ ↪ 𝔸¹` a dense open immersion on which `G`
is lisse. The *punctual part* of `G` is the kernel `G_p = ker(G ⟶ j_* j^* G)` of the unit of
`j^* ⊣ j_*` (`AlgebraicGeometry.WeilSheaf.punctualPart`). It is the largest subsheaf of `G` of
finite support (`AlgebraicGeometry.WeilSheaf.isGreatest_punctualPart`), the quotient `G / G_p`
has no nonzero subsheaf of finite support
(`AlgebraicGeometry.WeilSheaf.isZero_of_mono_cokernel_punctualPart`), and `G_p` does not depend
on `U₀` (`AlgebraicGeometry.WeilSheaf.punctualPart_eq`). (blueprint:
`lemma-largest-punctual-subsheaf`)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace WeilSheaf

attribute [local instance 1000] IsSeparated.isSeparated_of_mono

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ affineLine k₀)
  [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]

/-- The *punctual part* `G_p = ker(G ⟶ j_* j^* G)` of a Weil sheaf `G` on the affine line, for an
open immersion `j : U₀ ↪ 𝔸¹`, as a subobject of `G`.
(blueprint: `lemma-largest-punctual-subsheaf--2`) -/
noncomputable def punctualPart (G : WeilSheaf k₀ l (affineLine k₀)) : Subobject G :=
  kernelSubobject ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).unit.app G)

variable [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] [IsDominant j]

/-- The punctual part of a Weil sheaf `G` is the largest subsheaf of `G` of finite support, for a
dense open `j : U₀ ↪ 𝔸¹` on which `G` is lisse: it is punctual, as `G ⟶ j_* j^* G` is an
isomorphism on `U₀`, and a punctual subsheaf maps to zero in the direct image `j_* j^* G` of a
lisse sheaf. (blueprint: `lemma-largest-punctual-subsheaf--3`) -/
theorem isGreatest_punctualPart {G : WeilSheaf k₀ l (affineLine k₀)}
    (hG : ((upperStar j).obj G).IsLisse) :
    IsGreatest {S : Subobject G | (S : WeilSheaf k₀ l (affineLine k₀)).support.Finite}
      (punctualPart j G) := by
  refine ⟨?_, fun S hS ↦ le_kernelSubobject _ _ ?_⟩
  · have h := support_finite_kernel_unit_app (l := l) j G
    rwa [← support_congr (kernelSubobjectIso
      ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).unit.app G))] at h
  · exact eq_zero_of_support_finite_lowerStar j hG hS _

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] in
/-- The quotient `G / G_p` of a Weil sheaf `G` by its punctual part has no nonzero subsheaf of
finite support, for a dense open `j : U₀ ↪ 𝔸¹` on which `G` is lisse: it embeds into the
direct image `j_* j^* G` of a lisse sheaf. (blueprint: `lemma-largest-punctual-subsheaf--4`) -/
theorem isZero_of_mono_cokernel_punctualPart {G : WeilSheaf k₀ l (affineLine k₀)}
    (hG : ((upperStar j).obj G).IsLisse) (G' : WeilSheaf k₀ l (affineLine k₀))
    (i : G' ⟶ cokernel (punctualPart j G).arrow) [Mono i] (hG' : G'.support.Finite) :
    IsZero G' := by
  set u := (upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).unit.app G
  let e : cokernel (punctualPart j G).arrow ≅ Abelian.coimage u :=
    cokernelIsoOfEq (kernelSubobject_arrow u).symm ≪≫ cokernelEpiComp _ _
  refine IsZero.of_mono_eq_zero i ((cancel_mono (e.hom ≫ Abelian.factorThruCoimage u)).1 ?_)
  rw [zero_comp]
  exact eq_zero_of_support_finite_lowerStar j hG hG' _

/-- The punctual part of a Weil sheaf `G` does not depend on the dense open on which `G` is lisse:
both are the largest punctual subsheaf of `G`. (blueprint: `lemma-largest-punctual-subsheaf--5`)
-/
theorem punctualPart_eq {U' : Scheme.{u}} [U'.Over (Spec (CommRingCat.of k₀))]
    (j' : U' ⟶ affineLine k₀) [IsOpenImmersion j']
    [QuasiCompact j'] [j'.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U' ↘ Spec (CommRingCat.of k₀))] [IsDominant j']
    {G : WeilSheaf k₀ l (affineLine k₀)} (hG : ((upperStar j).obj G).IsLisse)
    (hG' : ((upperStar j').obj G).IsLisse) :
    punctualPart j G = punctualPart j' G :=
  (isGreatest_punctualPart j hG).unique (isGreatest_punctualPart j' hG')

end WeilSheaf

end AlgebraicGeometry
