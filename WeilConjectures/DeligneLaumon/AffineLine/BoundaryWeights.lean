/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import WeilConjectures.PointCountFiber
public import WeilConjectures.WeilSheaf.FourierTrace
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity
public import WeilConjectures.WeilSheaf.ShiftedSheaf
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.TraceBound

/-!
# The weights of the transform of the boundary sheaf

Let `M` be a lisse Weil sheaf on a dense open `j : U₀ ↪ 𝔸¹` with weights at most `w`, and let
`B = j_*M / j_!M` be its boundary sheaf, supported on the finite complement `S₀` of `U₀`. If the
Fourier transform of `B` is a shifted Weil sheaf `B'[1]`, then `B'` has weights at most `w`
(Step 4 of `prop-fd-zero-extension-comparison`).

By boundary semicontinuity `j_*M`, hence its quotient `B`, has weights at most `w`. The Fourier
trace formula writes the trace function of `B'` as the finite sum

`t_{B'}(y) = ∑_{x ∈ S₀(𝔽_{qⁿ})} t_B(x) ψ(Tr(x y))`,

whose terms are bounded by `N q^{nw/2}` since the Artin–Schreier values `ψ(Tr(x y))` are roots
of unity, and which has at most `∑_{s ∈ S₀} deg s` terms. At a closed point `y` of degree `d`
the traces of the powers `F_yᵐ` are values of `t_{B'}` at `𝔽_{q^{md}}`-points over `y`, so
they are `O(q_y^{mw/2})`, and the eigenvalues of `F_y` have absolute value at most `q_y^{w/2}`
(`FrobeniusModule.hasWeightsAtMost_of_norm_map_trace_pow_le`).

## Main statements

- `AlgebraicGeometry.WeilSheaf.hasWeightsAtMost_of_forall_norm_traceFunction_le`: a bound
  `O(q^{nw/2})` on the trace function gives weights at most `w`.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isZero_upperStar_boundarySheaf`: the boundary
  sheaf vanishes on `U₀`.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.hasWeightsAtMost_of_iso_fourierTransform`: the
  weight bound for `B'`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

end WeilSheaf

namespace WeilSheaf.LisseOnDenseOpen

variable (D : LisseOnDenseOpen k₀ l)

/-- **The boundary sheaf vanishes on `U₀`**: the restriction of `j_!M ⟶ j_*M` to `U₀` is an
isomorphism, and the restriction is exact. -/
theorem isZero_upperStar_boundarySheaf :
    IsZero ((WeilSheaf.upperStar D.j).obj D.boundarySheaf) := by
  rw [isZero_iff_isZero_carrier]
  have hj : IsOpenImmersion (Scheme.Hom.geometricFiberMap D.j
      (comp_over D.j (Spec (CommRingCat.of k₀)))) := inferInstance
  set jb := Scheme.Hom.geometricFiberMap D.j (comp_over D.j (Spec (CommRingCat.of k₀)))
  let Φ := (WeilSheaf.objectProperty k₀ l (affineLine k₀)).ι ⋙
    IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l (affineLine k₀))
  have h₀ : PreservesFiniteColimits (C := WeilSheaf k₀ l (affineLine k₀))
      (WeilSheaf.objectProperty k₀ l (affineLine k₀)).ι := inferInstance
  have h₁ : PreservesColimitsOfShape (C := WeilSheaf k₀ l (affineLine k₀)) WalkingParallelPair
      (WeilSheaf.objectProperty k₀ l (affineLine k₀)).ι := inferInstance
  have h₂ : PreservesColimitsOfShape WalkingParallelPair
      (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l (affineLine k₀))) := inferInstance
  have : PreservesColimitsOfShape WalkingParallelPair Φ :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair (_ ⋙ _))
  have : PreservesColimits (jb)^*ᵃ[l] :=
    (ProEtale.adicUpperStarLowerStarAdjunction l jb).leftAdjoint_preservesColimits
  have hc : Φ.map ((WeilSheaf.extensionByZeroToDirectImage D.j).app D.sheaf) =
      (ProEtale.adicOpenImmersionLowerShriekToLowerStar l jb).app D.sheaf.obj.carrier := rfl
  have : IsIso ((jb)^*ᵃ[l].map
      ((ProEtale.adicOpenImmersionLowerShriekToLowerStar l jb).app D.sheaf.obj.carrier)) := by
    have : IsIso ((ProEtale.adicOpenImmersionLowerShriekAdjunction l jb).unit.app
        D.sheaf.obj.carrier ≫ (jb)^*ᵃ[l].map
          ((ProEtale.adicOpenImmersionLowerShriekToLowerStar l jb).app D.sheaf.obj.carrier)) := by
      rw [ProEtale.adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((ProEtale.adicOpenImmersionLowerShriekAdjunction l jb).unit.app D.sheaf.obj.carrier) _
  have : Epi ((jb)^*ᵃ[l].map
      ((ProEtale.adicOpenImmersionLowerShriekToLowerStar l jb).app D.sheaf.obj.carrier)) :=
    IsIso.epi_of_iso _
  change IsZero ((jb)^*ᵃ[l].obj (Φ.obj (cokernel
    ((WeilSheaf.extensionByZeroToDirectImage D.j).app D.sheaf))))
  refine IsZero.of_iso (isZero_cokernel_of_epi ((jb)^*ᵃ[l].map
      ((ProEtale.adicOpenImmersionLowerShriekToLowerStar l jb).app D.sheaf.obj.carrier)))
    ((jb)^*ᵃ[l].mapIso (PreservesCokernel.iso Φ _ ≪≫ cokernel.mapIso _ _ (Iso.refl _)
      (Iso.refl _) (by rw [hc]; simp)) ≪≫ PreservesCokernel.iso _ _)

end WeilSheaf.LisseOnDenseOpen

end AlgebraicGeometry
