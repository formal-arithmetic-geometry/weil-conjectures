/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Stalk
public import Mathlib.Topology.Connected.Clopen
import WeilConjectures.WeilSheaf.DirectImageRestriction
import WeilConjectures.WeilSheaf.LisseFiltration
import WeilConjectures.WeilSheaf.FiniteEtaleLisse
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.WeilSheaf.LisseLocus

/-! # A simple lisse Weil sheaf cannot cross a clopen partition

Source: the connected-component reduction in `sk-i-dl-general-real`.
(blueprint: lem-zl-irreducible-lisse-clopen-support).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.WeilSheaf

private theorem not_isZero_restriction
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (V : WeilSheaf k₀ l X) (U : X.Opens) (x : X.finitePoints)
    (hxU : x.1 ∈ U) (hx : Nontrivial (V.stalk x).carrier) :
    ¬ IsZero ((upperStar U.ι).obj V) := by
  intro h
  let z : U.toScheme := ⟨x.1, hxU⟩
  have hz : z ∈ U.toScheme.finitePoints :=
    (Scheme.Hom.mem_finitePoints_iff_of_isIso U.ι z).mp x.2
  have hd : (U.toScheme ↘ Spec (.of k₀)).degreeOver z =
      (X ↘ Spec (.of k₀)).degreeOver x.1 := by
    rw [← comp_over U.ι (Spec (.of k₀)), Scheme.Hom.degreeOver_comp_of_isIso]
    rfl
  obtain ⟨e⟩ := nonempty_equiv_stalk_upperStar U.ι V ⟨z, hz⟩ x rfl hd
  have := subsingleton_stalk_of_isZero h ⟨z, hz⟩
  have : Subsingleton (V.stalk x).carrier := e.toLinearEquiv.toEquiv.symm.subsingleton
  exact not_nontrivial_iff_subsingleton.mpr this hx

/-- The nonzero stalks of an irreducible lisse Weil sheaf lie on the same side of
any clopen partition of the arithmetic scheme.

Source: blueprint `sk-i-dl-general-real`, connected-component reduction, and
`thm-zl-real-mixed-by-curves`, extension of component filtrations by zero.
(blueprint: lem-zl-irreducible-lisse-clopen-support).

Proof: Write W for the clopen complement of U. Both inclusions are finite etale.
The direct image G of the restriction of V to U is lisse. Let K be the kernel
of the adjunction unit V → G. Kernels of maps of lisse Weil sheaves are lisse,
so irreducibility makes K zero or K → V an isomorphism. In the first case the
unit is mono. Restricting it to W gives a monomorphism from V restricted to W
into zero, since the two opens are disjoint. If y lies in W, stalk restriction
contradicts the nonzero stalk at y. In the second case the kernel equation makes
the unit zero. The adjunction triangle identity then makes the identity of V
restricted to U zero, contradicting its nonzero stalk at x. All the operations
and morphisms are in the native Weil category, so Frobenius compatibility is
retained. For U empty the premise x ∈ U is impossible; for U full the conclusion
is immediate. No geometric irreducibility is assumed. -/
theorem IsIrreducibleLisse.mem_clopen_of_nontrivial_stalk
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (V : WeilSheaf k₀ l X) (hV : V.IsIrreducibleLisse)
    (U : X.Opens) (hU : IsClopen (U : Set X))
    (x y : X.finitePoints) (hxU : x.1 ∈ U)
    (hx : Nontrivial (V.stalk x).carrier) (hy : Nontrivial (V.stalk y).carrier) :
    y.1 ∈ U := by
  classical
  by_contra hyU
  let W : X.Opens := ⟨(U : Set X)ᶜ, hU.isClosed.isOpen_compl⟩
  have : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by simpa using hU.isClosed)
  have hW : IsClosed (W : Set X) := U.isOpen.isClosed_compl
  have : IsClosedImmersion W.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by simpa using hW)
  let F := (upperStar U.ι).obj V
  let G := (lowerStar U.ι).obj F
  let η : V ⟶ G := (upperStarLowerStarAdjunction U.ι).unit.app V
  have hG : G.IsLisse := (hV.1.upperStar U.ι).lowerStar_of_finite_etale U.ι
  have hK : (kernel η).IsLisse := (hV.1.kernel_cokernel hG η).1
  have hx' := not_isZero_restriction V U x hxU hx
  have hy' := not_isZero_restriction V W y hyU hy
  rcases hV.2.2 (kernel η) (kernel.ι η) inferInstance hK with hzero | hiso
  · have : Mono η := Abelian.mono_of_kernel_ι_eq_zero η (hzero.eq_of_src _ _)
    have hzero' : IsZero ((upperStar W.ι).obj G) := by
      have hij : IsCompl (Set.range U.ι.base) (Set.range W.ι.base) := by
        rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
        change IsCompl (U : Set X) (U : Set X)ᶜ
        exact isCompl_compl
      apply isZero_iff_isZero_carrier.mpr
      apply ProEtale.AdicSheaf.isZero_of_isZero_X
      exact ProEtale.isZero_upperStar_lowerStar_of_disjoint _
        (Scheme.Hom.geometricFiberMap U.ι (comp_over U.ι _))
        (Scheme.Hom.geometricFiberMap W.ι (comp_over W.ι _))
        (Scheme.Hom.isCompl_range_geometricFiberMap U.ι W.ι _ _ hij).disjoint
        F.obj.carrier.X
    exact hy' (IsZero.of_mono ((upperStar W.ι).map η) hzero')
  · have : IsIso (kernel.ι η) := hiso
    have hη : η = 0 := (cancel_epi (kernel.ι η)).mp (by simp)
    dsimp only [η] at hη
    have hid := (upperStarLowerStarAdjunction U.ι).left_triangle_components V
    rw [hη, Functor.map_zero, zero_comp] at hid
    have hid' : 𝟙 F = 0 := hid.symm
    exact hx' ((IsZero.iff_id_eq_zero F).mpr hid')

end AlgebraicGeometry.WeilSheaf
