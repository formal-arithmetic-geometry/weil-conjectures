/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

import Sheaf.Paper.DerivedNakayamaResolution
import Sheaf.Paper.DerivedNakayamaReductionComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.Topology.ProfiniteCondensedRing
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! The vanishing part of the derived Nakayama first-reduction argument.
Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-pe-derived-nakayama/sk-lem-pe-derived-nakayama-first-reduction.md`
(blueprint: det-pe-derived-nakayama-first-reduction-vanishing).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj
open ZeroObject
namespace AlgebraicGeometry.ProEtale

/-- Vanishing of every reduction and of a complete object from vanishing first reduction.
Source: the successive coefficient triangles and the completeness Roos triangle
(blueprint: det-pe-derived-nakayama-first-reduction-vanishing). -/
theorem derived_nakayama_first_reduction_vanishing
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    ∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      IsDerivedComplete l E X K →
      IsZero ((AdicCompletion.derivedReduction l E X 0).obj K) →
        (∀ n : ℕ, IsZero ((AdicCompletion.derivedReduction l E X n).obj K)) ∧
          IsZero K := by
  intro K hK hfirst
  classical
  have hzeroIntegral (n : ℕ) :
      IsZero ((DerivedNakayama.reductionFunctor l E X (n + 1)).obj K) ↔
        IsZero (AdicCompletion.integralLevel l E X K n) := by
    obtain ⟨e⟩ := derived_nakayama_reduction_comparison l E X n K
    exact e.isZero_iff.symm
  have hfirst' := (hzeroIntegral 0).2
    ((AdicCompletion.restrict l E X 0).map_isZero hfirst)
  obtain ⟨d, hd, r, hr, i, q, hi, hq, hres⟩ :=
    DerivedNakayama.derived_nakayama_resolution l E
  have hlevels (n : ℕ) :
      IsZero ((DerivedNakayama.reductionFunctor l E X (n + 1)).obj K) := by
    induction n with
    | zero => exact hfirst'
    | succ n ih =>
      obtain ⟨δ, hT⟩ := (hres X (n + 1) (Nat.succ_pos n)).2.2
        1 (by omega) (by omega) K
      exact Triangle.isZero₂_of_isZero₁₃ _ hT hfirst' ih
  have hint (n : ℕ) : IsZero (AdicCompletion.integralLevel l E X K n) :=
    (hzeroIntegral n).1 (hlevels n)
  have hfinite (n : ℕ) : IsZero ((AdicCompletion.derivedReduction l E X n).obj K) := by
    let G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (AdicCompletion.finiteRing l E X n) ⥤ AdicCompletion.Modules l E X :=
      Mod.comap (AdicCompletion.quotient l E X n)
    apply DerivedCategory.isZero_of_forall_isZero_homology
    intro j
    have hz := (DerivedCategory.homologyFunctor (AdicCompletion.Modules l E X) j).map_isZero
      (hint n)
    have hz' := hz.of_iso
      ((G.mapDerivedCategoryHomologyFunctorIso j).app
        ((AdicCompletion.derivedReduction l E X n).obj K))
    apply (IsZero.iff_id_eq_zero _).2
    apply G.map_injective
    rw [G.map_id, G.map_zero]
    exact hz'.eq_of_src _ _
  refine ⟨hfinite, ?_⟩
  obtain ⟨P, hP, ⟨e⟩, haug⟩ := hK
  let diagram := Discrete.functor (AdicCompletion.integralLevel l E X K)
  have hzdiagram : IsZero diagram :=
    (Functor.isZero_iff _).2 (fun n ↦ hint n.as)
  let cone : Cone diagram := Cone.mk 0 0
  let hc : IsLimit cone := IsLimit.ofIsZero cone hzdiagram (isZero_zero _)
  let : HasProduct (AdicCompletion.integralLevel l E X K) := ⟨⟨cone, hc⟩⟩
  have hzproduct : IsZero (∏ᶜ (AdicCompletion.integralLevel l E X K)) :=
    (limit.isLimit diagram).isZero_pt hzdiagram
  obtain ⟨p, δ, hT, hp⟩ := AdicCompletion.roos_isDerivedLimit l E X K P hP e
  have hzroos := Triangle.isZero₁_of_isZero₂₃ _ hT hzproduct hzproduct
  have := haug
  exact hzroos.of_iso (e.symm ≪≫ asIso (DerivedCategory.Q.map
    (AdicCompletion.augmentation l E X P)))

end AlgebraicGeometry.ProEtale
