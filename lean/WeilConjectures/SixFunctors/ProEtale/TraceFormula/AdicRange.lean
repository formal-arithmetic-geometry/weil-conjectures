/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitRange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractibleProducts
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Adic

/-!
# Cohomological range of the adic realization

The realization `K_{𝒪_E} = R lim_n K_n` of a normalized system `K_•` whose levels lie in a
common range of degrees `[a, b]` lies in the same range (blueprint `sk-prop-trace-adic` (i)).

Countable products of sheaves on the pro-étale site are exact, so the cohomology of
`R lim_n K_n` sits in the exact sequences
`0 ⟶ R¹lim_n H^{i-1}(K_n) ⟶ Hⁱ(R lim_n K_n) ⟶ lim_n Hⁱ(K_n) ⟶ 0`. In the top degree `b` the
transitions `H^b(K_{n+1}) ⟶ H^b(K_n)` are surjective (right exactness of the base change
`- ⊗ᴸ_{A_{n+1}} A_n` in the top degree, read off a strict model of the tower), and the
pro-étale site is covered by weakly contractible objects, so the `R¹lim` term vanishes there.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

namespace AlgebraicGeometry.ProEtale

variable {R : Type (u + 1)} [CommRing R] (I : Ideal R) {X : Scheme.{u}}

/-- On the pro-étale site, `1 - t` is an epimorphism on a product `∏ Fₙ` of the terms of a tower
`F` of sheaves of modules with epimorphic transitions, `t` being the transition endomorphism:
the `R¹lim` of such a tower vanishes. The site is covered by weakly contractible objects
(Stacks 0990), on which this is the Mittag-Leffler property of towers of surjections. -/
lemma epi_one_sub_of_epi {Λ : Type (u + 1)} [Ring Λ]
    {F : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    {P : Fan fun n : ℕ ↦ F.obj (op n)} (hP : IsLimit P) (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    (hF : ∀ n : ℕ, Epi (F.map (homOfLE n.le_succ).op)) : Epi (𝟙 P.pt - t) :=
  GrothendieckTopology.epi_one_sub_of_forall_exists.{u + 1, u}
    (fun W : X.ProEt ↦ IsAffine W.left ∧
      (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W)
    (fun V ↦ Scheme.ProEt.exists_isWeaklyContractible_cover V) (fun _ hW ↦ hW.2) hP t ht hF

variable {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})
  {K : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))}
  {L : ∀ n : ℕ,
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (R ⧸ I ^ n)))}
  (hK : IsNormalizedTower I K L) (c : Cone K) (hc : IsHomotopyLimit c)

include hϖ hI hK in
/-- The transitions `K_{n+1} ⟶ K_n` of a normalized system whose first level `K_1` lies in
degrees `≤ b` are surjective on `H^b`: this is right exactness of the base change
`- ⊗ᴸ_{A_{n+1}} A_n` in the top degree, read off a strict model of the tower
(`CochainComplex.IsNormalizedAdicTower.epi_homologyMap_map`). -/
lemma IsNormalizedTower.epi_homologyFunctor_map (b : ℤ) (hb : (K.obj (op 1)).IsLE b) (n : ℕ) :
    Epi ((DerivedCategory.homologyFunctor _ b).map (K.map (homOfLE n.le_succ).op)) := by
  obtain ⟨eK, t, ht, hmap⟩ := hK
  obtain ⟨T, e, hT, he⟩ := DerivedCategory.exists_isNormalizedAdicTower
    (J := Scheme.ProEt.topology X) (R := R) (A := fun n ↦ R ⧸ I ^ n)
    (fun h ↦ Ideal.Quotient.factor (Ideal.pow_le_pow_right h))
    (fun n ↦ Ideal.Quotient.mk (I ^ n)) (fun h ↦ Ideal.Quotient.factor_comp_mk _)
    (fun _ _ ↦ Ideal.Quotient.factor_comp _ _) (Ideal.Quotient.mk_pow_eq_zero_of_eq_span hI)
    (Ideal.Quotient.exact_mul_mk_pow hϖ hI) (fun _ ↦ Ideal.Quotient.factor_surjective _)
    (Ideal.Quotient.ker_factor_pow_eq_span hI) L t ht
  let E (n : ℕ) : DerivedCategory.Q.obj (T.obj (op n)) ≅ K.obj (op n) := e n ≪≫ (eK n).symm
  have hE (n : ℕ) : K.map (homOfLE n.le_succ).op =
      (E (n + 1)).inv ≫ DerivedCategory.Q.map (T.map (homOfLE n.le_succ).op) ≫ (E n).hom := by
    simp only [E, Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [reassoc_of% (he n), hmap n]
    simp
  have h₁ : (T.obj (op 1)).ExactAt (b + 1) := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    refine (DerivedCategory.isZero_of_isLE _ b (b + 1) (by lia) (hX := hb)).of_iso ?_
    exact ((DerivedCategory.homologyFunctorFactors _ (b + 1)).app _).symm ≪≫
      (DerivedCategory.homologyFunctor _ (b + 1)).mapIso (E 1)
  have := hT.epi_homologyMap_map b h₁ n
  rw [hE n, Functor.map_comp, Functor.map_comp]
  have hQ : (DerivedCategory.homologyFunctor _ b).map
      (DerivedCategory.Q.map (T.map (homOfLE n.le_succ).op)) = _ :=
    (NatIso.naturality_2 (DerivedCategory.homologyFunctorFactors _ b)
      (T.map (homOfLE n.le_succ).op)).symm
  rw [hQ]
  exact epi_comp' inferInstance (epi_comp' (epi_comp' inferInstance (epi_comp' this inferInstance))
    inferInstance)

include hϖ hI hK hc in
/-- Adic realization, cohomological range (blueprint `sk-prop-trace-adic` (i)): if all levels of
a normalized system lie in a common range of degrees `[a, b]`, so does its realization
`K_{𝒪_E} = R lim_n K_n`. -/
theorem isGE_and_isLE_realization (a b : ℤ)
    (hab : ∀ n : ℕ, (K.obj (op n)).IsGE a ∧ (K.obj (op n)).IsLE b) :
    c.pt.IsGE a ∧ c.pt.IsLE b := by
  have := CountableAB4Star.ofShape (C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) ℕ
  exact DerivedCategory.isGE_and_isLE_of_isHomotopyLimit hc a b hab
    (hK.epi_homologyFunctor_map I hϖ hI b (hab 1).2)
    fun _ _ hP t ht hF ↦ epi_one_sub_of_epi hP t ht hF

end AlgebraicGeometry.ProEtale
