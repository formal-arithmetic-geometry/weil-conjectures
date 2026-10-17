/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitRange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.ReductionTower
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractibleProducts
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.BoundedConstructibleTower

/-!
# Reconstruction of a uniformly bounded constructible tower

Let `R` be a commutative ring and `ϖ ∈ R` a nonzerodivisor generating the ideal `I`, and put
`P_n = R ⧸ Iⁿ`. Let `M` be a uniformly bounded constructible adic tower on `T_proét` with levels
in `[a, b]` (`AlgebraicGeometry.ProEtale.IsConstructibleInTower`), and let `M_∞ = R lim_n Res M_n`
be its derived limit (a homotopy limit of the tower `n ↦ Res M_n` in `D(T_proét, R)`). We show
(blueprint `lem-weil-pbc-reconstruction-uniform-tower`,
`AlgebraicGeometry.ProEtale.reconstruction_uniformTower`) that

* `M_∞` is derived `I`-complete;
* the reduction tower `n ↦ M_∞ ⊗ᴸ P_n` is isomorphic to `n ↦ Res M_n`, compatibly with the
  transition maps and with the derived-limit projections `M_∞ ⟶ Res M_n`;
* `M_∞` has no cohomology outside `[a, b]`.

The first two assertions hold for every normalized tower on any site: the tower is represented
by a strict normalized adic tower of complexes (`DerivedCategory.exists_isNormalizedAdicTower`).
For the bounds, the transitions of a normalized tower are surjective on the top cohomology `H^b`
(`CochainComplex.IsNormalizedAdicTower.epi_homologyMap_map`: `T_{n+1}` is an extension of
`T_{n+1}/ϖⁿ ≃ Tₙ` by `T_{n+1}/ϖ ≃ T₁`), and towers of epimorphisms of pro-étale sheaves have
vanishing `R¹ lim`, the pro-étale site having enough weakly contractible objects.

## Implementation notes

The blueprint phrases uniform boundedness through local models `L_{αj}` on a pro-étale covering
of the strata of a stratification, and the isomorphism `L_{αj} ≅ M_∞|_{U_{αj}}`; the definition
`AlgebraicGeometry.ProEtale.IsUniformlyBoundedConstructible` of the project records the levels
instead (see the implementation notes of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.BoundedConstructibleTower`), and
only the homological bounds of the levels are used here.
-/

@[expose] public section

universe v u' u

open CategoryTheory Category Limits Opposite Pretriangulated

namespace CategoryTheory.Sheaf.NormalizedTower

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {R : Type (u + 1)} [CommRing R] {I : Ideal R} {ϖ : R}

/-- A normalized tower is represented by a strict normalized adic tower of complexes `T`:
`T ⋙ Q` is isomorphic to the underlying tower `n ↦ Res M_n` in `D(J, R)`. -/
lemma exists_isNormalizedAdicTower_iso (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})
    (M : NormalizedTower J I) :
    ∃ (T : ℕᵒᵖ ⥤ CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ),
      CochainComplex.IsNormalizedAdicTower ϖ T ∧ Nonempty (T ⋙ DerivedCategory.Q ≅ M.restrict) := by
  obtain ⟨T, e, hT, he⟩ := DerivedCategory.exists_isNormalizedAdicTower
    (fun {_ _} h ↦ Ideal.Quotient.factorPow I h) (fun n ↦ Ideal.Quotient.mk (I ^ n))
    (fun _ ↦ Ideal.Quotient.factor_comp_mk _)
    (fun _ _ ↦ RingHom.ext fun x ↦ by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl)
    (Ideal.Quotient.mk_pow_eq_zero_of_eq_span hI) (Ideal.Quotient.exact_mul_mk_pow hϖ hI)
    (fun _ ↦ Ideal.Quotient.factor_surjective _)
    (fun h ↦ Ideal.Quotient.ker_factor_pow_eq_span hI h) M.obj M.map M.isDerivedBaseChange
  let φ : T ⋙ DerivedCategory.Q ⟶ M.restrict :=
    NatTrans.ofOpSequence (fun n ↦ (e n).hom) fun n ↦ by
      rw [M.restrict_map_succ]
      exact he n
  have : ∀ n, IsIso (φ.app n) := fun n ↦ inferInstanceAs (IsIso (e n.unop).hom)
  have : IsIso φ := NatIso.isIso_of_isIso_app _
  exact ⟨T, hT, ⟨asIso φ⟩⟩

/-- **Reconstruction of a normalized tower from its derived limit.** For a homotopy limit `c`
of the tower `n ↦ Res M_n` of a normalized tower `M` (its derived limit `R lim_n Res M_n`), the
object `c.pt` is derived complete and its tower of reductions `c.pt ⊗ᴸ R/Iⁿ` is isomorphic to
`n ↦ Res M_n`, compatibly with the legs of `c` and the reduction maps `c.pt ⟶ c.pt ⊗ᴸ R/Iⁿ`. -/
theorem derivedComplete_and_exists_iso_of_isHomotopyLimit (hϖ : ϖ ∈ nonZeroDivisors R)
    (hI : I = Ideal.span {ϖ}) (M : NormalizedTower J I) {c : Cone M.restrict}
    (hc : IsHomotopyLimit c) :
    DerivedCategory.derivedComplete J I c.pt ∧
      ∃ e : DerivedCategory.derivedCompletionDiagram J I c.pt ≅ M.restrict, ∀ n : ℕ,
        c.π.app (op n) =
          (DerivedCategory.derivedCompletionCone J I c.pt).π.app (op n) ≫ e.hom.app (op n) := by
  obtain ⟨T, hT, ⟨eT⟩⟩ := exists_isNormalizedAdicTower_iso hϖ hI M
  let c₂ : Cone (T ⋙ DerivedCategory.Q) := { pt := c.pt, π := c.π ≫ eT.inv }
  have hc₂ : IsHomotopyLimit c₂ := hc.of_iso eT.symm c₂ (Iso.refl _) fun n ↦ by simp [c₂]
  obtain ⟨E, hE⟩ :=
    DerivedCategory.exists_derivedCompletionDiagram_iso_of_isNormalizedAdicTower hϖ hI hT hc₂
  refine ⟨hc₂.of_iso E.symm _ (Iso.refl _) fun n ↦ ?_, E ≪≫ eT, fun n ↦ ?_⟩
  · rw [hE n]
    simp [c₂]
  · have := hE n
    simp only [c₂, NatTrans.comp_app] at this
    simp [← reassoc_of% this]

end CategoryTheory.Sheaf.NormalizedTower

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} {ϖ : R} {T : Scheme.{u}}

/-- On the pro-étale site, a tower of epimorphisms of sheaves of modules satisfies the
Mittag-Leffler property `R¹ lim = 0`: the map `1 - t` on a product `∏ Fₙ` is an epimorphism.
The pro-étale site has enough weakly contractible objects. -/
lemma epi_one_sub_of_epi {F : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R)}
    {P : Fan fun n : ℕ ↦ F.obj (op n)} (hP : IsLimit P) (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    (hF : ∀ n : ℕ, Epi (F.map (homOfLE n.le_succ).op)) : Epi (𝟙 P.pt - t) :=
  GrothendieckTopology.epi_one_sub_of_forall_exists.{u + 1, u}
    (fun W : T.ProEt ↦ IsAffine W.left ∧
      (Scheme.ProEt.topology T).IsWeaklyContractible.{u + 1} W)
    (fun V ↦ Scheme.ProEt.exists_isWeaklyContractible_cover V) (fun _ hW ↦ hW.2) hP t ht hF

/-- Blueprint `lem-weil-pbc-reconstruction-uniform-tower`: Reconstruction of a uniform local
tower.

Let `ϖ ∈ R` be a nonzerodivisor generating `I` and let `M` be a uniformly bounded constructible
adic tower on `T_proét` with levels in `[a, b]`. For a homotopy limit `c` of the tower
`n ↦ Res M_n` (the derived limit `M_∞ = R lim_n M_n`):

* `M_∞` is derived `I`-complete;
* the reductions `M_∞ ⊗ᴸ R/Iⁿ` are isomorphic to the levels `Res M_n`, by an isomorphism of
  towers (hence compatible with the normalization maps) through which the derived-limit
  projections `M_∞ ⟶ Res M_n` are the reduction maps;
* `M_∞` has no cohomology outside `[a, b]`.

The local models of the blueprint are not part of the definition of uniform boundedness used in
the project, see the module docstring. -/
theorem reconstruction_uniformTower (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})
    {M : Sheaf.NormalizedTower (Scheme.ProEt.topology T) I} {a b : ℤ}
    (hM : IsConstructibleInTower a b M) {c : Cone M.restrict} (hc : IsHomotopyLimit c) :
    DerivedCategory.derivedComplete (Scheme.ProEt.topology T) I c.pt ∧
      (∃ e : DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology T) I c.pt ≅
          M.restrict, ∀ n : ℕ,
        c.π.app (op n) = (DerivedCategory.derivedCompletionCone (Scheme.ProEt.topology T) I
          c.pt).π.app (op n) ≫ e.hom.app (op n)) ∧
      c.pt.IsGE a ∧ c.pt.IsLE b := by
  refine ⟨(Sheaf.NormalizedTower.derivedComplete_and_exists_iso_of_isHomotopyLimit hϖ hI M
    hc).1, (Sheaf.NormalizedTower.derivedComplete_and_exists_iso_of_isHomotopyLimit hϖ hI M
    hc).2, ?_⟩
  obtain ⟨T', hT, ⟨eT⟩⟩ := Sheaf.NormalizedTower.exists_isNormalizedAdicTower_iso hϖ hI M
  -- the levels `Res M_n` lie in degrees `[a, b]`
  have hF (n : ℕ) : (M.restrict.obj (op n)).IsGE a ∧ (M.restrict.obj (op n)).IsLE b :=
    (Sheaf.restrictScalars _ _).homologyConcentratedIn_mapDerivedCategory_obj (hM n).2
  let c₂ : Cone (T' ⋙ DerivedCategory.Q) := { pt := c.pt, π := c.π ≫ eT.inv }
  have hc₂ : IsHomotopyLimit c₂ := hc.of_iso eT.symm c₂ (Iso.refl _) fun n ↦ by simp [c₂]
  have hF₂ (n : ℕ) : ((T' ⋙ DerivedCategory.Q).obj (op n)).IsGE a ∧
      ((T' ⋙ DerivedCategory.Q).obj (op n)).IsLE b := by
    have := (hF n).1
    have := (hF n).2
    exact ⟨DerivedCategory.TStructure.t.isGE_of_iso (eT.app (op n)).symm a,
      DerivedCategory.TStructure.t.isLE_of_iso (eT.app (op n)).symm b⟩
  -- the transitions are surjective on `H^b`
  have hb₁ : (T'.obj (op 1)).ExactAt (b + 1) := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have : (DerivedCategory.Q.obj (T'.obj (op 1))).IsLE b := (hF₂ 1).2
    exact (DerivedCategory.isZero_of_isLE _ b (b + 1) (by lia)).of_iso
      ((DerivedCategory.homologyFunctorFactors _ (b + 1)).app (T'.obj (op 1))).symm
  have hb (n : ℕ) : Epi ((DerivedCategory.homologyFunctor _ b).map
      ((T' ⋙ DerivedCategory.Q).map (homOfLE n.le_succ).op)) := by
    have := hT.epi_homologyMap_map b hb₁ n
    let φ := DerivedCategory.homologyFunctorFactors (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} R)) b
    have h := φ.hom.naturality (T'.map (homOfLE n.le_succ).op)
    have h' : (DerivedCategory.homologyFunctor _ b).map
        ((T' ⋙ DerivedCategory.Q).map (homOfLE n.le_succ).op) =
        φ.hom.app _ ≫ HomologicalComplex.homologyMap (T'.map (homOfLE n.le_succ).op) b ≫
          φ.inv.app _ := by
      rw [← Category.assoc]
      erw [← h]
      rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
      rfl
    rw [h']
    infer_instance
  exact DerivedCategory.isGE_and_isLE_of_isHomotopyLimit hc₂ a b hF₂ hb
    fun _ _ hP t ht hG ↦ epi_one_sub_of_epi hP t ht hG

end AlgebraicGeometry.ProEtale
