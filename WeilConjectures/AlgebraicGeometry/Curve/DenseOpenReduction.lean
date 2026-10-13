/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.BiproductAssertions
public import WeilConjectures.AlgebraicGeometry.Curve.DenseOpen
public import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenTmp
public import WeilConjectures.AlgebraicGeometry.Curve.Reductions

/-!
# Localisation of the eight curve assertions to a dense open

Let `X` be a reduced curve over an algebraically closed field `k` and `F` a constructible sheaf
of `𝐅_r`-modules on `X`. There is a dense open `j : U ⟶ X`, a finite disjoint union of
irreducible opens `U_a`, on which `F` is finite locally constant, and the eight curve
assertions for `F` are equivalent to those for `j_! j^* F`, and to those for all the
`j_{a,!} (F|_{U_a})`.

## Main statements

- `AlgebraicGeometry.IsCurve.exists_dense_assertions_iff_lowerShriek`: localisation to a dense
  open on which the coefficients are finite locally constant.
- `AlgebraicGeometry.IsCurve.exists_dense_assertions_iff_forall_lowerShriek`: the same, split
  along the irreducible components of the dense open.

## References

- Stacks Project, Section 59.83, <https://stacks.math.columbia.edu/tag/03SB>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-! ### Helpers -/

section Helpers

attribute [local instance] Abelian.hasFiniteBiproducts

variable {Λ}

/-- The complement of an open subscheme is the range of a closed immersion (the reduced
closed subscheme structure). -/
lemma Scheme.Opens.exists_isClosedImmersion_range_eq_compl {X : Scheme.{u}} (U : X.Opens) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
      Set.range i.base = (Set.range U.ι.base)ᶜ := by
  let I := Scheme.IdealSheafData.vanishingIdeal ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
  refine ⟨I.subscheme, I.subschemeι, inferInstance, ?_⟩
  rw [Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal, Scheme.Opens.range_ι]
  rfl

/-- An additive functor preserves the vanishing of `r • 𝟙`. -/
lemma Etale.nsmul_id_obj_eq_zero {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (P : C ⥤ D) [P.Additive] {F : C} {r : ℕ} (hF : r • 𝟙 F = 0) :
    r • 𝟙 (P.obj F) = 0 := by
  rw [← P.map_id, ← P.map_nsmul, hF, P.map_zero]

/-- Finite local constancy restricts from an open to a smaller open. -/
lemma Etale.isFiniteLocallyConstantSheaf_upperStar_ι_of_le {X : Scheme.{u}} {U V : X.Opens}
    (h : U ≤ V) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf ((V.ι)^*[ModuleCat.{u + 1} Λ].obj F)] :
    Scheme.IsFiniteLocallyConstantSheaf ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F) := by
  have := Scheme.IsFiniteLocallyConstantSheaf.upperStar (X.homOfLE h)
    ((V.ι)^*[ModuleCat.{u + 1} Λ].obj F)
  exact Scheme.IsFiniteLocallyConstantSheaf.of_iso ((Etale.upperStarComp
    (ModuleCat.{u + 1} Λ) (X.homOfLE h) V.ι U.ι (Scheme.homOfLE_ι _ _).symm).app F).symm

/-- **The eight assertions for a finite biproduct.** If `H ≅ ⨁ₐ Gₐ` is a finite biproduct of
constructible étale sheaves of `Λ`-modules and the eight assertions hold for every `Gₐ`, they
hold for `H`: the cohomology of `H` and its pullback maps are the finite sums of those of the
`Gₐ`, and the coefficient hypotheses pass from `H` to its subsheaves `Gₐ`. -/
theorem IsCurve.Assertions.of_iso_biproduct {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} {I : Type} [Fintype I]
    {G : I → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : H ≅ ⨁ G)
    (hGc : ∀ a, Scheme.IsConstructibleSheaf (G a)) (hG : ∀ a, IsCurve.Assertions Λ f (G a)) :
    IsCurve.Assertions Λ f H := by
  classical
  set Φ := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let π (a : I) : H ⟶ G a := e.hom ≫ biproduct.π G a
  let ι (a : I) : G a ⟶ H := biproduct.ι G a ≫ e.inv
  have htot : ∑ a, π a ≫ ι a = 𝟙 H := by
    calc ∑ a, π a ≫ ι a = e.hom ≫ (∑ a, biproduct.π G a ≫ biproduct.ι G a) ≫ e.inv := by
          simp only [π, ι, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
      _ = 𝟙 H := by rw [biproduct.total, Category.id_comp, e.hom_inv_id]
  have htot' : ∑ a, Φ.map (π a) ≫ Φ.map (ι a) = 𝟙 _ := by
    simp only [← Φ.map_comp, ← Φ.map_sum, htot, Φ.map_id]
  have hsum (q : ℕ) (x : Sheaf.H (Φ.obj H) q) :
      ∑ a, Sheaf.H.map (Φ.map (ι a)) q (Sheaf.H.map (Φ.map (π a)) q x) = x := by
    simp only [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_sum_apply, htot', Sheaf.H.map_id_apply]
  have hsum' {Y : Scheme.{u}} (g : Y ⟶ X) (q : ℕ)
      (x : Sheaf.H ((g)^*[AddCommGrpCat.{u + 1}].obj (Φ.obj H)) q) :
      ∑ a, Sheaf.H.map ((g)^*[AddCommGrpCat.{u + 1}].map (Φ.map (ι a))) q
        (Sheaf.H.map ((g)^*[AddCommGrpCat.{u + 1}].map (Φ.map (π a))) q x) = x := by
    simp only [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_sum_apply, ← Functor.map_comp,
      ← Functor.map_sum, htot', CategoryTheory.Functor.map_id, Sheaf.H.map_id_apply]
  have hsub (q : ℕ) (h : ∀ a, Subsingleton (Sheaf.H (Φ.obj (G a)) q)) :
      Subsingleton (Sheaf.H (Φ.obj H) q) :=
    AddMonoidHom.subsingleton_of_sum_comp_eq (fun a ↦ Sheaf.H.map (Φ.map (π a)) q)
      (fun a ↦ Sheaf.H.map (Φ.map (ι a)) q) (hsum q)
  have hfin (q : ℕ) (h : ∀ a, Finite (Sheaf.H (Φ.obj (G a)) q)) :
      Finite (Sheaf.H (Φ.obj H) q) :=
    AddMonoidHom.finite_of_sum_comp_eq (fun a ↦ Sheaf.H.map (Φ.map (π a)) q)
      (fun a ↦ Sheaf.H.map (Φ.map (ι a)) q) (hsum q)
  have hbij {Y : Scheme.{u}} (g : Y ⟶ X) (q : ℕ)
      (h : ∀ a, Function.Bijective (cohomologyMap g (Φ.obj (G a)) q)) :
      Function.Bijective (cohomologyMap g (Φ.obj H) q) :=
    ⟨AddMonoidHom.injective_of_sum_comp_eq (hsum q)
        (fun a ↦ Sheaf.H.map ((g)^*[AddCommGrpCat.{u + 1}].map (Φ.map (π a))) q)
        (cohomologyMap g (Φ.obj H) q) (fun a ↦ cohomologyMap g (Φ.obj (G a)) q)
        (fun a x ↦ cohomologyMap_map g q (Φ.map (π a)) x) (fun a ↦ (h a).1),
      AddMonoidHom.surjective_of_sum_comp_eq _ _ (hsum' g q)
        (cohomologyMap g (Φ.obj H) q) (fun a ↦ cohomologyMap g (Φ.obj (G a)) q)
        (fun a x ↦ cohomologyMap_map g q (Φ.map (ι a)) x) (fun a ↦ (h a).2)⟩
  refine ⟨fun q hq ↦ hsub q fun a ↦ (hG a).subsingleton_of_two_lt q hq,
    fun q hq ↦ hsub q fun a ↦ (hG a).subsingleton_of_one_lt_of_isAffine q hq,
    fun p _ _ hp q hq ↦ hsub q fun a ↦
      (hG a).subsingleton_of_one_lt_of_isPrimaryTorsionSheaf p (hp.of_mono (ι a)) q hq,
    fun q ↦ ?_, fun q ↦ ?_, fun k' _ _ X' ι₀ f' ι' h q ↦ ?_, fun k' _ _ X' ι₀ f' ι' h q ↦ ?_,
    fun {W} b _ ↦ ?_⟩
  · refine hfin q fun a ↦ ?_
    have := hGc a
    have := Scheme.IsTorsionSheafOfInvertibleOrder.of_mono (Spec (.of k)) (ι a)
    exact (hG a).finite_of_isTorsionSheafOfInvertibleOrder q
  · refine hfin q fun a ↦ ?_
    have := hGc a
    exact (hG a).finite_of_isProper q
  · refine hbij ι' q fun a ↦ ?_
    have := Scheme.IsTorsionSheafOfInvertibleOrder.of_mono (Spec (.of k)) (ι a)
    exact (hG a).bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder k' h q
  · exact hbij ι' q fun a ↦ (hG a).bijective_cohomologyMap_of_isProper k' h q
  · exact AddMonoidHom.surjective_of_sum_comp_eq _ _ (hsum' b 2)
      (cohomologyMap b (Φ.obj H) 2) (fun a ↦ cohomologyMap b (Φ.obj (G a)) 2)
      (fun a x ↦ cohomologyMap_map b 2 (Φ.map (ι a)) x)
      (fun a ↦ (hG a).surjective_cohomologyMap_of_isOpenImmersion b)

/-- The eight assertions are invariant under isomorphism (the coefficient hypotheses are
inherited along the inverse monomorphism). -/
theorem IsCurve.assertions_iff_of_iso {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (e : G ≅ F) : IsCurve.Assertions Λ f G ↔ IsCurve.Assertions Λ f F :=
  ⟨fun h ↦ h.of_iso e.symm (fun _ hp ↦ hp.of_mono e.hom)
      (fun _ ↦ Scheme.IsTorsionSheafOfInvertibleOrder.of_mono _ e.hom),
    fun h ↦ h.of_iso e (fun _ hp ↦ hp.of_mono e.inv)
      (fun _ ↦ Scheme.IsTorsionSheafOfInvertibleOrder.of_mono _ e.inv)⟩

/-- The canonical map `⨁ₐ j_{a,!} j_a^* F ⟶ F` attached to finitely many opens `U a`, assembled
from the counits of `j_{a,!} ⊣ j_a^*`. -/
noncomputable abbrev Etale.biproductDescCounit {X : Scheme.{u}} {n : ℕ} (U : Fin n → X.Opens)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (⨁ fun a ↦ ((U a).ι)_!open[ModuleCat.{u + 1} Λ].obj
      (((U a).ι)^*[ModuleCat.{u + 1} Λ].obj F)) ⟶ F :=
  biproduct.desc fun a ↦
    (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (U a).ι).counit.app F

/-- For pairwise disjoint opens `U a`, the map `⨁ₐ j_{a,!} j_a^* F ⟶ F` restricts to an
isomorphism over each `U b`: there the summands with `a ≠ b` vanish and the counit of
`j_{b,!} ⊣ j_b^*` restricts to an isomorphism. -/
lemma Etale.isIso_upperStar_map_biproductDescCounit {X : Scheme.{u}} {n : ℕ}
    (U : Fin n → X.Opens) (hU : Pairwise fun a b ↦ Disjoint (U a : Set X) (U b))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (b : Fin n) :
    IsIso (((U b).ι)^*[ModuleCat.{u + 1} Λ].map (Etale.biproductDescCounit U F)) := by
  classical
  set A := ModuleCat.{u + 1} Λ
  set G : Fin n → Sheaf X.smallEtaleTopology A :=
    fun a ↦ ((U a).ι)_!open[A].obj (((U a).ι)^*[A].obj F)
  set P := ((U b).ι)^*[A]
  have hz (a : Fin n) (hab : a ≠ b) : IsZero (P.obj (G a)) :=
    Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range A (U a).ι (U b).ι
      (by simpa only [Scheme.Opens.range_ι] using hU hab) _
  have hιπ : P.map (biproduct.ι G b) ≫ P.map (biproduct.π G b) = 𝟙 _ := by
    rw [← P.map_comp, biproduct.ι_π_self, P.map_id]
  have hπι : P.map (biproduct.π G b) ≫ P.map (biproduct.ι G b) = 𝟙 _ := by
    have h := congrArg P.map (biproduct.total (f := G))
    rw [P.map_sum, P.map_id, Finset.sum_eq_single b] at h
    · rw [← P.map_comp]
      exact h
    · intro a _ hab
      rw [P.map_comp, (hz a hab).eq_zero_of_tgt (P.map (biproduct.π G a)), zero_comp]
    · intro h
      exact absurd (Finset.mem_univ b) h
  have : IsIso (P.map (biproduct.ι G b)) := ⟨⟨_, hιπ, hπι⟩⟩
  have : IsIso (P.map (biproduct.ι G b) ≫ P.map (Etale.biproductDescCounit U F)) := by
    rw [← P.map_comp, biproduct.ι_desc]
    infer_instance
  exact IsIso.of_isIso_comp_left (P.map (biproduct.ι G b)) _

/-- For pairwise disjoint opens `U a` with union `V`, the map `⨁ₐ j_{a,!} j_a^* F ⟶ F` restricts
to an isomorphism over `V`. -/
lemma Etale.isIso_upperStar_iSup_map_biproductDescCounit {X : Scheme.{u}} {n : ℕ}
    (U : Fin n → X.Opens) (hU : Pairwise fun a b ↦ Disjoint (U a : Set X) (U b))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (((⨆ a, U a).ι)^*[ModuleCat.{u + 1} Λ].map (Etale.biproductDescCounit U F)) := by
  refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
    (U := fun a : ULift.{u} (Fin n) ↦ (U a.down).toScheme)
    (fun a ↦ X.homOfLE (le_iSup U a.down)) (fun x ↦ ?_) _ fun a ↦ ?_
  · obtain ⟨a, ha⟩ := (TopologicalSpace.Opens.mem_iSup (s := U)).mp x.2
    exact ⟨⟨a⟩, ⟨x.1, ha⟩, Subtype.ext (Scheme.homOfLE_apply (le_iSup U a) _)⟩
  · exact (NatIso.isIso_map_iff (Etale.upperStarComp (ModuleCat.{u + 1} Λ)
      (X.homOfLE (le_iSup U a.down)) (⨆ a, U a).ι (U a.down).ι
      (Scheme.homOfLE_ι _ _).symm) _).1 (Etale.isIso_upperStar_map_biproductDescCounit U hU F _)

/-- The biproduct `⨁ₐ j_{a,!} j_a^* F` is the extension by zero of its restriction to the union
`V` of the `U a`: the counit of `j_! ⊣ j^*` at it is an isomorphism, since it is one over `V`
and both sides vanish over the complement of `V`. -/
lemma Etale.isIso_counit_app_biproduct {X : Scheme.{u}} {n : ℕ} (U : Fin n → X.Opens)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ)
      (⨆ a, U a).ι).counit.app (⨁ fun a ↦ ((U a).ι)_!open[ModuleCat.{u + 1} Λ].obj
        (((U a).ι)^*[ModuleCat.{u + 1} Λ].obj F))) := by
  classical
  set A := ModuleCat.{u + 1} Λ
  set V := ⨆ a, U a
  set G : Fin n → Sheaf X.smallEtaleTopology A :=
    fun a ↦ ((U a).ι)_!open[A].obj (((U a).ι)^*[A].obj F)
  obtain ⟨Z, i, _, hij⟩ := V.exists_isClosedImmersion_range_eq_compl
  refine Etale.isIso_of_isIso_upperStar_map A V.ι i hij _ inferInstance ?_
  have hzG (a : Fin n) : IsZero ((i)^*[A].obj (G a)) := by
    refine Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range A (U a).ι i ?_ _
    rw [hij, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact Set.disjoint_compl_right_iff_subset.2 (le_iSup U a)
  have hz : IsZero ((i)^*[A].obj (⨁ G)) := by
    rw [IsZero.iff_id_eq_zero, ← (i)^*[A].map_id, ← biproduct.total, Functor.map_sum]
    refine Finset.sum_eq_zero fun a _ ↦ ?_
    rw [Functor.map_comp, (hzG a).eq_zero_of_tgt ((i)^*[A].map (biproduct.π G a)), zero_comp]
  have hz' : IsZero ((i)^*[A].obj ((V.ι)_!open[A].obj ((V.ι)^*[A].obj (⨁ G)))) :=
    Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range A V.ι i
      (by rw [hij]; exact disjoint_compl_right) _
  exact hz'.isIso hz _

/-- For pairwise disjoint opens `U a` with union `V` (`j : V ⟶ X`), the extension by zero
`j_! j^* F` is the finite biproduct `⨁ₐ j_{a,!} j_a^* F`. -/
noncomputable def Etale.biproductIsoLowerShriekUpperStar {X : Scheme.{u}} {n : ℕ}
    (U : Fin n → X.Opens) (hU : Pairwise fun a b ↦ Disjoint (U a : Set X) (U b))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (⨁ fun a ↦ ((U a).ι)_!open[ModuleCat.{u + 1} Λ].obj
      (((U a).ι)^*[ModuleCat.{u + 1} Λ].obj F)) ≅
      ((⨆ a, U a).ι)_!open[ModuleCat.{u + 1} Λ].obj
        (((⨆ a, U a).ι)^*[ModuleCat.{u + 1} Λ].obj F) :=
  have := Etale.isIso_upperStar_iSup_map_biproductDescCounit U hU F
  have := Etale.isIso_counit_app_biproduct U F
  (asIso ((Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ)
    (⨆ a, U a).ι).counit.app _)).symm ≪≫ (((⨆ a, U a).ι)_!open[ModuleCat.{u + 1} Λ]).mapIso
      (asIso (((⨆ a, U a).ι)^*[ModuleCat.{u + 1} Λ].map (Etale.biproductDescCounit U F)))

end Helpers

/-- **Dense-open localisation reduction.** Let `X` be a reduced curve over an algebraically
closed field `k` and `F` a constructible sheaf of `Λ`-modules killed by a prime `r`, over a
finite ring `Λ`. There is a dense open `j : U ⟶ X` whose connected components are irreducible
and on which `F` is finite locally constant, and for it the eight assertions for `F` are
equivalent to those for `j_! j^* F`: the open–closed sequence `0 → j_! j^* F → F → i_* i^* F → 0`
has third term
supported on the zero-dimensional complement `Z` of `U`, whose cohomology is concentrated in
degree zero and invariant under field extension.
(blueprint: `lemma-weil-pbc-curve-dense-open-reduction`) -/
theorem IsCurve.exists_dense_assertions_iff_lowerShriek [Finite Λ] {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (r : ℕ) [Fact r.Prime] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] (hF : r • 𝟙 F = 0) :
    ∃ U : X.Opens, Dense (U : Set X) ∧
      (∀ x ∈ (U : Set X), IsIrreducible (connectedComponentIn (U : Set X) x)) ∧
      Scheme.IsFiniteLocallyConstantSheaf ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F) ∧
      (IsCurve.Assertions Λ f F ↔ IsCurve.Assertions Λ f
        ((U.ι)_!open[ModuleCat.{u + 1} Λ].obj ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F))) :=
  sorry

/-- **Dense-open localisation, componentwise.** Let `C` be a reduced curve over an
algebraically closed field `k` and `F` a constructible sheaf of `Λ`-modules killed by a prime
`r`, over a finite ring `Λ`. There are finitely many pairwise disjoint irreducible opens
`U_a ⊆ C`, with dense union `U` and zero-dimensional complement `Z = C ∖ U`, on each of which
`F` is finite locally constant, such that, writing `j_a : U_a ⟶ C` for the inclusions,
`C(C, F) ↔ ∀ a, C(C, j_{a,!}(F|_{U_a}))`. This combines the open–closed sequence
`0 → j_! j^* F → F → i_* i^* F → 0`, the assertions on the zero-dimensional `Z`, the
decomposition `j_! j^* F = ⨁_a j_{a,!}(F|_{U_a})` and dévissage.
(blueprint: `lem-weil-pbc-curve-dense-open-localization`) -/
theorem IsCurve.exists_dense_assertions_iff_forall_lowerShriek [Finite Λ] {k : Type u}
    [Field k]
    [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsReduced C]
    (r : ℕ) [Fact r.Prime] (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] (hF : r • 𝟙 F = 0) :
    ∃ (n : ℕ) (U : Fin n → C.Opens), Dense (⋃ a, (U a : Set C)) ∧
      Pairwise (fun a b ↦ Disjoint (U a : Set C) (U b)) ∧ (∀ a, IsIrreducible (U a : Set C)) ∧
      topologicalKrullDim ↥(⋃ a, (U a : Set C))ᶜ ≤ 0 ∧
      (∀ a, Scheme.IsFiniteLocallyConstantSheaf (((U a).ι)^*[ModuleCat.{u + 1} Λ].obj F)) ∧
      (IsCurve.Assertions Λ f F ↔ ∀ a, IsCurve.Assertions Λ f
        (((U a).ι)_!open[ModuleCat.{u + 1} Λ].obj (((U a).ι)^*[ModuleCat.{u + 1} Λ].obj F))) :=
  sorry

end AlgebraicGeometry
