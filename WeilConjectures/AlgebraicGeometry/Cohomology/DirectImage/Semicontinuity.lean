/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Semicontinuity.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex

/-!
# Upper semicontinuity of fibre cohomology

The fibre cohomology dimensions are computed by a finite free complex, hence are upper
semicontinuous (`AlgebraicGeometry.Scheme.Modules.upperSemicontinuous_hFiber`), and the perfect
locus is open (`AlgebraicGeometry.Scheme.Modules.isOpen_perfectLocus`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}
variable (f : X ⟶ T) (ℱ : X.Modules)

section Coherence

variable [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
  [HasInjectiveResolutions X.Modules] [ℱ.IsFinitePresentation]

omit [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
  [HasInjectiveResolutions X.Modules] [ℱ.IsFinitePresentation] in
/-- A point `s` of an open `U` of `T` lifts to a morphism `Spec κ(s) ⟶ U`. -/
lemma exists_comp_ι_eq_fromSpecResidueField {U : T.Opens} {s : T} (hs : s ∈ U) :
    ∃ g : Spec (T.residueField s) ⟶ U.toScheme, g ≫ U.ι = T.fromSpecResidueField s := by
  have hrange : Set.range (T.fromSpecResidueField s).base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι, Scheme.range_fromSpecResidueField]
    simpa using hs
  exact ⟨IsOpenImmersion.lift U.ι (T.fromSpecResidueField s) hrange,
    IsOpenImmersion.lift_fac _ _ _⟩

omit [LocallyOfFinitePresentation f] [HasInjectiveResolutions X.Modules] in
/-- At a point `s` of an open `U` of the base over which `R f_* ℱ` is computed by a complex `P`
compatibly with base change, the fibre dimension `h^q(s)` is the dimension of the cohomology of
the fibre `P ⊗ κ(s)` of `P`. -/
theorem hFiber_eq_finrank_homology {U : T.Opens} {P : CochainComplex U.toScheme.Modules ℤ}
    (hbc : ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)))
    {s : T} (g : Spec (T.residueField s) ⟶ U.toScheme) (hg : g ≫ U.ι = T.fromSpecResidueField s)
    (q : ℕ) :
    ℱ.hFiber f q s =
      Module.finrank (T.residueField s) ((moduleSpecΓFunctor (R := T.residueField s)).obj
        ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q)) := by
  have := isGrothendieckAbelian (f.fiber s)
  have sq : IsPullback (f.fiberι s) (f.fiberToSpecResidueField s) f (g ≫ U.ι) := by
    rw [hg]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨e⟩ := hbc g _ _ sq q
  rw [hFiber_eq_finrank_sections_higherDirectImage f ℱ s q,
    ← (appLinearEquivOfIso e ⊤).finrank_eq]
  have h := finrank_eq_of_coe_eq
    ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q) ⊤ ⊤ rfl
  rw [finrank_top, finrank_top] at h
  exact h.symm

/-- **Semicontinuity of the fibre dimension.** With `f : X ⟶ T` proper of finite presentation
and `ℱ` an `𝒪_X`-module of finite presentation which is flat over `T`, the fibre dimension
`t ↦ dim_{κ(t)} H^q(X_t, ℱ_t)` is upper semicontinuous on `T`.

Locally on `T` the fibre dimension is `dim_{κ(t)} H^q(P ⊗ κ(t))` for the bounded complex `P` of
finite free modules of
`AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`: the pullback of
`P` to `Spec κ(t)` computes the higher direct images of the fibre `ℱ_t` to the point, whose global
sections are `H^q(X_t, ℱ_t)`
(`AlgebraicGeometry.Scheme.Modules.hFiber_eq_finrank_sections_higherDirectImage`). The dimension
of the cohomology of a complex of finite free modules is upper semicontinuous in the point, by the
lower semicontinuity of the ranks of its differentials
(`AlgebraicGeometry.Scheme.Modules.exists_finrank_homology_pullback_le`).

(blueprint: `sk-thm-picard-semicon`, `thm-pc-semicontinuity-base-change`) -/
theorem upperSemicontinuous_hFiber (hℱ : ℱ.IsFlatOver f) (q : ℕ) :
    UpperSemicontinuous (ℱ.hFiber f q) := by
  intro t m hm
  obtain ⟨U, P, d, htU, hP, hbc⟩ := exists_isFiniteFreeComplex_higherDirectImage f ℱ hℱ t
  -- at a point `s ∈ U`, the fibre dimension is the dimension of `H^q(P ⊗ κ(s))`
  have key (s : T) (hs : s ∈ U) : ∃ g : Spec (T.residueField s) ⟶ U.toScheme,
      g ≫ U.ι = T.fromSpecResidueField s ∧ ℱ.hFiber f q s =
        Module.finrank (T.residueField s) ((moduleSpecΓFunctor (R := T.residueField s)).obj
          ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q)) :=
    have ⟨g, hg⟩ := exists_comp_ι_eq_fromSpecResidueField hs
    ⟨g, hg, hFiber_eq_finrank_homology f ℱ hbc g hg q⟩
  obtain ⟨g, hg, hgt⟩ := key t htU
  obtain ⟨V, hV, hle⟩ := exists_finrank_homology_pullback_le hP.exists_iso_free q
    (Field.toIsField _) g
  have hmem (s : T) (g' : Spec (T.residueField s) ⟶ U.toScheme)
      (hg' : g' ≫ U.ι = T.fromSpecResidueField s) (v : U.toScheme) (hv : U.ι.base v = s) :
      Set.range g'.base ⊆ {v} := by
    rintro _ ⟨x, rfl⟩
    refine U.ι.isOpenEmbedding.injective ?_
    rw [← Scheme.Hom.comp_apply, hg', hv]
    exact (Scheme.range_fromSpecResidueField s).subset ⟨x, rfl⟩
  have : Nonempty (Spec (T.residueField t)) := inferInstance
  obtain ⟨x⟩ := this
  refine Filter.mem_of_superset ((U.ι ''ᵁ V).isOpen.mem_nhds ⟨g.base x, hV ⟨x, rfl⟩, ?_⟩) ?_
  · have := (Scheme.range_fromSpecResidueField t).subset ⟨x, rfl⟩
    rw [← hg] at this
    exact this
  · rintro _ ⟨v, hv, rfl⟩
    have hvU : U.ι.base v ∈ U := by
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
      exact ⟨v, rfl⟩
    obtain ⟨g', hg', hgs⟩ := key _ hvU
    change ℱ.hFiber f q (U.ι.base v) < m
    rw [hgs]
    refine (hle (Field.toIsField _) g' ((hmem _ g' hg' v rfl).trans ?_)).trans_lt (hgt ▸ hm)
    simpa using hv

/-- **Grauert's theorem.** In the situation of
`AlgebraicGeometry.Scheme.Modules.upperSemicontinuous_hFiber`, if moreover `T` is reduced and
the `q`-th fibre dimension is locally constant, then `R^q f_* ℱ` is locally free of finite rank,
the rank at a point being the fibre dimension there.

The rank is only attached to a neighbourhood of each point, not to `T` as a whole: on a
disconnected base the fibre dimension can be locally constant without being constant.

(blueprint: `sk-thm-picard-semicon`) -/
theorem exists_isFiniteLocallyFreeOfRank_higherDirectImage_of_isLocallyConstant [IsReduced T]
    (hℱ : ℱ.IsFlatOver f) (q : ℕ) (hq : IsLocallyConstant (ℱ.hFiber f q)) (t : T) :
    ∃ U : T.Opens, t ∈ U ∧
      (((higherDirectImage f q).obj ℱ).restrict U.ι).IsFiniteLocallyFreeOfRank
        (ℱ.hFiber f q t) :=
  sorry

/-- **The fibre cohomology vanishes in large degrees, locally on the base.** In the situation of
`AlgebraicGeometry.Scheme.Modules.upperSemicontinuous_hFiber`, every point `t` of `T` has an open
neighbourhood `U` and a bound `d` with `H^q(X_{t'}, ℱ_{t'}) = 0` for all `t' ∈ U` and all `q > d`.

Take for `U` and `d` the neighbourhood and the length of the bounded complex `P` of finite free
modules of `AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`. For
`t' ∈ U` its pullback to `Spec κ(t')` computes the higher direct images of `ℱ_{t'}` along
`X_{t'} ⟶ Spec κ(t')`, whose global sections are `H^q(X_{t'}, ℱ_{t'})`; it vanishes in degrees
`q > d`.

(blueprint: `lem-pc-flat-rf-open`) -/
theorem exists_forall_hFiber_eq_zero (hℱ : ℱ.IsFlatOver f) (t : T) :
    ∃ (U : T.Opens) (d : ℕ), t ∈ U ∧ ∀ t' ∈ U, ∀ q, d < q → ℱ.hFiber f q t' = 0 := by
  obtain ⟨U, P, d, htU, hP, hbc⟩ := exists_isFiniteFreeComplex_higherDirectImage f ℱ hℱ t
  refine ⟨U, d, htU, fun t' ht' q hq ↦ ?_⟩
  have hrange : Set.range (T.fromSpecResidueField t').base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι, Scheme.range_fromSpecResidueField]
    simpa using ht'
  let g := IsOpenImmersion.lift U.ι (T.fromSpecResidueField t') hrange
  have hg : g ≫ U.ι = T.fromSpecResidueField t' := IsOpenImmersion.lift_fac _ _ _
  have := isGrothendieckAbelian (f.fiber t')
  have sq : IsPullback (f.fiberι t') (f.fiberToSpecResidueField t') f (g ≫ U.ι) := by
    rw [hg]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨e⟩ := hbc g _ _ sq q
  -- the pulled back complex vanishes in degree `q > d`, hence so does its cohomology
  have hX : IsZero (((Modules.pullback g).mapHomologicalComplex _).obj P |>.X q) :=
    (Modules.pullback g).map_isZero (by have := hP.isStrictlyLE; exact P.isZero_of_isStrictlyLE d q)
  have hR : IsZero ((higherDirectImage (f.fiberToSpecResidueField t') q).obj
      ((Modules.pullback (f.fiberι t')).obj ℱ)) :=
    (ShortComplex.isZero_homology_of_isZero_X₂ _ hX).of_iso e.symm
  have : IsSeparated (f.fiberToSpecResidueField t') := by
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  have : QuasiCompact (f.fiberToSpecResidueField t') := by
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  obtain ⟨φ⟩ := nonempty_sections_higherDirectImage_iso_H (f.fiberToSpecResidueField t')
    ((Modules.pullback (f.fiberι t')).obj ℱ) q
  have : Subsingleton (((Modules.pullback (f.fiberι t')).obj ℱ).H q) :=
    have : Subsingleton Γ((higherDirectImage (f.fiberToSpecResidueField t') q).obj
        ((Modules.pullback (f.fiberι t')).obj ℱ), ⊤) :=
      ModuleCat.subsingleton_of_isZero
        ((SheafOfModules.evaluation _ (Opposite.op ⊤)).map_isZero hR)
    φ.symm.injective.subsingleton
  let := f.fiberOverSpecResidueField t'
  exact Module.finrank_zero_of_subsingleton

/-- **Openness of the bounded perfect locus.** With `f : X ⟶ T` proper of finite presentation and
`ℱ` an `𝒪_X`-module of finite presentation which is flat over `T`, the locus `U_{i,≤r}` of points
`t` of the perfect locus `U_i` at which `H^i(X_t, ℱ_t)` has dimension at most `r` is open in `T`.

Near a point `t`, the fibre cohomology vanishes in degrees `q > d`
(`AlgebraicGeometry.Scheme.Modules.exists_forall_hFiber_eq_zero`), so there `U_{i,≤r}` is cut out
by the finitely many conditions `h^q < 1` for `q ≤ d`, `q ≠ i`, and `h^i < r + 1`, each of which is
open by upper semicontinuity (`AlgebraicGeometry.Scheme.Modules.upperSemicontinuous_hFiber`).

(blueprint: `sk-thm-picard-perfect`) -/
theorem isOpen_setOf_hFiber_le (hℱ : ℱ.IsFlatOver f) (i r : ℕ) :
    IsOpen {t ∈ ℱ.perfectLocus f i | ℱ.hFiber f i t ≤ r} := by
  have hopen (q n : ℕ) : IsOpen {t | ℱ.hFiber f q t < n} :=
    (upperSemicontinuous_hFiber f ℱ hℱ q).isOpen_preimage n
  rw [isOpen_iff_forall_mem_open]
  rintro t ⟨ht, hti⟩
  obtain ⟨U, d, htU, hU⟩ := exists_forall_hFiber_eq_zero f ℱ hℱ t
  refine ⟨U ∩ (⋂ q ∈ Set.Iic d, {t' | q ≠ i → ℱ.hFiber f q t' < 1}) ∩
    {t' | ℱ.hFiber f i t' < r + 1}, ?_, ?_, ?_⟩
  · rintro t' ⟨⟨ht'U, hq⟩, hi⟩
    refine ⟨fun q hqi ↦ ?_, Nat.lt_succ_iff.mp hi⟩
    rcases le_or_gt q d with hqd | hqd
    · exact Nat.lt_one_iff.mp (Set.mem_iInter₂.mp hq q hqd hqi)
    · exact hU t' ht'U q hqd
  · refine (U.isOpen.inter ((Set.finite_Iic d).isOpen_biInter fun q _ ↦ ?_)).inter (hopen i _)
    by_cases hqi : q = i
    · simp [hqi]
    · simpa [hqi] using hopen q 1
  · exact ⟨⟨htU, Set.mem_iInter₂.mpr fun q _ hqi ↦ by simp [ht q hqi]⟩, Nat.lt_succ_of_le hti⟩

/-- **Openness of the perfect locus.** The perfect locus `U_i` is open in `T`, being the union
over `r` of the open loci `U_{i,≤r}` of
`AlgebraicGeometry.Scheme.Modules.isOpen_setOf_hFiber_le`. -/
theorem isOpen_perfectLocus (hℱ : ℱ.IsFlatOver f) (i : ℕ) : IsOpen (ℱ.perfectLocus f i) := by
  convert isOpen_iUnion fun r ↦ isOpen_setOf_hFiber_le f ℱ hℱ i r
  ext t
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨fun ht ↦ ⟨_, ht, le_rfl⟩, fun ⟨_, ht, _⟩ ↦ ht⟩

end Coherence

end AlgebraicGeometry.Scheme.Modules
