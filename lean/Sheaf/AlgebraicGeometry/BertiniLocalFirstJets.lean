/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M7
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import Sheaf.AlgebraicGeometry.ConormalSequenceSmoothImmersion
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

import Sheaf.AlgebraicGeometry.CompleteLinearSystemClosed
import Sheaf.AlgebraicGeometry.DifferentialFibreLocalFractions
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartSections
import WeilConjectures.AlgebraicGeometry.Modules.GenericRank
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Local first jets of an immersive generating system

Source: Stacks Project, Varieties, Tag 0FD6, final paragraph of `lemma-bertini`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

noncomputable section

/-- The actual relative cotangent fibre on an open of the source.
Source: Stacks Project, Tags 01UM and 02G1.
(blueprint: lem-zl-bertini-local-first-jets). -/
abbrev bertiniCotangentFibre {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (U : Y.Opens) (z : U) :
    ModuleCat ((U : Scheme).residueField z) :=
  Scheme.Hom.relativeDifferentialsStalkFibre (U.ι ≫ f) (𝟙 (U : Scheme)) z

/-- The value and relative differential of an actual local regular function.
The two entries use the same germ, after restriction to the specified source open.
Source: Stacks Project, Tags 01UM and 0FD6.
(blueprint: lem-zl-bertini-local-first-jets). -/
def bertiniLocalFirstJet {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (U : Y.Opens) (z : U)
    (W : Y.Opens) (hz : U.ι z ∈ W) (a : Γ(Y, W)) :
    (U : Scheme).residueField z × bertiniCotangentFibre f U z :=
  ((U : Scheme).residue z
      ((U : Scheme).presheaf.germ (U.ι ⁻¹ᵁ W) z hz (U.ι.app W a)),
    Scheme.Hom.relativeDifferentialsStalkFibreGerm (U.ι ≫ f) (𝟙 (U : Scheme)) z
      (U.ι ⁻¹ᵁ W) hz (U.ι.app W a))

private theorem cotangent_fibre_basis
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (d : ℕ) [SmoothOfRelativeDimension d f] (x : X) :
    Nonempty (Scheme.Hom.relativeDifferentialsStalkFibre f (𝟙 X) x ≃ₗ[X.residueField x]
      (Fin d → X.residueField x)) := by
  classical
  have := f.isFiniteLocallyFreeOfRank_relativeDifferentials d
  obtain ⟨I, V, hV, e⟩ :=
    SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u, u, u}.mp
      (inferInstance : f.relativeDifferentials.IsFiniteLocallyFreeOfRank d)
  obtain ⟨W, a, ⟨i, ⟨b⟩⟩, hx⟩ := hV ⊤ x trivial
  obtain ⟨ei⟩ := e i
  obtain ⟨basis, _⟩ := Scheme.Modules.exists_basis_stalk_of_over_iso_free ei (b.le hx)
  let : Algebra (X.presheaf.stalk x) (X.residueField x) :=
    ((𝟙 X : X ⟶ X).stalkMap x ≫ X.residue x).hom.toAlgebra
  let B := (basis.reindex Equiv.ulift).baseChange (X.residueField x)
  exact ⟨B.equivFun⟩

private theorem span_value_differential
    {K M I : Type*} [Field K] [AddCommGroup M] [Module K M]
    (v : I → K × M) (i : I) (hi : v i = (1, 0))
    (hd : Submodule.span K (Set.range fun j ↦ (v j).2) = ⊤) :
    Submodule.span K (Set.range v) = ⊤ := by
  let P := Submodule.span K (Set.range v)
  have hone : (1, 0) ∈ P := hi ▸ Submodule.subset_span (Set.mem_range_self i)
  have hfirst (a : K) : (a, 0) ∈ P := by
    simpa using P.smul_mem a hone
  have hsecond (m : M) : (0, m) ∈ P := by
    have hm : m ∈ Submodule.span K (Set.range fun j ↦ (v j).2) := hd ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨j, rfl⟩ := hm
      have h := P.sub_mem (Submodule.subset_span (Set.mem_range_self j)) (hfirst (v j).1)
      simpa only [Prod.sub_def, sub_self, sub_zero] using h
    | zero => exact P.zero_mem
    | add a b ha hb ha' hb' => simpa using P.add_mem ha' hb'
    | smul a b hb hb' => simpa using P.smul_mem a hb'
  apply top_unique
  rintro ⟨a, m⟩ _
  simpa using P.add_mem (hfirst a) (hsecond m)

private theorem chart_polynomial_surjective
    (k : Type u) [Field k] (I : Type u) (i : I) :
    Function.Surjective
      (MvPolynomial.eval₂Hom
        (((ℙ(I; Spec (.of k)) ↘ Spec (.of k)).appLE ⊤
          (ProjectiveSpace.standardOpen I (Spec (.of k)) i) le_top).hom.comp
            (Scheme.ΓSpecIso (.of k)).inv.hom)
        (ProjectiveSpace.coordRatio I (Spec (.of k)) i)) := by
  let P := ℙ(I; Spec (.of k))
  let W := ProjectiveSpace.standardOpen I (Spec (.of k)) i
  let b : Γ(Spec (.of k), ⊤) →+* Γ(P, W) :=
    (P ↘ Spec (.of k)).appLE ⊤ W le_top |>.hom
  let E := MvPolynomial.eval₂Hom (b.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
    (ProjectiveSpace.coordRatio I (Spec (.of k)) i)
  have hle : Subring.closure (Set.range b ∪
      Set.range (ProjectiveSpace.coordRatio I (Spec (.of k)) i)) ≤ E.range := by
    apply Subring.closure_le.mpr
    rintro a (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · refine ⟨MvPolynomial.C ((Scheme.ΓSpecIso (.of k)).hom a), ?_⟩
      simp [E]
    · exact ⟨MvPolynomial.X j, by simp [E]⟩
  have hc := ProjectiveSpace.closure_range_appLE_union_range_coordRatio
    (Spec (.of k)) i
  change Subring.closure (Set.range b ∪ _) = ⊤ at hc
  rw [hc] at hle
  intro a
  exact hle (Subring.mem_top a)

private theorem affine_stalk_fractions
    {Z Y : Scheme.{u}} (f : Y ⟶ Z) [SurjectiveOnStalks f]
    (W : Z.Opens) (hW : IsAffineOpen W) (y : Y) (hy : f y ∈ W)
    {A : Type u} [CommRing A] (E : A →+* Γ(Z, W)) (hE : Function.Surjective E)
    (a : Y.presheaf.stalk y) :
    ∃ p q : A,
      IsUnit (f.stalkMap y (Z.presheaf.germ W (f y) hy (E q))) ∧
      a * f.stalkMap y (Z.presheaf.germ W (f y) hy (E q)) =
        f.stalkMap y (Z.presheaf.germ W (f y) hy (E p)) := by
  let z : W := ⟨f y, hy⟩
  let := TopCat.Presheaf.algebra_section_stalk Z.presheaf z
  let := hW.isLocalization_stalk z
  obtain ⟨b, rfl⟩ := f.stalkMap_surjective y a
  obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj
    (hW.primeIdealOf z).asIdeal.primeCompl b
  obtain ⟨p', rfl⟩ := hE p
  obtain ⟨q', hq'⟩ := hE q.val
  refine ⟨p', q', ?_, ?_⟩
  · rw [hq']
    exact (IsLocalization.map_units (Z.presheaf.stalk (f y)) q).map (f.stalkMap y).hom
  · change b * Z.presheaf.germ W (f y) hy q.val =
      Z.presheaf.germ W (f y) hy (E p') at hpq
    have h := congrArg (f.stalkMap y) hpq
    simpa only [TopCat.Presheaf.stalk_open_algebraMap, CommRingCat.hom_comp,
      RingHom.map_mul, hq'] using h

private theorem projective_chart_fractions
    {k : Type u} [Field k] {X : Scheme.{u}} {I : Type u} [Finite I]
    (f : X ⟶ Spec (.of k)) (g : X ⟶ ℙ(I; Spec (.of k))) [SurjectiveOnStalks g]
    (hg : g ≫ (ℙ(I; Spec (.of k)) ↘ Spec (.of k)) = f)
    (i : I) (x : X) (hi : g x ∈ ProjectiveSpace.standardOpen I (Spec (.of k)) i) :
    let ρ : k →+* X.presheaf.stalk x :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom
    let c : I → X.presheaf.stalk x := fun j ↦ g.stalkMap x
      ((ℙ(I; Spec (.of k))).presheaf.germ
        (ProjectiveSpace.standardOpen I (Spec (.of k)) i) (g x) hi
        (ProjectiveSpace.coordRatio I (Spec (.of k)) i j))
    ∀ a : X.presheaf.stalk x, ∃ p q : MvPolynomial I k,
      IsUnit (MvPolynomial.eval₂Hom ρ c q) ∧
      a * MvPolynomial.eval₂Hom ρ c q = MvPolynomial.eval₂Hom ρ c p := by
  dsimp only
  let P := ℙ(I; Spec (.of k))
  let W := ProjectiveSpace.standardOpen I (Spec (.of k)) i
  let b := ((P ↘ Spec (.of k)).appLE ⊤ W le_top).hom.comp
    (Scheme.ΓSpecIso (.of k)).inv.hom
  let E := MvPolynomial.eval₂Hom b (ProjectiveSpace.coordRatio I (Spec (.of k)) i)
  let ρ := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
    X.presheaf.germ ⊤ x trivial).hom
  let c : I → X.presheaf.stalk x := fun j ↦ g.stalkMap x
    (P.presheaf.germ W (g x) hi (ProjectiveSpace.coordRatio I (Spec (.of k)) i j))
  have hE : (g.stalkMap x).hom.comp ((P.presheaf.germ W (g x) hi).hom.comp E) =
      MvPolynomial.eval₂Hom ρ c := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      change g.stalkMap x (P.presheaf.germ W (g x) hi (E (MvPolynomial.C a))) = ρ a
      rw [show E (MvPolynomial.C a) = b a from MvPolynomial.eval₂Hom_C _ _ _]
      change g.stalkMap x (P.presheaf.germ W (g x) hi
        (P.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
          ((P ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv a)))) = _
      rw [P.presheaf.germ_res_apply, Scheme.Hom.germ_stalkMap_apply]
      change X.presheaf.germ ⊤ x trivial
        (g.appTop ((P ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv a))) = _
      apply congrArg (X.presheaf.germ ⊤ x trivial)
      change g.appTop ((P ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv a)) =
        f.appTop ((Scheme.ΓSpecIso (.of k)).inv a)
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hg]
    · intro j
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      change g.stalkMap x (P.presheaf.germ W (g x) hi (E (MvPolynomial.X j))) = _
      rw [show E (MvPolynomial.X j) = ProjectiveSpace.coordRatio I (Spec (.of k)) i j
        from MvPolynomial.eval₂Hom_X' _ _ _]
  intro a
  obtain ⟨p, q, hq, hpq⟩ := affine_stalk_fractions g W
    (ProjectiveSpace.isAffineOpen_standardOpen I (Spec (.of k)) i) x hi E
    (chart_polynomial_surjective k I i) a
  have hEp (p : MvPolynomial I k) :
      g.stalkMap x (P.presheaf.germ W (g x) hi (E p)) = MvPolynomial.eval₂Hom ρ c p :=
    DFunLike.congr_fun hE p
  exact ⟨p, q, (hEp q) ▸ hq, by rwa [hEp, hEp] at hpq⟩

set_option linter.unusedVariables false in
/-- In a local frame, the value-and-differential columns of an immersive generating
system span the direct sum of the residue field and the relative cotangent fibre.
That cotangent fibre has dimension equal to the specified smooth relative dimension.

Source: Stacks Project, Varieties, Tag 0FD6, final paragraph of `lemma-bertini`,
with Constructions Tags 01NE and 01NF, and Morphisms Tag 02G1.
(blueprint: lem-zl-bertini-local-first-jets).

Proof: Generation supplies an index i whose section is nonvanishing at U.ι z.
Restrict to a neighbourhood W on which this section is a free generator e. Write
s_j = a_j e there, so a_i = 1. The projective map restricts to the i-th affine
chart, with coordinate ratios pulling back to a_j. An immersion is locally a
closed immersion followed by an open immersion. The conormal sequence therefore
surjects from the ambient differential fibre onto the source differential fibre.
Polynomial coordinate differentials generate the former, and their images are
precisely da_j(z); these span the latter over kappa(z). Smooth relative dimension
d gives a free differential stalk of rank d and hence a linear equivalence b of
its residue fibre with kappa(z)^d. The first-jet column for i is (1,0).
Subtracting a_j(z) times that column from column j yields (0,da_j(z)). Thus all
of kappa(z) plus the differential fibre is spanned. The argument takes place over
the residue field of z, without any closed-point or algebraic-closure assumption.
For d=0 the distinguished column alone spans the target. -/
theorem exists_bertiniLocalFirstJets
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [Smooth f]
    (L : Y.Modules) [L.IsInvertible] (r : ℕ)
    (s : ULift.{u} (Fin (r + 1)) → Γ(L, ⊤))
    (hgen : Epi (L.freeHomEquiv.symm (fun i ↦
      (SheafOfModules.unitHomEquiv L) (Scheme.Modules.homOfGlobalSection L (s i)))))
    [IsImmersion (ProjectiveSpace.homOfGeneratingSections (ULift.{u} (Fin (r + 1))) f L
      (fun i ↦ (SheafOfModules.unitHomEquiv L)
        (Scheme.Modules.homOfGlobalSection L (s i))) hgen)]
    (U : Y.Opens) (d : ℕ) [SmoothOfRelativeDimension d (U.ι ≫ f)] (z : U) :
    ∃ (W : Y.Opens) (hz : U.ι z ∈ W) (e : Γ(L, W))
      (he : Scheme.Modules.IsFreeGenerator e)
      (b : bertiniCotangentFibre f U z ≃ₗ[(U : Scheme).residueField z]
        (Fin d → (U : Scheme).residueField z)),
      Submodule.span ((U : Scheme).residueField z)
        (Set.range (fun i : Fin (r + 1) ↦ bertiniLocalFirstJet f U z W hz
          (he.coeff (L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s ⟨i⟩))))) = ⊤ := by
  classical
  let I := ULift.{u} (Fin (r + 1))
  let t : I → L.sections := fun i ↦ (SheafOfModules.unitHomEquiv L)
    (Scheme.Modules.homOfGlobalSection L (s i))
  let φ := ProjectiveSpace.homOfGeneratingSections I f L t hgen
  let P := ℙ(I; Spec (.of k))
  have ht (j : I) : (t j).val (Opposite.op ⊤) = s j := by
    change (Scheme.Modules.homOfGlobalSection L (s j)).app ⊤ (1 : Γ(Y, ⊤)) = s j
    rw [Scheme.Modules.homOfGlobalSection_app_one, Scheme.Modules.presheaf_map_id_apply]
  obtain ⟨ε, hε⟩ := generatingSections_pair f L t hgen
  have hcover : φ (U.ι z) ∈ ⨆ i, ProjectiveSpace.standardOpen I (Spec (.of k)) i := by
    rw [ProjectiveSpace.iSup_standardOpen]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hcover
  let C := ProjectiveSpace.standardOpen I (Spec (.of k)) i
  let W := φ ⁻¹ᵁ C
  have hz : U.ι z ∈ W := hi
  let e := L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s i)
  have he : Scheme.Modules.IsFreeGenerator e := by
    simpa only [ht] using
      ProjectiveSpace.isFreeGenerator_of_twistRestrict_iso ε.hom hε i
  let a : I → Γ(Y, W) := fun j ↦
    he.coeff (L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s j))
  have ha (j : I) : a j = φ.app C (ProjectiveSpace.coordRatio I (Spec (.of k)) i j) := by
    apply (he.coeff_eq_iff _ _).mpr
    simpa only [ht] using
      (ProjectiveSpace.map_eq_coordRatio_smul_of_twistRestrict_iso ε.hom hε i j).symm
  have hai : a i = 1 := by
    change he.coeff e = 1
    exact (he.coeff_eq_iff _ _).mpr (one_smul _ _)
  let g := U.ι ≫ φ
  have hg : g ≫ (P ↘ Spec (.of k)) = U.ι ≫ f := by
    rw [Category.assoc, (ProjectiveSpace.homOfGeneratingSections_spec I f L t hgen).1]
  have hfrac := projective_chart_fractions (U.ι ≫ f) g hg i z hi
  dsimp only at hfrac
  have hc (j : I) : g.stalkMap z (P.presheaf.germ C (g z) hi
      (ProjectiveSpace.coordRatio I (Spec (.of k)) i j)) =
      (U : Scheme).presheaf.germ (U.ι ⁻¹ᵁ W) z hz (U.ι.app W (a j)) := by
    rw [Scheme.Hom.germ_stalkMap_apply, ha]
    rfl
  dsimp only [P, C] at hc
  have hd := Scheme.Hom.span_differentialFibreGerm_of_localFractions (U.ι ≫ f)
    z (U.ι ⁻¹ᵁ W) hz (fun j : I ↦ U.ι.app W (a j)) (by
      simpa only [hc] using hfrac)
  obtain ⟨b⟩ := cotangent_fibre_basis (U.ι ≫ f) d z
  refine ⟨W, hz, e, he, b, ?_⟩
  apply span_value_differential _ i.down
  · change bertiniLocalFirstJet f U z W hz (a ⟨i.down⟩) = (1, 0)
    rw [show (⟨i.down⟩ : I) = i from rfl, hai]
    simp only [bertiniLocalFirstJet, Scheme.Hom.relativeDifferentialsStalkFibreGerm,
      map_one, PresheafOfModules.Derivation.d_one, map_zero, TensorProduct.tmul_zero]
  · change Submodule.span ((U : Scheme).residueField z)
      (Set.range fun j : Fin (r + 1) ↦
        Scheme.Hom.relativeDifferentialsStalkFibreGerm (U.ι ≫ f) (𝟙 (U : Scheme)) z
          (U.ι ⁻¹ᵁ W) hz (U.ι.app W (a ⟨j⟩))) = ⊤
    convert hd using 2
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨⟨j⟩, rfl⟩
    · rintro ⟨⟨j⟩, rfl⟩
      exact ⟨j, rfl⟩

end

end AlgebraicGeometry
