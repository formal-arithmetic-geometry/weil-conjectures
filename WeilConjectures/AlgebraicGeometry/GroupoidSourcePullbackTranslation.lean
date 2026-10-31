/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupoidScheme
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant

/-!
# Translation of the source pullbacks of a groupoid scheme

Source: Stacks Project, Groupoid Schemes, Tag 02YE, `lemma-diagram`, and Tag 03BI,
`lemma-finite-locally-free-disjoint-free`
(blueprint: lem-a1-groupoid-source-pullback-translation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem groupoid_comp_cancel
    {U R H : Scheme.{u}} {s t : R ⟶ U} {e : U ⟶ R} {i : R ⟶ R}
    {c : pullback s t ⟶ R} (hG : IsGroupoidScheme s t e i c)
    (a b d : H ⟶ R) (hab : a ≫ s = b ≫ t) (hbd : b ≫ s = d ≫ t)
    (hl : (pullback.lift a b hab ≫ c) ≫ s = d ≫ t)
    (hu : pullback.lift b d hbd ≫ c = a ≫ s ≫ e) :
    pullback.lift (pullback.lift a b hab ≫ c) d hl ≫ c = a := by
  have hr : a ≫ s = (pullback.lift b d hbd ≫ c) ≫ t := by
    simpa only [Category.assoc, hG.composition_target, pullback.lift_fst_assoc] using hab
  rw [hG.associative H a b d hab hbd hl hr]
  have he : a ≫ s = (a ≫ s ≫ e) ≫ t := by
    simp only [Category.assoc, hG.identity_target, Category.comp_id]
  calc
    _ = pullback.lift a (a ≫ s ≫ e) he ≫ c := by
      apply congrArg (fun k : H ⟶ pullback s t ↦ k ≫ c)
      apply pullback.hom_ext <;> simp [hu]
    _ = a := hG.comp_identity H a he

/-- Right composition identifies the two source pullbacks over their second projections,
and a finite locally free source has invariant fibre-degree strata.
Source: Stacks Project, Groupoid Schemes, Tags 02YE and 03BI
(blueprint: lem-a1-groupoid-source-pullback-translation).

Proof plan, following the node's four steps:
1. The composition-source law gives the forward map `(c, p₂)`. For the inverse,
   the inverse-target law makes `(q₁, i q₂)` composable; compose this pair with `c`
   and retain `q₂`. The pullback universal property gives exactly the four
   projection identities below, hence the asserted formulas on every test scheme.
2. On test points, associativity gives
   `c(c(a,b),i(b)) = c(a,c(b,i(b))) = c(a,e(t(b))) = a` and
   `c(c(d,i(b)),b) = c(d,c(i(b),b)) = c(d,e(s(b))) = d`.
   The second coordinate is unchanged. Evaluate at the identity test points of
   the two pullbacks to obtain both inverse identities as scheme morphisms.
3. The squares `(p₁,p₂;s,t)` and `(c,p₂;s,s)` are cartesian, the latter by the
   translation isomorphism. If `s` is finite locally free, apply clause (2) of
   `lem-weil-pbc-finite-flat-rank-iso` to both squares. The two ranks at `z` equal
   the fibre dimensions at `t(z)` and `s(z)`, respectively, proving their equality.
4. Clause (1) of the same rank lemma makes each degree stratum open. The equality
   of degrees gives equality of its inverse-image opens, hence of their canonical
   open subschemes. Conversely, choose the stratum of degree `d(s(z))`.

The existential compatibility proof only types the canonical inverse lift; it follows
from `pullback.condition` and `hG.inverse_target`. The isomorphism includes both inverse
identities. The degree is the existing `finrankΓ` of the residue-field fibre, literally
its dimension over the residue field. No geometric hypothesis is needed for translation;
finite local freeness occurs only in the second conjunct. -/
theorem groupoid_source_pullback_translation
    {U R : Scheme.{u}} (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback s t ⟶ R) (hG : IsGroupoidScheme s t e i c) :
    (∃ (F : pullback s t ≅ pullback s s)
      (h : pullback.fst s s ≫ s = (pullback.snd s s ≫ i) ≫ t),
      F.hom ≫ pullback.fst s s = c ∧
      F.hom ≫ pullback.snd s s = pullback.snd s t ∧
      F.inv ≫ pullback.fst s t =
        pullback.lift (pullback.fst s s) (pullback.snd s s ≫ i) h ≫ c ∧
      F.inv ≫ pullback.snd s t = pullback.snd s s) ∧
    (s.IsFiniteLocallyFree →
      (∀ z : R, (s.fiberToSpecResidueField (t z)).finrankΓ =
        (s.fiberToSpecResidueField (s z)).finrankΓ) ∧
      ∀ r : ℕ, ∃ V : U.Opens,
        (∀ x : U, x ∈ V ↔ (s.fiberToSpecResidueField x).finrankΓ = r) ∧
        s ⁻¹ᵁ V = t ⁻¹ᵁ V) := by
  let f : pullback s t ⟶ pullback s s :=
    pullback.lift c (pullback.snd s t) hG.composition_source
  have h : pullback.fst s s ≫ s = (pullback.snd s s ≫ i) ≫ t := by
    simpa only [Category.assoc, hG.inverse_target] using pullback.condition (f := s) (g := s)
  let j : pullback s s ⟶ pullback s t :=
    pullback.lift (pullback.fst s s) (pullback.snd s s ≫ i) h
  have hj : (j ≫ c) ≫ s = pullback.snd s s ≫ t := by
    simp only [Category.assoc, hG.composition_source, j, pullback.lift_snd_assoc,
      hG.inverse_source]
  let g : pullback s s ⟶ pullback s t :=
    pullback.lift (j ≫ c) (pullback.snd s s) hj
  have hfg : f ≫ g = 𝟙 _ := by
    apply pullback.hom_ext
    · have hb : pullback.snd s t ≫ s = (pullback.snd s t ≫ i) ≫ t := by
        simp only [Category.assoc, hG.inverse_target]
      have hl : (pullback.lift (pullback.fst s t) (pullback.snd s t)
          pullback.condition ≫ c) ≫ s = (pullback.snd s t ≫ i) ≫ t := by
        simpa using hG.composition_source.trans hb
      have hu : pullback.lift (pullback.snd s t) (pullback.snd s t ≫ i) hb ≫ c =
          pullback.fst s t ≫ s ≫ e := by
        rw [hG.comp_inverse]
        exact congrArg (fun k ↦ k ≫ e) pullback.condition.symm
      have hc := groupoid_comp_cancel hG (pullback.fst s t) (pullback.snd s t)
        (pullback.snd s t ≫ i) pullback.condition hb hl hu
      have hfj : f ≫ j = pullback.lift c (pullback.snd s t ≫ i)
          (hG.composition_source.trans hb) := by
        apply pullback.hom_ext <;> simp [f, j, Category.assoc]
      simp only [Category.assoc, g, pullback.lift_fst, Category.id_comp]
      change (f ≫ j) ≫ c = pullback.fst s t
      rw [hfj]
      simpa only [pullback.lift_fst_snd, Category.id_comp] using hc
    · simp [f, g]
  have hgf : g ≫ f = 𝟙 _ := by
    apply pullback.hom_ext
    · have hb : (pullback.snd s s ≫ i) ≫ s = pullback.snd s s ≫ t := by
        simp only [Category.assoc, hG.inverse_source]
      have hu : pullback.lift (pullback.snd s s ≫ i) (pullback.snd s s) hb ≫ c =
          pullback.fst s s ≫ s ≫ e := by
        rw [hG.inverse_comp]
        exact congrArg (fun k ↦ k ≫ e) pullback.condition.symm
      have hc := groupoid_comp_cancel hG (pullback.fst s s) (pullback.snd s s ≫ i)
        (pullback.snd s s) h hb hj hu
      simpa [f, g, j, Category.assoc] using hc
    · simp [f, g]
  let F : pullback s t ≅ pullback s s := ⟨f, g, hfg, hgf⟩
  have hf₁ : F.hom ≫ pullback.fst s s = c := by simp [F, f]
  have hf₂ : F.hom ≫ pullback.snd s s = pullback.snd s t := by simp [F, f]
  refine ⟨⟨F, h, hf₁, hf₂, ?_, ?_⟩, ?_⟩
  · simp [F, g, j]
  · simp [F, g]
  · intro hs
    let := hs
    have hc : IsPullback c (pullback.snd s t) s s :=
      .of_iso_pullback ⟨hG.composition_source⟩ F hf₁ hf₂
    have heq (z : R) : s.fiberDegree (t z) = s.fiberDegree (s z) :=
      (s.fiberDegree_of_isPullback (.of_hasPullback s t) z).symm.trans
        (s.fiberDegree_of_isPullback hc z)
    refine ⟨heq, fun r ↦ ?_⟩
    have hd := (finiteLocallyFree_fiberDimension_isLocallyConstant s).2.1
    let V : U.Opens :=
      ⟨{x | (s.fiberToSpecResidueField x).finrankΓ = r}, hd.isOpen_fiber r⟩
    refine ⟨V, fun _ ↦ Iff.rfl, ?_⟩
    ext z
    change s.fiberDegree (s z) = r ↔ s.fiberDegree (t z) = r
    rw [heq]

end AlgebraicGeometry
