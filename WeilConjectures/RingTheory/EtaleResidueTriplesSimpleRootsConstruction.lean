/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.FieldTheory.IsSepClosed

import WeilConjectures.RingTheory.EtaleResidueTriplesColimit
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Etale.StandardEtale

/-!
# A finite étale stage carrying a prescribed simple root

Given a colimit of pointed étale residue triples, a monic polynomial over the colimit and a
simple root in `K`, we construct a single triple whose ring contains a root of the polynomial
mapping to the prescribed root.

## Implementation details

The union of the stage images is shown to be a subring by filteredness; restricting the cocone
maps to it gives a retraction of the inclusion, so every colimit element comes from a stage. This
argument needs no smallness assumption on the indexing category. The coefficients of the monic
polynomial are lifted to a common stage keeping the leading coefficient. Then the standard étale
algebra for the lifted polynomial and its derivative is formed; evaluation at the simple root
defines a map to `K`, whose kernel and induced residue-field embedding give a later triple.

## References

* [Stacks, Tag 04GN]
* [Stacks, Tag 04GP]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Cocone naturality makes the images grow along a transition map. -/
private theorem stage_range_subset {J : Type*} [Category J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) {j k : J} (a : j ⟶ k) :
    Set.range (c.ι.app j) ⊆ Set.range (c.ι.app k) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨F.map a x, ?_⟩
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (c.w a)) x

/-- Every element of the colimit of a filtered diagram of commutative rings lies in the image of
some stage. -/
private theorem stage_jointly_surjective {J : Type*} [Category J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c) (x : c.pt) :
    ∃ j, x ∈ Set.range (c.ι.app j) := by
  classical
  have : Nonempty J := IsFiltered.nonempty
  let S : Subring c.pt :=
    { carrier := {x | ∃ j, x ∈ Set.range (c.ι.app j)}
      zero_mem' := ⟨Classical.arbitrary J, 0, map_zero _⟩
      one_mem' := ⟨Classical.arbitrary J, 1, map_one _⟩
      add_mem' := by
        rintro x y ⟨j, hx⟩ ⟨k, hy⟩
        obtain ⟨x', hx'⟩ := stage_range_subset F c (IsFiltered.leftToMax j k) hx
        obtain ⟨y', hy'⟩ := stage_range_subset F c (IsFiltered.rightToMax j k) hy
        exact ⟨IsFiltered.max j k, x' + y', by
          change (c.ι.app _).hom (x' + y') = _
          rw [map_add, hx', hy']⟩
      mul_mem' := by
        rintro x y ⟨j, hx⟩ ⟨k, hy⟩
        obtain ⟨x', hx'⟩ := stage_range_subset F c (IsFiltered.leftToMax j k) hx
        obtain ⟨y', hy'⟩ := stage_range_subset F c (IsFiltered.rightToMax j k) hy
        exact ⟨IsFiltered.max j k, x' * y', by
          change (c.ι.app _).hom (x' * y') = _
          rw [map_mul, hx', hy']⟩
      neg_mem' := by
        rintro x ⟨j, y, rfl⟩
        exact ⟨j, -y, map_neg _ _⟩ }
  let d : Cocone F :=
    { pt := CommRingCat.of S
      ι :=
        { app := fun j ↦ CommRingCat.ofHom
            ((c.ι.app j).hom.codRestrict S (fun y ↦ ⟨j, y, rfl⟩))
          naturality := by
            intro j k a
            apply CommRingCat.hom_ext
            ext y
            apply Subtype.ext
            exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (c.w a)) y } }
  have he : hc.desc d ≫ CommRingCat.ofHom S.subtype = 𝟙 c.pt := by
    apply hc.hom_ext
    intro j
    rw [← Category.assoc, hc.fac]
    rfl
  have hx : ((hc.desc d).hom x : c.pt) = x :=
    DFunLike.congr_fun (congrArg CommRingCat.Hom.hom he) x
  exact hx ▸ ((hc.desc d).hom x).property

/-- A monic polynomial over the colimit of a filtered diagram of commutative rings is the image of
a monic polynomial over some stage. -/
private theorem stage_monic_polynomial {J : Type*} [Category J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (f : Polynomial c.pt) (hf : f.Monic) :
    ∃ j, ∃ g : Polynomial (F.obj j), g.Monic ∧ g.map (c.ι.app j).hom = f := by
  classical
  choose j hj using fun x : f.coeffs ↦ stage_jointly_surjective F c hc x.val
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  have hlifts : f ∈ Polynomial.lifts (c.ι.app k).hom := by
    rw [Polynomial.lifts_iff_coeffs_subset_range]
    intro x hx
    obtain ⟨a⟩ := hk (Finset.mem_image_of_mem j (Finset.mem_univ (⟨x, hx⟩ : f.coeffs)))
    exact stage_range_subset F c a (hj ⟨x, hx⟩)
  obtain ⟨g, hg, -, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hf
  exact ⟨k, g, hgm, hg⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The map from a triple's ring to the field `K` has kernel the distinguished prime. -/
private theorem triple_map_eq_zero {R : CommRingCat.{u}} {p : Spec R}
    {K : Type u} [Field K] {χ : (Spec R).residueField p ⟶ CommRingCat.of K}
    (t : EtaleResidueTriples R p K χ) (x : t.B) :
    ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom x = 0 ↔
      x ∈ t.q.asIdeal := by
  have he := Spec.algebraMap_residueFieldIso_inv t.B t.q
  change CommRingCat.ofHom (algebraMap t.B t.q.asIdeal.ResidueField) ≫
    (Spec.residueFieldIso t.B t.q).inv =
      (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q at he
  rw [← Category.assoc, ← he]
  change t.φ.hom ((Spec.residueFieldIso t.B t.q).inv.hom
    (algebraMap t.B t.q.asIdeal.ResidueField x)) = 0 ↔ _
  rw [map_eq_zero_iff _ t.φ.hom.injective,
    map_eq_zero_iff _ (Spec.residueFieldIso t.B t.q).inv.hom.injective,
    Ideal.algebraMap_residueField_eq_zero]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A monic polynomial over a triple's ring with a simple root in `K` acquires a root mapping to
that simple root in some later triple. -/
private theorem triple_simple_root_extension {R : CommRingCat.{u}} {p : Spec R}
    {K : Type u} [Field K] {χ : (Spec R).residueField p ⟶ CommRingCat.of K}
    (t : EtaleResidueTriples R p K χ) (g : Polynomial t.B) (hg : g.Monic)
    (a : K)
    (ha : g.eval₂ ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom a = 0)
    (hda : g.derivative.eval₂
      ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom a ≠ 0) :
    ∃ s : EtaleResidueTriples R p K χ, ∃ m : t ⟶ s, ∃ x : s.B,
      (g.map (etaleResidueTriplesRingDiagram R p K χ |>.map m).hom).IsRoot x ∧
      ((ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ).hom x = a := by
  classical
  let β := ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom
  let : Algebra t.B K := β.toAlgebra
  let P : StandardEtalePair t.B := ⟨g, hg, g.derivative, ⟨1, 0, 1, by simp⟩⟩
  have hP : P.HasMap a := ⟨ha, hda.isUnit⟩
  let γ : P.Ring →ₐ[t.B] K := P.lift a hP
  let q : Spec (CommRingCat.of P.Ring) := ⟨RingHom.ker γ.toRingHom, RingHom.ker_isPrime _⟩
  have : q.asIdeal.IsPrime := q.isPrime
  have hunit : q.asIdeal.primeCompl ≤ Submonoid.comap γ.toRingHom (IsUnit.submonoid K) :=
    fun x hx ↦ isUnit_iff_ne_zero.mpr (by simpa [q, RingHom.mem_ker] using hx)
  let e : q.asIdeal.ResidueField →+* K :=
    Ideal.ResidueField.lift q.asIdeal γ.toRingHom le_rfl hunit
  let φ : (Spec (CommRingCat.of P.Ring)).residueField q ⟶ CommRingCat.of K :=
    (Spec.residueFieldIso (CommRingCat.of P.Ring) q).hom ≫ CommRingCat.ofHom e
  have hγ : (ΓSpecIso (CommRingCat.of P.Ring)).inv ≫
      (Spec (CommRingCat.of P.Ring)).Γevaluation q ≫ φ =
      CommRingCat.ofHom γ.toRingHom := by
    have he := Spec.algebraMap_residueFieldIso_inv (CommRingCat.of P.Ring) q
    change CommRingCat.ofHom (algebraMap P.Ring q.asIdeal.ResidueField) ≫
      (Spec.residueFieldIso (CommRingCat.of P.Ring) q).inv =
        (ΓSpecIso (CommRingCat.of P.Ring)).inv ≫
          (Spec (CommRingCat.of P.Ring)).Γevaluation q at he
    rw [← Category.assoc, ← he]
    dsimp only [φ]
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    apply CommRingCat.hom_ext
    ext x
    exact Ideal.ResidueField.lift_algebraMap q.asIdeal γ.toRingHom le_rfl hunit x
  let i : t.B ⟶ CommRingCat.of P.Ring := CommRingCat.ofHom (algebraMap t.B P.Ring)
  have hi : i ≫ CommRingCat.ofHom γ.toRingHom =
      (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ := by
    apply CommRingCat.hom_ext
    ext x
    exact γ.commutes x
  have hq : Spec.map i q = t.q := by
    apply PrimeSpectrum.ext
    ext x
    change γ (algebraMap t.B P.Ring x) = 0 ↔ x ∈ t.q.asIdeal
    rw [γ.commutes]
    exact triple_map_eq_zero t x
  have : Etale (Spec.map i) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact (RingHom.etale_algebraMap).mpr inferInstance
  have : Etale (Spec.map t.α) := t.etale
  let s : EtaleResidueTriples R p K χ :=
    { B := CommRingCat.of P.Ring
      α := t.α ≫ i
      etale := by rw [Spec.map_comp]; infer_instance
      q := q
      over := by
        rw [Spec.map_comp]
        change Spec.map t.α (Spec.map i q) = p
        rw [hq, t.over]
      φ := φ
      compatible := by rw [Category.assoc, hγ, hi]; exact t.compatible }
  let m : t ⟶ s := InducedCategory.homMk
    (Under.homMk (Over.homMk i (by
      change i ≫ ((ΓSpecIso (CommRingCat.of P.Ring)).inv ≫
        (Spec (CommRingCat.of P.Ring)).Γevaluation q ≫ φ) = _
      rw [hγ, hi]
      rfl)) (by rfl))
  refine ⟨s, m, P.X, ?_, ?_⟩
  · change (g.map (algebraMap t.B P.Ring)).IsRoot P.X
    simpa only [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def]
      using P.hasMap_X.1
  · change ((ΓSpecIso (CommRingCat.of P.Ring)).inv ≫
      (Spec (CommRingCat.of P.Ring)).Γevaluation q ≫ φ).hom P.X = a
    rw [hγ]
    exact P.lift_X a hP

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Let `c` be a colimit of pointed étale residue triples with compatible map `ψ : c.pt → K`.
For every monic polynomial `f` over `c.pt` with a simple root `a₀` in `K` under `ψ`, there is a
triple `t` and an element `x` of its ring whose image in `c.pt` is a root of `f` mapping to
`a₀`. -/
theorem etaleResidueTriples_simple_root_stage
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    [Algebra ((Spec R).residueField p) K] [IsSepClosure ((Spec R).residueField p) K]
    (c : Cocone (etaleResidueTriplesRingDiagram R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))))
    (hc : IsColimit c)
    (ψ : c.pt →+* K)
    (hψ : ∀ t, ψ.comp (c.ι.app t).hom =
      ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom) :
    ∀ f : Polynomial c.pt, f.Monic → ∀ a₀ : K,
      f.eval₂ ψ a₀ = 0 → f.derivative.eval₂ ψ a₀ ≠ 0 →
      ∃ t : EtaleResidueTriples R p K
          (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K)),
        ∃ x : t.B, f.IsRoot (c.ι.app t x) ∧ ψ (c.ι.app t x) = a₀ := by
  classical
  have : IsFiltered (EtaleResidueTriples R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))) :=
    (etaleResidueTriples_filtered_colimit R p K).1
  intro f hf a₀ hfa hdfa
  obtain ⟨t, g, hg, hgf⟩ := stage_monic_polynomial _ c hc f hf
  have ha : g.eval₂
      ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom a₀ = 0 := by
    rw [← hψ, ← Polynomial.eval₂_map, hgf]
    exact hfa
  have hda : g.derivative.eval₂
      ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom a₀ ≠ 0 := by
    rw [← hψ, ← Polynomial.eval₂_map]
    erw [← Polynomial.derivative_map g (c.ι.app t).hom, hgf]
    exact hdfa
  obtain ⟨s, m, x, hx, hxa⟩ := triple_simple_root_extension t g hg a₀ ha hda
  refine ⟨s, x, ?_, ?_⟩
  · change f.eval ((c.ι.app s).hom x) = 0
    rw [← hgf]
    have hw : (c.ι.app s).hom.comp
        (etaleResidueTriplesRingDiagram R p K
          (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K)) |>.map m).hom =
        (c.ι.app t).hom := congrArg CommRingCat.Hom.hom (c.w m)
    rw [← hw, ← Polynomial.map_map, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    rw [show (g.map _).eval x = 0 from hx, map_zero]
  · change (ψ.comp (c.ι.app s).hom) x = a₀
    rw [hψ]
    exact hxa

end AlgebraicGeometry.Scheme
