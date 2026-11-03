/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.Valuation.LocalSubring
import WeilConjectures.AlgebraicGeometry.EtaleNormalComponents
import WeilConjectures.AlgebraicGeometry.DetWrpCoverOpenImmersion

/-!
# Geometric coverings of a normal scheme

Source: Stacks Project, Tags 033C, 033N, 035B, 0AVK, 05K0, 0AB1 and 00IA;
the proof paragraphs of the blueprint unit `sk-lem-wrp-normal-geometric-cover`
(literature/blueprint/latest/blueprint/part-six-operations/
sec-reduction-finite-coefficients/sec-lattices/sk-lem-wrp-normal-geometric-cover/
sk-lem-wrp-normal-geometric-cover.proof.md).
(blueprint: sk-lem-wrp-normal-geometric-cover)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

/-- Every connected component of a separated étale morphism satisfying the valuative
lifting property over a connected normal finite-type scheme over a field is finite étale
and surjective.

Source: Stacks Project, Tags 033C, 033N, 035B, 0AVK, 05K0, 0AB1 and 00IA; the first,
second, and final proof paragraphs of the blueprint unit `sk-lem-wrp-normal-geometric-cover`
(literature/blueprint/latest/blueprint/part-six-operations/
sec-reduction-finite-coefficients/sec-lattices/sk-lem-wrp-normal-geometric-cover/
sk-lem-wrp-normal-geometric-cover.proof.md).

Proof (the three steps of the node):
1. `lem-wrp-etale-normal-components` gives local Noetherianity and normality of `Y`
   and integral open-and-closed connected components. Restrict the lifting property
   to a component: the inverse image of that clopen subset in the connected `Spec R`
   contains the generic point and hence is all of `Spec R`.
2. Apply the same component result to the identity of `X` to see that `X` is integral.
   The nonempty open image of a component contains its generic point
   (`lem-weil-pbc-etale-morphism-open-map`). Its integral étale generic fibre is
   `Spec L` for a finite separable extension of the function field
   (`lem-weil-pbc-etale-fibre-discrete-separable-points`). By
   `det-wrp-cover-open-immersion`, the normalization `N` of `X` in `L` is finite
   over `X`, and the component factors through an open immersion into `N`.
3. For each point of `N`, choose a valuation ring in `L` dominating its local ring
   (`lemma-nagata-local-domain-valuation-dominates`). Extend the generic map to the
   component using the lifting hypothesis. Its composite into `N` equals the
   canonical map from the valuation ring, since the finite map `N → X` is separated
   (`lemma-nagata-separated-valuation-lift-unique`). Thus every point of `N` is in the
   open image, so the component is `N` and is finite étale over `X`. Its image is
   nonempty and open by étaleness, and closed by finiteness
   (`lem-weil-pbc-finite-closed-map-finite-fibres`), hence all of the connected `X`.
(blueprint: sk-lem-wrp-normal-geometric-cover)
-/
theorem connectedComponent_finiteEtale_surjective_of_normal_geometric_cover
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    [Nonempty X] [ConnectedSpace X]
    (hnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (p : Y ⟶ X) [IsSeparated p] [Etale p]
    (hval : ∀ (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
      (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
      (b : Scheme.Spec.obj (op (CommRingCat.of R)) ⟶ X)
      (a : Scheme.Spec.obj (op (CommRingCat.of K)) ⟶ Y),
      a ≫ p = Scheme.Spec.map (CommRingCat.ofHom (algebraMap R K)).op ≫ b →
      ∃ lift : Scheme.Spec.obj (op (CommRingCat.of R)) ⟶ Y,
        lift ≫ p = b ∧
          Scheme.Spec.map (CommRingCat.ofHom (algebraMap R K)).op ≫ lift = a) :
    ∀ y : Y, ∃ U : Y.Opens, (U : Set Y) = connectedComponent y ∧
      IsFinite (U.ι ≫ p) ∧ Etale (U.ι ≫ p) ∧ Surjective (U.ι ≫ p) := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := by
    change LocallyOfFiniteType f
    infer_instance
  have : QuasiCompact (X ↘ Spec (.of k)) := by
    change QuasiCompact f
    infer_instance
  obtain ⟨_, _, hcomponents⟩ := etale_normal_components (k := k) hnormal p
  change ∀ (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
      (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
      (b : Spec (.of R) ⟶ X) (a : Spec (.of K) ⟶ Y),
      a ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b →
      ∃ lift : Spec (.of R) ⟶ Y, lift ≫ p = b ∧
        Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ lift = a at hval
  intro y
  obtain ⟨hclopen, U, hU, hUI⟩ := hcomponents y
  let : IsIntegral U.toScheme := hUI
  let q := U.ι ≫ p
  have hqexist : ValuativeCriterion.Existence q := by
    intro sq
    obtain ⟨l, hl, hgeneric⟩ := hval sq.R sq.K sq.i₂ (sq.i₁ ≫ U.ι)
      (by simpa only [q, Category.assoc] using sq.commSq.w)
    have hrange : Set.range l ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      have hc : IsClopen (l ⁻¹' (U : Set Y)) := by
        rw [hU]
        exact hclopen.preimage l.continuous
      have hne : (l ⁻¹' (U : Set Y)).Nonempty := by
        let xK : Spec (.of sq.K) := IsLocalRing.closedPoint sq.K
        refine ⟨Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) xK, ?_⟩
        change (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ l) xK ∈ U
        rw [hgeneric]
        exact (sq.i₁ _).property
      have heq := hc.eq_univ hne
      rintro _ ⟨r, rfl⟩
      exact Set.eq_univ_iff_forall.mp heq r
    let a := IsOpenImmersion.lift U.ι l hrange
    have ha : a ≫ U.ι = l := IsOpenImmersion.lift_fac ..
    refine ⟨⟨⟨a, ?_, ?_⟩⟩⟩
    · apply (cancel_mono U.ι).mp
      rw [Category.assoc, ha]
      exact hgeneric
    · change a ≫ U.ι ≫ p = sq.i₂
      rw [← Category.assoc, ha]
      exact hl
  obtain ⟨hXI, hfactor⟩ := det_wrp_cover_open_immersion f hnormal q
  let : IsIntegral X := hXI
  obtain ⟨_, _, L, hL, hAlg, _, _, _, _, hfinite, j, hj, hjopen⟩ := hfactor
  let : Field L := hL
  let : Algebra X.functionField L := hAlg
  let : IsFinite (X.fromNormalizationIn L) := hfinite
  let : IsOpenImmersion j := hjopen
  let N := X.normalizationIn L
  let ν : N ⟶ X := X.fromNormalizationIn L
  let t : Spec (.of L) ⟶ N := (X.fromSpecOfAlgebraFunctionField L).toNormalization
  have htgen : t (IsLocalRing.closedPoint L) = genericPoint N := by
    have h := (genericPoint_spec (Spec (.of L))).image t.continuous
    rw [Set.image_univ, t.denseRange.closure_range] at h
    have hpoint : genericPoint (Spec (.of L)) = IsLocalRing.closedPoint L :=
      Subsingleton.elim _ _
    rw [hpoint] at h
    exact h.eq (genericPoint_spec N)
  -- the generic map `Spec L → U`: `t` lands in the generic point, which lies in the
  -- nonempty open image of `j`
  have htrange : Set.range t ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint L := Subsingleton.elim _ _
    rw [hx, htgen]
    exact ((genericPoint_spec N).mem_open_set_iff j.isOpenMap.isOpen_range).mpr
      (by simpa using Set.range_nonempty j)
  let a₀ : Spec (.of L) ⟶ U.toScheme := IsOpenImmersion.lift j t htrange
  have hgeneric : a₀ ≫ j = t := IsOpenImmersion.lift_fac ..
  -- final paragraph of the unit: every point of `N` is in the image of `j`
  have : Surjective j := by
    constructor
    intro n
    have hspec : t (IsLocalRing.closedPoint L) ⤳ n := by
      rw [htgen]
      exact genericPoint_specializes n
    let ρ : N.presheaf.stalk n ⟶ .of L :=
      N.presheaf.stalkSpecializes hspec ≫ Scheme.stalkClosedPointTo t
    obtain ⟨V, hV⟩ := (LocalSubring.range ρ.hom).exists_le_valuationSubring
    have hρV (x : N.presheaf.stalk n) : ρ.hom x ∈ V.toSubring := hV.1 ⟨x, rfl⟩
    let β : N.presheaf.stalk n ⟶ .of V :=
      CommRingCat.ofHom (ρ.hom.codRestrict V.toSubring hρV)
    have : IsLocalHom β.hom := by
      change IsLocalHom ((Subring.inclusion hV.1).comp ρ.hom.rangeRestrict)
      have : IsLocalHom (Subring.inclusion hV.1) := hV.2
      have : IsLocalHom ρ.hom.rangeRestrict :=
        IsLocalHom.of_surjective _ ρ.hom.rangeRestrict_surjective
      infer_instance
    let c : Spec (.of V) ⟶ N := Spec.map β ≫ N.fromSpecStalk n
    let v : Spec (.of L) ⟶ Spec (.of V) :=
      Spec.map (CommRingCat.ofHom (algebraMap V L))
    have hc : v ≫ c = t := by
      dsimp only [v, c]
      rw [← Spec.map_comp_assoc]
      change Spec.map ρ ≫ N.fromSpecStalk n = t
      dsimp only [ρ]
      rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
        Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
    have hcn : c (IsLocalRing.closedPoint V) = n := by
      have hclosed : Spec.map β (IsLocalRing.closedPoint V) =
          IsLocalRing.closedPoint (N.presheaf.stalk n) :=
        IsLocalRing.comap_closedPoint β.hom
      rw [Scheme.Hom.comp_apply, hclosed, Scheme.fromSpecStalk_closedPoint]
    let sq : ValuativeCommSq q :=
      { R := V
        K := L
        i₁ := a₀
        i₂ := c ≫ ν
        commSq := ⟨by
          change a₀ ≫ q = v ≫ c ≫ ν
          have hjν : j ≫ ν = q := hj
          simpa only [Category.assoc, hjν] using
            congrArg (fun k ↦ k ≫ ν) (hgeneric.trans hc.symm)⟩ }
    obtain ⟨a, ha₁, ha₂⟩ := (hqexist sq).exists_lift
    change v ≫ a = a₀ at ha₁
    change a ≫ q = c ≫ ν at ha₂
    let sqN : ValuativeCommSq ν :=
      { R := V
        K := L
        i₁ := t
        i₂ := c ≫ ν
        commSq := ⟨by rw [← hc, Category.assoc]⟩ }
    have hsep : Subsingleton sqN.commSq.LiftStruct := IsSeparated.valuativeCriterion ν sqN
    let l₁ : sqN.commSq.LiftStruct :=
      ⟨a ≫ j, by change v ≫ a ≫ j = t; rw [← Category.assoc, ha₁, hgeneric],
        by change (a ≫ j) ≫ ν = c ≫ ν; rw [Category.assoc, hj]; exact ha₂⟩
    let l₂ : sqN.commSq.LiftStruct := ⟨c, hc, rfl⟩
    have heq : a ≫ j = c := congrArg CommSq.LiftStruct.l
      (@Subsingleton.elim _ hsep l₁ l₂)
    refine ⟨a (IsLocalRing.closedPoint V), ?_⟩
    change (a ≫ j) (IsLocalRing.closedPoint V) = n
    rw [heq, hcn]
  let : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).mpr
    ⟨inferInstance, inferInstance⟩
  let : IsFinite q := by
    rw [← hj]
    infer_instance
  have hrange : Set.range q = Set.univ :=
    IsClopen.eq_univ ⟨q.isClosedMap.isClosed_range, q.isOpenMap.isOpen_range⟩
      (Set.range_nonempty q)
  let : Surjective q := ⟨Set.range_eq_univ.mp hrange⟩
  exact ⟨U, hU, inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry
