/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q95
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Constructible
import WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero

/-!
# Affine lisse stratifications across an open and its zero complement

Source: WeilConjectures/SixFunctors/ProEtale/Adic/ExtensionByZero.lean,
`IsAdicConstructibleSheaf.openImmersionLowerShriek`, affine-neighbourhood argument,
and `IsAdicStratifiedLisseSheaf.of_isCompl`.
(blueprint: lem-sf-native-adic-affine-open-zero-stratification)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry.ProEtale

private theorem finite_stratification_of_stratified
    {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}} {F : AdicSheaf l Y}
    (hF : IsAdicStratifiedLisseSheaf F) :
    ∃ S : Scheme.FiniteLocallyClosedStratification Y,
      (∀ r : Fin S.n, Topology.IsConstructible (S.stratum r)) ∧
      ∀ r : Fin S.n, IsAdicLisseSheaf ((adicUpperStar l (S.immersion r)).obj F) := by
  classical
  obtain ⟨ι, hι, Z, i, hi, hc, hcover, h⟩ := hF
  let := hι
  let := Fintype.ofFinite ι
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let S : Scheme.FiniteLocallyClosedStratification Y :=
    { n := Fintype.card ι
      stratum := fun r ↦ Set.range (i (e r))
      isLocallyClosed_stratum := fun r ↦ by
        have := hi (e r)
        exact (i (e r)).isLocallyClosed_range
      iUnion_stratum_eq_univ := by
        apply Set.eq_univ_of_forall
        intro y
        obtain ⟨k, hk, -⟩ := hcover y
        refine Set.mem_iUnion.mpr ⟨e.symm k, ?_⟩
        rw [e.apply_symm_apply]
        exact hk
      pairwise_disjoint_stratum := by
        intro r s hrs
        apply Set.disjoint_left.mpr
        intro y hyr hys
        obtain ⟨k, -, hk⟩ := hcover y
        exact hrs (e.injective ((hk _ hyr).trans (hk _ hys).symm))
      domain := fun r ↦ Z (e r)
      immersion := fun r ↦ i (e r)
      isImmersion := fun r ↦ hi (e r)
      range_immersion := fun _ ↦ rfl }
  exact ⟨S, fun r ↦ hc (e r), fun r ↦ h (e r)⟩

private theorem open_zero_chart
    (l : ℕ) [Fact l.Prime] {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (M : AdicSheaf l U) (N : AdicSheaf l X)
    (hM : IsAdicConstructibleSheaf M)
    (e : Nonempty ((adicUpperStar l j).obj N ≅ M))
    (hzero : ∀ (W : Scheme.{u}) (g : W ⟶ X),
      Disjoint (Set.range g) (Set.range j) →
        Nonempty ((adicUpperStar l g).obj N ≅ 0))
    (V : Scheme.{u}) (v : V ⟶ X) [IsAffine V] [IsOpenImmersion v] :
    IsAdicStratifiedLisseSheaf
        ((adicUpperStar l (pullback.fst j v)).obj M) ∧
      Nonempty ((adicUpperStar l (pullback.snd j v)).obj
          ((adicUpperStar l v).obj N) ≅
        (adicUpperStar l (pullback.fst j v)).obj M) ∧
      ∀ (Z : Scheme.{u}) (z : Z ⟶ V) [IsClosedImmersion z],
        Set.range z = (Set.range (pullback.snd j v))ᶜ →
          Nonempty ((adicUpperStar l z).obj ((adicUpperStar l v).obj N) ≅ 0) ∧
          IsAdicStratifiedLisseSheaf ((adicUpperStar l v).obj N) := by
  have : CompactSpace ↥(pullback j v) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd j v)
  have : QuasiSeparatedSpace ↥(pullback j v) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd j v)
  have hD := (hM.upperStar (pullback.fst j v)).isAdicStratifiedLisseSheaf
  obtain ⟨e⟩ := e
  let c := (adicUpperStarCompIso l pullback.condition.symm).app N ≪≫
    (adicUpperStar l (pullback.fst j v)).mapIso e
  refine ⟨hD, ⟨c⟩, ?_⟩
  intro Z z _ hz
  have hd : Disjoint (Set.range (z ≫ v)) (Set.range j) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨t, rfl⟩ ⟨u, hu⟩
    obtain ⟨d, -, hd⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := j) (g := v) u (z t) hu
    have hzt : z t ∈ (Set.range (pullback.snd j v))ᶜ := hz ▸ Set.mem_range_self t
    exact hzt ⟨d, hd⟩
  obtain ⟨ez⟩ := hzero Z (z ≫ v) hd
  let ez' := ((adicUpperStarComp l z v).app N).symm ≪≫ ez
  refine ⟨⟨ez'⟩, IsAdicStratifiedLisseSheaf.of_isCompl (pullback.snd j v) z
    (by rw [hz]; exact isCompl_compl) (hD.of_iso c.symm) ?_⟩
  exact (IsAdicLisseSheaf.of_isZero ((isZero_zero _).of_iso ez')).isAdicStratifiedLisseSheaf

/-- A sheaf whose constructible open restriction is prescribed and whose pullbacks away
from that open vanish has finite lisse stratifications on affine charts, and is constructible.
The reduced closed complement is specified by its reducedness and its exact image; this
allows any realization of the unique reduced induced closed subscheme.

Source: SixFunctors/ProEtale/Adic/ExtensionByZero.lean, `openImmersionLowerShriek`,
affine-neighbourhood argument, and `of_isCompl`.
(blueprint: lem-sf-native-adic-affine-open-zero-stratification)

Proof plan:
1. By lem-weil-pbc-open-immersion-base-change, the two projections from D = U ×_X V
   are open immersions. Quasi-compactness of j makes D quasi-compact over affine V.
   Affine qcqs and lem-weil-pbc-quasi-separated-affine-cover-criterion make D
   quasi-separated; no separation hypothesis on X is needed.
2. The image of D in V is a quasi-compact retrocompact open. By
   def-weil-constructible-subset it and its complement are constructible. The theorem
   lem-weil-pbc-reduced-induced-closed-subscheme realizes the complement as a reduced
   closed subscheme. These images are disjoint and cover V.
3. Pull back a local finite lisse stratification for M along the open b. Apply
   lemma-constructible-pullback-stratification and
   lem-weil-pbc-constructible-open-restriction to its strata. Lisse pullback preserves
   the restricted trivializations, so b* M is constructible on D.
4. Apply lem-sf-native-adic-qcqs-stratification on D and enumerate its finite strata.
   The module pullback compositors and v a = j b transport the given isomorphism
   j* N ≅ M to a* v* N ≅ b* M, then restrict it to every stratum.
5. The image of z followed by v misses j(U). The vanishing hypothesis and the module
   pullback compositor give z* v* N ≅ 0. Zero is lisse of rank zero.
6. Compose the strata of D with a and adjoin Z. Their images are constructible by
   lem-weil-pbc-constructible-image-retrocompact-open, and their immersions partition V.
   Step 4 and step 5 show all restrictions are lisse.
7. Affine opens form a neighbourhood basis (lem-weil-pbc-affine-opens-basis), so these
   stratifications imply constructibility of N. Empty D, empty Z, empty V and M = 0
   are included: omit empty strata and use the empty direct sum for zero restrictions.
-/
theorem affine_open_zero_stratification
    (l : ℕ) [Fact l.Prime] {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (M : AdicSheaf l U) (N : AdicSheaf l X)
    (hM : IsAdicConstructibleSheaf M)
    (e : Nonempty ((adicUpperStar l j).obj N ≅ M))
    (hzero : ∀ (W : Scheme.{u}) (g : W ⟶ X),
      Disjoint (Set.range g) (Set.range j) →
        Nonempty ((adicUpperStar l g).obj N ≅ 0)) :
    IsAdicConstructibleSheaf N ∧
      ∀ (V : Scheme.{u}) (v : V ⟶ X) [IsAffine V] [IsOpenImmersion v],
        CompactSpace ↥(pullback j v) ∧ QuasiSeparatedSpace ↥(pullback j v) ∧
        Topology.IsConstructible (Set.range (pullback.snd j v)) ∧
        ∀ (Z : Scheme.{u}) (z : Z ⟶ V) [IsClosedImmersion z] [IsReduced Z],
          Set.range z = (Set.range (pullback.snd j v))ᶜ →
          Topology.IsConstructible (Set.range z) ∧
          IsCompl (Set.range (pullback.snd j v)) (Set.range z) ∧
          (∃ S : Scheme.FiniteLocallyClosedStratification (pullback j v),
            (∀ r : Fin S.n, Topology.IsConstructible (S.stratum r)) ∧
            (∀ r : Fin S.n,
              IsAdicLisseSheaf ((adicUpperStar l (S.immersion r)).obj
                ((adicUpperStar l (pullback.fst j v)).obj M))) ∧
            (∀ r : Fin S.n,
              Nonempty ((adicUpperStar l (S.immersion r)).obj
                  ((adicUpperStar l (pullback.snd j v)).obj
                    ((adicUpperStar l v).obj N)) ≅
                (adicUpperStar l (S.immersion r)).obj
                  ((adicUpperStar l (pullback.fst j v)).obj M)))) ∧
          Nonempty ((adicUpperStar l z).obj ((adicUpperStar l v).obj N) ≅ 0) ∧
          (∃ T : Scheme.FiniteLocallyClosedStratification V,
            (∀ r : Fin T.n, Topology.IsConstructible (T.stratum r)) ∧
            ∀ r : Fin T.n,
              IsAdicLisseSheaf ((adicUpperStar l (T.immersion r)).obj
                ((adicUpperStar l v).obj N))) := by
  have hcharts : ∀ (V : Scheme.{u}) (v : V ⟶ X) [IsAffine V] [IsOpenImmersion v],
      IsAdicStratifiedLisseSheaf ((adicUpperStar l v).obj N) := by
    intro V v _ _
    let C : TopologicalSpace.Closeds V :=
      ⟨(Set.range (pullback.snd j v))ᶜ,
        (pullback.snd j v).isOpenEmbedding.isOpen_range.isClosed_compl⟩
    let z := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
    have hz : Set.range z = (Set.range (pullback.snd j v))ᶜ := by
      simp [z, C]
    exact ((open_zero_chart l j M N hM e hzero V v).2.2 _ z hz).2
  constructor
  · intro x
    obtain ⟨V, hV, hxV, -⟩ :
        ∃ V : X.Opens, V ∈ X.affineOpens ∧ x ∈ V ∧ V ≤ ⊤ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
        (show x ∈ (⊤ : X.Opens) from trivial)
    have : IsAffine V := hV
    exact ⟨V, V.ι, inferInstance, by simpa using hxV, hcharts V V.ι⟩
  · intro V v _ _
    have : CompactSpace ↥(pullback j v) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.snd j v)
    have : QuasiSeparatedSpace ↥(pullback j v) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd j v)
    have hc := (pullback.snd j v).isConstructible_range
    refine ⟨inferInstance, inferInstance, hc, ?_⟩
    intro Z z _ _ hz
    obtain ⟨hD, ⟨c⟩, hZ⟩ := open_zero_chart l j M N hM e hzero V v
    obtain ⟨ez, hV⟩ := hZ Z z hz
    refine ⟨hz ▸ hc.compl, by rw [hz]; exact isCompl_compl, ?_, ez,
      finite_stratification_of_stratified hV⟩
    obtain ⟨S, hcS, hS⟩ := finite_stratification_of_stratified hD
    exact ⟨S, hcS, hS, fun r ↦ ⟨(adicUpperStar l (S.immersion r)).mapIso c⟩⟩

end AlgebraicGeometry.ProEtale
