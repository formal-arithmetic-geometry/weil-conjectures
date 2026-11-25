/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtale
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.SetTheory.Cardinal.Arithmetic
import WeilConjectures.ProperBaseChange.PrincipalWLocalization.StrictWCover.ThmPeIndetaleRefinementPart3Supplement2
import WeilConjectures.ProperBaseChange.PrincipalWLocalization.StrictWCover.StrictWCoverSize
import WeilConjectures.RingTheory.ProperBaseChange.ProfiniteComponentRingPullback
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BoundedExtremallyDisconnectedCover
import WeilConjectures.RingTheory.WContractibleGeometricCriterion
import Mathlib.RingTheory.Localization.Cardinality

/-! # Bounded w-contractible extensions

Every ring `A` of cardinality at most `κ` has a faithfully flat ind-étale extension `D` of
bounded cardinality splitting all faithfully flat weakly étale extensions, and `Spec D → Spec A`
is a singleton pro-étale cover.

## Implementation details

Form the strict w-local cover `C_A`, of size at most `κ`. Its component space is identified with
its closed points, hence has size at most `2^κ`; take a profinite extremally disconnected
surjection `T` onto it and the profinite component ring pullback `C_A → D`, which is ind-Zariski,
identifies local rings and preserves w-locality. The w-contractibility criterion supplies the
retractions. The cardinality bound comes from the injective diagonal map of `D` into the product
of its maximal local rings, each of size at most `κ`, indexed by at most `|T|` ideals. The
pro-étale covering condition of Tag 0989 is verified on the single affine open `Spec D`.

## References

* [Stacks, Tags 0981, 0983, 0984, 0989]
-/

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry

namespace RingHom

/-- Every ring has a bounded faithfully flat ind-etale extension splitting all faithfully
flat weakly etale extensions, and its spectrum is a singleton pro-etale cover.
flat weakly etale extensions, and its spectrum is a singleton pro-etale cover. -/
theorem exists_bounded_wContractible_extension (A : Type u) [CommRing A]
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hA : Cardinal.mk A ≤ κ) :
    ∃ (D : Type u) (_ : CommRing D) (f : A →+* D),
      f.FaithfullyFlat ∧ f.IndEtale ∧
      Cardinal.mk D ≤ κ ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ))) ∧
      (∀ (B : Type (max u v)) [CommRing B] (g : D →+* B),
        g.FaithfullyFlat → g.WeaklyEtale →
          ∃ r : B →+* D, r.comp g = RingHom.id D) ∧
      Presieve.singleton (Spec.map (CommRingCat.ofHom f)) ∈
        Scheme.proetalePrecoverage (Spec (CommRingCat.of A)) := by
  classical
  let C := PrincipalWLocalization.StrictWCover.algebra A
  obtain ⟨hCfaith, hCind, hCw, hCstrict, _⟩ :=
    PrincipalWLocalization.StrictWCover.properties A
  have : Module.FaithfullyFlat A C := hCfaith
  have : Algebra.IndEtale A C := hCind
  have : IsWLocalRing C := hCw
  have hCsize : Cardinal.mk C ≤ κ := by
    simpa using PrincipalWLocalization.StrictWCover.cardinalMk_le A κ hκ (by simpa using hA)
  obtain ⟨hcompact, ht2, htd, _, hpull⟩ :=
    Algebra.exists_profinite_component_ring_pullback C
  have : CompactSpace (ConnectedComponents (PrimeSpectrum C)) := hcompact
  have : T2Space (ConnectedComponents (PrimeSpectrum C)) := ht2
  have : TotallyDisconnectedSpace (ConnectedComponents (PrimeSpectrum C)) := htd
  let P := Profinite.of (ConnectedComponents (PrimeSpectrum C))
  have hPsize : Cardinal.mk P ≤ (2 : Cardinal.{u}) ^ κ := by
    calc
      Cardinal.mk P ≤ Cardinal.mk (PrimeSpectrum C) :=
        Cardinal.mk_le_of_surjective ConnectedComponents.surjective_coe
      _ ≤ Cardinal.mk (Set C) := Cardinal.mk_le_of_injective
        (f := fun p : PrimeSpectrum C ↦ (p.asIdeal : Set C)) (by
          intro p q h
          exact PrimeSpectrum.ext (SetLike.coe_injective h))
      _ = (2 : Cardinal.{u}) ^ Cardinal.mk C := Cardinal.mk_set
      _ ≤ (2 : Cardinal.{u}) ^ κ := Cardinal.power_le_power_left (by norm_num) hCsize
  have hpow : Cardinal.aleph0 ≤ (2 : Cardinal.{u}) ^ κ :=
    hκ.trans (Cardinal.cantor κ).le
  obtain ⟨T, t, ht, hT, hTsize⟩ :=
    Profinite.exists_bounded_extremallyDisconnected_cover P _ hpow hPsize
  have : ExtremallyDisconnected T := hT
  obtain ⟨D, _, _, e, eπ, _, _, _, _, hind, hlocal, hw,
    hclosedD, hclosedT, hsurj⟩ := hpull T t
  have : IsWLocalRing D := hw
  have : Algebra.IndEtale C D := hind
  have : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum D)) :=
    extremallyDisconnected_of_homeo eπ.symm
  have hDstrict : ∀ (m : Ideal D) [m.IsMaximal],
      IsStrictlyHenselianLocalRing (Localization.AtPrime m) := by
    intro m hm
    let q : PrimeSpectrum D := ⟨m, inferInstance⟩
    have hq : q ∈ closedPoints (PrimeSpectrum D) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mpr hm
    rw [hclosedD] at hq
    have hmC : (m.comap (algebraMap C D)).IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hq
    have := hCstrict (m.comap (algebraMap C D))
    exact IsStrictlyHenselianLocalRing.of_ringEquiv
      (RingEquiv.ofBijective _ (hlocal q))
  have hCDfaith : (algebraMap C D).FaithfullyFlat := by
    apply RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr
    refine ⟨?_, hsurj ht⟩
    have : Algebra.WeaklyEtale C D := inferInstance
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  let : Algebra A D := Algebra.compHom D (algebraMap A C)
  have : IsScalarTower A C D := .of_algebraMap_eq' rfl
  have : Module.FaithfullyFlat C D :=
    RingHom.faithfullyFlat_algebraMap_iff.mp hCDfaith
  have : Module.FaithfullyFlat A D := Module.FaithfullyFlat.trans A C D
  have : Algebra.IndEtale A D := Algebra.IndEtale.trans A C D
  have hcard : Cardinal.mk D ≤
      κ ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ))) := by
    let M := closedPoints (PrimeSpectrum D)
    let L := fun m : M ↦ Localization.AtPrime m.val.asIdeal
    let δ : D → ((m : M) → L m) := fun d m ↦ algebraMap D (L m) d
    have hδ : Function.Injective δ := by
      intro x y hxy
      apply sub_eq_zero.mp
      apply eq_zero_of_localization (x - y)
      intro m hm
      let q : PrimeSpectrum D := ⟨m, hm.isPrime⟩
      have hq : q ∈ closedPoints (PrimeSpectrum D) :=
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mpr hm
      have h := congrFun hxy (⟨q, hq⟩ : M)
      simpa only [map_sub, sub_eq_zero] using h
    have hL : ∀ m : M, Cardinal.mk (L m) ≤ κ := by
      intro m
      let q := m.val
      let p := q.asIdeal.comap (algebraMap C D)
      let E := RingEquiv.ofBijective _ (hlocal q)
      calc
        Cardinal.mk (L m) = Cardinal.mk (Localization.AtPrime p) :=
          (Cardinal.mk_congr E.toEquiv).symm
        _ ≤ Cardinal.mk C := IsLocalization.cardinalMk_le p.primeCompl
        _ ≤ κ := hCsize
    have hM : Cardinal.mk M ≤
        (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ)) := by
      rw [Cardinal.mk_congr hclosedT.homeomorph.toEquiv]
      exact hTsize
    calc
      Cardinal.mk D ≤ Cardinal.mk ((m : M) → L m) := Cardinal.mk_le_of_injective hδ
      _ = Cardinal.prod (fun m : M ↦ Cardinal.mk (L m)) := Cardinal.mk_pi L
      _ ≤ Cardinal.prod (fun _ : M ↦ κ) := Cardinal.prod_le_prod _ _ hL
      _ = κ ^ Cardinal.mk M := Cardinal.prod_const' M κ
      _ ≤ κ ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ))) :=
        Cardinal.power_le_power_left (ne_of_gt (Cardinal.aleph0_pos.trans_le hκ)) hM
  refine ⟨D, inferInstance, algebraMap A D,
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance,
    (RingHom.IndEtale.algebraMap_iff (R := A) (S := D)).mpr inferInstance, hcard, ?_, ?_⟩
  · intro B _ g hg hwg
    exact exists_retraction_of_wlocal_geometric_criterion hDstrict g hg hwg
  · have hweak : AlgebraicGeometry.WeaklyEtale
        (Spec.map (CommRingCat.ofHom (algebraMap A D))) := inferInstance
    have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap A D))) := by
      rw [surjective_iff]
      exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
    change Presieve.singleton (Spec.map (CommRingCat.ofHom (algebraMap A D))) ∈
      Scheme.propQCPrecoverage @AlgebraicGeometry.WeaklyEtale (Spec (CommRingCat.of A))
    exact Scheme.Hom.singleton_mem_propQCPrecoverage hweak

end RingHom
