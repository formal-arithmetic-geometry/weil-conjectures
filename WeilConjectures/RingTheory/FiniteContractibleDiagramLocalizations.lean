/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Directed
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.FiniteWContractible
import all WeilConjectures.RingTheory.WContractibleGeometricCriterion
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.RingTheory.FilteredColimitStrictlyHenselianLocal

/-!
# Localizations of finite algebra diagrams over a w-contractible ring

Source: Stacks Project, Tags 0986, 00GK, 00OI, 00GU, 037D and 04GI
(blueprint: lem-sfb-finite-contractible-diagram-localizations).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

/-- Finite finitely presented stages over a w-contractible base are w-contractible.
Structural and transition maps are finite and integral and contract maximal ideals
to maximal ideals. At a colimit prime with maximal contractions, the canonical
localized transitions are local, their canonical cocone is colimiting, the localized
colimit is strictly henselian, and the contraction to the base is maximal.

Source: Stacks Project, Tags 0986, 00GK, 00OI with 00GU, the localization identity
in the proof of Tag 037D, and the strictly henselian case of Tag 04GI
(blueprint: lem-sfb-finite-contractible-diagram-localizations).

Proof for stage 3:
1. Apply `lem-ce-finite-finitely-presented-wcontractible` to each structural map.
   Use the existing ring-equivalence transport theorem to equalize universes.
   By `sk-def-pe-wlocal`, its conclusion includes w-locality and strict henselianity
   of every maximal localization.
2. A finite A-module generating list of a later stage also generates it over an
   earlier stage, because every transition is an A-algebra map. Thus structural
   and transition maps are module-finite, without any injectivity assumption.
3. Apply `lem-weil-pbc-finite-algebra-is-integral` to these maps, then
   `lem-weil-pbc-integral-maximal-contracts-maximal`. This proves the assertions
   about integrality and contraction of maximal ideals.
4. Construct the localized diagram and canonical cocone with
   `Localization.localRingHom`. Restrict any cocone to the original rings and use
   the given colimit. Every denominator comes from a stage by filtered-colimit
   representative existence, so its image is a unit. Extend across localization;
   localization and colimit extensionality prove factorization and uniqueness.
5. The canonical localized transitions are local by Mathlib
   `Localization.isLocalHom_localRingHom`. Apply `IsLocalRing.maximalIdeal_comap`
   to obtain the displayed inverse images of maximal ideals.
6. All stage localizations in step 4 are strictly henselian by step 1 and the
   maximality hypothesis. Apply `lem-sfb-filtered-colimit-strictly-henselian-local`
   using the local maps of step 5. Nonemptiness supplies a stage; contraction
   through it and step 3 show that the prime contracts to a maximal ideal of A.

The equalities of objects only identify the localized diagram and cocone with the
specified localization rings. No arbitrary maps or choices of algebra structures
replace the canonical fraction maps. Zero stages and noninjective maps are allowed. -/
theorem finiteContractibleDiagramLocalizations
    (A : Type v) [CommRing A] [IsWContractibleRing A]
    (D : Type u) [PartialOrder D] [Nonempty D] [IsDirected D (· ≤ ·)]
    (F : D ⥤ CommAlgCat.{u} A)
    (hfinite : ∀ d : D, Module.Finite A (F.obj d))
    (hfp : ∀ d : D, Algebra.FinitePresentation A (F.obj d))
    (c : Cocone F)
    (hc : IsColimit ((forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).mapCocone c)) :
    (∀ d : D, IsWContractibleRing (F.obj d)) ∧
    (∀ d : D,
      (algebraMap A (F.obj d)).Finite ∧ (algebraMap A (F.obj d)).IsIntegral ∧
        ∀ (m : Ideal (F.obj d)), m.IsMaximal →
          (m.comap (algebraMap A (F.obj d))).IsMaximal) ∧
    (∀ (i j : D) (hij : i ≤ j),
      (F.map (homOfLE hij)).hom.toRingHom.Finite ∧
        (F.map (homOfLE hij)).hom.toRingHom.IsIntegral ∧
        ∀ (m : Ideal (F.obj j)), m.IsMaximal →
          (m.comap (F.map (homOfLE hij)).hom.toRingHom).IsMaximal) ∧
    (∀ p : PrimeSpectrum c.pt,
      (∀ d : D, (p.asIdeal.comap (c.ι.app d).hom.toRingHom).IsMaximal) →
      IsStrictlyHenselianLocalRing (Localization.AtPrime p.asIdeal) ∧
        (p.asIdeal.comap (algebraMap A c.pt)).IsMaximal ∧
        ∃ (L : D ⥤ CommRingCat.{u})
          (hL : ∀ d : D, L.obj d = CommRingCat.of
            (Localization.AtPrime (p.asIdeal.comap (c.ι.app d).hom.toRingHom))),
          (∀ (i j : D) (hij : i ≤ j),
            CommRingCat.ofHom (algebraMap (F.obj i)
                (Localization.AtPrime (p.asIdeal.comap (c.ι.app i).hom.toRingHom))) ≫
                eqToHom (hL i).symm ≫ L.map (homOfLE hij) =
              CommRingCat.ofHom (F.map (homOfLE hij)).hom.toRingHom ≫
                CommRingCat.ofHom (algebraMap (F.obj j)
                  (Localization.AtPrime (p.asIdeal.comap (c.ι.app j).hom.toRingHom))) ≫
                eqToHom (hL j).symm) ∧
          (∀ (i j : D) (hij : i ≤ j),
            (IsLocalRing.maximalIdeal
                (Localization.AtPrime (p.asIdeal.comap (c.ι.app j).hom.toRingHom))).comap
                (eqToHom (hL i).symm ≫ L.map (homOfLE hij) ≫ eqToHom (hL j)).hom =
              IsLocalRing.maximalIdeal
                (Localization.AtPrime (p.asIdeal.comap (c.ι.app i).hom.toRingHom))) ∧
          ∃ (l : Cocone L) (hl : l.pt = CommRingCat.of (Localization.AtPrime p.asIdeal)),
            (∀ d : D,
              CommRingCat.ofHom (algebraMap (F.obj d)
                  (Localization.AtPrime (p.asIdeal.comap (c.ι.app d).hom.toRingHom))) ≫
                  eqToHom (hL d).symm ≫ l.ι.app d ≫ eqToHom hl =
                CommRingCat.ofHom (c.ι.app d).hom.toRingHom ≫
                  CommRingCat.ofHom (algebraMap c.pt (Localization.AtPrime p.asIdeal))) ∧
            Nonempty (IsColimit l)) := by
  classical
  have hw (d : D) : IsWContractibleRing (F.obj d) := by
    have := hfinite d
    have := hfp d
    let R := ULift.{u} A
    let B := ULift.{v} (F.obj d)
    let eR : R ≃+* A := ULift.ringEquiv
    let eB : B ≃+* (F.obj d) := ULift.ringEquiv
    let f : R →+* B := eB.symm.toRingHom.comp ((algebraMap A (F.obj d)).comp eR)
    let : Algebra R B := f.toAlgebra
    let : Module R B := (inferInstance : Algebra R B).toModule
    have : IsWContractibleRing R := RingHom.wContractible_of_ringEquiv eR.symm
    have : Module.Finite R B := by
      apply RingHom.finite_algebraMap.mp
      exact (RingHom.Finite.of_surjective _ eB.symm.surjective).comp
        ((RingHom.finite_algebraMap.mpr (hfinite d)).comp
          (RingHom.Finite.of_surjective _ eR.surjective))
    have : Algebra.FinitePresentation R B := by
      apply RingHom.finitePresentation_algebraMap.mp
      exact (RingHom.FinitePresentation.of_bijective eB.symm.bijective).comp
        ((RingHom.finitePresentation_algebraMap.mpr (hfp d)).comp
          (RingHom.FinitePresentation.of_bijective eR.bijective))
    have : IsWContractibleRing B := isWContractibleRing_of_finite_finitePresentation R B
    exact RingHom.wContractible_of_ringEquiv eB
  have hs (d : D) : (algebraMap A (F.obj d)).Finite := by
    exact (RingHom.finite_algebraMap).mpr (hfinite d)
  have ht (i j : D) (hij : i ≤ j) :
      (F.map (homOfLE hij)).hom.toRingHom.Finite := by
    apply RingHom.Finite.of_comp_finite (f := algebraMap A (F.obj i))
    have heq : (F.map (homOfLE hij)).hom.toRingHom.comp (algebraMap A (F.obj i)) =
        algebraMap A (F.obj j) := (F.map (homOfLE hij)).hom.comp_algebraMap
    rw [heq]
    exact hs j
  refine ⟨hw, ?_, ?_, ?_⟩
  · intro d
    refine ⟨hs d, (hs d).to_isIntegral, ?_⟩
    intro m hm
    have := hm
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'
      _ (hs d).to_isIntegral m
  · intro i j hij
    refine ⟨ht i j hij, (ht i j hij).to_isIntegral, ?_⟩
    intro m hm
    have := hm
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'
      _ (ht i j hij).to_isIntegral m
  · intro p hp
    let G := F ⋙ forget₂ (CommAlgCat.{u} A) CommRingCat.{u}
    let cG : Cocone G := (forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).mapCocone c
    let q (d : D) := p.asIdeal.comap (c.ι.app d).hom.toRingHom
    have hq (i j : D) (a : i ⟶ j) : q i = (q j).comap (G.map a).hom := by
      rw [Ideal.comap_comap]
      change p.asIdeal.comap (cG.ι.app i).hom =
        p.asIdeal.comap (G.map a ≫ cG.ι.app j).hom
      rw [cG.w]
    let L : D ⥤ CommRingCat.{u} :=
      { obj := fun i ↦ CommRingCat.of (Localization.AtPrime (q i))
        map := fun {i j} a ↦ CommRingCat.ofHom
          (Localization.localRingHom (q i) (q j) (G.map a).hom (hq i j a))
        map_id := by
          intro i
          ext1
          apply IsLocalization.ringHom_ext (q i).primeCompl
          ext x
          simp
          rfl
        map_comp := by
          intro i j k a b
          ext1
          apply IsLocalization.ringHom_ext (q i).primeCompl
          ext x
          simp
          rfl }
    have hmap (i j : D) (a : i ⟶ j) (x : F.obj i) :
        (L.map a).hom (algebraMap (F.obj i) (Localization.AtPrime (q i)) x) =
          algebraMap (F.obj j) (Localization.AtPrime (q j)) ((G.map a).hom x) :=
      Localization.localRingHom_to_map (q i) (q j) (G.map a).hom (hq i j a) x
    let κ (i : D) : L.obj i ⟶ CommRingCat.of (Localization.AtPrime p.asIdeal) :=
      CommRingCat.ofHom
        (Localization.localRingHom (q i) p.asIdeal (cG.ι.app i).hom rfl)
    have hκ (i : D) (x : F.obj i) :
        (κ i).hom (algebraMap (F.obj i) (Localization.AtPrime (q i)) x) =
          algebraMap c.pt (Localization.AtPrime p.asIdeal) ((cG.ι.app i).hom x) :=
      Localization.localRingHom_to_map (q i) p.asIdeal (cG.ι.app i).hom rfl x
    let l : Cocone L :=
      { pt := CommRingCat.of (Localization.AtPrime p.asIdeal)
        ι :=
          { app := κ
            naturality := by
              intro i j a
              simp only [Functor.const_obj_map]
              ext1
              apply IsLocalization.ringHom_ext (q i).primeCompl
              ext x
              change (κ j).hom ((L.map a).hom (algebraMap _ _ x)) =
                (κ i).hom (algebraMap _ _ x)
              rw [hmap, hκ, hκ]
              exact congrArg (algebraMap c.pt (Localization.AtPrime p.asIdeal))
                (ConcreteCategory.congr_hom (cG.w a) x) } }
    have hlc : IsColimit l := by
      let U (s : Cocone L) : Cocone G :=
        { pt := s.pt
          ι :=
            { app := fun i ↦
                CommRingCat.ofHom (algebraMap (F.obj i) (Localization.AtPrime (q i))) ≫
                  s.ι.app i
              naturality := by
                intro i j a
                change G.map a ≫ _ = _ ≫ 𝟙 s.pt
                rw [Category.comp_id, ← Category.assoc]
                have h : G.map a ≫
                    CommRingCat.ofHom
                      (algebraMap (F.obj j) (Localization.AtPrime (q j))) =
                    CommRingCat.ofHom
                      (algebraMap (F.obj i) (Localization.AtPrime (q i))) ≫ L.map a := by
                  apply CommRingCat.hom_ext
                  exact RingHom.ext fun x ↦ (hmap i j a x).symm
                rw [h, Category.assoc, s.w a] } }
      let f (s : Cocone L) : cG.pt ⟶ s.pt := hc.desc (U s)
      have hf (s : Cocone L) (i : D) (x : F.obj i) :
          (f s).hom ((cG.ι.app i).hom x) = (s.ι.app i).hom
            (algebraMap (F.obj i) (Localization.AtPrime (q i)) x) :=
        ConcreteCategory.congr_hom (hc.fac (U s) i) x
      have hu (s : Cocone L) (y : p.asIdeal.primeCompl) : IsUnit ((f s).hom (y : c.pt)) := by
        obtain ⟨i, x, hx⟩ := Types.jointly_surjective_of_isColimit
          (isColimitOfPreserves (forget CommRingCat) hc) (y : c.pt)
        change (cG.ι.app i).hom x = (y : c.pt) at hx
        have hxq : x ∈ (q i).primeCompl := by
          change (cG.ι.app i).hom x ∉ p.asIdeal
          rw [hx]
          exact y.property
        rw [← hx, hf]
        exact (IsLocalization.map_units (R := F.obj i)
          (Localization.AtPrime (q i)) ⟨x, hxq⟩).map (s.ι.app i).hom
      refine
        { desc := fun s ↦ CommRingCat.ofHom
            (IsLocalization.lift (S := Localization.AtPrime p.asIdeal) (hu s))
          fac := ?_
          uniq := ?_ }
      · intro s i
        ext1
        apply IsLocalization.ringHom_ext (q i).primeCompl
        ext x
        change IsLocalization.lift (hu s) ((κ i).hom (algebraMap _ _ x)) =
          (s.ι.app i).hom (algebraMap (F.obj i) (Localization.AtPrime (q i)) x)
        rw [hκ, IsLocalization.lift_eq]
        exact hf s i x
      · intro s m hm
        change CommRingCat.of (Localization.AtPrime p.asIdeal) ⟶ s.pt at m
        change ∀ i, κ i ≫ m = s.ι.app i at hm
        ext1
        apply IsLocalization.ringHom_ext p.asIdeal.primeCompl
        have hm' : CommRingCat.ofHom
            (m.hom.comp (algebraMap c.pt (Localization.AtPrime p.asIdeal))) = f s := by
          apply hc.hom_ext
          intro i
          have hi : cG.ι.app i ≫
              CommRingCat.ofHom (algebraMap c.pt (Localization.AtPrime p.asIdeal)) =
              CommRingCat.ofHom
                (algebraMap (F.obj i) (Localization.AtPrime (q i))) ≫ κ i := by
            apply CommRingCat.hom_ext
            exact RingHom.ext fun x ↦ (hκ i x).symm
          change (cG.ι.app i ≫ CommRingCat.ofHom
              (algebraMap c.pt (Localization.AtPrime p.asIdeal))) ≫ m =
            cG.ι.app i ≫ f s
          rw [hi, Category.assoc, hm i]
          exact (hc.fac (U s) i).symm
        ext x
        change m.hom (algebraMap c.pt (Localization.AtPrime p.asIdeal) x) =
          IsLocalization.lift (hu s) (algebraMap c.pt (Localization.AtPrime p.asIdeal) x)
        rw [IsLocalization.lift_eq]
        exact ConcreteCategory.congr_hom hm' x
    have hlocal (i j : D) (hij : i ≤ j) :
        (IsLocalRing.maximalIdeal (L.obj j)).comap (L.map (homOfLE hij)).hom =
          IsLocalRing.maximalIdeal (L.obj i) :=
      IsLocalRing.maximalIdeal_comap
        (Localization.localRingHom (q i) (q j) (G.map (homOfLE hij)).hom
          (hq i j (homOfLE hij)))
    have hstrict (d : D) : IsStrictlyHenselianLocalRing (L.obj d) := by
      change IsStrictlyHenselianLocalRing (Localization.AtPrime (q d))
      have := hw d
      have := hp d
      exact IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization (q d)
    have := hstrict
    have := isStrictlyHenselianLocalRing_colimit_of_local_maps L hlocal
    let e : colimit L ≅ CommRingCat.of (Localization.AtPrime p.asIdeal) :=
      (colimit.isColimit L).coconePointUniqueUpToIso hlc
    have hstrictp : IsStrictlyHenselianLocalRing (Localization.AtPrime p.asIdeal) :=
      IsStrictlyHenselianLocalRing.of_ringEquiv e.commRingCatIsoToRingEquiv
    refine ⟨hstrictp, ?_, L, fun _ ↦ rfl, ?_, ?_, l, rfl, ?_, ⟨hlc⟩⟩
    · obtain ⟨d⟩ := ‹Nonempty D›
      have := hp d
      have hm := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'
        (algebraMap A (F.obj d)) (hs d).to_isIntegral (q d)
      have heq : (c.ι.app d).hom.toRingHom.comp (algebraMap A (F.obj d)) =
          algebraMap A c.pt := (c.ι.app d).hom.comp_algebraMap
      simpa only [q, Ideal.comap_comap, heq] using hm
    · intro i j hij
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      apply CommRingCat.hom_ext
      exact RingHom.ext fun x ↦ hmap i j (homOfLE hij) x
    · intro i j hij
      simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hlocal i j hij
    · intro i
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      apply CommRingCat.hom_ext
      exact RingHom.ext fun x ↦ hκ i x

end CommRingCat
