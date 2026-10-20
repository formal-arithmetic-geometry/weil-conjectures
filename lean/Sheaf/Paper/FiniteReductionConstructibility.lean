/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.FiniteReductionSystem
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import Sheaf.AlgebraicGeometry.IntrinsicTorAmplitudeTransport
import Sheaf.Paper.FiniteReductionSystemExistence
import Sheaf.Paper.FiniteReductionFlatExtension
import Sheaf.Paper.FiniteReductionEtaleConstructibility

/-!
# Finite reduction and constructibility

Source: main-20261015 blueprint, sec-smooth-purity/sk-lem-sp-reduction,
first paragraph; Stacks Tags 08G1, 06YQ, 094H and 09AL
(blueprint: lem-pur-finite-reduction-constructibility).

## Main definitions

* `AlgebraicGeometry.FiniteReduction.System`: universal derived extensions with
  canonical representative normalizations.
* `AlgebraicGeometry.FiniteReduction.System.CoherentAt`: their associator square.

## Main statements

* `AlgebraicGeometry.FiniteReduction.finiteReduction_constructibility`: finite reduction,
  its bounded flat models, intrinsic finiteness and coherent etale origin.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteReduction

/-- The origin comparison for the specified isomorphism, with no new choice of map.
Source: blueprint sk-lem-sp-reduction, first paragraph
(blueprint: lem-pur-finite-reduction-constructibility). -/
def System.originComparison {T : Scheme.{u}} {l : ℕ} (S : System T l)
    {r m : ℕ} (h : m ≤ r)
    {K₀ : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r)))}
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Coeff.{u} l r)))}
    (e : (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l r)) T).mapDerivedCategory.obj K₀ ≅ K) :
    (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l m)) T).mapDerivedCategory.obj
      ((S.etale r m h).functor.obj K₀) ≅ (S.proetale r m h).functor.obj K :=
by
  let i := (S.comparison r m h).app K₀
  let j := (S.proetale r m h).functor.mapIso e
  exact { hom := i.hom ≫ j.hom
          inv := j.inv ≫ i.inv
          hom_inv_id := by simp
          inv_hom_id := by simp }


private theorem reflect_tor (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (r : ℕ) (a b : ℤ) (hab : a ≤ b)
    (K : DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Coeff.{u} l r))))
    (htor : Scheme.HasProEtaleTorAmplitude T (Ring.{u} l r)
      ((realize T l r).obj K) a b)
    (K₀ : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r))))
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (Coeff.{u} l r)) T).mapDerivedCategory.obj K₀ ≅ K) :
    Etale.DerivedCategory.hasTorAmplitudeIn (Coeff.{u} l r) T a b K₀ := by
  have h := (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
    (Ring.{u} l r) T a b hab K).mp htor
  have h' := (DerivedCategory.torAmplitudeIn
    (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Coeff.{u} l r))) a b).prop_of_iso
      e.symm h
  exact (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn
    (Λ := Coeff.{u} l r) (K := K₀)).mpr
    ((ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff
      (Λ := Coeff.{u} l r) a b K₀).mp h')

private theorem bounded_flat_kflat {T : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    {a b : ℤ} (Q : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hQ : Etale.IsBoundedFlatComplex A a b Q) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q := by
  obtain ⟨hge, hle, hflat⟩ := Etale.isBoundedFlatComplex_iff.mp hQ
  let := hge
  let := hle
  exact CochainComplex.kFlat_of_bounded_of_flat Q a b hflat

/-- Finite quotient reduction preserves bounded intrinsic constructibility and the exact
Tor interval, with bounded flat etale representatives and the canonical coherent origin
comparison. The pro-etale objects use fixed-scalar sheaves; `realize` is the recorded
canonical exact equivalence to modules over the constant ring sheaf. Thus every intrinsic
predicate is exactly the recorded one, and tests all pro-etale module sheaves.

Source: main-20261015 blueprint, sec-smooth-purity/sk-lem-sp-reduction,
first paragraph; Stacks 08G1, 06YQ, 094H and 09AL
(blueprint: lem-pur-finite-reduction-constructibility).

Proof:
1. Construct the universal reduction system with its representative normalizations and
coherence using exists_coherent_system. Reflect the given intrinsic Tor interval through
realization and the specified origin isomorphism using the proved comparison Tor
equivalence.
2. The generic Tor-amplitude criterion gives a bounded flat model Q in the same interval.
Its scalar extension is flat by flat_extend_of_surjective and remains zero outside that
interval. Both complexes are K-flat, so the universal counit computes reduction on Q.
3. boundedConstructible_extend proves constructibility over the quotient ring by the
proved bounded-constructible tensor theorem and exact scalar restriction. The specified
originComparison and finiteRing_constructibleDerived_origin transfer constructibility
and boundedness to intrinsic pro-etale modules.
4. The extended bounded flat complex has the same Tor interval. Transport this predicate
through its computation isomorphism, exact site comparison, and intrinsic realization.
Finally specialize the already proved coherence of the chosen system. -/
theorem finiteReduction_constructibility (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (_hinvert : ∀ x : T, IsUnit (l : T.presheaf.stalk x)) :
    ∃ S : System T l,
    ∀ (r m : ℕ) (_hm : 1 ≤ m) (hmr : m ≤ r) (a b : ℤ) (_hab : a ≤ b)
      (K : DerivedCategory
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Coeff.{u} l r))))
      (_hconstructible : ∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T (Ring.{u} l r)
        ((DerivedCategory.homologyFunctor
          (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T (Ring.{u} l r))) i).obj
            ((realize T l r).obj K)))
      (_hbounded : ∃ c d : ℤ, c ≤ d ∧ ∀ i : ℤ, (i < c ∨ d < i) →
        IsZero ((DerivedCategory.homologyFunctor
          (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T (Ring.{u} l r))) i).obj
            ((realize T l r).obj K)))
      (_htor : Scheme.HasProEtaleTorAmplitude T (Ring.{u} l r)
        ((realize T l r).obj K) a b)
      (K₀ : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r))))
      (_hK₀ : Etale.DerivedCategory.isBoundedConstructible (Coeff.{u} l r) T K₀)
      (e : (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l r)) T).mapDerivedCategory.obj K₀ ≅ K),
    Etale.DerivedCategory.hasTorAmplitudeIn (Coeff.{u} l r) T a b K₀ ∧
    ∃ Q : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r))) ℤ,
      Etale.IsBoundedFlatComplex (Coeff.{u} l r) a b Q ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q ∧
      Nonempty (K₀ ≅ DerivedCategory.Q.obj Q) ∧
      Etale.IsBoundedFlatComplex (Coeff.{u} l m) a b
        (((extend T.smallEtaleTopology (quotient l hmr)).mapHomologicalComplex (.up ℤ)).obj Q) ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
        (((extend T.smallEtaleTopology (quotient l hmr)).mapHomologicalComplex (.up ℤ)).obj Q) ∧
      Nonempty ((S.etale r m hmr).functor.obj K₀ ≅ DerivedCategory.Q.obj
        (((extend T.smallEtaleTopology (quotient l hmr)).mapHomologicalComplex (.up ℤ)).obj Q)) ∧
      Etale.DerivedCategory.isBoundedConstructible (Coeff.{u} l m) T
        ((S.etale r m hmr).functor.obj K₀) ∧
      (∃ origin :
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (Coeff.{u} l m)) T).mapDerivedCategory.obj
          ((S.etale r m hmr).functor.obj K₀) ≅ (S.proetale r m hmr).functor.obj K,
        origin.hom = (S.comparison r m hmr).hom.app K₀ ≫
          (S.proetale r m hmr).functor.map e.hom) ∧
      (∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T (Ring.{u} l m)
        ((DerivedCategory.homologyFunctor
          (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T (Ring.{u} l m))) i).obj
            ((realize T l m).obj ((S.proetale r m hmr).functor.obj K)))) ∧
      (∃ c d : ℤ, c ≤ d ∧ ∀ i : ℤ, (i < c ∨ d < i) →
        IsZero ((DerivedCategory.homologyFunctor
          (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T (Ring.{u} l m))) i).obj
            ((realize T l m).obj ((S.proetale r m hmr).functor.obj K)))) ∧
      Scheme.HasProEtaleTorAmplitude T (Ring.{u} l m)
        ((realize T l m).obj ((S.proetale r m hmr).functor.obj K)) a b ∧
      ∀ (n : ℕ) (_hn : 1 ≤ n) (hnm : n ≤ m), S.CoherentAt r m n hmr hnm K₀ := by
  obtain ⟨S, hcoh⟩ := exists_coherent_system T l
  refine ⟨S, ?_⟩
  intro r m hm hmr a b hab K hc hb ht K₀ hK₀ e
  have ht₀ := reflect_tor T l r a b hab K ht K₀ e
  refine ⟨ht₀, ?_⟩
  obtain ⟨Q, hge, hle, hflat, ⟨eQ⟩⟩ :=
    (DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat a b K₀).mp
      ((Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn
        (Λ := Coeff.{u} l r) (K := K₀)).mp ht₀)
  let := hge
  let := hle
  have hQ : Etale.IsBoundedFlatComplex (Coeff.{u} l r) a b Q :=
    Etale.isBoundedFlatComplex_iff.mpr ⟨hge, hle, hflat⟩
  have hq : Function.Surjective (quotient.{u} l hmr) := by
    intro y
    obtain ⟨x, hx⟩ := ZMod.castHom_surjective (pow_dvd_pow l hmr) y.down.down
    exact ⟨⟨⟨x⟩⟩, congrArg (fun z ↦ (⟨⟨z⟩⟩ : Coeff.{u} l m)) hx⟩
  let Qm := ((extend T.smallEtaleTopology (quotient l hmr)).mapHomologicalComplex
    (.up ℤ)).obj Q
  have hQm : Etale.IsBoundedFlatComplex (Coeff.{u} l m) a b Qm := by
    refine ⟨fun q hi ↦ (extend T.smallEtaleTopology (quotient l hmr)).map_isZero
      (hQ.1 q hi), fun q ↦ ?_⟩
    exact flat_extend_of_surjective T.smallEtaleTopology (quotient l hmr) hq (hflat q)
  have hkQ := bounded_flat_kflat Q hQ
  have hkQm := bounded_flat_kflat Qm hQm
  let E := S.etale r m hmr
  have : IsIso (E.counit.app Q) := E.computation Q hkQ
  let em : E.functor.obj K₀ ≅ DerivedCategory.Q.obj Qm :=
    E.functor.mapIso eQ.symm ≪≫ asIso (E.counit.app Q)
  have hcm := boundedConstructible_extend T (quotient l hmr) E K₀ hK₀ a b hab ht₀
  let origin := S.originComparison hmr e
  have hfin := (Scheme.finiteRing_constructibleDerived_origin T (Ring.{u} l m)).2.2.1
    ((realize T l m).obj ((S.proetale r m hmr).functor.obj K))
  have hess : (ObjectProperty.ι
      (Etale.DerivedCategory.isBoundedConstructible (Coeff.{u} l m) T) ⋙
      ProEtale.finiteCoefficientIntrinsicDerivedComparison T (Ring.{u} l m)).essImage
        ((realize T l m).obj ((S.proetale r m hmr).functor.obj K)) := by
    refine ⟨⟨E.functor.obj K₀, hcm⟩, ⟨?_⟩⟩
    exact (Functor.mapDerivedCategoryCompIso
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (Coeff.{u} l m)) T)
      (ProEtale.finiteCoefficientIntrinsicRealization T (Ring.{u} l m))).app
        (E.functor.obj K₀) ≪≫ (realize T l m).mapIso origin
  obtain ⟨hconstructible, hbounded⟩ := hfin.mp hess
  have htm : DerivedCategory.torAmplitudeIn
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l m))) a b
      (E.functor.obj K₀) := by
    obtain ⟨hgem, hlem, hflatm⟩ := Etale.isBoundedFlatComplex_iff.mp hQm
    let := hgem
    let := hlem
    exact (DerivedCategory.torAmplitudeIn _ a b).prop_of_iso em.symm
      (DerivedCategory.torAmplitudeIn_Q_obj_of_flat Qm a b hflatm)
  have htp : ProEtale.DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (Coeff.{u} l m)) T a b
      ((S.proetale r m hmr).functor.obj K) := by
    exact (DerivedCategory.torAmplitudeIn _ a b).prop_of_iso origin
      ((ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff
        (Λ := Coeff.{u} l m) a b (E.functor.obj K₀)).mpr htm)
  refine ⟨Q, hQ, hkQ, ⟨eQ.symm⟩, hQm, hkQm, ⟨em⟩, hcm,
    ⟨origin, rfl⟩, hconstructible, hbounded, ?_, ?_⟩
  · exact (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
      (Ring.{u} l m) T a b hab _).mpr htp
  · intro n hn hnm
    exact hcoh r m n hmr hnm K₀

end AlgebraicGeometry.FiniteReduction
