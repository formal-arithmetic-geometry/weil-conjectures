/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Constructible
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingClassicalGenerator
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import WeilConjectures.Topology.ConstructibleIsRetrocompact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality
import Sheaf.AlgebraicGeometry.ProEtale.SingleWContractibleCover
import Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation
import Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative

/-! # Boundedness from stratified dualizability

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Definition 3.3,
Lemma 4.10 and Corollary 4.11 (blueprint: lem-pod-stratified-dualizable-bounded).

The category is the ordinary unbounded derived category of module objects over the
pulled-back condensed ring, with its ordinary relative derived tensor. The explicit
exact pairings specify the two duality contractions on each stratum. No Noetherian,
finite-dimensional or regularity assumption is made.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem wContractible_of_ringEquiv
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [IsWContractibleRing R]
    (e : R ≃+* S) : IsWContractibleRing S := by
  have : IsWLocalRing S := IsWLocalRing.of_surjective (f := e.toRingHom) e.surjective
  have : IsWStrictlyLocalRing S := by
    refine ⟨fun m hm ↦ ?_⟩
    have : (m.comap e.toRingHom).IsMaximal :=
      (Ideal.isMaximal_comap_iff_of_bijective e.toRingHom e.bijective).mpr hm
    have := IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization
      (m.comap e.toRingHom)
    have hM : (m.comap e.toRingHom).primeCompl.map e.toMonoidHom = m.primeCompl := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
        change e (e.symm x) ∉ m
        rwa [e.apply_symm_apply]
    exact IsStrictlyHenselianLocalRing.of_ringEquiv
      (IsLocalization.ringEquivOfRingEquiv
        (Localization.AtPrime (m.comap e.toRingHom)) (Localization.AtPrime m) e hM)
  have := IsWContractibleRing.extremallyDisconnected_connectedComponents (R := R)
  let h := PrimeSpectrum.homeomorphOfRingEquiv e
  have hc : ∀ y, _root_.IsConnected (h ⁻¹' {y}) := by
    intro y
    have heq : h ⁻¹' {y} = {h.symm y} := by
      ext x
      change h x = y ↔ x = h.symm y
      exact ⟨fun hx ↦ h.injective (hx.trans (h.apply_symm_apply y).symm),
        fun hx ↦ hx ▸ h.apply_symm_apply y⟩
    rw [heq]
    exact isConnected_singleton
  exact ⟨extremallyDisconnected_of_homeo
    (h.isQuotientMap.isCoinducing.connectedComponentsHomeomorph hc)⟩

private theorem bounded_realization_perfect
    {A : Type (u + 1)} [CommRing A]
    {C : Type (u + 2)} [Category.{u + 1} C] [Abelian C]
    [HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} A)] [HasDerivedCategory.{u + 1} C]
    (F : DerivedCategory (ModuleCat.{u + 1} A) ⥤ DerivedCategory C)
    [F.CommShift ℤ] [F.IsTriangulated]
    (hF : DerivedCategory.TStructure.t.bounded
      (F.obj ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of A A))))
    (P : DerivedCategory (ModuleCat.{u + 1} A))
    (hP : DerivedCategory.IsPerfectRingComplex P) :
    DerivedCategory.TStructure.t.bounded (F.obj P) := by
  let T := DerivedCategory.TStructure.t (C := C)
  let B : ObjectProperty (DerivedCategory (ModuleCat.{u + 1} A)) :=
    T.bounded.inverseImage F
  have : B.IsStableUnderRetracts := ⟨fun r h ↦ by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h
    have h' : DerivedCategory.homologyConcentratedIn a b (F.obj _) := ⟨ha, hb⟩
    have h'' := (DerivedCategory.homologyConcentratedIn a b).prop_of_retract (r.map F) h'
    exact ⟨⟨a, h''.1⟩, ⟨b, h''.2⟩⟩⟩
  have hle : (ObjectProperty.singleton
      ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of A A))).triangEnvelope ≤ B :=
    (ObjectProperty.triangEnvelope_le_iff _).mpr
      (ObjectProperty.singleton_le_iff.mpr hF)
  apply hle
  rwa [← DerivedCategory.isPerfectRingComplex_eq_triangEnvelope_singleton A]

open CategoryTheory.MonoidalCategory in
private theorem bounded_wcontractible_dualizable
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (T : Scheme.{u}) [IsAffine T] [IsWContractibleRing Γ(T, ⊤)]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ.X T)))
    (hK : IsDualizable K) : DerivedCategory.TStructure.t.bounded K := by
  let J := Scheme.ProEt.topology T
  let O := condensedRingObj Λ.X T
  let U := Scheme.ProEt.mk (𝟙 T)
  let hU := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale T
  obtain ⟨_, ⟨hshift, htri⟩, hbraid, e, ⟨ef⟩, _⟩ :=
    ((CondensedRing.condensed_wcontractible_lisse_evaluation Λ).1 T).1
  let F := CondensedRing.Evaluation.F J O U hU
  let := hshift
  let := htri
  obtain ⟨hb⟩ := hbraid
  let := hb
  let L : (CondensedRing.Evaluation.lisse J O).FullSubcategory := ⟨K, hK⟩
  let P := e.inverse.obj L
  have ep : F.obj P.obj ≅ K :=
    (ef.app P).symm ≪≫ (CondensedRing.Evaluation.lisse J O).ι.mapIso
      (e.counitIso.app L)
  have hunit : DerivedCategory.TStructure.t.bounded (𝟙_ (DerivedCategory
      (Mod (Sheaf J Ab.{u + 1}) O))) := by
    apply DerivedCategory.TStructure.t.bounded.prop_of_iso
      (DerivedCategory.singleFunctorObjUnitIso _)
    exact ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩
  have hF : DerivedCategory.TStructure.t.bounded
      (F.obj ((DerivedCategory.singleFunctor _ 0).obj
        (ModuleCat.of (CondensedRing.Evaluation.A J O U)
          (CondensedRing.Evaluation.A J O U)))) := by
    apply DerivedCategory.TStructure.t.bounded.prop_of_iso
      ((Functor.Monoidal.εIso F) ≪≫
        F.mapIso (DerivedCategory.singleFunctorObjUnitIso _).symm) hunit
  exact DerivedCategory.TStructure.t.bounded.prop_of_iso ep
    (bounded_realization_perfect F hF P.obj P.property)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem bounded_dualizable
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (T : Scheme.{u}) [CompactSpace T]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ.X T)))
    (hK : IsDualizable K) : DerivedCategory.TStructure.t.bounded K := by
  obtain ⟨D, f, hf, g, hD, hcover⟩ :=
    exists_single_wContractible_affine_cover T (Scheme.ProEt.mk (𝟙 T))
      (by change CompactSpace T; infer_instance)
  let := hf
  let := hD
  have : IsWContractibleRing Γ(Spec D, ⊤) :=
    wContractible_of_ringEquiv (Scheme.ΓSpecIso D).commRingCatIsoToRingEquiv.symm
  have hgf : g.left = f := by
    have h := g.w
    change g.left ≫ 𝟙 T = f ≫ 𝟙 T at h
    change (show Spec D ⟶ T from g.left) = f
    exact (Category.comp_id (show Spec D ⟶ T from g.left)).symm.trans
      (h.trans (Category.comp_id f))
  have hcover' : Presieve.singleton f ∈ Scheme.proetalePrecoverage T := by
    simpa [Scheme.ProEt.precoverage, Presieve.map_singleton, Scheme.ProEt.forget,
      MorphismProperty.Over.forget, MorphismProperty.Comma.forget,
      MorphismProperty.Comma.Hom.hom, hgf, Scheme.ProEt.mk, MorphismProperty.Over.mk]
      using hcover
  let 𝒰 : Scheme.Cover.{0} Scheme.proetalePrecoverage T :=
    { I₀ := PUnit, X := fun _ ↦ Spec D, f := fun _ ↦ f
      mem₀ := by
        change Presieve.ofArrows (fun _ : PUnit ↦ Spec D) (fun _ ↦ f) ∈ _
        simpa only [Presieve.ofArrows_pUnit] using hcover' }
  let F := CondensedRing.upperStar Λ.X f
  have hlocal : IsDualizable (F.mapDerivedCategory.obj K) :=
    condensed_derivedPullback_preserves_dualizable Λ f K hK
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := bounded_wcontractible_dualizable Λ (Spec D) _ hlocal
  have hzero (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ.X T)) (hM : IsZero (F.obj M)) : IsZero M := by
    have hs : IsZero ((DerivedCategory.singleFunctor _ 0).obj M) :=
      (condensed_cover_restriction_conservative Λ T 𝒰).2 _ (fun _ ↦
        ((DerivedCategory.singleFunctor _ 0).map_isZero hM).of_iso
          ((F.mapDerivedCategorySingleFunctor 0).app M))
    exact ((DerivedCategory.homologyFunctor _ 0).map_isZero hs).of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm
  have hz (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K) := by
    apply hzero
    apply IsZero.of_iso _ ((F.mapDerivedCategoryHomologyFunctorIso q).app K)
    rcases hq with hq | hq
    · exact (DerivedCategory.isGE_iff _ a).1 ha q hq
    · exact (DerivedCategory.isLE_iff _ b).1 hb q hq
  exact ⟨⟨a, (DerivedCategory.isGE_iff _ a).2 (fun q hq ↦ hz q (.inl hq))⟩,
    ⟨b, (DerivedCategory.isLE_iff _ b).2 (fun q hq ↦ hz q (.inr hq))⟩⟩

/-- A complex dualizable on finitely many constructible locally closed strata of a qcqs
scheme has bounded cohomology, and admits a representative vanishing below the same bound.
Source: Hemo--Richarz--Scholbach, Definition 3.3, Lemma 4.10 and Corollary 4.11
(blueprint: lem-pod-stratified-dualizable-bounded).

Proof:
1. Constructible subsets of a quasi-compact scheme are quasi-compact, using
lem-weil-pbc-constructible-is-retrocompact. Each stratum immersion is an embedding,
so its domain is quasi-compact; its map to the quasi-separated root is quasi-compact.
2. On a quasi-compact scheme T, det-pe-hypercover-single-cover gives a singleton
w-contractible affine cover. Pullback preserves dualizability by
lem-zl-condensed-lisse-proetale-locality. The equivalence of
lem-zl-condensed-wcontractible-lisse-evaluation realizes the resulting dualizable
object as a perfect complex over the actual section ring.
3. By lem-sf-perfect-ring-classical-generator, perfect complexes form the thick
subcategory generated by the ring in degree zero. The inverse image of bounded objects
under the triangulated realization is triangulated and closed under retracts. It contains
the ring because realization is monoidal and its target unit is the coefficient sheaf
in degree zero. Hence the realized perfect complex is bounded.
4. Exact restriction commutes with homology. Apply
lem-zl-condensed-cover-restriction-conservative to each homology sheaf placed in degree
zero to descend these bounds through the singleton cover.
5. Enlarge the finitely many stratum intervals to the ordered interval whose endpoints
are minus the sum of absolute lower bounds and the sum of absolute upper bounds.
The finite quasi-compact jointly surjective family of stratum immersions detects zero
morphisms of abelian sheaves (DetectionAb). Apply it to each homology sheaf's identity,
using the coefficient comparison to identify its pullbacks with the underlying sheaves
of the module pullbacks. This also covers an empty family and an empty scheme.
6. Mathlib's exists_iso_Q_obj_of_isGE gives a cochain representative vanishing below
the lower bound, by good lower truncation. -/
theorem stratified_dualizable_bounded
    (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y)))
    (S : Scheme.FiniteLocallyClosedStratification Y)
    (hconstructible : ∀ i : Fin S.n, Topology.IsConstructible (S.stratum i))
    (hdual : ∀ i : Fin S.n, ∃ D : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (S.domain i)) Ab.{u + 1})
        (condensedRingObj Λ.X (S.domain i))),
      Nonempty (ExactPairing
        ((CondensedRing.upperStar Λ.X (S.immersion i)).mapDerivedCategory.obj K) D)) :
    ∃ a b : ℤ, a ≤ b ∧
      (∀ j : ℤ, j < a ∨ b < j →
        IsZero ((DerivedCategory.homologyFunctor _ j).obj K)) ∧
      ∃ C : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y)) ℤ,
        Nonempty (DerivedCategory.Q.obj C ≅ K) ∧
          ∀ j : ℤ, j < a → IsZero (C.X j) := by
  classical
  have hqc (i : Fin S.n) : CompactSpace (S.domain i) := by
    let := S.isImmersion i
    apply isCompact_univ_iff.mp
    apply (S.immersion i).isEmbedding.isCompact_iff.mpr
    simpa only [Set.image_univ, S.range_immersion] using
      (hconstructible i).isRetrocompact.isCompact
  let (i : Fin S.n) := hqc i
  let (i : Fin S.n) : QuasiCompact (S.immersion i) := inferInstance
  have hb (i : Fin S.n) : DerivedCategory.TStructure.t.bounded
      ((CondensedRing.upperStar Λ.X (S.immersion i)).mapDerivedCategory.obj K) := by
    obtain ⟨D, ⟨hD⟩⟩ := hdual i
    let := hD
    exact bounded_dualizable Λ (S.domain i) _ ⟨⟨D⟩⟩
  have hb' (i : Fin S.n) :
      (∃ a : ℤ, ((CondensedRing.upperStar Λ.X (S.immersion i)).mapDerivedCategory.obj K).IsGE a) ∧
      (∃ b : ℤ, ((CondensedRing.upperStar Λ.X (S.immersion i)).mapDerivedCategory.obj K).IsLE b) :=
    hb i
  choose hl hu using hb'
  choose a ha using hl
  choose b hb using hu
  let a₀ : ℤ := -∑ i, |a i|
  let b₀ : ℤ := ∑ i, |b i|
  have haz (i : Fin S.n) : a₀ ≤ a i := by
    have := Finset.single_le_sum (f := fun i ↦ |a i|) (fun i _ ↦ abs_nonneg _)
      (Finset.mem_univ i)
    dsimp [a₀]
    linarith [neg_abs_le (a i)]
  have hbz (i : Fin S.n) : b i ≤ b₀ := by
    have := Finset.single_le_sum (f := fun i ↦ |b i|) (fun i _ ↦ abs_nonneg _)
      (Finset.mem_univ i)
    dsimp [b₀]
    linarith [le_abs_self (b i)]
  have hz (q : ℤ) (hq : q < a₀ ∨ b₀ < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K) := by
    let M := (DerivedCategory.homologyFunctor _ q).obj K
    apply CondensedRing.isZero_of_isZero_X Λ.X
    apply (IsZero.iff_id_eq_zero _).2
    apply eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp S.immersion
      (fun x ↦ by
        have hx : x ∈ ⋃ i, S.stratum i := by rw [S.iUnion_stratum_eq_univ]; trivial
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        exact ⟨i, (S.range_immersion i).symm ▸ hi⟩)
    intro i
    have hlocal : IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.upperStar Λ.X (S.immersion i)).mapDerivedCategory.obj K)) := by
      rcases hq with hq | hq
      · exact (DerivedCategory.isGE_iff _ _).1 (ha i) q (lt_of_lt_of_le hq (haz i))
      · exact (DerivedCategory.isLE_iff _ _).1 (hb i) q (lt_of_le_of_lt (hbz i) hq)
    have hm : IsZero ((CondensedRing.upperStar Λ.X (S.immersion i)).obj M) :=
      hlocal.of_iso
        (((CondensedRing.upperStar Λ.X (S.immersion i)).mapDerivedCategoryHomologyFunctorIso
          q).app K)
    exact (((Mod.forget _).map_isZero hm).of_iso
      (CondensedRing.upperStarObjXIso Λ.X (S.immersion i) M).symm).eq_of_src _ _
  have hab : a₀ ≤ b₀ := by
    have ha' : 0 ≤ ∑ i, |a i| := Finset.sum_nonneg (fun i _ ↦ abs_nonneg _)
    have hb' : 0 ≤ ∑ i, |b i| := Finset.sum_nonneg (fun i _ ↦ abs_nonneg _)
    dsimp [a₀, b₀]
    omega
  have : K.IsGE a₀ := (DerivedCategory.isGE_iff _ _).2 (fun q hq ↦ hz q (.inl hq))
  obtain ⟨C, hC, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K a₀
  exact ⟨a₀, b₀, hab, hz, C, ⟨e.symm⟩, fun q hq ↦
    C.isZero_of_isStrictlyGE a₀ q hq⟩

end AlgebraicGeometry.ProEtale
