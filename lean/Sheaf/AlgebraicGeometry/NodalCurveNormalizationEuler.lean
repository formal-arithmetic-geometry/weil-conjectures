/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q157, H7
-/
module

public import Sheaf.AlgebraicGeometry.NodalNormalizationQuotient
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward

/-! # Euler characteristic of a nodal curve from its normalization

Source: Stacks Project, Varieties, Tag 0C1R (lemma-prepare-delta-invariant), and Curves,
Tag 0CBW (lemma-split-node) (blueprint: lem-trf-nodal-curve-normalization-euler).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private theorem normalization_iso {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (e : X ≅ Y) : ∃ E : X.normalization ≅ Y.normalization,
      E.hom ≫ Y.fromNormalization = X.fromNormalization ≫ e.hom := by
  have key (x : X) (y : Y) (h : e.hom x = y) :
      ∃ d : Spec (X.presheaf.stalk x) ≅ Spec (Y.presheaf.stalk y),
        d.hom ≫ Y.fromSpecStalk y = X.fromSpecStalk x ≫ e.hom := by
    subst y
    exact ⟨Scheme.Spec.mapIso (asIso (e.hom.stalkMap x)).op,
      SpecMap_stalkMap_fromSpecStalk e.hom⟩
  obtain ⟨d, hd⟩ := key (genericPoint X) (genericPoint Y)
    (genericPoint_eq_of_isOpenImmersion e.hom)
  change d.hom ≫ Y.fromSpecFunctionField = X.fromSpecFunctionField ≫ e.hom at hd
  have hd' : d.inv ≫ X.fromSpecFunctionField = Y.fromSpecFunctionField ≫ e.inv := by
    apply (cancel_epi d.hom).mp
    simp only [← Category.assoc, hd]
    simp
  let m := X.fromSpecFunctionField.normalizationDesc
    (d.hom ≫ Y.fromSpecFunctionField.toNormalization) (Y.fromNormalization ≫ e.inv)
    (by simp only [Category.assoc, Hom.toNormalization_fromNormalization_assoc]
        rw [← Category.assoc, hd]
        simp)
  let n := Y.fromSpecFunctionField.normalizationDesc
    (d.inv ≫ X.fromSpecFunctionField.toNormalization) (X.fromNormalization ≫ e.hom)
    (by simp only [Category.assoc, Hom.toNormalization_fromNormalization_assoc]
        rw [← Category.assoc, hd']
        simp)
  have hm : m ≫ Y.fromNormalization = X.fromNormalization ≫ e.hom := by
    apply (cancel_mono e.inv).mp
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      X.fromSpecFunctionField.normalizationDesc_comp _ _ _
  have hn : n ≫ X.fromNormalization = Y.fromNormalization ≫ e.inv := by
    apply (cancel_mono e.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      Y.fromSpecFunctionField.normalizationDesc_comp _ _ _
  have hmn : m ≫ n = 𝟙 _ := by
    apply Hom.normalization.hom_ext X.fromSpecFunctionField _ _ X.fromNormalization
    · simp [m, n]
    · rw [Category.assoc, hn, ← Category.assoc, hm]
      simp
    · simp
  have hnm : n ≫ m = 𝟙 _ := by
    apply Hom.normalization.hom_ext Y.fromSpecFunctionField _ _ Y.fromNormalization
    · simp [m, n]
    · rw [Category.assoc, hm, ← Category.assoc, hn]
      simp
    · simp
  exact ⟨⟨m, n, hmn, hnm⟩, hm⟩

set_option backward.isDefEq.respectTransparency false in
private theorem reduced_component_iso {B Z : Scheme.{u}} [IsIntegral Z]
    (j : Z ⟶ B) [IsClosedImmersion j] (C : irreducibleComponents B)
    (hj : Set.range j = C.1) :
    ∃ e : Z ≅ B.reducedNormalizationComponent C,
      e.hom ≫ (IdealSheafData.vanishingIdeal
        ⟨C.1, isClosed_of_mem_irreducibleComponents _ C.2⟩).subschemeι = j := by
  let c : B.reducedNormalizationComponent C ⟶ B :=
    (IdealSheafData.vanishingIdeal
      ⟨C.1, isClosed_of_mem_irreducibleComponents _ C.2⟩).subschemeι
  have hc : Set.range c = C.1 := by
    change Set.range (IdealSheafData.vanishingIdeal
      ⟨C.1, isClosed_of_mem_irreducibleComponents _ C.2⟩).subschemeι = C.1
    rw [IdealSheafData.range_subschemeι]
    rfl
  obtain ⟨f, hf, -⟩ := IsClosedImmersion.existsUnique_fac_of_range_subset_range c j
    (by rw [hj, hc])
  obtain ⟨g, hg, -⟩ := IsClosedImmersion.existsUnique_fac_of_range_subset_range j c
    (by rw [hj, hc])
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply (cancel_mono j).mp
    simp [Category.assoc, hg, hf]
  · apply (cancel_mono c).mp
    simp [Category.assoc, hf, hg]

set_option backward.isDefEq.respectTransparency false in
private theorem component_euler (k : Type u) [Field k] [IsAlgClosed k]
    (B : Scheme.{u}) [B.Over (Spec (.of k))] [IsProper (B ↘ Spec (.of k))]
    (Z : Scheme.{u}) [IsIntegral Z] (j : Z ⟶ B) [IsClosedImmersion j]
    (hdim : topologicalKrullDim (Set.range j) = 1)
    [IsProper (Z.fromNormalization ≫ j ≫ B ↘ Spec (.of k))]
    [Smooth (Z.fromNormalization ≫ j ≫ B ↘ Spec (.of k))]
    [ConnectedSpace Z.normalization] :
    letI : Z.normalization.Over (Spec (.of k)) :=
      ⟨Z.fromNormalization ≫ j ≫ B ↘ Spec (.of k)⟩
    Modules.eulerChar k (Modules.unit Z.normalization) =
      1 - ((Z.fromNormalization ≫ j ≫ B ↘ Spec (.of k)).genus : ℤ) := by
  let : Z.normalization.Over (Spec (.of k)) :=
    ⟨Z.fromNormalization ≫ j ≫ B ↘ Spec (.of k)⟩
  have : IsProper (Z.normalization ↘ Spec (.of k)) :=
    inferInstanceAs (IsProper (Z.fromNormalization ≫ j ≫ B ↘ Spec (.of k)))
  have : Smooth (Z.normalization ↘ Spec (.of k)) :=
    inferInstanceAs (Smooth (Z.fromNormalization ≫ j ≫ B ↘ Spec (.of k)))
  have hZ : topologicalKrullDim Z = 1 :=
    j.isClosedEmbedding.isEmbedding.topologicalKrullDim_eq_range.trans hdim
  have : SmoothOfRelativeDimension 1 (Z.normalization ↘ Spec (.of k)) :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq _ 1).mpr
      ((Z.topologicalKrullDim_normalization (j ≫ B ↘ Spec (.of k))).trans hZ)
  rw [eulerChar_unit_eq, ← genus_eq_arithmeticGenus]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem euler_iso (k : Type u) [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    (e : X ⟶ Y) [IsIso e] [e.IsOver (Spec (.of k))] :
    Modules.eulerChar k (Modules.unit X) = Modules.eulerChar k (Modules.unit Y) := by
  have := SheafOfModules.isQuasicoherent_unit (R := Y.ringCatSheaf)
  rw [← Modules.eulerChar_congr k (Modules.pullbackObjUnitIso e)]
  unfold Modules.eulerChar
  congr 1
  funext q
  rw [Modules.finrankH_pullback_of_isIso e]

set_option backward.isDefEq.respectTransparency false in
private theorem euler_sigma (k : Type u) [Field k] (v : ℕ)
    (Y : Fin v → Scheme.{u}) (q : (∐ Y) ⟶ Spec (.of k)) [IsProper q] :
    letI : (∐ Y).Over (Spec (.of k)) := ⟨q⟩
    Modules.eulerChar k (Modules.unit (∐ Y)) = ∑ a : Fin v,
      letI : (Y a).Over (Spec (.of k)) := ⟨Sigma.ι Y a ≫ q⟩
      Modules.eulerChar k (Modules.unit (Y a)) := by
  classical
  let : (∐ Y).Over (Spec (.of k)) := ⟨q⟩
  have : IsProper ((∐ Y) ↘ Spec (.of k)) := inferInstanceAs (IsProper q)
  have : CompactSpace (∐ Y : Scheme.{u}) := QuasiCompact.compactSpace_of_compactSpace q
  have : IsSeparated (terminal.from (∐ Y)) := by
    rw [← terminal.comp_from q]
    infer_instance
  let U (a : Fin v) := (Sigma.ι Y a).opensRange
  have hcover : ⨆ a, U a = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨a, y, rfl⟩ := (sigmaOpenCover Y).exists_eq x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨a, ⟨y, rfl⟩⟩
  have hdisj : Pairwise (fun a b ↦ Disjoint (U a) (U b)) :=
    fun _ _ h ↦ disjoint_opensRange_sigmaι Y _ _ h
  have := SheafOfModules.isQuasicoherent_unit (R := (∐ Y : Scheme.{u}).ringCatSheaf)
  have : (SheafOfModules.unit (∐ Y : Scheme.{u}).ringCatSheaf).IsInvertible :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  have : (SheafOfModules.unit (∐ Y : Scheme.{u}).ringCatSheaf).IsFiniteLocallyFree :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
  have : (SheafOfModules.unit (∐ Y : Scheme.{u}).ringCatSheaf).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have (q' : ℕ) : FiniteDimensional k ((Modules.unit (∐ Y)).H q') :=
    Modules.finiteDimensional_H_of_isProper _ q'
  rw [Modules.eulerChar_eq_sum_of_pairwise_disjoint_of_isQuasicoherent k U hdisj hcover]
  apply Finset.sum_congr rfl
  intro a _
  let : (Y a).Over (Spec (.of k)) := ⟨Sigma.ι Y a ≫ q⟩
  let : (U a).toScheme.Over (Spec (.of k)) := ⟨(U a).ι ≫ q⟩
  rw [Modules.eulerChar_congr k (Modules.pullbackObjUnitIso (U a).ι)]
  have : (Sigma.ι Y a).isoOpensRange.hom.IsOver (Spec (.of k)) := by
    constructor
    change (Sigma.ι Y a).isoOpensRange.hom ≫ (U a).ι ≫ q = _
    rw [← Category.assoc, Hom.isoOpensRange_hom_ι]
    rfl
  exact (euler_iso k (Sigma.ι Y a).isoOpensRange.hom).symm

set_option backward.isDefEq.respectTransparency false in
private theorem normalization_presentation (B : Scheme.{u}) (v : ℕ)
    (components : Fin v ≃ irreducibleComponents B)
    (Z : Fin v → Scheme.{u}) [∀ a, IsIntegral (Z a)]
    (j : ∀ a, Z a ⟶ B) [∀ a, IsClosedImmersion (j a)]
    (hj : ∀ a, Set.range (j a) = (components a).1) :
    ∃ e : (∐ fun a ↦ (Z a).normalization) ≅ B.reducedNormalization,
      e.hom ≫ B.fromReducedNormalization =
        Sigma.desc (fun a ↦ (Z a).fromNormalization ≫ j a) := by
  classical
  have key (a : Fin v) :
      ∃ e : (Z a).normalization ≅ (B.reducedNormalizationComponent (components a)).normalization,
        e.hom ≫ (B.reducedNormalizationComponent (components a)).fromNormalization ≫
          (IdealSheafData.vanishingIdeal ⟨(components a).1,
            isClosed_of_mem_irreducibleComponents _ (components a).2⟩).subschemeι =
          (Z a).fromNormalization ≫ j a := by
    obtain ⟨e, he⟩ := reduced_component_iso (j a) (components a) (hj a)
    obtain ⟨E, hE⟩ := normalization_iso e
    refine ⟨E, ?_⟩
    rw [← Category.assoc, hE, Category.assoc, he]
  choose e he using key
  let E : (∐ fun a ↦ (Z a).normalization) ≅ B.reducedNormalization :=
    Sigma.whiskerEquiv components (fun a ↦ (e a).symm)
  refine ⟨E, ?_⟩
  apply Sigma.hom_ext
  intro a
  dsimp [E, Scheme.fromReducedNormalization]
  simp only [Sigma.whiskerEquiv_hom, Sigma.ι_comp_map'_assoc, Sigma.ι_desc]
  exact he a

/- The normalization exact sequence contributes one copy of the residue field at every
nonsmooth point. Euler additivity and affine pushforward identify the Euler characteristic
of the original curve with the sum of the component Euler characteristics minus that
number. Each smooth proper connected normalized component has Euler characteristic
`1 - genus`, because its structure-sheaf cohomology vanishes above degree one, has
degree-zero dimension one, and degree-one dimension its genus. -/
set_option backward.isDefEq.respectTransparency false in
/-- For a proper reduced connected nodal curve, the structure-sheaf Euler characteristic
is the number of irreducible components minus the number of internal nodes minus the sum
of the genera of the normalized components.

Source: Stacks Project, Varieties, Tag 0C1R (lemma-prepare-delta-invariant), normalization
exact sequence; Curves, Tag 0CBW (lemma-split-node), completed split-node model
(blueprint: lem-trf-nodal-curve-normalization-euler).

Proof:
1. Apply `nodal_normalization_quotient` to the finite nonsmooth locus. It supplies the
   coherent short exact sequence from the structure sheaf to the pushforward of the
   componentwise normalization and gives Euler characteristic equal to the number of
   nonsmooth points.
2. Identify the supplied integral closed components with the canonical reduced
   components, and identify their normalizations by the normalization universal property.
   Euler additivity and affine pushforward invariance identify the Euler characteristic
   of the curve with that of its normalization minus the nonsmooth-point count. The
   disjoint-open-cover Euler formula expresses the latter as the sum over components.
3. Each normalized component has dimension one because its normalization preserves
   dimension. It is smooth, proper and connected by hypothesis. Apply `eulerChar_unit_eq`
   and `genus_eq_arithmeticGenus` to obtain Euler characteristic `1 - genus`.
4. Summing these values gives the displayed formula. A self-node contributes exactly one
   copy in the normalization quotient and is therefore counted once.
-/
theorem nodal_curve_normalization_euler
    (k : Type u) [Field k] [IsAlgClosed k]
    (B : Scheme.{u}) [B.Over (Spec (.of k))]
    [IsProper (B ↘ Spec (.of k))] [IsReduced B] [ConnectedSpace B]
    (hpure : ∀ Z : Set B, Z ∈ irreducibleComponents B → topologicalKrullDim Z = 1)
    (hnodal : ∀ x : B, x ∉ (B ↘ Spec (.of k)).smoothLocus →
      Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (B.presheaf.stalk x))
        (B.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸ Ideal.span
            {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})))
    (N : Set B) (hN : N = {x : B | x ∉ (B ↘ Spec (.of k)).smoothLocus})
    (v : ℕ) (components : Fin v ≃ irreducibleComponents B)
    (Z : Fin v → Scheme.{u}) [∀ a : Fin v, IsIntegral (Z a)]
    (j : ∀ a : Fin v, Z a ⟶ B) [∀ a : Fin v, IsClosedImmersion (j a)]
    (hcomponents : ∀ a : Fin v, Set.range (j a) = (components a).1)
    (hnormalizations : ∀ a : Fin v,
      IsProper ((Z a).fromNormalization ≫ j a ≫ B ↘ Spec (.of k)) ∧
      Smooth ((Z a).fromNormalization ≫ j a ≫ B ↘ Spec (.of k)) ∧
      ConnectedSpace (Z a).normalization) :
    Scheme.Modules.eulerChar k (Modules.unit B) =
      (v : ℤ) - (N.ncard : ℤ) -
        ∑ a : Fin v,
          (((Z a).fromNormalization ≫ j a ≫ B ↘ Spec (.of k)).genus : ℤ) := by
  classical
  obtain ⟨hNfin, hfinite, hO, hP, Q, q, hq, hseq, hQ, ⟨i, hi, ⟨ei⟩⟩, -, hchiQ⟩ :=
    nodal_normalization_quotient k B hpure hnodal N hN
  have : IsFinite B.fromReducedNormalization := hfinite
  have : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian
    (B ↘ Spec (.of k))
  have : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace
    (B ↘ Spec (.of k))
  have : IsSeparated (terminal.from B) := by
    rw [← terminal.comp_from (B ↘ Spec (.of k))]
    infer_instance
  have : Finite N := hNfin.to_subtype
  have (x : N) : IsClosedImmersion (i x) := (hi x).1
  have : Q.IsFinitePresentation := by
    have (x : N) := Modules.isFinitePresentation_pushforward_unit (i x)
    have := Modules.isFinitePresentation_sigma
      (fun x : N ↦ (Modules.pushforward (i x)).obj (Modules.unit (Spec (.of k))))
    exact Modules.isFinitePresentation_of_iso ei.symm
  let P := (Modules.pushforward B.fromReducedNormalization).obj
    (Modules.unit B.reducedNormalization)
  have := Modules.isFinitePresentation_pushforward_unit B.fromReducedNormalization
  have := SheafOfModules.isQuasicoherent_unit (R := B.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_unit (R := B.reducedNormalization.ringCatSheaf)
  have : P.IsQuasicoherent := Modules.isQuasicoherent_pushforward_of_isAffineHom _ _
  have : (SheafOfModules.unit B.ringCatSheaf).IsInvertible :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  have : (SheafOfModules.unit B.ringCatSheaf).IsFiniteLocallyFree :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
  have : (SheafOfModules.unit B.ringCatSheaf).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have (q' : ℕ) := Modules.finiteDimensional_H_of_isProper (k := k) (Modules.unit B) q'
  have (q' : ℕ) := Modules.finiteDimensional_H_of_isProper (k := k) P q'
  have (q' : ℕ) := Modules.finiteDimensional_H_of_isProper (k := k) Q q'
  obtain ⟨D, hD⟩ := Modules.exists_forall_subsingleton_H_of_isQuasicoherent (X := B)
  change (ShortComplex.mk (show Modules.unit B ⟶ P from
    SheafOfModules.unitToPushforwardObjUnit
      B.fromReducedNormalization.toRingCatSheafHom) q hq).ShortExact at hseq
  have hadd := Modules.eulerChar_eq_add_of_shortExact k hseq D
    (hD (Modules.unit B)) (hD P) (hD Q)
  have hchi : P.eulerChar k = (Modules.unit B).eulerChar k + (N.ncard : ℤ) := by
    simpa only [hchiQ] using hadd
  obtain ⟨E, hE⟩ := normalization_presentation B v components Z j hcomponents
  let : B.reducedNormalization.Over (Spec (.of k)) :=
    ⟨B.fromReducedNormalization ≫ B ↘ Spec (.of k)⟩
  have : B.fromReducedNormalization.IsOver (Spec (.of k)) := ⟨rfl⟩
  have hpush := Modules.eulerChar_pushforward_of_isAffineHom k B.fromReducedNormalization
    (Modules.unit B.reducedNormalization)
  let Y (a : Fin v) := (Z a).normalization
  let f : (∐ Y) ⟶ B := Sigma.desc (fun a ↦ (Z a).fromNormalization ≫ j a)
  have (a : Fin v) : IsFinite (Z a).fromNormalization :=
    (Z a).isFinite_fromNormalization_of_locallyOfFiniteType (j a ≫ B ↘ Spec (.of k))
  have (a : Fin v) : IsFinite ((Z a).fromNormalization ≫ j a) := inferInstance
  have : IsFinite f := IsFinite.sigmaDesc _
  let p := f ≫ B ↘ Spec (.of k)
  have : IsProper p := inferInstance
  let : (∐ Y).Over (Spec (.of k)) := ⟨p⟩
  have : E.hom.IsOver (Spec (.of k)) := by
    constructor
    change E.hom ≫ B.fromReducedNormalization ≫ B ↘ Spec (.of k) = p
    rw [← Category.assoc, hE]
  have hiso := euler_iso k E.hom
  have hsum := euler_sigma k v Y p
  have hvalues : (∑ a : Fin v,
      letI : (Y a).Over (Spec (.of k)) := ⟨Sigma.ι Y a ≫ p⟩
      Modules.eulerChar k (Modules.unit (Y a))) =
      ∑ a : Fin v, (1 - ((Z a).fromNormalization ≫ j a ≫
        B ↘ Spec (.of k)).genus : ℤ) := by
    apply Finset.sum_congr rfl
    intro a _
    have hp : Sigma.ι Y a ≫ p = (Z a).fromNormalization ≫ j a ≫ B ↘ Spec (.of k) := by
      simp [p, f, Category.assoc]
    change @Modules.eulerChar k _ (Z a).normalization ⟨Sigma.ι Y a ≫ p⟩ _ = _
    rw [hp]
    have := (hnormalizations a).1
    have := (hnormalizations a).2.1
    have := (hnormalizations a).2.2
    exact component_euler k B (Z a) (j a)
      (by rw [hcomponents a]; exact hpure _ (components a).2)
  have hnum : (∑ a : Fin v,
      (1 - ((Z a).fromNormalization ≫ j a ≫ B ↘ Spec (.of k)).genus : ℤ)) =
      (v : ℤ) - ∑ a : Fin v,
        (((Z a).fromNormalization ≫ j a ≫ B ↘ Spec (.of k)).genus : ℤ) := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [hvalues, hnum] at hsum
  change P.eulerChar k = _ at hpush
  linarith

end AlgebraicGeometry.Scheme
