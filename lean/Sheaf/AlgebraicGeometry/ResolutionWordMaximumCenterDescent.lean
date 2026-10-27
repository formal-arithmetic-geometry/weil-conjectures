module

public import Sheaf.AlgebraicGeometry.NormalizedResolutionWordGluing
public import Sheaf.AlgebraicGeometry.HilbertSamuelReachableLevels
public import Sheaf.AlgebraicGeometry.MarkedIdealNumericalResolutionEngine
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.Topology.Irreducible


import Sheaf.AlgebraicGeometry.ResolutionWordLocalMaximumModels
import WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial
import Mathlib.Data.Finset.Max
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.RingTheory.FlatUnderRegular
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # Étale descent of normalized-word maximum centers

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé VIII, 2.3.11, p. 93;
Stacks Project, Tags 02GO, 033B, 00FN and 00FP
(blueprint: lem-trf-resolution-word-maximum-center-descent).

The theorem states the reduced maximum center, its local étale marked-history models,
and coherence of its defining ideals.  The local model clause uses the existing
`ResolutionWordChart` and `MarkedIdeal.IsMaximumStep` interfaces.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.EmbeddedResolutionHistory

/-- The final intrinsic map of a local resolution-word presentation chart.
This is the chart's given étale map, transported by its final-index equality.
Source: ILO VIII 2.3.11, local presentation comparison in node proof steps 3--4
(blueprint: lem-trf-resolution-word-maximum-center-descent). -/
def ResolutionWordChart.finalMap {R : MarkedIdeal.NumericalResolution.{u}}
    {A : EmbeddedResolutionPair.{u}} {n : ℕ} {H : EmbeddedResolutionHistory A n}
    {x : H.X} (C : ResolutionWordChart R H x) : C.history.last.ambient.X ⟶ H.X :=
  C.intrinsic (Fin.last C.length) ≫
    eqToHom (congrArg (fun j ↦ H.intrinsic.obj (op j)) C.last)


/-- The reduced full maximum center is regular and nowhere dense, with coherent
intrinsic and ambient ideals. Each maximum point has an étale presentation chart
on which the actual marked-history maximum center is its scheme-theoretic pullback.
The hypothesis `hν` is exactly the property supplied by
`normalized_resolution_word_gluing`, for the same fixed numerical engine.

Source: ILO VIII 2.3.11, p. 93, and 2.3.13, pp. 93--94; Stacks Tags 02GO, 033B,
00FN and 00FP (blueprint: lem-trf-resolution-word-maximum-center-descent).

Proof:
1. The current ambient is Noetherian by finite type over Q
   (lem-weil-pbc-finite-type-over-noetherian). Its closed strict transform is
   Noetherian by quotient permanence (lem-weil-pbc-surjective-image-noetherian).
2. The normalized-resolution-word-gluing finite-image and upper-level clauses give
   an attained greatest value m > bottom at a nonregular stage. Its equality locus
   T is closed, nonempty and disjoint from the regular points. Use
   lem-weil-pbc-reduced-induced-closed-subscheme to give it its reduced structure.
3. At a maximum point choose the Hilbert--Samuel minimal-envelope presentation,
   retaining its ordered earlier history. Shrink away larger heads by the finite
   upper semicontinuous head (lem-trf-hilbert-samuel-smooth-dimension-profile).
   Its cosupport is the equality stratum of this head. The presenting word is
   (1,t), while the normalized word is (A,t). Deleting the common leading 1
   preserves comparisons. Thus the full local maximum is exactly the preimage
   of T. The numerical engine gives its smooth adapted maximum-center step.
4. Étale pullback of the reduced structure is reduced
   (lem-trf-etale-reduced-cartier-descent). The smooth local center is reduced
   (lem-sc-smooth-algebra-reduced-field), and factors through the pulled-back
   strict transform because its defining functions vanish on a reduced scheme.
   Uniqueness of reduced induced structures identifies the ideals and the whole
   pullback square, not only the underlying sets. The ambient composite has the
   reduced structure as well; these identifications agree on overlaps.
5. The local centers are regular by lem-weil-pbc-smooth-scheme-over-field-regular.
   Their maps to the descended center are étale by base change, hence flat.
   Noetherianity of the local rings follows from localization permanence.
   The flat-local criterion lem-weil-pbc-flat-under-regular proves regularity
   of the descended center, including its local Noetherianity.
6. Reducedness implies Serre R0 (lem-weil-pbc-serre-criterion-reduced); hence
   every component generic point is regular and is excluded from T. Any nonempty
   open set contains a component generic point, proving the asserted empty interior.
7. Both center ideals are quasi-coherent by the reduced-induced construction.
   On Noetherian affine charts they are finitely generated submodules of the
   rank-one free module (lem-weil-pbc-noetherian-submodule-finite). Apply
   pqf-lem-coherent-ft-locnoeth to obtain coherence on both schemes.
-/
theorem resolution_word_maximum_center_descent
    (R : MarkedIdeal.NumericalResolution.{u})
    (ν : ValueFamily.{u} HilbertSamuel.ResolutionWord)
    (hν : ∀ {B : EmbeddedResolutionPair.{u}} {k : ℕ}
      (G : EmbeddedResolutionHistory B k), Admissible ν G →
      (∀ x : G.X, ¬ IsRegularLocalRing (G.X.presheaf.stalk x) →
        Nonempty (ResolutionWordChart R G x)) ∧
      (∀ (x : G.X) (C : ResolutionWordChart R G x),
        (R.value C.history ⟨C.supportPoint, C.cosupport⟩).head? =
          some (MarkedIdeal.rational 1) ∧ ν G x = C.word) ∧
      (Set.range (ν G)).Finite ∧
      (∀ v : HilbertSamuel.ResolutionWord, IsClosed {x : G.X | v ≤ ν G x}) ∧
      (∀ x : G.X, ν G x = ⊥ ↔ IsRegularLocalRing (G.X.presheaf.stalk x)) ∧
      ∀ (D : ℕ) (_hD : topologicalKrullDim G.X ≤ (D : WithBot ℕ∞)) (x y : G.X),
        (HilbertSamuel.sumResolutionWord D (ν G x) ≤
            HilbertSamuel.sumResolutionWord D (ν G y) ↔ ν G x ≤ ν G y) ∧
        (HilbertSamuel.sumResolutionWord D (ν G x) =
            HilbertSamuel.sumResolutionWord D (ν G y) ↔ ν G x = ν G y))
    {A : EmbeddedResolutionPair.{u}} {n : ℕ} (H : EmbeddedResolutionHistory A n)
    (hH : Admissible ν H)
    (hP : Smooth H.base ∧ IsSeparated H.base ∧ LocallyOfFiniteType H.base ∧
      QuasiCompact H.base)
    (hX : IsReduced H.X) (hNR : ¬ IsRegularScheme H.X) :
    ∃ (m : HilbertSamuel.ResolutionWord) (T : TopologicalSpace.Closeds H.X),
      IsGreatest (Set.range (ν H)) m ∧ ⊥ < m ∧
      (T : Set H.X) = {x | ν H x = m} ∧
      Nonempty (Scheme.IdealSheafData.vanishingIdeal T).subscheme ∧
      IsRegularScheme (Scheme.IdealSheafData.vanishingIdeal T).subscheme ∧
      (∀ x ∈ T, ¬ IsRegularLocalRing (H.X.presheaf.stalk x)) ∧
      (∀ Z ∈ irreducibleComponents H.X, ¬ Z ⊆ (T : Set H.X)) ∧
      interior (T : Set H.X) = ∅ ∧
      RingedSpace.IsCoherent H.X.toRingedSpace
        (Scheme.IdealSheafData.vanishingIdeal T).toModules ∧
      RingedSpace.IsCoherent H.P.toRingedSpace
        ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫
          H.inclusion.app (op (Fin.last n))).ker.toModules ∧
      (∀ x ∈ T, ∃ C : ResolutionWordChart R H x,
        Etale C.finalMap ∧
        ∃ (K : MarkedIdeal.History (C.length + 1))
          (E : MarkedIdeal.Extension C.history K),
          MarkedIdeal.IsMaximumStep R.value E ∧
          IsReduced (K.step (Fin.last C.length)).step.center.subscheme ∧
          Smooth (E.centerMap ≫ C.history.last.marked.j ≫ C.history.last.ambient.p) ∧
          HasAdaptedNormalCrossingsCenter
            (E.centerMap ≫ C.history.last.marked.j).ker
            (fun i ↦ C.history.last.ambient.boundary.get i) ∧
          ∃ i : (K.step (Fin.last C.length)).step.center.subscheme ⟶
              C.history.last.ambient.X,
            IsClosedImmersion i ∧
            i ≫ C.history.last.ambient.i = E.centerMap ≫ C.history.last.marked.j ∧
            i.ker = (Scheme.IdealSheafData.vanishingIdeal T).comap C.finalMap ∧
            ∃ c : (K.step (Fin.last C.length)).step.center.subscheme ⟶
                (Scheme.IdealSheafData.vanishingIdeal T).subscheme,
              IsPullback i c C.finalMap
                (Scheme.IdealSheafData.vanishingIdeal T).subschemeι) := by
  classical
  have : LocallyOfFiniteType H.base := hP.2.2.1
  have : IsLocallyNoetherian H.P := LocallyOfFiniteType.isLocallyNoetherian H.base
  have : IsClosedImmersion (H.inclusion.app (op (Fin.last n))) := H.closed _
  have : IsLocallyNoetherian (H.ambient.obj (op (Fin.last n))) :=
    ‹IsLocallyNoetherian H.P›
  have : IsLocallyNoetherian (H.intrinsic.obj (op (Fin.last n))) :=
    LocallyOfFiniteType.isLocallyNoetherian (H.inclusion.app (op (Fin.last n)))
  have : IsLocallyNoetherian H.X := ‹IsLocallyNoetherian (H.intrinsic.obj _)›
  obtain ⟨hcharts, hwords, hfin, hclosed, hbot, hsum⟩ := hν H hH
  obtain ⟨x₀, hx₀⟩ : ∃ x : H.X, ¬ IsRegularLocalRing (H.X.presheaf.stalk x) := by
    by_contra h
    apply hNR
    exact ⟨inferInstance, ⟨fun x ↦ by simpa using not_exists_not.mp h x⟩⟩
  let S := hfin.toFinset
  have hS : S.Nonempty := by
    exact ⟨ν H x₀, hfin.mem_toFinset.mpr (Set.mem_range_self _)⟩
  let m := S.max' hS
  have hm : IsGreatest (Set.range (ν H)) m := by
    simpa only [S, Set.Finite.coe_toFinset] using S.isGreatest_max' hS
  have hpos : ⊥ < m := lt_of_lt_of_le
    (bot_lt_iff_ne_bot.mpr (fun h ↦ hx₀ ((hbot x₀).mp h)))
    (hm.2 (Set.mem_range_self x₀))
  have heq : {x : H.X | m ≤ ν H x} = {x | ν H x = m} := by
    ext x
    exact ⟨fun h ↦ le_antisymm (hm.2 (Set.mem_range_self x)) h,
      fun h ↦ h.symm.le⟩
  let T : TopologicalSpace.Closeds H.X := ⟨{x | ν H x = m}, heq ▸ hclosed m⟩
  have hT : (T : Set H.X) = {x | ν H x = m} := rfl
  have hsing : ∀ x ∈ T, ¬ IsRegularLocalRing (H.X.presheaf.stalk x) := by
    intro x hx hreg
    have hx' : ν H x = m := hx
    exact (ne_of_gt hpos) (hx'.symm.trans ((hbot x).mpr hreg))
  have hlocal := resolution_word_local_maximum_models R ν hν H hH hP hX m T hm hpos hT
  have hmodels : ∀ x ∈ T, ∃ C : ResolutionWordChart R H x,
      Etale C.finalMap ∧
      ∃ (K : MarkedIdeal.History (C.length + 1))
        (E : MarkedIdeal.Extension C.history K),
        MarkedIdeal.IsMaximumStep R.value E ∧
        IsReduced (K.step (Fin.last C.length)).step.center.subscheme ∧
        Smooth (E.centerMap ≫ C.history.last.marked.j ≫ C.history.last.ambient.p) ∧
        HasAdaptedNormalCrossingsCenter
          (E.centerMap ≫ C.history.last.marked.j).ker
          (fun i ↦ C.history.last.ambient.boundary.get i) ∧
        ∃ i : (K.step (Fin.last C.length)).step.center.subscheme ⟶
            C.history.last.ambient.X,
          IsClosedImmersion i ∧
          i ≫ C.history.last.ambient.i = E.centerMap ≫ C.history.last.marked.j ∧
          i.ker = (Scheme.IdealSheafData.vanishingIdeal T).comap C.finalMap ∧
          ∃ c : (K.step (Fin.last C.length)).step.center.subscheme ⟶
              (Scheme.IdealSheafData.vanishingIdeal T).subscheme,
            IsPullback i c C.finalMap
              (Scheme.IdealSheafData.vanishingIdeal T).subschemeι := by
    intro x hx
    obtain ⟨C, hC⟩ := hlocal x hx
    refine ⟨C, ?_, hC⟩
    have := C.etale (Fin.last C.length)
    dsimp only [ResolutionWordChart.finalMap]
    infer_instance
  have hregular : IsRegularScheme (Scheme.IdealSheafData.vanishingIdeal T).subscheme := by
    have : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal T).subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian
        (Scheme.IdealSheafData.vanishingIdeal T).subschemeι
    refine ⟨inferInstance, ⟨fun z ↦ ?_⟩⟩
    let j := (Scheme.IdealSheafData.vanishingIdeal T).subschemeι
    have hz : j z ∈ T := by
      have hrange := (Scheme.IdealSheafData.reduced_induced_closed_subscheme H.X T).2.2.2.2.2.1
      change j z ∈ (T : Set H.X)
      rw [← hrange]
      exact Set.mem_range_self z
    obtain ⟨C, hC, K, E, hmax, hred, hsm, hnc, i, hi, hcomp, hker, c, hpb⟩ :=
      hmodels (j z) hz
    have hp : C.finalMap (C.point (Fin.last C.length)) = j z := by
      have htransport (k : Fin (n + 1)) (e : k = Fin.last n) :
          H.wordStageMap k ≫ eqToHom (congrArg (fun t ↦ H.intrinsic.obj (op t)) e) =
            𝟙 H.X := by
        subst k
        simp [wordStageMap, X]
      change (eqToHom (congrArg (fun t ↦ H.intrinsic.obj (op t)) C.last))
        ((C.intrinsic (Fin.last C.length)) (C.point (Fin.last C.length))) = j z
      rw [C.pointed (Fin.last C.length)]
      change (H.wordStageMap _ ≫ eqToHom _) (j z) = j z
      rw [htransport _ C.last]
      rfl
    obtain ⟨w, hw, hwz⟩ := Scheme.exists_preimage_of_isPullback hpb
      (C.point (Fin.last C.length)) z hp
    have : Etale C.finalMap := hC
    have : Etale c := MorphismProperty.of_isPullback hpb hC
    have : Smooth (E.centerMap ≫ C.history.last.marked.j ≫ C.history.last.ambient.p) := hsm
    have := IsRegular.of_smooth
      (E.centerMap ≫ C.history.last.marked.j ≫ C.history.last.ambient.p)
    have hr := IsRegularLocalRing.of_ringHom_flat (c.stalkMap w).hom (Flat.stalkMap c w)
    exact hwz ▸ hr
  have hgeneric (x : H.X) (hx : closure {x} ∈ irreducibleComponents H.X) : x ∉ T := by
    have : IsReduced H.X := hX
    let := (isField_stalk_of_closure_mem_irreducibleComponents H.X x hx).toField
    exact fun hxT ↦ hsing x hxT inferInstance
  have hcomponents : ∀ Z ∈ irreducibleComponents H.X, ¬ Z ⊆ (T : Set H.X) := by
    intro Z hZ hZT
    have hη := hZ.1.isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents Z hZ)
    exact hgeneric _ (hη.def.symm ▸ hZ) (hZT hη.mem)
  have hinterior : interior (T : Set H.X) = ∅ := by
    have hd : Dense ((T : Set H.X)ᶜ) := by
      apply Dense.mono (fun x hx ↦ hgeneric x hx)
      exact dense_iff_closure_eq.mpr genericPoints.closure
    exact interior_eq_empty_iff_dense_compl.mpr hd
  have hcoherent {Y : Scheme.{u}} [IsLocallyNoetherian Y] (I : Y.IdealSheafData) :
      RingedSpace.IsCoherent Y.toRingedSpace I.toModules := by
    have := Scheme.Modules.isQuasicoherent_toModules I
    have := Scheme.Modules.isFinitePresentation_toModules I
    exact (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Y _).mpr
      ⟨inferInstance, inferInstance⟩
  obtain ⟨x, hx⟩ := hm.1
  have hxT : x ∈ T := hx
  have hnonempty : Nonempty (Scheme.IdealSheafData.vanishingIdeal T).subscheme := by
    have hxrange : x ∈ Set.range (Scheme.IdealSheafData.vanishingIdeal T).subschemeι := by
      rw [(Scheme.IdealSheafData.reduced_induced_closed_subscheme H.X T).2.2.2.2.2.1]
      exact hxT
    obtain ⟨z, hz⟩ := hxrange
    exact ⟨z⟩
  exact ⟨m, T, hm, hpos, hT, hnonempty, hregular, hsing, hcomponents, hinterior,
    hcoherent _, hcoherent _, hmodels⟩

end AlgebraicGeometry.EmbeddedResolutionHistory
