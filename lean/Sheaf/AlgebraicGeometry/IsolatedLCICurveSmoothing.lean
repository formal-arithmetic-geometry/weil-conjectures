module

public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.TraceFormula.LciPointwiseCriterion
import Sheaf.AlgebraicGeometry.FiniteJetSmoothGenericFibre
import Sheaf.RingTheory.LCILocalFittingSmoothing
import Sheaf.AlgebraicGeometry.IsolatedCurveLocalAlgebraization
import Sheaf.AlgebraicGeometry.IsolatedCurveLocalFittingCriterion

/-! # Smoothing proper curves with isolated complete-intersection singularities

Source: Stacks Project, examples-defos.tex, Tag 0E7Y,
`lemma-smoothing-proper-curve-isolated-lci`.
(blueprint: lem-sfb-isolated-lci-curve-smoothing).

The special fibre uses the constant-coefficient homomorphism `k[[t]] → k`.
The generic fibre uses the localization `k[[t]][1/t]`, as in the node statement.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem ci_local_of_regular_presentation
    (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A] [IsLocalRing A]
    (R : Type u) [CommRing R] [Algebra k R] [IsRegularLocalRing R]
    [Algebra.EssFiniteType k R] (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs)
    (e : (R ⧸ Ideal.span (Set.range (fun i : Fin rs.length ↦ rs.get i))) ≃ₐ[k] A) :
    Algebra.IsCompleteIntersectionLocalAlgebra k A := by
  classical
  have hid : Ideal.span (Set.range (fun i : Fin rs.length ↦ rs.get i)) =
      Ideal.ofList rs := by
    congr 1
    ext r
    simp only [Set.mem_range, Set.mem_ofPred_eq]
    exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ List.get_mem rs i,
      fun hr ↦ List.mem_iff_get.mp hr⟩
  let e' : (R ⧸ Ideal.ofList rs) ≃ₐ[k] A :=
    (Ideal.quotientEquivAlgOfEq k hid.symm).trans e
  have hproper : Ideal.ofList rs ≠ ⊤ := by
    intro h
    have := hreg.top_ne_smul
    simp [h] at this
  have hmax : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R :=
    fun _ hr ↦ IsLocalRing.le_maximalIdeal hproper (Ideal.subset_span hr)
  exact ⟨inferInstance,
    Algebra.EssFiniteType.of_surjective e'.toAlgHom e'.surjective,
    R, inferInstance, inferInstance, inferInstance, inferInstance, rs, hreg, hmax, ⟨e'⟩⟩

private theorem smooth_away_of_smooth_laurent
    (k : Type u) [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of (PowerSeries k)))
    (h : Smooth (pullback.snd g (Spec.map (CommRingCat.ofHom
      (algebraMap (PowerSeries k) (LaurentSeries k)))))) :
    Smooth (pullback.snd g (Spec.map (CommRingCat.ofHom
      (algebraMap (PowerSeries k)
        (Localization.Away (PowerSeries.X : PowerSeries k)))))) := by
  let e : Localization.Away (PowerSeries.X : PowerSeries k) ≃ₐ[PowerSeries k]
      LaurentSeries k := IsLocalization.algEquiv (Submonoid.powers PowerSeries.X) _ _
  let b : Spec (.of (LaurentSeries k)) ⟶
      Spec (.of (Localization.Away (PowerSeries.X : PowerSeries k))) :=
    Spec.map (CommRingCat.ofHom e.toRingHom)
  have hb : IsIso b := by
    change IsIso (Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom))
    exact inferInstance
  have heq : b ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (PowerSeries k)
        (Localization.Away (PowerSeries.X : PowerSeries k)))) =
      Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k))) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact e.commutes a
  let a := Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k)
    (Localization.Away (PowerSeries.X : PowerSeries k))))
  let l := Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))
  let q := pullback.map g l g a (𝟙 Y) b (𝟙 _) (by simp) (by simpa using heq.symm)
  have hq : IsIso q := by dsimp [q]; infer_instance
  have hcomm : q ≫ pullback.snd g a = pullback.snd g l ≫ b := by
    simp [q]
  have hs : Smooth (q ≫ pullback.snd g a) := by
    rw [hcomm]
    have : Smooth (pullback.snd g l) := h
    infer_instance
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @Smooth) q _).mp hs

private theorem smooth_generic_of_fitting_open_cover
    (k : Type u) [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of (PowerSeries k)))
    (U : Fin 2 → Y.Opens) (hcover : (⨆ i, U i) = ⊤)
    [∀ i, IsProper ((U i).ι ≫ g)] [Flat g] [LocallyOfFinitePresentation g]
    (hCM : ∀ i, ∀ x : ↥(pullback ((U i).ι ≫ g) (Spec.map (CommRingCat.ofHom
        (PowerSeries.constantCoeff (R := k))))),
      (IsLocalRing.depth
        (R := (pullback ((U i).ι ≫ g) (Spec.map (CommRingCat.ofHom
          (PowerSeries.constantCoeff (R := k))))).presheaf.stalk x)
        ((pullback ((U i).ι ≫ g) (Spec.map (CommRingCat.ofHom
          (PowerSeries.constantCoeff (R := k))))).presheaf.stalk x) : WithBot ℕ∞) =
      ringKrullDim ((pullback ((U i).ι ≫ g) (Spec.map (CommRingCat.ofHom
        (PowerSeries.constantCoeff (R := k))))).presheaf.stalk x))
    (hpure : ∀ i, (pullback ((U i).ι ≫ g) (Spec.map (CommRingCat.ofHom
      (PowerSeries.constantCoeff (R := k))))).IsPureDimension i.val)
    (hjet : ∀ i, ∃ n : ℕ, 1 ≤ n ∧
      (pullback.snd ((U i).ι ≫ g) (Scheme.powerSeriesJetBaseMap k n)).appTop
        ((Scheme.ΓSpecIso (.of ((PowerSeries k) ⧸
          Ideal.span {(PowerSeries.X : PowerSeries k) ^ n}))).inv
          (Ideal.Quotient.mk _ ((PowerSeries.X : PowerSeries k) ^ (n - 1)))) ∈
      (Scheme.Modules.fittingIdealSheaf
        (pullback.snd ((U i).ι ≫ g) (Scheme.powerSeriesJetBaseMap k n)).relativeDifferentials
          i.val).idealOfOpens ⊤) :
    Smooth (pullback.snd g (Spec.map (CommRingCat.ofHom
      (algebraMap (PowerSeries k)
        (Localization.Away (PowerSeries.X : PowerSeries k)))))) := by
  let a := Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k)
    (Localization.Away (PowerSeries.X : PowerSeries k))))
  let 𝒰 := Y.openCoverOfIsOpenCover (s := Set.range U) Subtype.val
    (by ext; simp [← hcover])
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth)
    (𝒰.pullback₁ (pullback.fst g a))
  rintro ⟨_, i, rfl⟩
  have hs := smooth_away_of_smooth_laurent k ((U i).ι ≫ g)
    (smooth_genericFibre_of_finiteJet_fitting k ((U i).ι ≫ g) i.val
      (hCM i) (hpure i) (hjet i))
  have hpb := (IsPullback.of_hasPullback (pullback.fst g a) (U i).ι).flip.paste_vert
    (IsPullback.of_hasPullback g a)
  have heq := hpb.isoPullback_hom_snd
  have hiso : IsIso hpb.isoPullback.hom := inferInstance
  change Smooth (pullback.fst (pullback.fst g a) (U i).ι ≫ pullback.snd g a)
  rw [← heq]
  have : Smooth (pullback.snd ((U i).ι ≫ g) a) := hs
  infer_instance

/-- A proper local-complete-intersection scheme of dimension at most one, smooth away
from finitely many closed points, admits a flat finitely presented H-projective smoothing.
Source: Stacks Project, examples-defos.tex, Tag 0E7Y,
`lemma-smoothing-proper-curve-isolated-lci`.
(blueprint: lem-sfb-isolated-lci-curve-smoothing).

Proof:
1. Apply the pointwise lci criterion. Replacing its finite-indexed span by the ideal
   generated by the regular list gives a complete-intersection local algebra at each point.
2. Enumerate the given finite set of closed points; the empty set gives an empty list.
   Apply the local Fitting smoothing theorem at each listed stalk to obtain B_i and exponents.
3. Reduce each B_i modulo t^(n+1) and use isolated_curve_local_algebraization. This helper
   proves the compatibility of polynomial and power-series truncations, applies formal
   lifting and proper formal-curve algebraization, and transports the finite-jet stalk maps.
4. Apply isolated_curve_local_fitting_criterion to that family. This is the remaining
   local-to-global Fitting calculation: it supplies a proper open cover indexed by
   dimensions zero and one, Cohen--Macaulay pure special fibres, and finite-jet bounds.
5. Apply smooth_genericFibre_of_finiteJet_fitting on each member of the cover. The
   canonical equivalence k[[t]][1/t] = k((t)) transports its conclusion to the specified
   localization. Pullback pasting identifies these with an open cover of the generic
   fibre; smoothness is local on its source, giving the asserted conclusion.
-/
theorem isolated_lci_curve_smoothing
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    (hlci : ∃ (I : Type u) (A : I → CommRingCat.{u})
      (aA : ∀ i, Algebra k (A i)) (ft : ∀ i, Algebra.FiniteType k (A i))
      (φ : ∀ i, Spec (A i) ⟶ X),
      (∀ i, IsOpenImmersion (φ i)) ∧
        (∀ i, φ i ≫ f =
          Spec.map (CommRingCat.ofHom (@algebraMap k (A i) _ _ (aA i)))) ∧
        (∀ x : X, ∃ i, ∃ y : Spec (A i), φ i y = x) ∧
        (∀ i, @Algebra.IsLocalCompleteIntersection k (A i) _ _ (aA i) (ft i)))
    (hsmooth : ∃ S : Set X, S.Finite ∧ (∀ x ∈ S, IsClosed ({x} : Set X)) ∧
      ∀ x ∉ S, ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of (PowerSeries k))),
      Flat g ∧ LocallyOfFinitePresentation g ∧ QuasiCompact g ∧ QuasiSeparated g ∧
        IsHProjective g ∧
        (∃ e : pullback g (Spec.map (CommRingCat.ofHom
            (PowerSeries.constantCoeff (R := k)))) ≅ X,
          e.hom ≫ f = pullback.snd g (Spec.map (CommRingCat.ofHom
            (PowerSeries.constantCoeff (R := k))))) ∧
        Smooth (pullback.snd g (Spec.map (CommRingCat.ofHom
          (algebraMap (PowerSeries k)
            (Localization.Away (PowerSeries.X : PowerSeries k)))))) := by
  classical
  have hlocal : ∀ x : X,
      let : Algebra k (X.presheaf.stalk x) :=
        (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top ≫
          X.presheaf.germ ⊤ x trivial).hom.toAlgebra)
      Algebra.IsCompleteIntersectionLocalAlgebra k (X.presheaf.stalk x) := by
    intro x
    let : Algebra k (X.presheaf.stalk x) :=
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top ≫
        X.presheaf.germ ⊤ x trivial).hom.toAlgebra)
    obtain ⟨R, hR, aR, localR, noethR, regR, ftR, rs, hreg, ⟨e⟩⟩ :=
      (lci_pointwise_criterion.{u, u} k X f).1.mp hlci x
    let := hR
    let := aR
    have := localR
    have := noethR
    have := regR
    have := ftR
    exact ci_local_of_regular_presentation k (X.presheaf.stalk x) R rs hreg e
  obtain ⟨S, hfinite, hclosed, hsmooth⟩ := hsmooth
  let : Fintype S := hfinite.fintype
  let r := Fintype.card S
  let p : Fin r → X := fun i ↦ ((Fintype.equivFin S).symm i).1
  have hp : Function.Injective p :=
    Subtype.val_injective.comp (Fintype.equivFin S).symm.injective
  have hprange : Set.range p = S := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ((Fintype.equivFin S).symm i).2
    · intro hx
      exact ⟨(Fintype.equivFin S) ⟨x, hx⟩, by simp [p]⟩
  have hc : ∀ i, IsClosed ({p i} : Set X) :=
    fun i ↦ hclosed _ ((Fintype.equivFin S).symm i).2
  have hs : ∀ x ∉ Set.range p, ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f) := by
    simpa only [hprange] using hsmooth
  have hdef (i : Fin r) :=
    let : Algebra k (X.presheaf.stalk (p i)) :=
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top ≫
        X.presheaf.germ ⊤ (p i) trivial).hom.toAlgebra)
    Algebra.exists_local_fitting_smoothing k (X.presheaf.stalk (p i)) (hlocal (p i))
  choose ex B ringB localB algB algkB towerB flatB ftB special m π hπ hbound using hdef
  let := ringB
  have := localB
  let := algB
  let := algkB
  have := towerB
  have := flatB
  have := ftB
  let eB := fun i ↦ (special i).some
  obtain ⟨Y, g, hflat, hfp, hqc, hqs, hproj, e, he, j, hj, h, hscalar⟩ :=
    isolated_curve_local_algebraization k X f hdim r p hp hc hs B eB
  have := hflat
  have := hfp
  have := hproj
  obtain ⟨U, hcover, hproper, hCM, hpure, hjet⟩ :=
    isolated_curve_local_fitting_criterion k X f hdim hlci r p hp hc hs B
      ex m π hπ hbound Y g e he j hj h hscalar
  have := hproper
  exact ⟨Y, g, hflat, hfp, hqc, hqs, hproj, ⟨e, he⟩,
    smooth_generic_of_fitting_open_cover k g U hcover hCM hpure hjet⟩

end AlgebraicGeometry
