/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F9
-/
module

public import Sheaf.AlgebraicGeometry.FiniteJetSmoothGenericFibre
public import Sheaf.AlgebraicGeometry.IsolatedCurveFormalLifting
public import Sheaf.AlgebraicGeometry.ProperFormalCurveAlgebraization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Sheaf.RingTheory.PresentationFittingIdeal
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.SetTheory.Cardinal.ToNat
public import WeilConjectures.RingTheory.CompleteIntersectionOverField

import all Sheaf.AlgebraicGeometry.FiniteJetSmoothGenericFibre
import Sheaf.AlgebraicGeometry.IsolatedCurveLocalFittingBounds
import Sheaf.AlgebraicGeometry.LCICohenMacaulayStalks
import WeilConjectures.AlgebraicGeometry.CohenMacaulayFibreDimensionDecomposition
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents

/-! # Local Fitting bounds on an algebraized curve

Source: Stacks Project, Tag 0E7Y, first and last paragraphs.
(blueprint: lem-sfb-isolated-curve-local-fitting-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
private theorem dimension_open_immersion {X Z : Scheme.{u}} (q : X ⟶ Z)
    [IsOpenImmersion q] (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (q x) := by
  let e := IsOpenImmersion.isoOfRangeEq q q.opensRange.ι
    (by rw [Scheme.Opens.range_ι]; rfl)
  have hx : (e.hom x).val = q x :=
    congr($(IsOpenImmersion.isoOfRangeEq_hom_fac q q.opensRange.ι
      (by rw [Scheme.Opens.range_ι]; rfl)) x)
  have hd : topologicalKrullDimAt (e.hom x) =
      topologicalKrullDimAt (e.hom x).val :=
    q.opensRange.isOpen.topologicalKrullDimAt_eq (e.hom x).property
  rw [hx] at hd
  exact (local_dimension_iso e x).trans hd

set_option backward.isDefEq.respectTransparency.types false in
private theorem curve_dimension_partition
    (k : Type u) [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of (PowerSeries k))) [IsProper g]
    [Flat g] [LocallyOfFinitePresentation g]
    (hCM : ∀ x : ↥(pullback g (Spec.map (CommRingCat.ofHom
        (PowerSeries.constantCoeff (R := k))))),
      (IsLocalRing.depth
        (R := (pullback g (Spec.map (CommRingCat.ofHom
          (PowerSeries.constantCoeff (R := k))))).presheaf.stalk x)
        ((pullback g (Spec.map (CommRingCat.ofHom
          (PowerSeries.constantCoeff (R := k))))).presheaf.stalk x) : WithBot ℕ∞) =
      ringKrullDim ((pullback g (Spec.map (CommRingCat.ofHom
        (PowerSeries.constantCoeff (R := k))))).presheaf.stalk x))
    (hsmall : topologicalKrullDim ↥(pullback g (Spec.map (CommRingCat.ofHom
      (PowerSeries.constantCoeff (R := k))))) ≤ (1 : WithBot ℕ∞)) :
    ∃ U : Fin 2 → Y.Opens, (⨆ i, U i) = ⊤ ∧
      (∀ i, IsProper ((U i).ι ≫ g)) ∧
      (∀ i, ∀ x : ↥(pullback ((U i).ι ≫ g) (Spec.map (CommRingCat.ofHom
          (PowerSeries.constantCoeff (R := k))))),
        (IsLocalRing.depth
          (R := (pullback ((U i).ι ≫ g) (Spec.map (CommRingCat.ofHom
            (PowerSeries.constantCoeff (R := k))))).presheaf.stalk x)
          ((pullback ((U i).ι ≫ g) (Spec.map (CommRingCat.ofHom
            (PowerSeries.constantCoeff (R := k))))).presheaf.stalk x) : WithBot ℕ∞) =
        ringKrullDim ((pullback ((U i).ι ≫ g) (Spec.map (CommRingCat.ofHom
          (PowerSeries.constantCoeff (R := k))))).presheaf.stalk x)) ∧
      (∀ i, (pullback ((U i).ι ≫ g) (Spec.map (CommRingCat.ofHom
        (PowerSeries.constantCoeff (R := k))))).IsPureDimension i.val) := by
  classical
  let c := Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))
  have hspecial (x : ↥(pullback g c)) :
      (IsLocalRing.depth
        (R := (g.fiber (g (pullback.fst g c x))).presheaf.stalk
          (g.asFiber (pullback.fst g c x)))
        ((g.fiber (g (pullback.fst g c x))).presheaf.stalk
          (g.asFiber (pullback.fst g c x))) : WithBot ℕ∞) =
        ringKrullDim ((g.fiber (g (pullback.fst g c x))).presheaf.stalk
          (g.asFiber (pullback.fst g c x))) := by
    obtain ⟨e, he⟩ := special_fibre_point_iso g x
    let r := ((g.fiber (g (pullback.fst g c x))).presheaf.stalkCongr
      (.of_eq he.symm) ≪≫ asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv
    rw [depth_eq_of_ringEquiv r, ringKrullDim_eq_of_ringEquiv r]
    exact hCM x
  let W : Y.Opens := ⟨_, isOpen_fibre_depth_eq_ringKrullDim g⟩
  have hW : W = ⊤ := open_eq_top_of_special_fibre g W hspecial
  have hcm (y : Y) :
      (IsLocalRing.depth (R := (g.fiber (g y)).presheaf.stalk (g.asFiber y))
        ((g.fiber (g y)).presheaf.stalk (g.asFiber y)) : WithBot ℕ∞) =
      ringKrullDim ((g.fiber (g y)).presheaf.stalk (g.asFiber y)) :=
    hW.ge (Set.mem_univ y)
  obtain ⟨V, hcover, hdisj, hdim⟩ :=
    exists_fibre_dimension_open_partition_of_depth_eq_ringKrullDim g ⊤ ⊤
      (fun y _ ↦ ⟨trivial, hcm y⟩)
  have hclopen (n : ℕ) : IsClosed (V n : Set Y) := by
    have heq : (V n : Set Y)ᶜ = ((⨆ (m : ℕ) (_ : m ≠ n), V m) : Y.Opens) := by
      ext y
      change (¬ y ∈ V n) ↔ y ∈ (⨆ (m : ℕ) (_ : m ≠ n), V m)
      simp only [TopologicalSpace.Opens.mem_iSup]
      constructor
      · intro hy
        obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover.ge (Set.mem_univ y))
        exact ⟨m, fun he ↦ hy (he ▸ hm), hm⟩
      · rintro ⟨m, hmn, hm⟩ hn
        have hd : V m ⊓ V n ≤ ⊥ := le_of_eq (disjoint_iff.mp (hdisj hmn))
        exact hd ⟨hm, hn⟩
    apply isOpen_compl_iff.mp
    rw [heq]
    exact (⨆ (m : ℕ) (_ : m ≠ n), V m).isOpen
  let U : Fin 2 → Y.Opens := fun i ↦ V i.val
  have hu : (⨆ i, U i) = ⊤ := by
    apply open_eq_top_of_special_fibre g
    intro x
    obtain ⟨n, hn⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hcover.ge (Set.mem_univ (pullback.fst g c x)))
    have hndim : (n : WithBot ℕ∞) ≤ 1 := by
      obtain ⟨e, he⟩ := special_fibre_point_iso g x
      rw [← hdim n _ hn, ← he, ← local_dimension_iso e]
      exact (iInf₂_le ⊤ trivial).trans
        ((IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ _) 
          (Homeomorph.Set.univ _).isHomeomorph).le.trans hsmall)
    have hnlt : n < 2 := by
      have : n ≤ 1 := by exact_mod_cast hndim
      omega
    exact (le_iSup U ⟨n, hnlt⟩) hn
  have hproper (i : Fin 2) : IsProper ((U i).ι ≫ g) := by
    have : IsClosedImmersion (U i).ι := IsClosedImmersion.of_isPreimmersion _
      (by rw [Scheme.Opens.range_ι]; exact hclopen i.val)
    infer_instance
  let q (i : Fin 2) : pullback ((U i).ι ≫ g) c ⟶ pullback g c :=
    (pullbackRightPullbackFstIso g c (U i).ι).inv ≫
      pullback.snd (U i).ι (pullback.fst g c)
  have hq (i : Fin 2) : IsOpenImmersion (q i) := by dsimp [q]; infer_instance
  have hqfac (i : Fin 2) : q i ≫ pullback.fst g c =
      pullback.fst ((U i).ι ≫ g) c ≫ (U i).ι := by
    dsimp [q]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      pullbackRightPullbackFstIso_inv_fst]
  have hmem (i : Fin 2) (z : ↥(pullback ((U i).ι ≫ g) c)) :
      pullback.fst g c (q i z) ∈ V i.val := by
    rw [← Scheme.Hom.comp_apply, hqfac, Scheme.Hom.comp_apply]
    exact (pullback.fst ((U i).ι ≫ g) c z).property
  refine ⟨U, hu, hproper, ?_, ?_⟩
  · intro i z
    let e := (asIso ((q i).stalkMap z)).commRingCatIsoToRingEquiv
    rw [← depth_eq_of_ringEquiv e, ← ringKrullDim_eq_of_ringEquiv e]
    exact hCM (q i z)
  · intro i
    let Z := pullback ((U i).ι ≫ g) c
    have : IsLocallyNoetherian Z := by
      have : LocallyOfFiniteType (pullback.snd ((U i).ι ≫ g) c) :=
        MorphismProperty.pullback_snd _ _ inferInstance
      infer_instance
    have hzdim (z : Z) : topologicalKrullDimAt z = (i.val : WithBot ℕ∞) := by
      rw [dimension_open_immersion (q i)]
      obtain ⟨e, he⟩ := special_fibre_point_iso g (q i z)
      rw [local_dimension_iso e, he]
      exact hdim i.val _ (hmem i z)
    intro C hC
    let E : Z ≃ₜ ↥(⊤ : Z.Opens) := (Homeomorph.Set.univ _).symm
    have himage : E '' C ∈ irreducibleComponents ↥(⊤ : Z.Opens) :=
      image_mem_irreducibleComponents_of_isPreirreducible_fiber E E.continuous
        E.isOpenMap (fun y ↦ (Set.subsingleton_singleton.preimage E.injective).isPreirreducible)
        E.surjective hC
    exact (IsHomeomorph.topologicalKrullDim_eq (E.image C)
      (E.image C).isHomeomorph).trans
        (topologicalKrullDim_component_eq_of_constant_local_dimension
          (⊤ : Z.Opens) i.val (fun z _ ↦ hzdim z) _ himage)


/-- Finite local Fitting bounds on a projective deformation yield the finite-jet
hypotheses on its two pure-dimensional open-and-closed pieces.

Source: Stacks Project, Tag 0E7Y, first paragraph and final paragraph, using
Algebra Tags 00OU, 00RT, 00RV, Divisors Tag 0C3K and More on Algebra Tag 07ZA.
(blueprint: lem-sfb-isolated-curve-local-fitting-criterion).

Proof: Lci stalks are Cohen--Macaulay. Transport their depth-dimension equalities
and the topological dimension bound through the given special-fibre isomorphism.
The fibre Cohen--Macaulay locus is open and contains the special fibre. Since g
is proper over the local base, its closed complement has empty image and is
empty. Apply the relative local-dimension open partition. Its pieces are clopen:
the complement of one is the union of the other pieces. Every special point has
local fibre dimension zero or one, so the union of these two pieces contains the
special fibre; properness again makes that union all of Y. A clopen inclusion is
a closed immersion, hence its composite with g is proper. Its special fibre maps
by an open immersion to the original special fibre, so its stalks retain the
depth-dimension equality. Local dimension is invariant under this open immersion
and under the special-fibre comparison with the point fibre. It equals the
piece index everywhere. The constant-local-dimension component theorem makes
these locally Noetherian special fibres pure of that dimension. Take the sum E
of the finitely many local exponents. Each exponent is at
most E, so multiplying its given ideal member by t^(E-ex_i) gives the uniform
bound t^E. Finally apply
isolated_curve_local_fitting_bounds to these already constructed proper pure
pieces and the given local presentations. This last theorem contains precisely
the remaining finite-jet Fitting calculation; no generic-smoothness theorem is
used to construct the partition. Empty schemes and pieces satisfy the assertions
vacuously. -/
theorem isolated_curve_local_fitting_criterion
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    (hlci : ∃ (I : Type u) (A : I → CommRingCat.{u})
      (aA : ∀ i, Algebra k (A i)) (ft : ∀ i, Algebra.FiniteType k (A i))
      (φ : ∀ i, Spec (A i) ⟶ X),
      (∀ i, IsOpenImmersion (φ i)) ∧
        (∀ i, φ i ≫ f =
          Spec.map (CommRingCat.ofHom (@algebraMap k (A i) _ _ (aA i)))) ∧
        (∀ x : X, ∃ i, ∃ y : Spec (A i), φ i y = x) ∧
        (∀ i, @Algebra.IsLocalCompleteIntersection k (A i) _ _ (aA i) (ft i)))
    (r : ℕ) (p : Fin r → X) (hp : Function.Injective p)
    (hclosed : ∀ i, IsClosed ({p i} : Set X))
    (hsmooth : ∀ x ∉ Set.range p, ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f))
    (B : Fin r → Type u) [∀ i, CommRing (B i)] [∀ i, IsLocalRing (B i)]
    [∀ i, Algebra (PowerSeries k) (B i)] [∀ i, Algebra k (B i)]
    [∀ i, IsScalarTower k (PowerSeries k) (B i)]
    [∀ i, Module.Flat (PowerSeries k) (B i)]
    [∀ i, Algebra.EssFiniteType (PowerSeries k) (B i)]
    (ex : Fin r → ℕ) (m : Fin r → ℕ)
    (π : ∀ i, (Fin (m i) → B i) →ₗ[B i] KaehlerDifferential (PowerSeries k) (B i))
    (hπ : ∀ i, Function.Surjective (π i))
    (hbound : ∀ i,
      let : Algebra k (X.presheaf.stalk (p i)) :=
        (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top ≫
          X.presheaf.germ ⊤ (p i) trivial).hom.toAlgebra)
      (algebraMap (PowerSeries k) (B i) PowerSeries.X) ^ ex i ∈
        (π i).presentationFittingIdeal
          ((WithBot.unbotD 0 (ringKrullDim (X.presheaf.stalk (p i)))).toNat +
            (Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk (p i)))).toNat))
    (Y : Scheme.{u}) (g : Y ⟶ Spec (.of (PowerSeries k)))
    [Flat g] [LocallyOfFinitePresentation g] [IsHProjective g]
    (e : pullback g (Spec.map (CommRingCat.ofHom
      (PowerSeries.constantCoeff (R := k)))) ≅ X)
    (he : e.hom ≫ f = pullback.snd g (Spec.map (CommRingCat.ofHom
      (PowerSeries.constantCoeff (R := k)))))
    (j : ∀ n, X ⟶ pullback g (formalCurveBaseι k n))
    (hj : ∀ n, j n ≫ pullback.fst g (formalCurveBaseι k n) =
      e.inv ≫ pullback.fst g (Spec.map (CommRingCat.ofHom
        (PowerSeries.constantCoeff (R := k)))))
    (h : ∀ i n,
      (pullback g (formalCurveBaseι k n)).presheaf.stalk (j n (p i))
        ≃+* (B i ⧸ Ideal.span
          {(algebraMap (PowerSeries k) (B i) PowerSeries.X) ^ (n + 1)}))
    (hscalar : ∀ i n a, h i n (isolatedCurveScalarToStalk
      (pullback.snd g (formalCurveBaseι k n)) (j n (p i))
      (Ideal.Quotient.mk _ a)) = Ideal.Quotient.mk _ (algebraMap _ _ a)) :
    ∃ U : Fin 2 → Y.Opens, (⨆ i, U i) = ⊤ ∧
      (∀ i, IsProper ((U i).ι ≫ g)) ∧
      (∀ i, ∀ x : ↥(pullback ((U i).ι ≫ g) (Spec.map (CommRingCat.ofHom
          (PowerSeries.constantCoeff (R := k))))),
        (IsLocalRing.depth
          (R := (pullback ((U i).ι ≫ g) (Spec.map (CommRingCat.ofHom
            (PowerSeries.constantCoeff (R := k))))).presheaf.stalk x)
          ((pullback ((U i).ι ≫ g) (Spec.map (CommRingCat.ofHom
            (PowerSeries.constantCoeff (R := k))))).presheaf.stalk x) : WithBot ℕ∞) =
        ringKrullDim ((pullback ((U i).ι ≫ g) (Spec.map (CommRingCat.ofHom
          (PowerSeries.constantCoeff (R := k))))).presheaf.stalk x)) ∧
      (∀ i, (pullback ((U i).ι ≫ g) (Spec.map (CommRingCat.ofHom
        (PowerSeries.constantCoeff (R := k))))).IsPureDimension i.val) ∧
      (∀ i, ∃ n : ℕ, 1 ≤ n ∧
        (pullback.snd ((U i).ι ≫ g) (Scheme.powerSeriesJetBaseMap k n)).appTop
          ((Scheme.ΓSpecIso (.of ((PowerSeries k) ⧸
            Ideal.span {(PowerSeries.X : PowerSeries k) ^ n}))).inv
            (Ideal.Quotient.mk _ ((PowerSeries.X : PowerSeries k) ^ (n - 1)))) ∈
        (Scheme.Modules.fittingIdealSheaf
          (pullback.snd ((U i).ι ≫ g) (Scheme.powerSeriesJetBaseMap k n)).relativeDifferentials
            i.val).idealOfOpens ⊤) := by
  let c := Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))
  have hCM (x : ↥(pullback g c)) :
      (IsLocalRing.depth (R := (pullback g c).presheaf.stalk x)
        ((pullback g c).presheaf.stalk x) : WithBot ℕ∞) =
      ringKrullDim ((pullback g c).presheaf.stalk x) := by
    let r := (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv
    rw [← depth_eq_of_ringEquiv r, ← ringKrullDim_eq_of_ringEquiv r]
    exact (isNoetherianRing_stalk_and_depth_eq_ringKrullDim_of_lci k X f hlci _).2
  have hsmall : topologicalKrullDim ↥(pullback g c) ≤ (1 : WithBot ℕ∞) :=
    (IsHomeomorph.topologicalKrullDim_eq e.hom.homeomorph
      e.hom.homeomorph.isHomeomorph).le.trans hdim
  obtain ⟨U, hcover, hproper, hCMU, hpure⟩ := curve_dimension_partition k g hCM hsmall
  let E : ℕ := ∑ i, ex i
  have hE (i : Fin r) : ex i ≤ E :=
    Finset.single_le_sum (fun j _ ↦ Nat.zero_le (ex j)) (Finset.mem_univ i)
  have hboundE (i : Fin r) :
      let : Algebra k (X.presheaf.stalk (p i)) :=
        (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top ≫
          X.presheaf.germ ⊤ (p i) trivial).hom.toAlgebra)
      (algebraMap (PowerSeries k) (B i) PowerSeries.X) ^ E ∈
        (π i).presentationFittingIdeal
          ((WithBot.unbotD 0 (ringKrullDim (X.presheaf.stalk (p i)))).toNat +
            (Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk (p i)))).toNat) := by
    have hm := ((π i).presentationFittingIdeal _).mul_mem_left
      ((algebraMap (PowerSeries k) (B i) PowerSeries.X) ^ (E - ex i)) (hbound i)
    simpa only [← pow_add, Nat.sub_add_cancel (hE i)] using hm
  have hjet := isolated_curve_local_fitting_bounds k X f r p hp hclosed hsmooth B E m π
    hπ hboundE Y g e he j hj h hscalar U hproper hpure
  refine ⟨U, hcover, hproper, hCMU, hpure, fun i ↦ ⟨E + 1, Nat.succ_pos _, ?_⟩⟩
  simpa only [Nat.add_sub_cancel] using hjet i

end AlgebraicGeometry
