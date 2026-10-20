/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data

import Sheaf.AlgebraicGeometry.ProjectiveLineGenusZero
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
import WeilConjectures.AlgebraicGeometry.Curve.RootsOfUnityTop
import WeilConjectures.AlgebraicGeometry.Curve.Estimate

/-!
# The two Kummer-normalized projective-line components

Source: blueprint thm-amb-p1-decomposition and its proof.
(blueprint: lem-asd-ordinary-finite-p1-kummer-maps).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

attribute [local irreducible] ordinaryFinitePullback ordinaryFinitePushforward
  ordinaryFiniteTensor Scheme.rootsOfUnitySheaf ProjectiveSpace.twist
  ordinaryFiniteP1ChernSpec ordinaryFiniteP1Exchange
  ordinaryFiniteP1DecompositionSourceMap ordinaryFiniteShiftedLinePullback
  ordinaryFiniteP1Unit ordinaryFiniteP1ChernPushforward


/-- Invertibility on the projective line is the image of invertibility on the base.
Source: functoriality of units under the projection's map on global sections.
(blueprint: lem-asd-ordinary-finite-p1-kummer-maps).
Proof: map the given unit along q.appTop and identify the image of the natural cast. -/
theorem ordinaryFiniteP1_isUnit (N : ℕ) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤))) : IsUnit (N : Γ(ProjectiveLine S, ⊤)) :=
  (map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
    hS.map (ProjectiveLine S ↘ S).appTop.hom

/-- A family of projective-line Chern arrows on Noetherian bases.
Source: blueprint thm-amb-p1-decomposition.
(blueprint: lem-asd-ordinary-finite-p1-kummer-maps). -/
abbrev OrdinaryFiniteP1ChernFamily (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) :=
  ∀ (S : Scheme.{u}) [IsNoetherian S], IsUnit (N : Γ(S, ⊤)) →
    (ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)

/-- The Chern family represents the actual scalar-extended Kummer boundary of O(1).
Source: blueprint thm-amb-p1-decomposition.
(blueprint: lem-asd-ordinary-finite-p1-kummer-maps). -/
def OrdinaryFiniteP1ChernFamilySpec (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (c : OrdinaryFiniteP1ChernFamily A N hA) : Prop :=
  ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
    ordinaryFiniteP1ChernSpec A N hA S
      (ordinaryFiniteP1_isUnit N S hS) (c S hS)

/-- The specified twisted-unit and Chern components, before proving invertibility.
Source: blueprint thm-amb-p1-decomposition.
(blueprint: lem-asd-ordinary-finite-p1-kummer-maps). -/
def ordinaryFiniteP1KummerMap (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (c : OrdinaryFiniteP1ChernFamily A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ⟶
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) :=
  biprod.desc (ordinaryFiniteP1Unit A N hA t S hS)
    (ordinaryFiniteP1ChernPushforward A N hA S (c S hS))

/-- The decomposition square uses the exact ordinary-etale exchange of the item.
Source: blueprint thm-amb-p1-decomposition, base-change assertion.
(blueprint: lem-asd-ordinary-finite-p1-kummer-maps). -/
def OrdinaryFiniteP1KummerMapBaseChange (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (c : OrdinaryFiniteP1ChernFamily A N hA) : Prop :=
  ∀ {S' S : Scheme.{u}} [IsNoetherian S'] [IsNoetherian S]
    (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤))),
    (ordinaryFinitePullback A f).map (ordinaryFiniteP1KummerMap A N hA t c S hS) ≫
        ordinaryFiniteP1Exchange A f
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteShiftedLinePullback A N hA t
            (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
            (ordinaryFiniteP1_isUnit N S hS)).hom =
      ordinaryFiniteP1DecompositionSourceMap A N hA t f hS ≫
        ordinaryFiniteP1KummerMap A N hA t c S' hS'

/-- Compute the divisor degree of O(1) from its two-chart cohomology. -/
private theorem p1_twist_degree_one (k : Type u) [Field k] :
    (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) 1).degree k = 1 := by
  have hchi (d : ℕ) :
      (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d).eulerChar k =
        (d + 1 : ℕ) := by
    obtain ⟨e⟩ := ProjectiveLine.nonempty_H_zero_twist_equiv k d
    let b := (ProjectiveSpace.homogeneousSubmoduleBasis (ULift.{u} (Fin 2)) k d).reindex
      (ProjectiveLine.degreeEqEquivFin d)
    have hzero : Scheme.Modules.finrankH k
        (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d) 0 = d + 1 := by
      rw [Scheme.Modules.finrankH, e.finrank_eq, Module.finrank_eq_card_basis b]
      simp
    have := ProjectiveLine.subsingleton_H_one_twist k d (by omega)
    have hone : Scheme.Modules.finrankH k
        (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d) 1 = 0 :=
      Module.finrank_zero_of_subsingleton
    rw [Scheme.Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one, hzero, hone]
    simp
  unfold Scheme.Modules.degree
  rw [Scheme.Modules.eulerChar_congr k
    (ProjectiveSpace.unitIsoTwistZero (ULift.{u} (Fin 2)) (Spec (.of k)))]
  have h1 := hchi 1
  have h0 := hchi 0
  simp only [Nat.cast_one] at h1
  simp only [Nat.cast_zero] at h0
  rw [h1, h0]
  norm_num

/-- The degree-normalized Kummer isomorphism sends the actual class of O(1) to one.
Source: Curve.RootsOfUnityTop.sheafHTwoTrace and the two-chart computation of O(d).
(blueprint: lem-asd-ordinary-finite-p1-kummer-maps).
Proof: the Kummer trace is bijective and takes a line bundle's boundary to its degree
modulo N. The two-chart cohomology of O(d) gives Euler characteristic d+1 for d>=0.
Since the unit is O(0), O(1) has degree 2-1=1. Substitute this in the trace equation. -/
theorem ordinaryFiniteP1_geometric_kummer_normalization
    (k : Type u) [Field k] [IsAlgClosed k] (N : ℕ) (hN : (N : k) ≠ 0)
    (hP : IsUnit (N : Γ(ProjectiveLine (Spec (.of k)), ⊤))) :
    ∃ e : Sheaf.H ((ProjectiveLine (Spec (.of k))).rootsOfUnitySheaf N) 2 ≃+ ZMod N,
      e ((ProjectiveLine (Spec (.of k))).kummerδ₁ N hP
        (Scheme.Pic.toCohomologicalPicardGroup (ProjectiveLine (Spec (.of k)))
          (Scheme.Pic.ofIsInvertible
            (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) 1)))) = 1 := by
  have : NeZero N := ⟨by intro h; simp [h] at hN⟩
  have hgeom := ProjectiveSpace.isConnectedCurve_smooth_proper_genus_zero k
  have := hgeom.1
  have := hgeom.2.1
  have : ConnectedSpace (ProjectiveLine (Spec (.of k))) :=
    IsConnectedCurve.connectedSpace
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  have : GeometricallyIntegral
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) :=
    GeometricallyIntegral.of_isSepClosed
  let e := AddEquiv.ofBijective
    (Scheme.sheafHTwoTrace (k := k) (X := ProjectiveLine (Spec (.of k))) N hN)
    (Scheme.bijective_sheafHTwoTrace N hN)
  refine ⟨e, ?_⟩
  change Scheme.sheafHTwoTrace (k := k) (X := ProjectiveLine (Spec (.of k))) N hN
    (Scheme.picToSheafHTwo N hN (Additive.ofMul (Scheme.Pic.ofIsInvertible
      (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) 1)))) = 1
  rw [Scheme.sheafHTwoTrace_picToSheafHTwo]
  change (((Scheme.picDegreeHom k _ (Scheme.Pic.ofIsInvertible
    (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) 1))).toAdd : ℤ) : ZMod N) = 1
  rw [Scheme.picDegreeHom_ofIsInvertible, p1_twist_degree_one]
  simp

/-- On an algebraically closed geometric fibre the root sheaf has cohomology only
in degrees zero and two, both cyclic of order N. The isomorphisms here do not yet
normalize the actual Chern arrow.
Source: ProjectiveLineGenusZero and Curve.Estimate, the geometric-fibre part of
blueprint thm-amb-p1-decomposition.
(blueprint: lem-asd-ordinary-finite-p1-kummer-maps).
Proof: apply the proper-curve calculation to the genus-zero projective line. Its
first cohomology is a function group on Fin 0, hence zero. A primitive root
identifies the constant Z/N sheaf with the root sheaf in every degree; transport
these computations along the induced cohomology isomorphisms. -/
theorem ordinaryFiniteP1_geometric_cohomology (k : Type u) [Field k] [IsAlgClosed k]
    (N : ℕ) (hN : (N : k) ≠ 0) :
    Nonempty (Sheaf.H ((ProjectiveLine (Spec (.of k))).rootsOfUnitySheaf N) 0 ≃+
      ZMod N) ∧
    Subsingleton (Sheaf.H ((ProjectiveLine (Spec (.of k))).rootsOfUnitySheaf N) 1) ∧
    Nonempty (Sheaf.H ((ProjectiveLine (Spec (.of k))).rootsOfUnitySheaf N) 2 ≃+
      ZMod N) ∧
    ∀ q : ℕ, 2 < q →
      Subsingleton (Sheaf.H ((ProjectiveLine (Spec (.of k))).rootsOfUnitySheaf N) q) := by
  obtain ⟨hcurve, hsmooth, hproper, hgenus, _⟩ :=
    ProjectiveSpace.isConnectedCurve_smooth_proper_genus_zero k
  have := hcurve
  have := hsmooth
  have := hproper
  obtain ⟨hzero, hone, htwo, hhigher⟩ :=
    IsConnectedCurve.sheafH_constantZMod_of_isProper
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) N hN
  have transport (q : ℕ) :=
    Scheme.nonempty_addEquiv_sheafH_constantZMod_rootsOfUnitySheaf
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) N hN q
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨e⟩ := transport 0
    obtain ⟨e0⟩ := hzero
    exact ⟨e.symm.trans e0⟩
  · obtain ⟨e⟩ := transport 1
    obtain ⟨e1⟩ := hone
    have htriv : Subsingleton
        (Sheaf.H ((ProjectiveLine (Spec (.of k))).constantZMod N) 1) := by
      rw [hgenus, mul_zero] at e1
      exact e1.toEquiv.subsingleton
    exact e.symm.toEquiv.subsingleton
  · obtain ⟨e⟩ := transport 2
    obtain ⟨e2⟩ := htwo
    exact ⟨e.symm.trans e2⟩
  · intro q hq
    obtain ⟨e⟩ := transport q
    have := hhigher q hq
    exact e.symm.toEquiv.subsingleton

/-- The Kummer-normalized two-component map is invertible and commutes with base change.
This concerns only cohomology and its two specified arrows; it asserts no duality adjunction.
Source: blueprint thm-amb-p1-decomposition.md and its proof, and the decomposition/trace
part of lem-asd-ordinary-finite-p1-adjunction, steps 2--4.
(blueprint: lem-asd-ordinary-finite-p1-kummer-maps).

Proof: First use Z/N coefficients. At an algebraically closed geometric fibre the projective
line is a smooth proper connected genus-zero curve. Proper-curve cohomology gives Z/N in
degrees zero and two and zero otherwise. A primitive root identifies the root sheaf with
Z/N. The actual second Kummer boundary identifies H²(mu_N) with Pic/N. The split degree
sequence and divisibility of Pic⁰ identify Pic/N with Z/N, and O(1), the dual of the ideal
of one rational point, has degree one. Hence the Chern component is an isomorphism in
degree two, and the twisted unit is an isomorphism in degree zero. Proper exchange,
exact conservative geometric stalks and the unbounded cohomology criterion prove that
the two-component map is invertible over Z/N. Apply derived coefficient extension to A.
The proper finite-coefficient extension comparison is an isomorphism; flatness of mu_N
identifies the extended twist even when A is not flat over Z/N. Its mate normalization
identifies the unit component, and its scalar normalization identifies the Chern component.
This proves invertibility over A. For base change, pull back the infinity divisor. On its
chart its equation is a polynomial variable, hence remains a nonzerodivisor after arbitrary
base change, and its dual ideal is O(1). Naturality of the supported Kummer class gives
the pulled-back Chern arrow. The unit/exchange equation follows from the mate formula and
an adjunction triangle identity. Tensor/exchange coherence and the normalized line
comparison identify the two components. Additivity and the biproduct universal property
give exactly the displayed square. The zero ring (N=1) and empty base have zero objects
and satisfy the same assertions. -/
theorem ordinaryFiniteP1_kummer_maps (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (c : OrdinaryFiniteP1ChernFamily A N hA)
    (hc : OrdinaryFiniteP1ChernFamilySpec A N hA c) :
    (∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
      IsIso (ordinaryFiniteP1KummerMap A N hA t c S hS)) ∧
    OrdinaryFiniteP1KummerMapBaseChange A N hA t c := by
  sorry

end AlgebraicGeometry.Etale
