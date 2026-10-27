/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.AlgebraicGeometry.ResolutionInvariantCalculusData
import Sheaf.AlgebraicGeometry.ResolutionWordMaximumCenterDescent
import Sheaf.AlgebraicGeometry.ResolutionWordProgressTermination
import Sheaf.AlgebraicGeometry.ResolutionWordFiniteHistoryComparison
import WeilConjectures.AlgebraicGeometry.Modules.IdealSheafFiniteType
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.Order.BoundedOrder.Basic

/-!
# Local dimension-corrected embedded resolution invariant calculus

Source: ILO, Expose VIII, 2.3.11 and 2.3.13, pp. 93--94; Bierstone--Milman--Temkin,
Q-universal desingularization, Theorem 6.1 and Addendum, sections 6.1--6.3
(blueprint: lem-trf-hilbert-samuel-resolution-invariant-calculus).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite EmbeddedResolutionHistory

private theorem reduced_ideal_eq_vanishing {X : Scheme.{u}} (J : X.IdealSheafData)
    (hJ : IsReduced J.subscheme) : J = Scheme.IdealSheafData.vanishingIdeal J.support := by
  let _ := hJ
  rw [← Scheme.IdealSheafData.ker_subschemeι J, J.subschemeι.ker_eq_vanishingIdeal]
  congr 1

private theorem ideal_coherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    (J : X.IdealSheafData) : J.toModules.IsFiniteTypeWithFiniteTypeKernels := by
  apply (Scheme.Modules.isFiniteTypeWithFiniteTypeKernels_iff _).2
  have := SheafOfModules.isQuasicoherent_unit (R := J.subscheme.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : ((SheafOfModules.pushforward J.subschemeι.toRingCatSheafHom).obj
      (SheafOfModules.unit J.subscheme.ringCatSheaf)).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pushforward_of_isClosedImmersion J.subschemeι
      (SheafOfModules.unit J.subscheme.ringCatSheaf)
  exact ⟨Scheme.Modules.isQuasicoherent_kernel J.toPushforwardSubscheme,
    J.isFiniteType_toModules J.ofFiniteType_of_isLocallyNoetherian⟩

private theorem final_values (ν : ValueFamily.{u} HilbertSamuel.ResolutionWord)
    {A B : EmbeddedResolutionPair.{u}} {m n : ℕ}
    (H : EmbeddedResolutionHistory A m) (K : EmbeddedResolutionHistory B n)
    {j : Fin (m + 1)} (hj : j = Fin.last m)
    (g : H.intrinsic.obj (op j) ⟶ K.X)
    (hg : ∀ y, wordAtStage ν H j y = ν K (g y)) :
    ∀ x : H.X, ν H x = ν K
      ((eqToHom (congrArg (fun i ↦ H.intrinsic.obj (op i)) hj.symm) ≫ g) x) := by
  subst j
  exact hg

private theorem final_reduced {A B : EmbeddedResolutionPair.{u}} {m n : ℕ}
    (H : EmbeddedResolutionHistory A m) (K : EmbeddedResolutionHistory B n)
    {j : Fin (m + 1)} (hj : j = Fin.last m)
    (g : H.intrinsic.obj (op j) ⟶ K.X) (J : K.X.IdealSheafData)
    (hg : IsReduced (J.comap g).subscheme) :
    IsReduced (J.comap
      (eqToHom (congrArg (fun i ↦ H.intrinsic.obj (op i)) hj.symm) ≫ g)).subscheme := by
  subst j
  exact hg

private theorem exists_word_calculus :
    Nonempty (ResolutionInvariantCalculus.{u, 0} HilbertSamuel.ResolutionWord) := by
  obtain ⟨R⟩ := MarkedIdeal.exists_numerical_resolution.{u}
  obtain ⟨ν, hν⟩ := normalized_resolution_word_gluing R
  obtain ⟨hgeometry, _, hpullback, hsmooth, hintrinsic, _, _⟩ :=
    resolution_word_finite_history_comparison R ν hν
  have hgeom {A : EmbeddedResolutionPair.{u}} {n : ℕ}
      (H : EmbeddedResolutionHistory A n) (hH : Admissible ν H) :
      HasResolutionGeometry H := hgeometry H hH (Fin.last n)
  have hsvalues {A B : EmbeddedResolutionPair.{u}} {m n : ℕ}
      {f : EmbeddedResolutionSmoothMap A B} {H : EmbeddedResolutionHistory A m}
      {K : EmbeddedResolutionHistory B n} (c : SmoothPullback f H K)
      (hK : Admissible ν K) : ∀ x : H.X, ν H x = ν K (c.finalMap x) := by
    exact final_values ν H K c.last (c.intrinsic (Fin.last n))
      (fun y ↦ ((hsmooth c hK (Fin.last n)).1 y).1)
  refine ⟨{
    value := ν
    finiteImage := fun H hH ↦ (hν H hH).2.2.1
    regularPoint := fun H hH ↦ (hν H hH).2.2.2.2.1
    maximumExists := fun H hH ↦ (resolution_word_progress R ν hν H hH (hgeom H hH)).1
    maximumGeometry := ?_
    nextGeometry := ?_
    strictProgress := ?_
    pullbackExists := hpullback
    smoothValues := hsvalues
    smoothIdeals := ?_
    intrinsicValues := ?_
    intrinsicIdeals := ?_
    termination := resolution_word_termination R ν hν }⟩
  · intro A n H K E hH hE
    obtain ⟨m, hm, hmpos, hred, hrange⟩ := hE
    have hNR : ¬ IsRegularScheme H.X := by
      intro hreg
      obtain ⟨x, hx⟩ := hm.1
      have hb := ((hν H hH).2.2.2.2.1 x).2 (hreg.2.isRegularLocalRing_stalk x)
      exact (ne_of_gt hmpos) (hx.symm.trans hb)
    have hg := hgeom H hH
    obtain ⟨a, T, ha, _, hT, hne, hreg, _, _, hnowhere, _⟩ :=
      resolution_word_maximum_center_descent R ν hν H hH
        ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1⟩ hg.2.2.2.2 hNR
    have ham : a = m := ha.unique hm
    have hr : Set.range E.centerMap = (T : Set H.X) := by
      rw [hrange, hT, ham]
    have : IsClosedImmersion E.centerMap := by
      have := K.centerClosed (Fin.last n)
      dsimp only [Extension.centerMap]
      infer_instance
    have := hred
    obtain ⟨_, e, he, _⟩ :=
      (Scheme.IdealSheafData.reduced_induced_closed_subscheme H.X T).2.2.2.2.2.2.2
        _ E.centerMap hr
    have : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal T).subscheme := hreg.1
    have : IsRegular (Scheme.IdealSheafData.vanishingIdeal T).subscheme := hreg.2
    have hcReg : IsRegularScheme (K.center (Fin.last n)).subscheme :=
      ⟨isLocallyNoetherian_of_isOpenImmersion e.hom,
        ⟨fun x ↦ isRegularLocalRing_stalk_of_etale e.hom
          (fun y ↦ inferInstance) x⟩⟩
    have hft : LocallyOfFiniteType H.base := hg.2.2.1
    have : IsLocallyNoetherian (H.ambient.obj (op (Fin.last n))) :=
      LocallyOfFiniteType.isLocallyNoetherian H.base
    have := H.closed (Fin.last n)
    have : IsLocallyNoetherian H.X :=
      LocallyOfFiniteType.isLocallyNoetherian (H.inclusion.app (op (Fin.last n)))
    have : IsLocallyNoetherian (K.ambient.obj (op (Fin.last n).castSucc)) :=
      isLocallyNoetherian_of_isOpenImmersion (E.ambient (Fin.last n)).inv
    refine ⟨?_, hcReg, ?_, ideal_coherent _, ideal_coherent _⟩
    · exact hne.map e.inv
    · rw [hr]
      exact hnowhere
  · intro A n H K E hH hE
    exact ((resolution_word_progress R ν hν H hH (hgeom H hH)).2 K E hE).1
  · intro A n H K E hH hE a b ha hb hbpos
    apply ((resolution_word_progress R ν hν H hH (hgeom H hH)).2 K E hE).2 a b ha hb
    intro hregular
    obtain ⟨x, hx⟩ := hb.1
    have hK := Admissible.step E hH hE
    have hbot := ((hν K hK).2.2.2.2.1 x).2
      (hregular.2.isRegularLocalRing_stalk x)
    exact (ne_of_gt hbpos) (hx.symm.trans hbot)
  · intro A B m n f H K c hK a J ha hJ
    have h := (hsmooth c hK (Fin.last n)).2.2 a J.support
    obtain ⟨hid, _, _⟩ := h ha (Set.ext hJ.2)
    have hr : IsReduced ((Scheme.IdealSheafData.vanishingIdeal J.support).comap
        (c.intrinsic (Fin.last n))).subscheme := by
      rw [hid]
      infer_instance
    have hred := final_reduced H K c.last (c.intrinsic (Fin.last n))
      (Scheme.IdealSheafData.vanishingIdeal J.support) hr
    rw [← reduced_ideal_eq_vanishing J hJ.1] at hred
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact hred
    · intro x
      rw [Scheme.IdealSheafData.support_comap]
      change c.finalMap x ∈ J.support ↔ ν H x = a
      constructor
      · intro hx
        exact (hsvalues c hK x).trans ((hJ.2 (c.finalMap x)).mp hx)
      · intro hx
        exact (hJ.2 (c.finalMap x)).mpr ((hsvalues c hK x).symm.trans hx)
    · intro hem
      apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
      apply TopologicalSpace.Closeds.ext
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      rw [Scheme.IdealSheafData.support_comap] at hx
      exact hem x ((hsvalues c hK x).trans ((hJ.2 (c.finalMap x)).mp hx))
  · intro A B n e H K c hH hK
    have h := (hintrinsic c hH hK (Fin.last n)).1
    exact h
  · intro A B n e H K c hH hK a I J ha hI hJ
    have h := hintrinsic c hH hK (Fin.last n)
    have hv := h.1
    have hmax : IsGreatest (Set.range (ν H)) a := by
      constructor
      · obtain ⟨y, hy⟩ := ha.1
        obtain ⟨x, hx⟩ := (c.iso.app (op (Fin.last n))).hom.homeomorph.surjective y
        change (c.iso.app (op (Fin.last n))).hom x = y at hx
        have hvx : ν H x = ν K ((c.iso.app (op (Fin.last n))).hom x) := hv x
        exact ⟨x, hvx.trans (by rw [hx]; exact hy)⟩
      · rintro b ⟨x, rfl⟩
        have hvx : ν H x = ν K ((c.iso.app (op (Fin.last n))).hom x) := hv x
        rw [hvx]
        exact ha.2 (Set.mem_range_self _)
    have hid := h.2 a I.support J.support hmax (Set.ext hI.2) (Set.ext hJ.2)
    simpa only [← reduced_ideal_eq_vanishing I hI.1,
      ← reduced_ideal_eq_vanishing J hJ.1] using hid

private theorem greatest_up {X : Type u} {V : Type v} [LinearOrder V]
    (f : X → V) (a : V) :
    IsGreatest (Set.range (fun x ↦ ULift.up.{w} (f x))) (ULift.up a) ↔
      IsGreatest (Set.range f) a := by
  constructor
  · rintro ⟨⟨x, hx⟩, h⟩
    refine ⟨⟨x, ULift.up_injective hx⟩, ?_⟩
    rintro b ⟨y, rfl⟩
    exact h (Set.mem_range_self y)
  · rintro ⟨⟨x, hx⟩, h⟩
    refine ⟨⟨x, congrArg ULift.up hx⟩, ?_⟩
    rintro b ⟨y, rfl⟩
    exact h (Set.mem_range_self y)

private theorem maximum_up {V : Type v} [LinearOrder V] [OrderBot V]
    (ν : ValueFamily.{u} V) {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    {H : EmbeddedResolutionHistory A n} {K : EmbeddedResolutionHistory A (n + 1)}
    (E : Extension H K) :
    IsMaximumStep (fun H x ↦ ULift.up.{w} (ν H x)) E ↔ IsMaximumStep ν E := by
  constructor
  · rintro ⟨⟨a⟩, ha, hpos, hred, hrange⟩
    exact ⟨a, (greatest_up _ _).mp ha, hpos, hred, by simpa only [ULift.up_inj] using hrange⟩
  · rintro ⟨a, ha, hpos, hred, hrange⟩
    exact ⟨ULift.up a, (greatest_up _ _).mpr ha, hpos, hred,
      by simpa only [ULift.up_inj] using hrange⟩

private theorem admissible_up {V : Type v} [LinearOrder V] [OrderBot V]
    (ν : ValueFamily.{u} V) {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    (H : EmbeddedResolutionHistory A n) :
    Admissible (fun H x ↦ ULift.up.{w} (ν H x)) H ↔ Admissible ν H := by
  constructor
  · intro h
    induction h with
    | empty H => exact .empty H
    | step E _ hE ih => exact .step E ih ((maximum_up _ _).mp hE)
    | pullback f c _ ih => exact .pullback f c ih
  · intro h
    induction h with
    | empty H => exact .empty H
    | step E _ hE ih => exact .step E ih ((maximum_up _ _).mpr hE)
    | pullback f c _ ih => exact .pullback f c ih

private theorem calculus_up {V : Type v} [LinearOrder V] [OrderBot V]
    (C : ResolutionInvariantCalculus.{u, v} V) :
    Nonempty (ResolutionInvariantCalculus.{u, max v w} (ULift.{w} V)) := by
  let ν : ValueFamily.{u} (ULift.{w} V) := fun H x ↦ ULift.up (C.value H x)
  have ha {A : EmbeddedResolutionPair.{u}} {n : ℕ} (H : EmbeddedResolutionHistory A n) :
      Admissible ν H ↔ Admissible C.value H := admissible_up C.value H
  have he {A : EmbeddedResolutionPair.{u}} {n : ℕ}
      {H : EmbeddedResolutionHistory A n} {K : EmbeddedResolutionHistory A (n + 1)}
      (E : Extension H K) : IsMaximumStep ν E ↔ IsMaximumStep C.value E :=
    maximum_up C.value E
  have hs {A : EmbeddedResolutionPair.{u}} {n : ℕ} (H : EmbeddedResolutionHistory A n)
      (a : V) (J : H.X.IdealSheafData) :
      IsResolutionStratumIdeal ν H (ULift.up a) J ↔
        IsResolutionStratumIdeal C.value H a J := by
    simp only [IsResolutionStratumIdeal, ν, ULift.up_inj]
  refine ⟨{
    value := ν
    finiteImage := ?_
    regularPoint := ?_
    maximumExists := ?_
    maximumGeometry := fun E hH hE ↦ C.maximumGeometry E ((ha _).mp hH) ((he E).mp hE)
    nextGeometry := fun E hH hE ↦ C.nextGeometry E ((ha _).mp hH) ((he E).mp hE)
    strictProgress := ?_
    pullbackExists := fun f K hK ↦ C.pullbackExists f K ((ha K).mp hK)
    smoothValues := ?_
    smoothIdeals := ?_
    intrinsicValues := ?_
    intrinsicIdeals := ?_
    termination := ?_ }⟩
  · intro A n H hH
    change (Set.range (ULift.up ∘ C.value H)).Finite
    rw [Set.range_comp]
    exact (C.finiteImage H ((ha H).mp hH)).image ULift.up
  · intro A n H hH x
    exact (ULift.up_inj (x := C.value H x) (y := ⊥)).trans
      (C.regularPoint H ((ha H).mp hH) x)
  · intro A n H hH hNR
    obtain ⟨K, E, hE⟩ := C.maximumExists H ((ha H).mp hH) hNR
    exact ⟨K, E, (he E).mpr hE⟩
  · intro A n H K E hH hE a b hab hbb hpos
    exact C.strictProgress E ((ha H).mp hH) ((he E).mp hE) a.down b.down
      ((greatest_up _ _).mp hab) ((greatest_up _ _).mp hbb) hpos
  · intro A B m n f H K c hK x
    exact congrArg ULift.up (C.smoothValues c ((ha K).mp hK) x)
  · intro A B m n f H K c hK a J hmax hJ
    obtain ⟨hstr, hempty⟩ := C.smoothIdeals c ((ha K).mp hK) a.down J
      ((greatest_up _ _).mp hmax) ((hs K a.down J).mp hJ)
    refine ⟨(hs H a.down _).mpr hstr, ?_⟩
    intro hem
    apply hempty
    intro x hx
    exact hem x (congrArg ULift.up hx)
  · intro A B n e H K c hH hK x
    exact congrArg ULift.up (C.intrinsicValues c ((ha H).mp hH) ((ha K).mp hK) x)
  · intro A B n e H K c hH hK a I J hmax hI hJ
    exact C.intrinsicIdeals c ((ha H).mp hH) ((ha K).mp hK) a.down I J
      ((greatest_up _ _).mp hmax) ((hs H a.down I).mp hI) ((hs K a.down J).mp hJ)
  · intro A h
    obtain ⟨H, E, hE⟩ := h
    exact C.termination A ⟨H, E, fun n ↦ (he (E n)).mp (hE n)⟩
/-- There is one ordered synchronization value set with a least regular value, and a
simultaneous normalized local invariant for all embedded pairs and their admissible
histories, with the maximum-stratum calculus and termination clauses.

Source: ILO VIII 2.3.11, 2.3.13; BMT Theorem 6.1 and Addendum, sections 6.1--6.3
(blueprint: lem-trf-hilbert-samuel-resolution-invariant-calculus).

Proof plan, following the seven DAG steps:

1. For a local ring at x form h_x, q_x and c_x as in
   [lem-trf-hilbert-samuel-smooth-dimension-profile], and use the normalized head
   A_x=(c_x,\Delta^{q_x}h_x). For a fixed input choose an integer D at least its dimension. The
   common shift \Lambda^D is strictly increasing in lexicographic order: if f and g first differ
   at n, their partial sums first differ there with the same sign. Its inverse \Delta has the same
   property. Thus comparing normalized heads is exactly comparing the modified heads with this
   common D. Changing the dimension of a different input never enters this comparison. The cited
   statement gives finite image, upper semicontinuity and detection of regularity. Keep the
   normalized head, not D, as part of the synchronization value.

2. At a singular point take a minimal-embedding, maximal-order, codimension-zero presentation from
   [lem-trf-hilbert-samuel-local-presentations]. Apply
   [lem-trf-marked-ideal-numerical-resolution-engine] to that marked ideal and delete its first
   entry 1. Prefix the remaining word by A_x. On points already regular set \nu=\bot, irrespective
   of exceptional-divisor cleanup. Use the same lexicographic word space for every input and
   append the one new least element \bot. Minimal-embedding equivalence makes this definition
   independent of the local presentation: equivalent presentations give the same tail word, and
   the head is intrinsic. The transformed presentations use controlled ideal transforms while the
   scheme uses strict transforms; equality of their test sequences is precisely what permits
   applying the marked-ideal construction at every admissible stage.

3. On a finite affine cover, the heads and their tail words have finite images, so their union is
   finite. At a maximum head, its presentation identifies its stratum with the relevant
   marked-ideal cosupport. Upper semicontinuity of the head makes the maximum head closed; upper
   semicontinuity of the tail on that closed stratum makes the full maximum T=\{\nu_H=m\} closed
   in X_H. Let M_H be its reduced induced closed subscheme
   [lem-weil-pbc-reduced-induced-closed-subscheme]. Each point of T lies under a point of an etale
   neighbourhood U\to X_H carrying a presentation; by Step 2, \nu_H on U is the word of that
   presentation, and the marked-ideal engine makes the preimage of T the underlying set of a
   smooth closed center C_U transverse to the exceptional divisors. The base change
   M_H\times_{X_H}U\to M_H is etale [lem-weil-pbc-etale-scheme-base-change], so M_H\times_{X_H}U
   is reduced [etale-proposition-etale-reduced] with the same underlying set as C_U, hence equals
   C_U by the uniqueness clause (3). Now C_U is smooth over \mathbf Q, so its local rings are
   regular [lem-trf-smooth-geometrically-normal]. Etale maps are flat [def-weil-etale-morphism],
   so each local ring of M_H maps flatly and locally to a regular local ring of C_U and is regular
   [lem-weil-pbc-flat-under-regular]. Thus M_H is a nonempty regular closed subscheme when X_H is
   singular. No maximum greater than \bot meets the regular locus. Every generic point of a
   reduced scheme has a field as its local ring: localization at a minimal prime is reduced with
   only its zero prime, so each nonzero element is invertible. Thus a closed subset of singular
   points contains no irreducible component and hence no nonempty open subset. This proves the
   claimed nowhere density.

4. Each affine coordinate ring of X_H and P_H is Noetherian by
   [lem-weil-pbc-finite-type-algebra-noetherian]. A closed subscheme ideal is quasi-coherent by
   [lem-weil-pbc-reduced-induced-closed-subscheme]. Every submodule of a finite module over such a
   ring is finitely generated and finitely presented by
   [lem-trf-noetherian-submodule-finitely-presented]; applying this also to kernels of maps from
   finite free modules proves coherence of the two ideals. The center is smooth over \mathbf Q by
   [lem-trf-regular-perfect-field-smooth]. The ambient blowup and reduced strict transform remain
   in the required class by [lem-trf-smooth-center-blowup-geometry]. At the selected maximum,
   either the head drops or it stays fixed and the tail maximum strictly drops by the marked-ideal
   engine. At other points the admissible-transform heads and tails cannot increase. The next
   positive global maximum is therefore strictly smaller.

5. For a smooth pullback and y\mapsto x, [lem-trf-hilbert-samuel-smooth-dimension-profile] gives
   h_y=\Lambda^s h_x and q_y=q_x+s, with c_y=c_x. Hence \Delta^{q_y}h_y=\Delta^{q_x}h_x. This uses
   the fibre-local dimension s at this point and requires no constant relative dimension. The
   local presentation theorem and the marked-ideal engine give equality of the tail words under
   this pullback, including the ordered exceptional data. Consequently \nu(y)=\nu(x) at each
   finite stage. The maximum center is smooth over \mathbf Q by Step 4. Its inverse image is
   smooth over it, as a base change of the smooth ambient map [lem-pc-proper-base-change], hence
   smooth over \mathbf Q [lem-trf-smooth-composition] and reduced
   [lem-trf-smooth-geometrically-normal]; it has the same underlying inverse-image stratum.
   Uniqueness in [lem-weil-pbc-reduced-induced-closed-subscheme] gives equality of its extended
   ideal and the reduced stratum ideal. If empty, its ideal is the unit ideal. Restriction is the
   same comparison on an open neighbourhood. Deleting an empty center adds no exceptional
   hypersurface and changes none of the local data.

6. Suppose two histories satisfy (3). Their local rings identify, so their heads agree. The local
   presentation theorem identifies the maximal-order presentation equivalence classes using
   exactly the strict-transform schemes and the ordered earlier center ideals. The numerical
   marked-ideal engine then gives equal tail words. The retained ideals matter even for an
   intrinsic identity blowup: they determine the same ordered exceptional information used by the
   presentations. Thus the functions agree. Their images, maxima and maximum subsets agree, and
   uniqueness of reduced induced structure identifies their center ideals. The comparison is
   independent of local choices, so computing it before or after the restriction or smooth
   pullback in the preceding step gives the same head, presentation class and word. This proves
   the stated compatibility for finite histories, without identifying distinct ambient schemes.

7. Assume an infinite maximum-center process from one initial pair. Its heads cannot increase. By
   [lem-trf-hilbert-samuel-smooth-dimension-profile] they can strictly drop only finitely many
   times, so there is an infinite tail with the same maximum head. On this tail use its finitely
   many local presentations. The marked-ideal process is exactly the engine process at that head,
   since Step 2 used its tail word and Step 3 its full maximum center. By
   [lem-trf-marked-ideal-numerical-resolution-engine] this process terminates with empty
   cosupport; by [lem-trf-hilbert-samuel-local-presentations] this removes that head, a
   contradiction. Equivalently the engine's coefficient-dimension induction and terminal monomial
   case exclude the putative infinite constant-head tail. For a finite disjoint union use its
   finite cover and the same global maximum rule, so the same argument applies. The empty scheme
   and every regular scheme have no positive maximum and yield zero steps. This proves (4) for the
   very functions constructed above; no well-foundedness of an arbitrary ordered set is asserted.
-/
theorem exists_resolution_invariant_calculus :
    ∃ (V : Type (u + 1)) (order : LinearOrder V) (bottom : OrderBot V),
      Nonempty (@ResolutionInvariantCalculus.{u, u + 1} V order bottom) := by
  -- Assemble the current four-node split, then lift its small word type.
  obtain ⟨C⟩ := exists_word_calculus.{u}
  exact ⟨ULift.{u + 1} HilbertSamuel.ResolutionWord, inferInstance, inferInstance,
    calculus_up.{u, 0, u + 1} C⟩

end AlgebraicGeometry
