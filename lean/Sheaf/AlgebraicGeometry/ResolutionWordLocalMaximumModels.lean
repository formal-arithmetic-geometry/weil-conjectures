/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.NormalizedResolutionWordGluing
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-! # Local comparison of normalized-word maximum centers

Source: ILO VIII 2.3.11 and 2.3.13, pp. 93--94; Stacks Tags 034E and 01J3.
(blueprint: lem-trf-resolution-word-local-maximum-models).
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.EmbeddedResolutionHistory

/-- The local marked maximum is the scheme-theoretic inverse image of the given
positive global maximum stratum. This is only the local comparison assertion; it does
not assert existence of the global maximum, regularity descent, density or coherence.

Source: ILO VIII 2.3.11 and 2.3.13, pp. 93--94, and Stacks Tags 034E and 01J3.
(blueprint: lem-trf-resolution-word-local-maximum-models).

Proof: At a point of T choose a minimal Hilbert--Samuel envelope retaining the ordered
history. The finite upper semicontinuous modified head allows shrinking away all larger
heads. Its presentation cosupport is then the head equality locus. On this cosupport the
engine word has leading entry 1 and tail t, whereas the intrinsic word has head A and the
same tail t. The prescribed agreement on all representative charts and invariance under
common etale comparison identify their maximum sets with the inverse image of T.
Apply the numerical engine's maximum extension to this admissible presentation history.
It gives a smooth reduced maximum center adapted to the ordered boundary. Its map into
the envelope factors through the strict transform: the defining functions vanish at all
points of the center and its rings are reduced. The etale inverse image of the reduced
induced center is reduced by Tag 034E. These two reduced closed subschemes have equal
supports, so uniqueness in Tag 01J3 identifies their kernel ideals and gives the asserted
cartesian square. In the ambient envelope the same factorization retains the engine's
normal crossings condition and its original smooth structure map. No termination or
regularity descent is used here. -/
theorem resolution_word_local_maximum_models
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
    (hX : IsReduced H.X)
    (m : HilbertSamuel.ResolutionWord) (T : TopologicalSpace.Closeds H.X)
    (hm : IsGreatest (Set.range (ν H)) m) (hpos : ⊥ < m)
    (hT : (T : Set H.X) = {x | ν H x = m}) :
    ∀ x ∈ T, ∃ C : ResolutionWordChart R H x,
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
            i.ker = (Scheme.IdealSheafData.vanishingIdeal T).comap
              (C.intrinsic (Fin.last C.length) ≫
                eqToHom (congrArg (fun j ↦ H.intrinsic.obj (op j)) C.last)) ∧
            ∃ c : (K.step (Fin.last C.length)).step.center.subscheme ⟶
                (Scheme.IdealSheafData.vanishingIdeal T).subscheme,
              IsPullback i c (C.intrinsic (Fin.last C.length) ≫
                  eqToHom (congrArg (fun j ↦ H.intrinsic.obj (op j)) C.last))
                (Scheme.IdealSheafData.vanishingIdeal T).subschemeι := by
  sorry

end AlgebraicGeometry.EmbeddedResolutionHistory
