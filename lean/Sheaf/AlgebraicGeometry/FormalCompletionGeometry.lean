/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.AlgebraicGeometry.AdicFormalCompletion
public import Sheaf.AlgebraicGeometry.SmallSingularLocusPair

/-! # Geometry of adic formal completions

Source: Temkin, Non-embedded desingularization, §§2.4.1,2.4.3,2.4.9,2.4.11,3.1.1,3.1.4
(blueprint: def-per-formal-completion-geometry).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- The radical ideal of the absolute nonregular locus, as opposed to a relative
nonsmoothness ideal. Source: Temkin §2.4.9
(blueprint: def-per-formal-completion-geometry). -/
noncomputable def absoluteSingularIdeal (A : Type u) [CommRing A] : Ideal A :=
  PrimeSpectrum.vanishingIdeal
    {p : PrimeSpectrum A | ¬ IsRegularLocalRing (Localization.AtPrime p.asIdeal)}

/-- The reduced closed singular subscheme; closure has no effect when the regular locus
is open. Source: Temkin §2.1.10 (blueprint: def-per-formal-completion-geometry). -/
noncomputable def singularLocusIdeal (X : Scheme.{u}) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨closure {x : X | ¬ IsRegularLocalRing (X.presheaf.stalk x)}, isClosed_closure⟩

/-- The canonical completion associated with a small-singular-locus pair.
Source: Temkin Theorem 3.4.1 (blueprint: def-per-formal-completion-geometry). -/
def SmallSingularLocusPair.completion (P : SmallSingularLocusPair.{u}) :
    AdicFormalCompletion.{u} :=
  ⟨P.scheme, P.divisor⟩

namespace AdicFormalCompletion

/-- Reducedness and quasi-excellence on every Noetherian formal affine chart, including
charts not induced by the ambient scheme. Source: Temkin §§2.4.3,2.4.9
(blueprint: def-per-formal-completion-geometry). -/
def IsReducedQuasiExcellent (C : AdicFormalCompletion.{u}) : Prop :=
  ∀ (U : Opens C.space) (A : CommRingCat.{u}) (K : Ideal A),
    IsNoetherianRing A → K.FG → IsAdicComplete K A →
    Nonempty (C.space.restrict U.isOpenEmbedding ≅ formalSpectrum A K) →
    _root_.IsReduced A ∧ IsQuasiExcellent A

/-- The extended ideal is invertible and defines the adic topology. A finite affine
cover with regular-principal extended ideals expresses invertibility without requiring
a global generator. Source: Temkin §3.1.4
(blueprint: def-per-formal-completion-geometry). -/
def HasInvertibleIdealOfDefinition (C : AdicFormalCompletion.{u}) : Prop :=
  (∀ U : C.scheme.affineOpens,
    (C.chartIdeal U).FG ∧ IsAdicComplete (C.chartIdeal U) (C.chartRing U)) ∧
  ∃ (n : ℕ) (U : Fin n → C.scheme.affineOpens), (⨆ i, (U i).1) = ⊤ ∧
    ∀ i, (C.chartIdeal (U i)).IsRegularPrincipal

/-- A finite disjoint union of formal varieties in characteristic zero. Each open and
closed piece is itself a completion with reduced closed fibre of finite type over a
field of characteristic zero. The field can vary between pieces, and `n = 0` is allowed.
Source: Temkin §§2.4.1,3.1.1,3.1.5
(blueprint: def-per-formal-completion-geometry). -/
def IsFiniteDisjointUnionOfFormalVarieties (C : AdicFormalCompletion.{u}) : Prop :=
  ∃ (n : ℕ) (U : Fin n → Opens C.space) (F : Fin n → AdicFormalCompletion.{u})
    (k : Fin n → CommRingCat.{u}) (s : ∀ i, (F i).closedFibre ⟶ Spec (k i)),
    (⨆ i, U i) = ⊤ ∧ Pairwise (fun i j ↦ Disjoint (U i) (U j)) ∧
    ∀ i, IsClopen (U i : Set C.space) ∧ IsNoetherianFormalSpace (F i).space ∧
      Nonempty (C.space.restrict (U i).isOpenEmbedding ≅ (F i).space) ∧
      IsField (k i) ∧ CharZero (k i) ∧ LocallyOfFiniteType (s i) ∧ QuasiCompact (s i)

/-- The singular ideal is the extension of the reduced singular ideal of the original
scheme, on every completed affine chart. The corresponding closed subspace is therefore
`C.closedSubspace (singularLocusIdeal C.scheme)`, the completion of the original singular
subscheme, with thickenings `B/(J + I^n)`. This states equality of ideals, rather than just
of supports. Source: Temkin §§2.1.10,2.4.9
(blueprint: def-per-formal-completion-geometry). -/
def HasCompletedSingularLocus (C : AdicFormalCompletion.{u}) : Prop :=
  ∀ U : C.scheme.affineOpens,
    absoluteSingularIdeal (C.chartRing U) = C.extendedIdeal (singularLocusIdeal C.scheme) U

/-- Rig-regularity means that the singular ideal is open in the adic topology.
Source: Temkin §2.4.11 (blueprint: def-per-formal-completion-geometry). -/
def IsRigRegular (C : AdicFormalCompletion.{u}) : Prop :=
  ∀ U : C.scheme.affineOpens,
    ∃ N : ℕ, 0 < N ∧ C.chartIdeal U ^ N ≤ absoluteSingularIdeal (C.chartRing U)

end AdicFormalCompletion
end AlgebraicGeometry
