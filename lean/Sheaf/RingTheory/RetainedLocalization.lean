/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.RingTheory.PrincipalWLocalization

/-! # Retaining a closed subset in the principal w-localization

Source: blueprint, proper base change, Retaining a closed subset, order 1224
(blueprint: def-weil-pbc-retained-localization).

Selectors are constructed at the two-part partition into a constructible set and its
complement, omitting empty parts. Their localizations form a reverse-inclusion diagram.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace PrincipalWLocalization.Retained

variable {R : Type u} [CommRing R]

open Classical in
/-- The nonempty parts of the partition into `E` and its complement.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
noncomputable def parts (E : Set (PrimeSpectrum R)) : Finset (Set (PrimeSpectrum R)) :=
  Finset.filter Set.Nonempty ({E, Eᶜ} : Finset (Set (PrimeSpectrum R)))

/-- The two-part partition satisfies the index conditions with denominator one.
Proof: filter out the empty sets; constructibility is closed under complement; each point
lies in exactly one of `E` and its complement; `D(1)` is the whole spectrum.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
theorem parts_valid (E : Set (PrimeSpectrum R)) (hE : Topology.IsConstructible E) :
    (∀ F ∈ parts E, Set.Nonempty F) ∧
    (∀ F ∈ parts E, Topology.IsConstructible F) ∧
    (∀ p : PrimeSpectrum R, ∃! F : parts E, p ∈ F.val) ∧
    (∀ F : parts E, F.val ⊆ PrimeSpectrum.basicOpen (1 : R)) := by
  sorry

/-- The partition index used to construct the selector, with constant denominator one.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
noncomputable def selectorIndex (E : Set (PrimeSpectrum R)) (hE : Topology.IsConstructible E) :
    Index R where
  parts := parts E
  nonempty := (parts_valid E hE).1
  constructible := (parts_valid E hE).2.1
  partition := (parts_valid E hE).2.2.1
  denominator := fun _ ↦ 1
  nonvanishing := (parts_valid E hE).2.2.2

open Classical in
/-- The image in `R^w` of the stage element which is one on `E` and zero on its complement.
This specifies the selector by actual data, including when `E` or the spectrum is empty.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
noncomputable def selector (E : Set (PrimeSpectrum R)) (hE : Topology.IsConstructible E) :
    algebra R :=
  (colimit.ι (diagram (A := R)) (selectorIndex E hE)).hom
    (fun F ↦ if F.val ⊆ E then 1 else 0)

/-- The selector is idempotent. Proof: each stage coordinate is zero or one, so its square
is itself; the colimit inclusion preserves multiplication.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
theorem selector_idempotent (E : Set (PrimeSpectrum R)) (hE : Topology.IsConstructible E) :
    IsIdempotentElem (selector E hE) := by
  sorry

/-- Constructible neighbourhoods of `T`, ordered by reverse inclusion.
Here neighbourhood means a constructible superset, exactly as in the source.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
abbrev Neighborhood (T : Set (PrimeSpectrum R)) :=
  OrderDual {E : Set (PrimeSpectrum R) // Topology.IsConstructible E ∧ T ⊆ E}

/-- The neighbourhood index is filtered. Proof: the whole spectrum is a neighbourhood;
the intersection of two neighbourhoods contains `T`, is constructible, and is an upper
bound for reverse inclusion. The preorder has at most one arrow between any two objects.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
theorem neighborhood_isFiltered (T : Set (PrimeSpectrum R)) : IsFiltered (Neighborhood T) := by
  sorry

attribute [instance] neighborhood_isFiltered

/-- For `F ⊆ E`, the selector of `E` is a unit after localizing at the selector of `F`.
Proof: refine both two-part partitions by their nonempty intersections with denominator one.
The coordinate selectors satisfy `e_E * e_F = e_F`, hence so do their colimit images.
After inverting `e_F`, the image of `e_E` is one and thus a unit.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
theorem selector_isUnit {E F : Set (PrimeSpectrum R)}
    (hE : Topology.IsConstructible E) (hF : Topology.IsConstructible F) (hFE : F ⊆ E) :
    IsUnit (algebraMap (algebra R) (Localization.Away (selector F hF)) (selector E hE)) := by
  sorry

/-- The transition is the unique `R^w`-algebra map between the selector localizations.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
noncomputable def transition {T : Set (PrimeSpectrum R)} {E F : Neighborhood T} (h : E ≤ F) :
    Localization.Away (selector E.val E.property.1) →ₐ[algebra R]
      Localization.Away (selector F.val F.property.1) :=
  IsLocalization.Away.liftAlgHom (selector E.val E.property.1)
    (f := Algebra.ofId (algebra R) (Localization.Away (selector F.val F.property.1)))
    (selector_isUnit E.property.1 F.property.1 h)

/-- Identity transitions are identities by uniqueness of maps out of localization.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
theorem transition_id {T : Set (PrimeSpectrum R)} (E : Neighborhood T) :
    transition (le_refl E) = AlgHom.id (algebra R)
      (Localization.Away (selector E.val E.property.1)) := by
  sorry

/-- Transitions compose: both maps agree on `R^w`, so localization uniqueness identifies them.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
theorem transition_comp {T : Set (PrimeSpectrum R)} {E F G : Neighborhood T}
    (hEF : E ≤ F) (hFG : F ≤ G) :
    transition (le_trans hEF hFG) = (transition hFG).comp (transition hEF) := by
  sorry

/-- The reverse-inclusion diagram of localizations at the constructible selectors.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
noncomputable def localizationDiagram (T : Set (PrimeSpectrum R)) :
    Neighborhood T ⥤ CommAlgCat.{u} (algebra R) where
  obj E := CommAlgCat.of (algebra R) (Localization.Away (selector E.val E.property.1))
  map h := CommAlgCat.ofHom (transition h.le)
  map_id E := congrArg CommAlgCat.ofHom (transition_id E)
  map_comp h g := congrArg CommAlgCat.ofHom (transition_comp h.le g.le)

/-- The retained localization `R_[T]` is the colimit of `(R^w)[1/e_E]` over all constructible
supersets `E` of the closed set `T`, with reverse-inclusion transition maps.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
noncomputable def algebra (T : Set (PrimeSpectrum R)) (_hT : IsClosed T) :
    CommAlgCat.{u} (PrincipalWLocalization.algebra R) :=
  colimit (localizationDiagram T)

end PrincipalWLocalization.Retained
