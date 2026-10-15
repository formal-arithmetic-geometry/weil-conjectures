/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import WeilConjectures.RingTheory.ProEtale.WLocal
public import Sheaf.RingTheory.IndPrincipalZariski
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Algebra.Pi

/-! # The finite-partition principal w-localization

Source: blueprint, proper base change, definition of the affine w-localization, order 1222
(blueprint: def-weil-pbc-w-localization).

The indices remember both the finite constructible partition and its denominators.
Refinement requires divisibility of denominators, so the component localization maps exist.
This construction is distinct from the upstream `WLocalization`, whose stages use localizations
at larger submonoids. No geometric property or comparison with that construction is asserted.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace PrincipalWLocalization

variable (A : Type u) [CommRing A]

/-- A finite constructible partition of `Spec A` with one nonvanishing denominator per part.
The unique-membership condition allows the empty partition precisely for an empty spectrum.
Source: blueprint order 1222 (blueprint: def-weil-pbc-w-localization). -/
structure Index where
  parts : Finset (Set (PrimeSpectrum A))
  nonempty : ∀ E ∈ parts, Set.Nonempty E
  constructible : ∀ E ∈ parts, Topology.IsConstructible E
  partition : ∀ p : PrimeSpectrum A, ∃! E : parts, p ∈ E.val
  denominator : parts → A
  nonvanishing : ∀ E : parts, E.val ⊆ PrimeSpectrum.basicOpen (denominator E)

variable {A}

/-- Refinement together with divisibility from each parent denominator to the child denominator.
Source: blueprint order 1222 (blueprint: def-weil-pbc-w-localization). -/
def Refines (i j : Index A) : Prop :=
  ∀ F : j.parts, ∃ E : i.parts, F.val ⊆ E.val ∧ i.denominator E ∣ j.denominator F

/-- Refinement is reflexive: use each part itself and reflexivity of subset and divisibility.
Source: blueprint order 1222 (blueprint: def-weil-pbc-w-localization). -/
theorem refines_refl (i : Index A) : Refines i i := by
  sorry

/-- Refinement is transitive: choose the intermediate parent, then its parent, and compose
subset inclusions and divisibility relations. Source: blueprint order 1222
(blueprint: def-weil-pbc-w-localization). -/
theorem refines_trans (i j k : Index A) (hij : Refines i j) (hjk : Refines j k) :
    Refines i k := by
  sorry

/-- The index preorder, with exactly the refinement/divisibility relation as its order.
Source: blueprint order 1222 (blueprint: def-weil-pbc-w-localization). -/
instance indexPreorder : Preorder (Index A) where
  le := Refines
  le_refl := refines_refl
  le_trans := refines_trans

/-- The product of principal localizations at an index; the empty product is the zero ring.
Its ring operations and its diagonal algebra structure are the standard Pi structures.
Source: blueprint order 1222 (blueprint: def-weil-pbc-w-localization). -/
abbrev Stage (i : Index A) : Type u :=
  (E : i.parts) → Localization.Away (i.denominator E)

/-- Choose the parent supplied by refinement. It is unique because the child is nonempty
and different parts of a partition are disjoint. Source: blueprint order 1222
(blueprint: def-weil-pbc-w-localization). -/
noncomputable def parent {i j : Index A} (h : i ≤ j) (F : j.parts) : i.parts :=
  Classical.choose (h F)

/-- The chosen parent's denominator divides the child's denominator, by the refinement data.
Source: blueprint order 1222 (blueprint: def-weil-pbc-w-localization).
Proof: take the divisibility clause of the witness selected by `parent`. -/
theorem parent_dvd {i j : Index A} (h : i ≤ j) (F : j.parts) :
    i.denominator (parent h F) ∣ j.denominator F := by
  sorry

/-- The component map is projection to the parent followed by the unique localization map.
The parent's denominator is a unit in the child localization by divisibility. The lift sends
`a/f^n` to `(a/1)(f/1)^(-n)`. Source: blueprint order 1222
(blueprint: def-weil-pbc-w-localization). -/
noncomputable def transition {i j : Index A} (h : i ≤ j) : Stage i →ₐ[A] Stage j :=
  AlgHom.pi fun F ↦
    (IsLocalization.Away.liftAlgHom (i.denominator (parent h F))
      (f := Algebra.ofId A (Localization.Away (j.denominator F)))
      (IsLocalization.Away.isUnit_of_dvd (j.denominator F) (parent_dvd h F))).comp
        (Pi.evalAlgHom A (fun E : i.parts ↦ Localization.Away (i.denominator E)) (parent h F))

/-- Identity transitions are identities. A nonempty part has itself as its unique parent;
localization uniqueness identifies its component map with the identity.
Source: blueprint order 1222 (blueprint: def-weil-pbc-w-localization). -/
theorem transition_id (i : Index A) : transition (le_refl i) = AlgHom.id A (Stage i) := by
  sorry

/-- Transitions compose. For each final child the two successive parents equal its direct
parent by the partition property. The resulting localization maps agree on `A`, so
`IsLocalization.ringHom_ext` identifies them; product extensionality finishes.
Source: blueprint order 1222 (blueprint: def-weil-pbc-w-localization). -/
theorem transition_comp {i j k : Index A} (hij : i ≤ j) (hjk : j ≤ k) :
    transition (le_trans hij hjk) = (transition hjk).comp (transition hij) := by
  sorry

/-- The diagram of commutative `A`-algebras with the specified component localization maps.
Source: blueprint order 1222 (blueprint: def-weil-pbc-w-localization). -/
noncomputable def diagram : Index A ⥤ CommAlgCat.{u} A where
  obj i := CommAlgCat.of A (Stage i)
  map h := CommAlgCat.ofHom (transition h.le)
  map_id i := congrArg CommAlgCat.ofHom (transition_id i)
  map_comp h g := congrArg CommAlgCat.ofHom (transition_comp h.le g.le)

/-- The index category is filtered. It is inhabited by the one-part partition with denominator
one when the spectrum is nonempty, and by the empty partition otherwise. For two indices,
take all nonempty intersections, with denominator the product of the two denominators.
Constructibility is closed under intersections; primality gives nonvanishing of the product.
Each factor divides that product, giving both refinement arrows. Parallel arrows are equal
because the category is a preorder. Source: blueprint order 1222
(blueprint: def-weil-pbc-w-localization). -/
theorem index_isFiltered : IsFiltered (Index A) := by
  sorry

attribute [instance] index_isFiltered

/-- The affine principal w-localization is the colimit of the partition/denominator diagram
in commutative `A`-algebras. Its algebra structure is the structural map induced by the diagonal
maps into the stages. Source: blueprint order 1222 (blueprint: def-weil-pbc-w-localization). -/
noncomputable def algebra (A : Type u) [CommRing A] : CommAlgCat.{u} A :=
  colimit (diagram (A := A))

/-- This colimit is ind-Zariski in the principal-localization sense. Use the filtered diagram
above and its colimit cocone; enumerate each finite set of parts by `Fin n` and transport the
product along that enumeration. The empty set gives `n = 0`.
Source: blueprint order 1222 (blueprint: def-weil-pbc-w-localization). -/
theorem isIndPrincipalZariski : Algebra.IsIndPrincipalZariski A (algebra A) := by
  sorry

end PrincipalWLocalization
