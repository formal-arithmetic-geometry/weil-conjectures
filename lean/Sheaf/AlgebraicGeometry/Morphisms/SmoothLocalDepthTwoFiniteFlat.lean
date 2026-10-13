/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.RingTheory.Depth
import Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatTargetLocus
import Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat

/-!
# Flatness of a finite depth-two extension on a smooth local scheme

Source: Stacks Project, Tag 0EYB, formal completion step; Tags 0EYA and 0EY6.
(blueprint: lem-sbc-smooth-local-depth-two-finite-flat)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Formal completion proves flatness of the supplied finite extension.

Source: Stacks Project, Tag 0EYB (pione-lemma-purity-smooth-over-depth2),
formal completion step, with Tags 0EYA and 0EY6(2),(a),(b).
(blueprint: lem-sbc-smooth-local-depth-two-finite-flat)

Proof: Smoothness over the Noetherian base makes L locally Noetherian.
At points outside U the flat local depth formula gives depth at least two on L.
By 0EY6(2), the boundary depth on E identifies p with the canonical extension
of its finite etale restriction; this identification commutes with flat base change.
Finiteness over L gives finite presentation, so the flat locus on E is open.
Finiteness makes the image of its closed complement closed; the complementary
target open where p is flat contains U. If its complement
is nonempty, choose a closed point in an affine closed-fibre chart. The residue
extension is finite. Realize it by a finite flat local base change (07NE), and
then obtain a section through that point by an etale slice (057G).
Complete a smooth affine chart in the section ideal. By 05D5 the result is
A'[[x_1,...,x_d]], and the completion map is flat (00MB). The new base has
depth at least two by the flat local depth formula. If d = 0, q is etale at
the section point, making that point generic in its closed fibre, contrary to fibre density and
its lying outside U. For d > 0
the prime m(A') times the power-series ring maps to a generic point of the
closed fibre, hence lies inside the inverse image of U. Apply 0EYA to extend
the finite etale cover on that open of the completion. Flat base change and uniqueness in 0EY6
identify this extension with the completed p. It is therefore flat.
The completion is faithfully flat after localizing at the section point;
descent gives flatness at all source points above the chosen target point.
Openness and finiteness then give a flat target neighbourhood, contradicting
the choice of point outside the flat target open. Thus p is flat globally.
The argument works affine locally, without quasi-compactness of L; empty E
and U = L have no bad points. This conclusion asserts only flatness. -/
theorem flat_of_smooth_local_depth_two_finite_extension
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {L : Scheme.{u}} (q : L ⟶ Spec (.of A)) [Smooth q]
    (U : L.Opens)
    (haway : ∀ y : L, q y ≠ IsLocalRing.closedPoint A → y ∈ U)
    (hclosed : Dense (↑((q.fiberι (IsLocalRing.closedPoint A)) ⁻¹ᵁ U) :
      Set (q.fiber (IsLocalRing.closedPoint A))))
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    {E : Scheme.{u}} (p : E ⟶ L) [IsFinite p] [Etale (p ∣_ U)]
    (hboundary : ∀ z : E, p z ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z)) :
    Flat p := by
  classical
  have : IsLocallyNoetherian L := LocallyOfFiniteType.isLocallyNoetherian q
  let F : Set L := {y | ∀ z : E, p z = y → (p.stalkMap z).hom.Flat}
  have hF : IsOpen F := isOpen_setOf_finite_flat_stalks p
  have hUF : (U : Set L) ⊆ F := by
    intro y hy z hz
    let zU : (p ⁻¹ᵁ U).toScheme := ⟨z, by change p z ∈ U; rwa [hz]⟩
    exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap p U zU)).mp (Flat.stalkMap (p ∣_ U) zU)
  let B : Set (q.fiber (IsLocalRing.closedPoint A)) :=
    (q.fiberι (IsLocalRing.closedPoint A)) ⁻¹' Fᶜ
  have hB : IsClosed B := hF.isClosed_compl.preimage (q.fiberι _).continuous
  have hBempty : B = ∅ := by
    by_contra hne
    obtain ⟨x, hxB, hxclosed⟩ := nonempty_inter_closedPoints
      (Set.nonempty_iff_ne_empty.mpr hne) hB.isLocallyClosed
    have hxU : q.fiberι (IsLocalRing.closedPoint A) x ∉ U := by
      intro hxU
      exact hxB (hUF hxU)
    apply hxB
    intro z hz
    exact flat_stalk_of_smooth_local_depth_two_closed_fiber A q U haway hclosed hdepth
      p hboundary x hxclosed hxU z hz
  apply Flat.of_stalkMap
  intro z
  have hpz : p z ∈ F := by
    by_cases hy : q (p z) = IsLocalRing.closedPoint A
    · let x := (q.fiberHomeo (IsLocalRing.closedPoint A)).symm ⟨p z, hy⟩
      have hx : q.fiberι (IsLocalRing.closedPoint A) x = p z :=
        q.fiberι_fiberHomeo_symm _ _
      by_contra hnot
      have hxB : x ∈ B := by
        change q.fiberι (IsLocalRing.closedPoint A) x ∉ F
        rwa [hx]
      rw [hBempty] at hxB
      exact hxB
    · exact hUF (haway (p z) hy)
  exact hpz z rfl


end AlgebraicGeometry.Scheme
