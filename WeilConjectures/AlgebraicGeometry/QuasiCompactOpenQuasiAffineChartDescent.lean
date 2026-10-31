/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.QuasiAffineTargetLocality

/-!
# Quasi-affineness of quasi-compact opens from affine target charts

Source: Stacks Project, More on Morphisms, Tags 0F1U and 0AP6,
lemma-ind-quasi-affine-alternative-definition, (3) implies (4), with the affine-chart
scheme formulation of (1) iff (2)
(blueprint: lem-a1-qc-open-quasi-affine-chart-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- Quasi-affineness of quasi-compact opens over affine target charts implies quasi-affineness
of a quasi-compact open over any quasi-compact, quasi-separated target open. Over an affine
open target the source is a quasi-affine scheme. No global compactness or separation is assumed.

Source: Stacks Project, More on Morphisms, Tags 0F1U and 0AP6,
lemma-ind-quasi-affine-alternative-definition, (3) implies (4), with (1) iff (2)
(blueprint: lem-a1-qc-open-quasi-affine-chart-descent).

The map in the conclusion is the open inclusion of K followed by the restriction of f to V.
The local hypothesis uses Mathlib's quasi-affine schemes, which include quasi-compactness
and are precisely the schemes isomorphic to quasi-compact opens of affine schemes.

Proof:
1. Write h : K → V for the induced map. Quasi-compactness of K and quasi-separatedness
   of V give quasi-compactness of h by lem-weil-pbc-qcqs-morphism-permanence(1).
2. At each point v of V choose a chart U i containing v. Apply
   lem-weil-pbc-affine-opens-basis to V ∩ U i to find an affine open W containing v
   inside this intersection. These W form an affine open cover of V; the intersections
   V ∩ U i themselves need not be affine or quasi-compact.
3. For each such W, the inverse image L = h⁻¹(W) is quasi-compact by step 1 and
   def-weil-finite-type-morphism. It is open in f⁻¹(U i), so the local hypothesis
   makes L a quasi-affine scheme.
4. Apply the reverse implication of lem-a1-quasi-affine-target-locality to h and
   this affine cover of V to conclude that h is quasi-affine.
5. If V is affine, use its whole underlying open in def-nagata-quasi-affine-morphism.
   Its inverse image is all of K, so K is a quasi-affine scheme.
-/
theorem isQuasiAffineHom_quasiCompact_open_of_affine_charts
    {X Y : Scheme.{u}} (f : X ⟶ Y) {I : Type v} (U : I → Y.Opens)
    (hU : ∀ i : I, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
    (hlocal : ∀ (i : I) (L : (f ⁻¹ᵁ U i).toScheme.Opens),
      IsCompact (L : Set (f ⁻¹ᵁ U i).toScheme) → L.toScheme.IsQuasiAffine)
    (V : Y.Opens) (hV : IsCompact (V : Set Y)) [QuasiSeparatedSpace V.toScheme]
    (K : (f ⁻¹ᵁ V).toScheme.Opens)
    (hK : IsCompact (K : Set (f ⁻¹ᵁ V).toScheme)) :
    IsQuasiAffineHom (K.ι ≫ (f ∣_ V)) ∧
      (IsAffineOpen V → K.toScheme.IsQuasiAffine) := by
  sorry

end AlgebraicGeometry
