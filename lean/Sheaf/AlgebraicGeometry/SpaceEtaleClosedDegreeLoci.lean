/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q128
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.SetTheory.Cardinal.Finite
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.EtaleCohomology.SepClosedFieldVanishing

/-!
# Closed degree loci of a separated étale scheme chart

Source: Stacks Project, Decent Algebraic Spaces, Tag 07S8, étale specialization;
Tag 09YB, the strict degree-decrease paragraph
(blueprint: lem-sfb-space-etale-closed-degree-loci).

A geometric point is a field-valued representative whose field is algebraically closed.
Its fibre is the actual presheaf pullback along the corresponding Yoneda map. Point
classes and their atlas topology are the existing `Point` and `pointTopologicalSpace`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a quasi-compact separated étale scheme chart with uniformly bounded geometric
fibres, the locus of geometric degree at most `r` is closed. A bound on a dense open
subspace therefore holds everywhere. The characterization of `D` uses every geometric
representative, so it also asserts independence of that representative.
Source: Stacks Project, Decent Algebraic Spaces, Tags 07S8 and 09YB
(blueprint: lem-sfb-space-etale-closed-degree-loci).

Proof, following the five steps of the node:
1. For `m = r + 1`, form the successive products `P₁ = W` and `Pₖ₊₁ = Pₖ ×_X W`.
   They are schemes by lem-trf-space-fibre-products-etale-covers. Their maps to `X`
   are étale by base change and composition in lem-trf-space-chartwise-etale-permanence.
   Their field-valued sections are tuples of sections of `W` with the same image in `X`.
2. Pull back the diagonal along every pair of coordinate maps. Separatedness makes
   these equality loci closed immersions, by def-weil-closed-immersion. Remove their
   finite union to obtain an open subscheme `Cₘ` of `Pₘ`, using def-weil-open-immersion.
   A field-valued tuple belongs to `Cₘ` exactly when its coordinates are pairwise distinct.
   For `m = 1` there are no equality loci and `C₁ = W`.
3. The open immersion `Cₘ → Pₘ` is étale by
   lem-weil-pbc-etale-composition-cancellation. Composition in
   lem-trf-space-chartwise-etale-permanence makes `Cₘ → X` étale. Its image `Iₘ` is
   open by lem-a1-space-etale-open-image, including that lemma's base-change formula.
4. Pull back to an algebraically closed field. By the decomposition clause of
   lem-kun-0ezp, an étale scheme over this field is a disjoint union of field spectra.
   The fibre of `Cₘ` thus has a point exactly when the fibre of `W` has `m` distinct
   points. The image-base-change formula identifies `Iₘ` with the degree-at-least-`m`
   locus, independently of the geometric representative. Thus `Dᵣ` is its complement.
5. The complement of `Iᵣ₊₁` is closed. If it contains a dense open point image, it
   contains its closure, which is all of `|X|`; the same bound then holds at every
   geometric point. This includes `r = 0`, the empty base, the empty chart, and `r ≥ N`.
-/
theorem etale_closed_degree_loci {S : Scheme.{u}} (W : Over S) (X : AlgebraicSpace S)
    (f : yoneda.obj W ⟶ X.obj.obj)
    (hqc : IsQuasiCompactPresheafMap f) (hsep : IsSeparatedPresheafMap f)
    (het : IsEtale f)
    (hbound : ∃ N : ℕ, ∀ (x : PointRepresentative X.obj.obj) [IsAlgClosed x.K],
      Cardinal.mk (Point (Limits.pullback f (yonedaEquiv.symm x.value))) ≤ (N : Cardinal)) :
    ∀ r : ℕ, ∃ D : Set (Point X.obj.obj),
      IsClosed D ∧
      (∀ (x : PointRepresentative X.obj.obj) [IsAlgClosed x.K],
        Quot.mk _ x ∈ D ↔
          Cardinal.mk (Point (Limits.pullback f (yonedaEquiv.symm x.value))) ≤ (r : Cardinal)) ∧
      (∀ O : OpenSubspace X, Dense (pointImage O.val.ι) →
        (∀ (x : PointRepresentative X.obj.obj) [IsAlgClosed x.K],
          Quot.mk _ x ∈ pointImage O.val.ι →
            Cardinal.mk (Point (Limits.pullback f (yonedaEquiv.symm x.value))) ≤ (r : Cardinal)) →
        ∀ (x : PointRepresentative X.obj.obj) [IsAlgClosed x.K],
          Cardinal.mk (Point (Limits.pullback f (yonedaEquiv.symm x.value))) ≤ (r : Cardinal)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
