/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q91
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.DescendAffine
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition

/-!
# Affine span models with fixed target families

Source: Stacks Project, Limits, Tags 01ZM (parts 1 and 2) and 01ZN; More on Morphisms,
Tag 0GDX, finite-stage span paragraph (blueprint: lem-trf-fixed-family-affine-span-model).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- An affine finitely presented span descends with its two target models fixed.
Finite presentation is expressed by local finite presentation: all sources and bases
are affine (including the limit), so quasi-compactness and quasi-separatedness follow.
The last two equations compare the arrows after projection to the fixed models P₀, Q₀.
Together with the equation over the limit base, these are precisely the equations for
the actual base changes under the unique projection-preserving pullback comparisons.

Source: Stacks Project, Limits, Tags 01ZM (parts 1 and 2) and 01ZN; More on Morphisms,
Tag 0GDX, finite-stage span paragraph (blueprint: lem-trf-fixed-family-affine-span-model).

Proof:
1. Affine stages and U are qcqs (lem-weil-pbc-affine-scheme-qcqs), and all transition
   maps are affine (lem-weil-pbc-morphism-affine-schemes-affine). Restrict to the upper
   tail of i₀: any cone extends uniquely to the original system by taking common
   upper bounds, so this restriction preserves the given limit and every later tail.
2. Apply thm-pd-spreading-out (1) to descend U to a finitely presented W_j at j ≥ i₀.
   Its source is qcqs by lem-weil-pbc-qcqs-morphism-permanence (2). Part (3) preserves
   finite presentation under subsequent base change, also for the fixed P₀ and Q₀.
3. The limit B is affine by lem-weil-pbc-limit-affine-transition. The isomorphism to U
   makes (W_j)_B affine, so its map to B is affine by
   lem-weil-pbc-morphism-affine-schemes-affine. Apply lem-weil-pbc-descend-affine to
   W_j → S_j. At some k ≥ j this map is affine; its source V_k is affine by
   lem-weil-pbc-affine-morphism-permanence (2). Finite presentation persists by
   lem-weil-pbc-qcqs-morphism-permanence (3). Iterated pullback uniqueness
   (def-pc-fibre-product) gives an isomorphism e_k : (V_k)_B ≅ U over B.
4. Apply thm-pd-spreading-out (2) to a composed with e_k and the fixed models V_k,P_k.
   At some l ≥ k this gives α_l : V_l → P_l. Identify the iterated target pullback
   with the prescribed P_l using def-pc-fibre-product. Apply part (2) again to
   c composed with e_l and the fixed models V_l,Q_l, obtaining β_r at r ≥ l.
   Define α_r by base change of α_l and the projection-preserving comparison to P_r.
5. Affineness of V_r follows from lem-weil-pbc-affine-morphism-permanence (1),(2)
   over the affine stages. Finite presentation follows from
   lem-weil-pbc-qcqs-morphism-permanence (3).
6. Compose e_l with the iterated pullback comparison to obtain e_r. The two
   projections characterize the base-changed arrows (def-pc-fibre-product): after
   projection to P₀ or Q₀ both composites agree by construction, and after projection
   to B they agree because e_r is over B. Uniqueness proves both desired arrow
   equalities, with the actual target comparisons. Finally r ≥ l ≥ k ≥ j ≥ i₀. -/
theorem exists_fixedFamily_affine_span_model
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ i : Iᵒᵖ, IsAffine (D.obj i)]
    (L : Cone D) (hL : IsLimit L)
    (i₀ : I) (P₀ Q₀ : Scheme.{u}) [IsAffine P₀] [IsAffine Q₀]
    (fP : P₀ ⟶ D.obj (op i₀)) (fQ : Q₀ ⟶ D.obj (op i₀))
    [LocallyOfFinitePresentation fP] [LocallyOfFinitePresentation fQ]
    (U : Scheme.{u}) [IsAffine U] (fU : U ⟶ L.pt) [LocallyOfFinitePresentation fU]
    (a : U ⟶ pullback fP (L.π.app (op i₀)))
    (c : U ⟶ pullback fQ (L.π.app (op i₀)))
    (ha : a ≫ pullback.snd fP (L.π.app (op i₀)) = fU)
    (hc : c ≫ pullback.snd fQ (L.π.app (op i₀)) = fU) :
    ∃ (r : I) (hr : i₀ ≤ r) (V : Scheme.{u}) (fV : V ⟶ D.obj (op r)),
      IsAffine V ∧ LocallyOfFinitePresentation fV ∧
      ∃ (α : V ⟶ pullback fP (D.map (homOfLE hr).op))
        (β : V ⟶ pullback fQ (D.map (homOfLE hr).op)),
        α ≫ pullback.snd fP (D.map (homOfLE hr).op) = fV ∧
        β ≫ pullback.snd fQ (D.map (homOfLE hr).op) = fV ∧
        ∃ e : pullback fV (L.π.app (op r)) ≅ U,
          e.hom ≫ fU = pullback.snd fV (L.π.app (op r)) ∧
          e.hom ≫ a ≫ pullback.fst fP (L.π.app (op i₀)) =
            pullback.fst fV (L.π.app (op r)) ≫ α ≫
              pullback.fst fP (D.map (homOfLE hr).op) ∧
          e.hom ≫ c ≫ pullback.fst fQ (L.π.app (op i₀)) =
            pullback.fst fV (L.π.app (op r)) ≫ β ≫
              pullback.fst fQ (D.map (homOfLE hr).op) := by
  sorry

end AlgebraicGeometry
