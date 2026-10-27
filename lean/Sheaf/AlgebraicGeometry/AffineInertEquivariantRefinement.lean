/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Algebra.Group.Subgroup.Defs

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.UnramifiedMorphism

/-! # Affine inert refinements of equivariant pointed etale neighbourhoods

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, VI 4.1, printed p.76,
and VIII 5.3.6 and the initial localization in proof 5.3.7, printed p.124
(blueprint: lem-per-affine-inert-equivariant-refinement).

Actions are homomorphisms into the scheme automorphism group. All fixed-point
conditions are equalities of scheme morphisms from a field spectrum, so include
the residue-field embedding. The subgroup is specified by its exact membership
condition rather than by a separately chosen abstract group.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- An equivariant pointed etale neighbourhood admits an affine Noetherian inert
refinement inside any prescribed invariant open neighbourhood.

Source: ILO VI 4.1, printed p.76; VIII 5.3.6 and the initial localization in
proof 5.3.7, printed p.124
(blueprint: lem-per-affine-inert-equivariant-refinement).

Proof:
1. For each g in G form the closed fixed subscheme F_g in X, using separatedness
   and closed-immersion base change (def-weil-proper-morphism,
   lem-weil-pbc-closed-immersion-base-change). Remove the finitely many F_g for
   g outside H. The resulting H-invariant open X_0 contains x and all its geometric
   stabilizers lie in H. Conjugation carries F_g to F_(hgh^{-1}).
2. For h in H, pull F_h back to P_h in V. Equivariance defines the map
   (inclusion,h inclusion) to V times_X V. Pulling back the open diagonal of f
   gives E_h open in P_h (def-weil-etale-morphism, def-weil-unramified-morphism,
   lem-weil-pbc-open-immersion-base-change). Thus B_h = P_h minus E_h is closed
   in V. Membership of a geometric point in P_h means h fixes its image in X;
   membership in E_h means h also fixes the point in V. A field-valued point
   whose image lies in a closed subscheme factors through that subscheme.
3. Intersect O, the inverse image of X_0, and the complements of all B_h.
   This open T contains the fixed geometric point. Conjugation permutes the B_h,
   so T is H-invariant. Its geometric stabilizers in H equal those of their
   images in G: fixing the image first forces membership in H and then excludes
   B_h; the converse follows from equivariance.
4. Choose an affine open A in T containing the image of the marked point
   (lem-weil-pbc-affine-opens-basis). The finite intersection of its H-translates
   is invariant and contained in A, hence separated as an open of the affine A
   (lem-weil-pbc-affine-source-morphism-separated,
   lem-weil-pbc-closed-immersion-base-change). Affineness is not asserted yet.
5. Choose an affine open C inside this separated neighbourhood containing the
   point. The finite intersection W of its H-translates is affine by successive
   intersections of affine opens in a separated scheme
   (lem-weil-pbc-separated-affine-open-intersection). It is invariant, contains
   the point, and is contained in T and hence in O.
6. Restrict the action to W and lift the marked geometric point through the open
   immersion a. Monomorphy makes the lift H-fixed. The inclusion is etale
   (lem-weil-pbc-open-immersion-etale), factors through O, and monomorphy
   identifies the source stabilizers with those already calculated on T.
7. The etale map f is locally of finite type, so V is locally Noetherian
   (def-weil-unramified-morphism, pqf-lem-locnoeth-lft). Its affine open W
   has Noetherian coordinate ring (pqf-lem-affine-open-locnoeth), hence W
   is Noetherian.
-/
theorem exists_affine_inert_equivariant_refinement
    {G : Type v} [Group G] [Finite G]
    {X : Scheme.{u}} [X.IsSeparated] [IsLocallyNoetherian X]
    (ρX : G →* Aut X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (H : Subgroup G)
    (hH : ∀ g : G, g ∈ H ↔ x ≫ (ρX g).hom = x)
    {V : Scheme.{u}} (ρV : H →* Aut V) (f : V ⟶ X) [Etale f]
    (hf : ∀ h : H, (ρV h).hom ≫ f = f ≫ (ρX h.val).hom)
    (t : Spec (.of Ω) ⟶ V) (ht : t ≫ f = x)
    (ht_fixed : ∀ h : H, t ≫ (ρV h).hom = t)
    (O : V.Opens) (htO : t default ∈ O)
    (hO : ∀ (h : H) (p : V), (ρV h).hom p ∈ O ↔ p ∈ O) :
    ∃ (W : Scheme.{u}) (_ : IsAffine W) (_ : IsNoetherian W)
      (ρW : H →* Aut W) (w : Spec (.of Ω) ⟶ W) (a : W ⟶ V),
      Etale a ∧
      (∀ h : H, (ρW h).hom ≫ a = a ≫ (ρV h).hom) ∧
      (∃ b : W ⟶ O.toScheme, b ≫ O.ι = a) ∧
      w ≫ a = t ∧
      (∀ h : H, w ≫ (ρW h).hom = w) ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (z : Spec (.of K) ⟶ W) (g : G),
        z ≫ a ≫ f ≫ (ρX g).hom = z ≫ a ≫ f ↔
          ∃ h : H, h.val = g ∧ z ≫ (ρW h).hom = z := by
  sorry

end AlgebraicGeometry
