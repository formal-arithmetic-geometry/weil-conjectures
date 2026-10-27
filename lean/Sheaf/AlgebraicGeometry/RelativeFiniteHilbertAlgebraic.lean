/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.RelativeFiniteHilbertGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.SpaceChangeBase
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus
import Sheaf.AlgebraicGeometry.RepresentableSourceAlgebraic

/-! # Algebraicity of a relative finite Hilbert stack

Source: Stacks Project, criteria.tex, Tag 06CI (lemma-hilbert-stack-relative-space);
examples-stacks.tex, Tag 05WC
(blueprint: lem-sfb-relative-finite-hilbert-algebraic).

The source stack is equivalent to an algebraic space. Each represented fibre projection
is flat and locally of finite presentation on étale charts, and is surjective on
field-valued point classes. No diagonal hypothesis on the target stack is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open CategoryTheory

namespace AlgebraicGeometry.RelativeFiniteHilbert

/-- The positive-degree relative finite Hilbert groupoid of an algebraic-space fppf
presentation is an algebraic stack.

Source: Stacks Project, criteria.tex, Tag 06CI; examples-stacks.tex, Tag 05WC
(blueprint: lem-sfb-relative-finite-hilbert-algebraic).

Proof:
1. Fix d ≥ 1 and write H = H_d(F), H_X = H_d(X → h_S). Both are fppf stacks by
   lem-sfb-finite-hilbert-stack-descent. The forgetful map q : H → H_X is faithful:
   equal cover maps and x-isomorphisms force the y-isomorphisms to agree on Z.
   Positive-degree finite locally free Z → T is an fppf cover, so the isomorphism
   sheaf condition in Y makes those y-isomorphisms equal.
2. Derive the algebraic-space diagonal of Y, rather than assuming it. For y₁,y₂
   over T form A_i = X ×_Y h_T and B = X ×_S h_T. Fibre products of spaces exist
   by lem-trf-space-fibre-products-etale-covers; use
   lem-sfb-space-change-base-to-integers to regard them as spaces over T.
   P = A₁ ×_B A₂ maps to Isom(y₁,y₂) by (α₁,α₂) ↦ α₂α₁⁻¹.
   Its pullback along any isomorphism over T' is A₁ ×_T T'. It is flat, locally
   finitely presented and surjective by lem-sfb-space-fppf-covering-calculus.
   The sheaf bootstrap lem-sfb-fppf-space-atlas-bootstrap makes Isom(y₁,y₂)
   an algebraic space, establishing the diagonal.
3. H_X → C_d is representable: its fibre over Z → T is the discrete functor of
   maps Z ×_T T' → X, represented by Res_{Z/T}(Z ×_S X) using
   lem-sfb-finite-locally-free-weil-restriction. Normalizing the cover along its
   specified comparison gives a natural equivalence of groupoids, with unique
   arrows. Since C_d is algebraic by lem-sfb-finite-cover-stack-algebraic,
   lem-sfb-stack-representable-source-algebraic makes H_X algebraic.
4. The map (q,p_d) : H → H_X ×_S Y is representable. Over a cover Z → T, a map
   x : Z → X and y ∈ Y(T), its fibre is Res_{Z/T}(Isom_Z(y|_Z,F(x))). The
   Isom space is algebraic by step 2 and its Weil restriction by the same lemma
   as in step 3. Transport along the specified cover, x and y comparisons leaves
   exactly α; normalization and its inverse commute with restriction and retain
   all arrows, proving the required equivalence of fibred groupoids.
5. For any scheme T → H_X, put W = H ×_{H_X} h_T. Descent holds componentwise
   by lem-sfb-finite-hilbert-stack-descent and the 2-fibre-product definition.
   Faithfulness of q makes all automorphisms trivial. Its isomorphism-class
   presheaf is an fppf sheaf: local comparisons are unique, hence satisfy the
   cocycle condition, and stack descent glues objects. Thus W is equivalent to
   that discrete sheaf, retaining the full fibred-groupoid information.
6. Put V = W ×_Y X. The explicit 2-fibre-product formula identifies V with
   H ×_{H_X ×_S Y} (h_T ×_S X), preserving objects and compatible arrows.
   By step 4, lem-trf-space-fibre-products-etale-covers and
   lem-sfb-representable-pullback-over-space, V is an algebraic space. Its
   scheme fibres over W are the given X_y → T', hence flat, locally finitely
   presented and surjective. Apply lem-sfb-fppf-space-atlas-bootstrap to V → W.
   Every W is an algebraic space, so q is representable. Step 3 and
   lem-sfb-stack-representable-source-algebraic now give algebraicity of H.
   The argument used no assumed diagonal representability for Y. -/
theorem isAlgebraicModuliStack_groupoid
    {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    (F : BasedFunctor X Y) (hX : IsFppfModuliStack X) (hY : IsFppfModuliStack Y)
    (hF : IsRepresentableByAlgebraicSpaces F)
    (R : ∀ (T : Over S) (y : Functor.Fiber Y.p T), Representative (F := F) T y)
    (hflat : FlatLfp R)
    (hspace : ∃ (A : AlgebraicSpace S) (e : BasedFunctor (discreteModuli A.obj.obj) X),
      e.toFunctor.IsEquivalence)
    (hsurj : ∀ (T : Over S) (y : Functor.Fiber Y.p T),
      AlgebraicSpace.IsJointlySurjective (fun _ : Unit ↦ (R T y).projection))
    (d : ℕ+) :
    IsAlgebraicModuliStack (groupoid F d hX hY) := by
  sorry

end AlgebraicGeometry.RelativeFiniteHilbert
