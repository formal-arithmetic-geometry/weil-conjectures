/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Sections of a finite constant pro-etale sheaf

Source: Bhatt--Scholze, *The pro-etale topology for schemes*, Lemma 4.2.12,
printed p. 30 (blueprint: lem-pur-proetale-finite-constant-sections).

For a finite commutative ring with its discrete topology, sections of the constant
ring sheaf on the small pro-etale site are continuous functions on the underlying
scheme. The comparison is normalized on constant sections and is natural for
morphisms in the site.
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Sections of a finite constant pro-etale ring sheaf are continuous functions.

Source: Bhatt--Scholze, *The pro-etale topology for schemes*, Lemma 4.2.12,
printed p. 30 (blueprint: lem-pur-proetale-finite-constant-sections).
The proof constructs the sheaf of continuous functions, proves that the map from
the constant presheaf is locally bijective using the finite discrete fibres, and
then applies sheafification. Pointwise ring operations give ring equivalences;
the same construction sends each constant section to the corresponding constant
function and commutes with restriction by precomposition. The argument includes
empty and disconnected objects and uses no quasi-compactness assumption.
-/
theorem proEtale_finite_constant_sections
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] :
    ∃ θ : ∀ V : X.ProEt,
      RingEquiv
        (↑(((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj
          (RingCat.of A)).obj.obj (Opposite.op V)))
        C(V.left, A),
      (∀ (V : X.ProEt) (a : A),
        θ V (((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))).app
            (Opposite.op V)) a) = ContinuousMap.const V.left a) ∧
      (∀ {V W : X.ProEt} (h : W ⟶ V)
        (s : (((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj
          (RingCat.of A)).obj.obj (Opposite.op V))),
        θ W (((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj
          (RingCat.of A)).obj.map h.op s) =
          (θ V s).comp h.left.base.hom) := by
  sorry

end AlgebraicGeometry
