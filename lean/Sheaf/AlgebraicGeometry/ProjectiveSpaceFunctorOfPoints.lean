/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# Projective space as a functor of points

Source: literature/stacks-project/constructions.tex, Lemma 27.13.1 (Tag 01NE)
(blueprint: lem-weil-pbc-projective-space-functor-of-points)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

set_option hygiene false in
local notation "P" n:max => ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of (ULift.{u} ℤ)))
set_option hygiene false in
local notation "O" n:max => ProjectiveSpace.twist
  (ULift.{u} (Fin (n + 1))) (Spec (CommRingCat.of (ULift.{u} ℤ))) 1
set_option hygiene false in
local notation "T" n:max i:max => ProjectiveSpace.twistOneSection
  (ULift.{u} (Fin (n + 1))) (Spec (CommRingCat.of (ULift.{u} ℤ))) (ULift.up i)
set_option hygiene false in
local notation "pb" f:max M:max s:max => (((Classical.choose
  (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app M).val.app (Opposite.op ⊤) s)

/-- The universal pair on integral projective space and its classification of all
invertible modules with fibrewise generating sections. The first clause says that
pulling back the universal pair always gives such a pair; the second classifies them
uniquely up to section-preserving isomorphism. The last clause asserts compatibility
with pullback. Equivalence invariance and injectivity on equivalence classes follow
from the same unique classification; surjectivity is the first clause with identity
isomorphism. Thus these clauses give the stated representing functor.

`P n` is `ℙ^n_ℤ = ℙ(Fin (n+1); Spec ℤ)` (def-nagata-projective-space-base-change over
`Spec ℤ`), `O n` its twisting sheaf `twist _ _ 1` (def-pc-projective-space-twist) and
`T n i` the coordinate section `twistOneSection _ _ i`; `pb f M s` is the pullback of a
global section along the unit of `exists_tensorPullbackAdjunction f`.

Source: Stacks Project, Constructions, Lemma 27.13.1 (Tag 01NE), via 01NA and 01N9
(blueprint: lem-weil-pbc-projective-space-functor-of-points).

Proof:
1. The standard charts cover projective space, and each coordinate trivializes O(1)
   there (prop-nagata-proj-standard-open and the twisting-sheaf-charts node).
2. Nonvanishing-section-trivializes gives the opens Y_s and the ratios s_l/s_j;
   invertible-generating-sections-fibre shows that these opens cover Y.
3. The ratios give ring maps from each affine chart and hence local morphisms by
   morphism-into-affine-scheme.
4. The ratio identities show agreement on overlaps, by equality on chart generators.
5. Scheme-morphism-gluing gives the global morphism and its chart inverse images.
6. The local trivializations sending pulled-back coordinates to s_i agree and glue
   to an isomorphism, by invertible-pullback-invertible and sheaf-hom-is-sheaf.
7. Any other morphism has the same chart inverse images and the same ratios;
   morphism-into-affine-scheme and scheme-morphism-gluing give uniqueness.
8. Section-preserving isomorphisms preserve this morphism by uniqueness, and every
   morphism yields a generating pulled-back pair (invertible-pullback-tensor).
9. Pulling back the isomorphism gives the composite's pair via the canonical
   composition isomorphism (invertible-pullback-tensor). Uniqueness proves naturality;
   the classification is bijective on equivalence classes, hence representable. -/
theorem projectiveSpace_functor_of_points (n : ℕ) :
    (∀ (Y : Scheme.{u}) (ψ : Y ⟶ P n),
      ((Scheme.Modules.tensorPullback ψ).obj (O n)).IsInvertible ∧
      ∀ y : Y, ∃ i : Fin (n + 1), y ∈ Scheme.Modules.nonvanishingLocus
        ((Scheme.Modules.tensorPullback ψ).obj (O n)) (pb ψ (O n) (T n i))) ∧
    (∀ (Y : Scheme.{u}) (L : Y.Modules) [L.IsInvertible]
      (s : Fin (n + 1) → (Γ(L, ⊤) : Type u)),
      (∀ y : Y, ∃ i, y ∈ Scheme.Modules.nonvanishingLocus L (s i)) →
      ∃! ψ : Y ⟶ P n,
        ∃ e : (Scheme.Modules.tensorPullback ψ).obj (O n) ≅ L,
          ∀ i, e.hom.app ⊤ (pb ψ (O n) (T n i)) = s i) ∧
    (∀ (Y Y' : Scheme.{u}) (h : Y' ⟶ Y) (ψ : Y ⟶ P n)
      (L : Y.Modules) (s : Fin (n + 1) → (Γ(L, ⊤) : Type u))
      (e : (Scheme.Modules.tensorPullback ψ).obj (O n) ≅ L),
      (∀ i, e.hom.app ⊤ (pb ψ (O n) (T n i)) = s i) →
      ∃ e' : (Scheme.Modules.tensorPullback (h ≫ ψ)).obj (O n) ≅
          (Scheme.Modules.tensorPullback h).obj L,
        ∀ i, e'.hom.app ⊤ (pb (h ≫ ψ) (O n) (T n i)) = pb h L (s i)) := by
  sorry

end AlgebraicGeometry
