/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Right adjoints of proper perfect pushforward preserve coproducts

Source: Stacks Project, Duality for Schemes, Lemma 48.13.1, Tag 0A9R
(blueprint: lem-sc-smooth-proper-tensor-direct-sums).
-/

universe u wX wY v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A right adjoint to quasi-coherent derived pushforward along a proper perfect morphism
of Noetherian schemes preserves every set-indexed direct sum. Finite Tor dimension is
written stalkwise: the source stalk, restricted along `f.stalkMap x`, has vanishing Tor
above some bound against every module over the target stalk. The functor `R` and `eR`
represent the restriction of the shared `schemeDerivedDirectImage f` to the full
quasi-coherent subcategories; they do not supply an unrelated direct-image functor.
Preservation of colimits of discrete shape says exactly that the canonical coproduct
comparison is an isomorphism for every family, including the empty family.

Source: Stacks Project, Duality for Schemes, Lemma 48.13.1, Tag 0A9R
(blueprint: lem-sc-smooth-proper-tensor-direct-sums).

Proof. For a perfect object P on X, proper perfect direct image makes Rf_*P perfect
(lem-pc-proper-perfect-direct-image-perfect). Perfect objects on Noetherian schemes are
compact (lem-pc-perfect-object-compact), so Hom(Rf_*P,-) commutes with direct sums.
Adjunction identifies this calculation with Hom(P,c(-)); compactness of P identifies
Hom(P, the direct sum of c(K_j)) with the direct sum of Hom(P,c(K_j)). Thus Hom(P,-)
of the canonical comparison is an isomorphism for every perfect P, and also every
shift of P. The long exact Hom sequence makes its cone orthogonal to all these shifts.
The class of objects whose shifts are orthogonal to that cone is closed under shifts,
cones, retracts, and arbitrary sums. Perfect generation
(lem-pc-derived-qcoh-perfect-generation) makes this class the entire category.
Taking the cone itself gives its identity zero, so the cone vanishes and the comparison
is an isomorphism. -/
theorem properPerfect_rightAdjoint_preservesCoproducts
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [IsProper f]
    (hTor : ∀ x : X, ∃ n : ℕ,
      ∀ (N : ModuleCat.{u} (Y.presheaf.stalk (f x))) (i : ℕ), n < i →
        IsZero (((Tor (ModuleCat.{u} (Y.presheaf.stalk (f x))) i).obj
          ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
            (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)))).obj N))
    (R : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (eR : R ⋙ (schemeDerivedQCohProperty Y).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adj : R ⊣ c) :
    ∀ I : Type v, PreservesColimitsOfShape (Discrete I) c := by
  sorry

end AlgebraicGeometry
