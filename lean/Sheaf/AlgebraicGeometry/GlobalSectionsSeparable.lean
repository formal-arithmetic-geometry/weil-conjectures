/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Sheaf.AlgebraicGeometry.SmoothProjectiveCurve
import Sheaf.AlgebraicGeometry.ProperGeometricallyReducedGlobalSectionsSeparable

/-!
# Separability of global sections of a smooth projective curve

Source: Stacks Project, Varieties, Lemma 0BUG (clause (4))
(blueprint: lem-pc-global-sections-separable).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a smooth projective curve over a field whose global sections form a field,
those global sections are separable over the base field.
Source: Stacks Project, Varieties, Lemma 0BUG, clause (4)
(blueprint: lem-pc-global-sections-separable).
By `def-pc-smooth-projective-curve`, the structure morphism is projective and smooth.
Apply `lem-pc-projective-proper` to obtain properness. Apply
`sbc-lem-smooth-geometrically-reduced` to obtain geometrically reduced fibres; the fibre
over the unique point of `Spec k`, whose residue field is `k`, is `X`, so `X` is
geometrically reduced over `k`. Finally apply
`lem-pc-proper-geometrically-reduced-global-sections-separable`, rendered by
`proper_geometricallyReduced_globalSections_isSeparable`, using the assumed field
extension `def-pc-field-extension`. This gives exactly the separability of the canonical
global-sections extension.
-/
theorem globalSections_isSeparable_of_isSmoothProjectiveCurve
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [Scheme.Hom.IsSmoothProjectiveCurve (X ↘ Spec (.of k))]
    (hA : IsField Γ(X, ⊤)) :
    @Algebra.IsSeparableExtension k Γ(X, ⊤) _ hA.toField
      (Scheme.globalSectionsRingHom k (X := X)).toAlgebra := by
  sorry

end AlgebraicGeometry
