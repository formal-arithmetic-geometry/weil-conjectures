/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.AlgebraicGeometry.KoszulOpenSystem
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.AffineKoszulCechDerivedComparison
import Sheaf.AlgebraicGeometry.DerivedStructureSheafHomHypercohomology
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

/-! # Degree-zero consequences of the Koszul-to-Čech comparison

Source: Stacks Project, Tag 08DD, proof of Proposition 36.9.5.
-/

@[expose] public section

universe uMain wMain
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- A derived morphism killed by restriction vanishes after a Koszul power transition.
Source: Stacks Project, Tag 08DD, proof of Proposition 36.9.5.
(blueprint: lem-sc-koszul-open-hom-restriction-eventually-zero)

Proof: Use the affine derived equivalence (Tag 06Z0) to represent E by a termwise
quasi-coherent complex F, corresponding to an A-module complex M. Since each tail is
bounded finite free, its Hom-complex H^0 is derived Hom (K-projectivity). These
identifications respect precomposition by the power transitions. Exactness of filtered
colimits identifies the colimit of these Hom groups with H^0 of their Hom-complex
colimit. The canonical Koszul/Čech/derived-sections comparison is a quasi-isomorphism
(Tags 08D1, 08D2), hence injective on H^0. The image of a morphism is its restriction
composed with the inverse restricted augmentation, so a restriction-zero morphism has
zero image. Injectivity makes its colimit class zero. The element criterion for a
filtered colimit of modules gives a later stage b and equality to zero after the
transition I_b to I_e. For r=0 all tails vanish; if the open is empty because all f_i
are nilpotent, sufficiently large power transitions vanish. The zero morphism works
with b=e, and the case E=0 is immediate. -/
theorem koszulOpenHom_restriction_eventually_zero
    (A : Type uMain) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))]
    (E : schemeDerivedQCohCategory (Spec (.of A)))
 :
    let R := ((SheafOfModules.overFunctor.{uMain}
      (moduleRings (Spec (.of A)).toRingedSpace) (koszulOpen A r f)) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uMain}
          ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
        (D := SheafOfModules.{uMain}
          (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory
    ∀ (e : ℕ) (φ : koszulOpenObject A r f e ⟶ E.1), R.map φ = 0 →
      ∃ (b : ℕ) (h : e ≤ b), koszulOpenMap A r f e b h ≫ φ = 0 := by
  sorry

end AlgebraicGeometry
