/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOriginRecursiveData

/-! # Composition of the specified compact-support source at the origin

Source: `det-sp-trace-basic`, Proof (2), successive closed sections
(blueprint: lem-sp-affine-origin-source-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

open ProEtale.CoordinateSectionNormalization

/-- The specified compact-support source has the identity and successor normalizations.
This concerns only support functors and their compositors; it contains no Cartier class
or trace map.

Source: `det-sp-trace-basic`, Proof (2), compact-support composition along the origin
(blueprint: lem-sp-affine-origin-source-coherence).

Proof: expand the tower source into the lower-shriek identity comparison, the
congruence for the zero-section/projection equation, the compact-support compositor,
the proper shriek/star comparison, and the inverse ordered compactification comparison.
In rank zero the unit law for the compact-support compositor and the derived identity
comparison reduce it to the inverse direct-image identity comparison. For a successor,
write the origin as the old origin followed by the last zero section, using
`affineOriginTowerZeroSection_succ`, and the projection as the last projection followed
by the old projection. Use associativity of the compact-support compositor to regroup
these four maps. Its proper/proper specialization identifies the two closed-section
factors with `affineOriginClosedSourceIso`; this specialization follows by deriving
the sheaf direct-image composition isomorphism. Naturality of proper shriek/star moves
that identification through the old compact pushforward. The last section/projection
pair composes to identity, and the compact-support unit law reduces this pair to
`sectionComposition`. The defining successor equation of the ordered compactification
comparison leaves the old tower source on the other side. Cancelling the common
comparison isomorphisms yields the displayed successor equation. These equations use
only canonical functorial comparisons, so also hold in rank zero and over empty bases.
-/
theorem affineOriginTowerSource_coherence
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] :
    (affineOriginTowerSourceIso A S 0).hom = (affineOriginZeroSupportIso A S).inv ∧
      ∀ d : ℕ,
        letI := affineTraceNoetherian S d
        (affineOriginTowerSourceIso A S (d + 1)).hom ≫
          (affineTraceLeft A S (d + 1)).map (affineOriginClosedSourceIso A S d).hom =
        (affineOriginTowerSourceIso A S d).hom ≫
          (affineTraceLeft A S d).map
            ((sectionComposition A (affineTraceTower S d)).inv.app
              ((ordinaryFinitePushforward A (affineOriginTowerZeroSection S d)).obj
                (ordinaryFiniteUnit A S))) := by
  sorry

end AlgebraicGeometry.Etale
