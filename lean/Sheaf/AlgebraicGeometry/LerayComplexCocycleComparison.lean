/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Paper.PQFCohomology

/-!
# The cycle comparison for direct image before deriving

Source: Stacks Project, Cohomology, Tag 01F4 (2), construction on complexes
(blueprint: lem-pc-leray-complex-cocycle-comparison).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- The comparison from cohomology of global sections to global sections of the
cohomology sheaf is natural in arbitrary nonnegative complexes, before any resolution
or derived-functor identification is chosen.

Source: Stacks Project, Cohomology, Tag 01F4 (2), cycle construction of the edge;
the direct-proof exercise in its proof (expanded by K1)
(blueprint: lem-pc-leray-complex-cocycle-comparison).

Proof: Sections of the direct image on the whole target are sections on the inverse
image of that open, identified with the whole source by `Opens.map_top`. This gives a
natural isomorphism of the underlying abelian-group complexes. Global sections
preserve kernels, so cycles of the sections complex identify with sections of the
cycle sheaf. Apply sections to the cycle-to-homology quotient. The resulting map
annihilates boundaries: the incoming differential factors through the boundary sheaf,
whose composite with the cycle-to-homology quotient is zero. It therefore factors
uniquely through the homology quotient of the sections complex. This factorization
is a group homomorphism. For a cochain map, both composites with this quotient agree
by naturality of the cycle inclusion and quotient; the quotient is epic, so the
factorizations agree. These maps form the displayed natural transformation. The
kernel identification supplies z and its inclusion equation, and the defining
factorization supplies the homology equation. This argument includes degree zero
(where the incoming differential is zero), zero complexes, and the empty scheme. -/
theorem leray_complex_cocycle_comparison {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℕ) :
    ∃ τ :
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ) ⋙ HomologicalComplex.homologyFunctor _ _ q ⋙
          forget₂ _ AddCommGrpCat) ⟶
      ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℕ) ⋙ HomologicalComplex.homologyFunctor _ _ q ⋙
          RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙ forget₂ _ AddCommGrpCat),
      ∀ (C : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℕ)
        (s : (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj C).cycles q),
        ∃ z : (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj
          ((((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj C).cycles q),
          (C.X q).val.presheaf.map
            (eqToHom (congrArg op (Opens.map_top f.base).symm))
            ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj C).iCycles q s) =
            (RingedSpace.globalSectionsFunctor Y.toRingedSpace).map
              ((((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj C).iCycles q) z ∧
          (τ.app C)
            ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj C).homologyπ q s) =
            (RingedSpace.globalSectionsFunctor Y.toRingedSpace).map
              ((((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj C).homologyπ q) z := by sorry

end AlgebraicGeometry
