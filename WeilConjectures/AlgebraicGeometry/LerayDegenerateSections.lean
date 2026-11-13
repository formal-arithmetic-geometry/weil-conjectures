/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.LerayEdgeCocycleData
import WeilConjectures.AlgebraicGeometry.LerayEdgeVanishingIso

/-!
# The canonical Leray edge and its degeneration

Source: Stacks Project, Cohomology, Tag 01F4 (2), with Tags 01F2 and 01EX.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The cocycle-defined Leray edge is a natural homomorphism, independent of the injective
resolution, and is an isomorphism if every higher cohomology group of every higher direct
image vanishes. The first conjunct describes its value on every resolution: `s` is a cycle
of its global-sections complex and `z` is the corresponding section of the cycle sheaf of
the direct-image complex `K`. The restriction along `Opens.map_top` identifies their
representatives. Projection by `homologyπ` followed by the inverse resolution comparison
is precisely the class of `z` in the higher direct image. The universally quantified `K`
and equality `hK` merely name the direct-image complex, without introducing a new notion.

Source: Stacks Project, Cohomology, Tag 01F4 (2), with Tags 01F2 and 01EX.

Proof:
1. Choose an injective resolution. Sections of its direct
image are sections on inverse-image opens. A global cocycle is a
section of its cycle sheaf; quotienting by boundaries gives the displayed map. Cohomology
and higher direct images are the right derived functors.
2. Apply thm-sp-grothendieck to direct image followed by global sections. The module-sheaf
categories are Grothendieck abelian, as is Ab. Both functors are additive and left exact; lem-weil-pbc-module-pushforward-injective-acyclic
supplies composite acyclicity. The composite is global
sections on X. By lem-sp-derived-well-defined the derived identifications are independent
of resolution; lem-sp-grothendieck-edge-maps gives naturality and
lem-pc-grothendieck-edge-cocycle identifies this edge with the cocycle formula.
3. Under the vanishing hypothesis all columns except p = 0 vanish. The first-quadrant
spectral sequence and finite abutment filtration collapse. The edge-isomorphism clause of
lem-pc-grothendieck-edge-cocycle therefore makes this same edge an isomorphism. -/
theorem exists_lerayEdge_isIso_of_vanishing {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ ε : ∀ q : ℕ,
      (RingedSpace.moduleCohomology X.toRingedSpace q ⋙ forget₂ _ AddCommGrpCat) ⟶
        (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived q ⋙
          RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙ forget₂ _ AddCommGrpCat,
      (∀ (q : ℕ) (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (I : InjectiveResolution F)
        (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℕ)
        (hK : K = ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)
        (s : (RingedSpace.globalSectionsComplex I).cycles q),
        ∃ z : (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj (K.cycles q),
          (I.cocomplex.X q).val.presheaf.map
              (eqToHom (congrArg op (Opens.map_top f.base).symm))
              ((RingedSpace.globalSectionsComplex I).iCycles q s) =
            (RingedSpace.globalSectionsFunctor Y.toRingedSpace).map
              (K.iCycles q ≫ (eqToHom hK).f q) z ∧
          (ε q).app F
              ((I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) q).inv
                ((RingedSpace.globalSectionsComplex I).homologyπ q s)) =
            (RingedSpace.globalSectionsFunctor Y.toRingedSpace).map
              ((K.homologyπ q) ≫ HomologicalComplex.homologyMap (eqToHom hK) q ≫
                (I.isoRightDerivedObj
                  (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) q).inv) z) ∧
      (∀ (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
        (∀ (q p : ℕ), 0 < p →
          IsZero ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj
            (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived q).obj F))) →
        ∀ q : ℕ, IsIso ((ε q).app F)) := by
  obtain ⟨ε, hε⟩ := leray_edge_cocycle_data f
  exact ⟨ε, hε, leray_edge_isIso_of_vanishing f ε hε⟩

end AlgebraicGeometry
