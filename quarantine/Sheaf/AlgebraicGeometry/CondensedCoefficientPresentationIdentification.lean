/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.AlgebraicGeometry.ProEtalePointPullback
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import Sheaf.Topology.ContinuousMapCondensedRingMap

/-!
# Identification of condensed coefficients and local presentations

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-sfb-qlbar-two-colimit/lem-sfb-constructible-cocone-obj.proof.md,
Modules and Complexes paragraphs
(blueprint: lem-sfb-condensed-coefficient-presentation-identification).

The archived definitions and the current definitions use the same published internal-module
and ordinary-derived-category constructions. Equalities below are equalities of bundled ring
objects and full subcategories, so they identify all operations and all morphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The coefficient rings, scalar inclusions, finite local presentations and bounded
constructible categories agree in the two conventions, including the specified
finite-subfield-valued algebraic-closure input.

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-sfb-qlbar-two-colimit/lem-sfb-constructible-cocone-obj.proof.md,
Modules and Complexes paragraphs
(blueprint: lem-sfb-condensed-coefficient-presentation-identification).

Proof:
1. For E the two inputs are C(-,E) with the restricted norm topology; for Omega they
are the same finite-subfield-valued continuous functions. Restrictions are precomposition.
The point inverse image is the common sheafified left Kan extension followed by the
structure inverse image (sk-def-sfb-pullback-from-point). Transporting the identity on
these inputs gives equality of bundled ring objects, hence of units and multiplication
(sk-def-sfb-pulled-back-coefficients). Coefficient inclusions are postcomposition in both
conventions (def-sfb-continuous-map-condensed-ring-map); their point pullbacks agree.
2. Both module categories are Mod of this ring in the same abelian sheaf category
(sk-def-sfb-module-objects and def-weil-pbc-condensed-e-module-category). Objects have the
same associative unital action, and arrows are the same action-compatible sheaf maps.
Stratum and covering restrictions apply the same monoidal inverse image to these actions.
3. A finite presentation is precisely m,n and a map R^m to R^n with an isomorphism
from the module to its cokernel (def-sfb-finitely-presented-module). The common regular
module, finite sums and cokernel universal property keep each presentation unchanged,
also when either rank is zero. Keeping the same cover gives the identical local finite
presentation condition (def-sfb-locally-finitely-presented).
4. Keep the finite stratification and every cover and presentation on its strata.
This identifies constructibility in both directions (def-sfb-constructible-module).
For Omega only the predicate specified in lem-weil-pbc-condensed-constructible-serre
is used; none of its closure conclusions is needed.
5. The common module category has the same complexes, cohomology and quasi-isomorphisms.
Its ordinary derived localization (def-weil-abstract-derived-category) therefore
identifies every morphism, including the formal inverses of quasi-isomorphisms.
Membership is exactly constructible cohomology and vanishing outside one finite interval
(sk-def-sfb-bounded-constructible, def-sfb-dcons-subfield and def-sfb-dcons-qlbar).
The last equivalence keeps any specified ordered interval [a,b], not just its existence.
The full subcategory equalities retain all ambient arrows, identities and composition.
No finite Tor amplitude or derived completeness condition occurs. -/
theorem condensed_coefficient_presentation_identification
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (Mon.mk (padicSubfieldRingObj X ℓ E) =
      coefficientRing X (Mon.mk
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
            (Profinite.padicSubfieldCondensedRing ℓ E.val)))) ∧
    (Mon.mk (padicAlgClRingObj X ℓ) =
      coefficientRing X (Mon.mk (Profinite.padicAlgClRingObj ℓ))) ∧
    (∀ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F),
      padicSubfieldRingObjMap X ℓ h =
        (sfbPullbackFromPoint X).map (Profinite.padicSubfieldRingObjMap ℓ h)) ∧
    (padicSubfieldRingObjToPadicAlgCl X ℓ E =
      (sfbPullbackFromPoint X).map (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)) ∧
    (∀ Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}),
      (Λ = Mon.mk (Profinite.continuousMapRingObj E.val) ∨
        Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ)) →
      (coefficientRing X Λ = (sfbPullbackFromPoint X).mapMon.obj Λ) ∧
      (∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ.X X),
        IsConstructibleModuleObject (condensedRingObj Λ.X X) M ↔
          ∃ S : Scheme.Stratification X, ∀ a : Fin S.n,
            ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a),
              ∀ i : U.I₀,
                Mod.IsFinitelyPresented
                  ((upperStar Ab.{u + 1} (U.f i)).obj
                    ((upperStar Ab.{u + 1} (S.immersion a)).obj
                      (condensedRingObj Λ.X X)))
                  (((upperStar Ab.{u + 1} (U.f i)).mapMod
                    ((upperStar Ab.{u + 1} (S.immersion a)).obj
                      (condensedRingObj Λ.X X))).obj
                    (((upperStar Ab.{u + 1} (S.immersion a)).mapMod
                      (condensedRingObj Λ.X X)).obj M))) ∧
      (∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ.X X)),
        boundedConstructible (condensedRingObj Λ.X X) K ↔
          (∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
            IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) ∧
          ∀ i : ℤ, IsConstructibleModuleObject (condensedRingObj Λ.X X)
            ((DerivedCategory.homologyFunctor _ i).obj K)) ∧
      (∀ (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ.X X))) (a b : ℤ), a ≤ b →
        ((boundedConstructible (condensedRingObj Λ.X X) K ∧
          ∀ i : ℤ, (i < a ∨ b < i) →
            IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) ↔
        ((∀ i : ℤ, IsConstructibleModuleObject (condensedRingObj Λ.X X)
          ((DerivedCategory.homologyFunctor _ i).obj K)) ∧
          ∀ i : ℤ, (i < a ∨ b < i) →
            IsZero ((DerivedCategory.homologyFunctor _ i).obj K))))) ∧
    (PadicSubfieldConstructible X ℓ E =
      (boundedConstructible (condensedRingObj
        (continuousMapCondensedRing E.val).X X)).FullSubcategory) ∧
    (PadicAlgClConstructible X ℓ =
      (boundedConstructible (condensedRingObj
        (Mon.mk (Profinite.padicAlgClRingObj ℓ)).X X)).FullSubcategory) := by
  sorry

end AlgebraicGeometry.ProEtale
