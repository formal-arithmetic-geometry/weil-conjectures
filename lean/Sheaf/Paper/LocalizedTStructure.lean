/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.IntegralTStructure
public import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology

/-! # The bounded rational t-structure

Source: blueprint, smooth base change, order 1432; BBD 1.3.3--1.3.6
(blueprint: prop-weil-localized-tstructure).
The category is the raw scalar localization of the completed integral category.
The last, levelwise computation carries its explicit higher-Tor hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
variable [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable [hNoeth : IsNoetherian T] [hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
variable [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
include hNoeth hDim hInv

set_option linter.defProp false in
/-- The existing scalar-localization theorem specialized to the integral category.
It fixes the induced shift, the identity comparison for Q, and exactly the isomorphic
images of integral distinguished triangles. Source: order 1432
(blueprint: prop-weil-localized-tstructure). -/
abbrev pbcLocalizedTriangulationData :=
  ScalarLocalization.exists_triangulated_scalarLocalization (PbcIntegralRing l E)
    (PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)) (pbcUniformizer l E)

/-- The localized zero object, supplied by scalar localization.
Source: order 1432 (blueprint: prop-weil-localized-tstructure). -/
instance pbcLocalizedZero : HasZeroObject
    (PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)) :=
  (pbcLocalizedTriangulationData T l E).choose

/-- The induced rational integer shift.
Source: order 1432 (blueprint: prop-weil-localized-tstructure). -/
instance pbcLocalizedShift : HasShift
    (PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)) ℤ :=
  (pbcLocalizedTriangulationData T l E).choose_spec.choose

/-- Additivity of the induced shifts.
Source: order 1432 (blueprint: prop-weil-localized-tstructure). -/
instance pbcLocalizedShiftAdditive (n : ℤ) :
    Functor.Additive
      (shiftFunctor (PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)) n) :=
  (pbcLocalizedTriangulationData T l E).choose_spec.choose_spec.2.choose n

/-- The canonical comparison between localization and shifts.
Source: order 1432 (blueprint: prop-weil-localized-tstructure). -/
instance pbcLocalizedCommShift :
    (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).CommShift ℤ :=
  (pbcLocalizedTriangulationData T l E).choose_spec.choose_spec.2.choose_spec.choose

/-- Distinguished triangles are exactly the isomorphic images of integral ones.
Source: order 1432 (blueprint: prop-weil-localized-tstructure). -/
instance pbcLocalizedPretriangulated : Pretriangulated
    (PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)) :=
  Exists.choose
    (pbcLocalizedTriangulationData T l E).choose_spec.choose_spec.2.choose_spec.choose_spec.2

/-- Octahedra descend to the raw scalar localization.
Source: order 1432 (blueprint: prop-weil-localized-tstructure). -/
instance pbcLocalizedIsTriangulated : IsTriangulated
    (PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)) :=
  And.left (Exists.choose_spec
    (pbcLocalizedTriangulationData T l E).choose_spec.choose_spec.2.choose_spec.choose_spec.2)

/-- Q is exact for precisely this induced triangulation.
Source: order 1432 (blueprint: prop-weil-localized-tstructure). -/
instance pbcLocalizedQIsTriangulated :
    (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).IsTriangulated :=
  And.left (And.right (Exists.choose_spec
    (pbcLocalizedTriangulationData T l E).choose_spec.choose_spec.2.choose_spec.choose_spec.2))

/-- Rationalization descends the bounded standard integral t-structure. Its two parts
are the strictly full images of the integral parts; Q is t-exact and commutes naturally
with both canonical truncations. The heart is the image of a single integral heart
object. Under the stated Tor condition, rational truncations are also the images of
the Roos limits of the levelwise truncated normalized reduction tower.
Source: blueprint order 1432 (blueprint: prop-weil-localized-tstructure).

Proof:
1. The actual integral category and its bounded t-structure are those of
   def-weil-pbc-bounded-constructible-complete and prop-weil-pbc-integral-tstructure.
   Apply lem-weil-linear-scalar-localization-triangulated to its constant-section
   scalar action and uniformizer. This gives precisely the triangulation used here
   and the exact localization Q; no Karoubi envelope is introduced.
2. Close the two image classes under isomorphisms. Exactness of Q and the integral
   shift axioms give the rational shift axioms.
3. For opposite integral bounds, the integral Hom module is zero. The localized Hom
   formula tensors it with the fraction field, so the rational Hom is zero as well.
   Composing with the chosen representative isomorphisms proves orthogonality for
   every object in the strictly full classes.
4. Apply Q to the integral canonical truncation triangle. Its end terms have the
   prescribed image bounds, so this is a truncation triangle. Every rational object
   has an integral representative, so this proves the existence axiom.
5. Integral bounds give bounds on every rational representative. This proves
   boundedness. The definitions of the two parts give t-exactness of Q.
6. By lem-weil-heart-short-exact-triangles, uniqueness of truncation triangles with
   identity on QK gives the lower and upper
   comparison isomorphisms. Their counit, respectively unit, equations and the
   adjunctions show naturality at every integral morphism. The fraction formula
   extends the induced truncations to rational morphisms independently of a fraction
   presentation or an integral representative.
7. Images of integral heart objects are in the rational heart. Conversely, if X=QK
   is in the rational heart, its rational H^0 is X. The natural comparisons identify
   it with Q of the integral H^0 of K, which lies in the integral heart. This proves
   the single-object essential-image description.
8. Finally impose thm-weil-pbc-integral-truncations' higher-Tor condition. That theorem
   identifies the ambient integral canonical truncations with the Roos limits of
   the two levelwise truncated diagrams. Use their integral representatives as L
   and U below, and apply the natural comparisons in step 6. This last computation
   is conditional; the preceding scalar-localization claims are unconditional. -/
theorem pbc_localized_tstructure :
    ∃ tE : Triangulated.TStructure
        (PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)),
      (∀ X : PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E),
        (tE.le 0 X ↔
          ∃ L : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E),
            (pbcIntegralTStructure T l E).le 0 L ∧
              Nonempty (X ≅ (pbcRationalization T (pbcIntegralDatum l E)
                (pbcUniformizer l E)).obj L)) ∧
        (tE.ge 0 X ↔
          ∃ L : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E),
            (pbcIntegralTStructure T l E).ge 0 L ∧
              Nonempty (X ≅ (pbcRationalization T (pbcIntegralDatum l E)
                (pbcUniformizer l E)).obj L))) ∧
      tE.bounded = ⊤ ∧
      (∀ (K : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)) (m : ℤ),
        ((pbcIntegralTStructure T l E).le m K →
          tE.le m ((pbcRationalization T (pbcIntegralDatum l E)
            (pbcUniformizer l E)).obj K)) ∧
        ((pbcIntegralTStructure T l E).ge m K →
          tE.ge m ((pbcRationalization T (pbcIntegralDatum l E)
            (pbcUniformizer l E)).obj K))) ∧
      (∀ m : ℤ,
        Nonempty (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
            tE.truncLE m ≅ (pbcIntegralTStructure T l E).truncLE m ⋙
              pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)) ∧
        Nonempty (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
            tE.truncGE m ≅ (pbcIntegralTStructure T l E).truncGE m ⋙
              pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E))) ∧
      (∀ X : PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E),
        tE.heart X ↔
          ∃ H : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E),
            (pbcIntegralTStructure T l E).heart H ∧
              Nonempty (X ≅ (pbcRationalization T (pbcIntegralDatum l E)
                (pbcUniformizer l E)).obj H)) ∧
      ∀ (K : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E))
        (_hTor : PbcTruncationTorCompatible T (pbcIntegralDatum l E) K.obj) (m : ℤ),
        ∃ L U : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E),
          IsDerivedLimit
            (K := fun n ↦ ((pbcAmbientTStructure T l E).truncLE m).obj
              ((pbcCanonicalReductionDiagram T (pbcIntegralDatum l E) K.obj).obj (op n)))
            (fun n ↦ ((pbcAmbientTStructure T l E).truncLE m).map
              ((pbcCanonicalReductionDiagram T (pbcIntegralDatum l E) K.obj).map
                (homOfLE (Nat.le_succ n)).op)) L.obj ∧
          IsDerivedLimit
            (K := fun n ↦ ((pbcAmbientTStructure T l E).truncGE m).obj
              ((pbcCanonicalReductionDiagram T (pbcIntegralDatum l E) K.obj).obj (op n)))
            (fun n ↦ ((pbcAmbientTStructure T l E).truncGE m).map
              ((pbcCanonicalReductionDiagram T (pbcIntegralDatum l E) K.obj).map
                (homOfLE (Nat.le_succ n)).op)) U.obj ∧
          Nonempty ((tE.truncLE m).obj
              ((pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) ≅
            (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).obj L) ∧
          Nonempty ((tE.truncGE m).obj
              ((pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) ≅
            (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).obj U) := by
  sorry

end AlgebraicGeometry.Scheme
