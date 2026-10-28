/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.LisseTowerEtaleDescentData
import Sheaf.Paper.LisseFiniteLevelProEtaleLocalIsoSections
import Sheaf.Paper.LisseFiniteLevelEtaleLocalRepresentative

/-! # Local isomorphism representatives for a finite-level model

Source: Stacks Project, proetale.tex, Tags 099Y, 099Z, 09B1 and 09BV.
(blueprint: lem-weil-pbc-lisse-finite-level-etale-local-isomorphisms).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard
  pbcDerivedRestrict constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow etaleIsomorphismNormalizationArrow
  lisseTowerAlgebraArrow lisseTowerFixedRealization

/-- The comparison and local model hypotheses produce an étale representative of an
isomorphism at every geometric point.  This is the local comparison part of the
finite-level descent argument; no sheafification or stalk evaluation is included.

Source: Stacks Project, proetale.tex, Tags 099Y, 099Z, 09B1 and 09BV.
(blueprint: lem-weil-pbc-lisse-finite-level-etale-local-isomorphisms).

Proof: The four bounded finite-lisse Hom comparisons are invertible, hence the
inverse-pair equalizer comparison is invertible.  On every member of the supplied
pro-étale covering sieve, compose the given model isomorphism with the inverse of
the fixed-realization comparison.  The fixed realization is an equivalence, so this
comparison lifts to an actual isomorphism after restricting to an étale neighbourhood
of any geometric point.  The resulting representative is the required local section
of the Isom presheaf.  Empty schemes and zero complexes are covered by the same
construction.
-/
theorem lisse_finite_level_etale_local_isomorphisms
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : Y.ProEt) (n : ℕ)
    (N : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (D : DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (hDbounded : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj D))
    (hDlisse : ∀ q : ℤ, IsFiniteLocallyConstantSheaf
      ((DerivedCategory.homologyFunctor _ q).obj D))
    (hcomparison : Nonempty ((lisseTowerFixedRealization (U.hom ≫ g) d n).obj
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) U.left).mapDerivedCategory.obj D) ≅
        (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj N))
    (hmodels : ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
      ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
        Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ≅
          (adicTowerPullback (W.hom ≫ g)
            ((pbcAdicRings X d).obj (op n))).obj N)) :
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ U.left),
      ∃ (V : U.left.Etale) (v : (pointSmallEtale x).fiber.obj V),
        Nonempty ((localIsomorphismRestriction U.left
          (lisseTowerEtaleRing d n) V).obj
            ((normalizationConstant U.left.smallEtaleTopology).obj E) ≅
          (localIsomorphismRestriction U.left
            (lisseTowerEtaleRing d n) V).obj D) := by
  have hsections :=
    lisse_finite_level_proetale_local_iso_sections X Y g d U n N E D
      hDbounded hDlisse hcomparison hmodels
  exact exists_etale_local_representative_of_proetale_local_iso_sections Y U
    ((normalizationConstant U.left.smallEtaleTopology).obj E) D
    hsections

end AlgebraicGeometry.Scheme
