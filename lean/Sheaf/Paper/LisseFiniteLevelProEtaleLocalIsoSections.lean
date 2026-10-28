/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H8
-/
module

public import Sheaf.Paper.LisseTowerEtaleDescentData
public import Sheaf.AlgebraicGeometry.DerivedIsomSheafComparisonFromHom
import Sheaf.AlgebraicGeometry.DerivedMorphismSheafComparison

/-! # Pro-etale local sections of the finite-level derived Isom sheaf

Source: Stacks Project, proetale.tex, Tags 099Y, 099Z, 09B1 and 09BV.
(blueprint: new-lem-weil-pbc-lisse-finite-level-proetale-local-iso-sections).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard
  pbcDerivedRestrict constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow etaleIsomorphismNormalizationArrow
  lisseTowerAlgebraArrow lisseTowerFixedRealization

/-- The finite-level comparison data yields a local section of the pro-etale derived Isom
presheaf through every geometric point.

Source: Stacks Project, proetale.tex, Tags 099Y, 099Z, 09B1 and 09BV.
(blueprint: new-lem-weil-pbc-lisse-finite-level-proetale-local-iso-sections).

Proof: on a pro-etale refinement of the supplied sieve, compose its finite-level model
marking with the inverse of the fixed-realization comparison.  Finite-lisse descent and
the point fibre give an etale object V containing the chosen geometric point.  Transporting
the inverse pair along comparison gives the displayed pro-etale Isom section on V.  The
construction also covers empty schemes and zero complexes.
-/
theorem lisse_finite_level_proetale_local_iso_sections
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
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ U.left),
      ∃ (V : U.left.Etale) (v : (pointSmallEtale x).fiber.obj V),
        Nonempty ((derivedLocalIsoPresheaf (ProEt.topology U.left)
          (lisseTowerEtaleRing d n)
          ((derivedComparison U.left (lisseTowerEtaleRing d n)).obj
            ((normalizationConstant U.left.smallEtaleTopology).obj E))
          ((derivedComparison U.left (lisseTowerEtaleRing d n)).obj D)).obj
            (op ((toProEt U.left).obj V))) := by
  sorry

end AlgebraicGeometry.Scheme
