/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerEtaleDescentData
import Submission.WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteLevelEtaleLocalIsomorphisms
import Submission.WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteLevelEtaleStalkFromLocal

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Geometric Isom stalks for a supplied finite-level model

Source: Stacks Tags 099Y and 09BV.
(blueprint: new-lem-weil-pbc-lisse-finite-level-etale-stalks).
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

/--
A bounded finite-lisse etale model carrying the fixed-realization comparison
has inhabited geometric stalks of its local derived Isom sheaf whenever the
pro-etale local markings exist. This is the stalk-and-Isom part of
`lisse_finite_level_etale_descent`; the etale model is supplied as input.

Source: Stacks Project, proetale.tex, Tags 099Y and 09BV.
(blueprint: new-lem-weil-pbc-lisse-finite-level-etale-stalks).

Proof: compare the four derived Hom sheaves for the constant source and the
supplied model. Bounded finite-lisse hypotheses make each comparison invertible;
the inverse-pair equalizer then makes the Isom comparison invertible. Pulling a
local marking through this comparison gives a local section, and geometric
stalks of the etale Isom sheaf are therefore inhabited. Empty bases have no
geometric points.
-/
theorem lisse_finite_level_etale_stalks
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
      Nonempty ((pointSmallEtale x).sheafFiber.obj (derivedLocalIsomorphismSheaf
        ((normalizationConstant U.left.smallEtaleTopology).obj E) D)) := by
  intro Ω instField instSep x
  obtain ⟨V, v, hV⟩ := lisse_finite_level_etale_local_isomorphisms X Y g d U n N E D
    hDbounded hDlisse hcomparison hmodels Ω x
  exact lisse_finite_level_etale_stalk_from_local_section U.left
    (lisseTowerEtaleRing d n)
    ((normalizationConstant U.left.smallEtaleTopology).obj E) D Ω x V v hV

end AlgebraicGeometry.Scheme
