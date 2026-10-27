/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.Paper.LisseTowerEtaleDescentData
import Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.DerivedHomSheafComparisonLisse
import Sheaf.AlgebraicGeometry.DerivedIsomSheafComparisonFromHom
import Sheaf.Paper.ProEtaleLisseOrigin
import Sheaf.Paper.ProEtaleFiniteLocalConstancyReflection
import Sheaf.Paper.LisseFiniteLevelEtaleModel
import Sheaf.Paper.LisseFiniteLevelEtaleStalks

/-! # Descent of one separately marked finite level

Source: Stacks Tags 099Y, 099Z, 09B1 and 09BV.
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

/-- A single finite-coefficient level with local bounded finite algebraic markings
has an etale model. Its comparison uses the explicitly constructed fixed realization.
This statement contains no tower, transition, normalization or coefficient-square data.

Source: Stacks Project, proetale.tex, Tags 099Y, 099Z, 09B1 and 09BV.
(blueprint: lem-weil-pbc-lisse-finite-level-etale-descent).

Proof: identify the completion quotient with A/I^(n+1), using finite generation of I.
The scalar map in lisseTowerFiniteScalarMap is locally bijective, so its associated
module-sheaf realization is an exact equivalence. Its inverse sends the pullback of N
to a fixed-ring complex on U.left. The separate local markings identify the cohomology
locally with the constant finite cohomology of E, since realization and inverse image
are exact. Therefore this complex has the same cohomological bounds as E, and its
cohomology sheaves are finite locally constant. Finite pro-etale local systems descend
to etale local systems (Tag 099Y), so this cohomology is classical. The bounded-below
classical derived equivalence (Tags 099Z and 09B1) provides an etale complex D and the
stated comparison. Exact faithful inverse image reflects the bounds and the finite
local constancy of the descended cohomology. Apply the Hom-sheaf comparison to the four
pairs formed by constant(E) and D. Both complexes are bounded with finite locally
constant cohomology, so the comparison on their Isom sheaf is invertible. Each marking
gives a section of its pro-etale pullback on the corresponding covering member.
Consequently that pullback maps epimorphically to the terminal sheaf. Faithful
comparison reflects epimorphisms, so the etale Isom sheaf is locally inhabited and
all its geometric stalks are inhabited. No finite-local-constancy assertion for
the Isom sheaf is needed. These are separate stalk assertions at this one level. For an
empty U there are no geometric points, and the zero complex supplies the model.
No transition, reduction of isomorphisms, or simultaneous marking is chosen. -/
theorem lisse_finite_level_etale_descent
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : Y.ProEt) (n : ℕ)
    (N : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (hbounded : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj E))
    (hfinite : ∀ q : ℤ, Module.Finite (lisseTowerEtaleRing d n)
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) q).obj E))
    (hmodels : ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
      ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
        Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ≅
          (adicTowerPullback (W.hom ≫ g)
            ((pbcAdicRings X d).obj (op n))).obj N)) :
    ∃ D : DerivedCategory
        (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))),
      (∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj D)) ∧
      (∀ q : ℤ, IsFiniteLocallyConstantSheaf
        ((DerivedCategory.homologyFunctor _ q).obj D)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ U.left),
        Nonempty ((pointSmallEtale x).sheafFiber.obj (derivedLocalIsomorphismSheaf
          ((normalizationConstant U.left.smallEtaleTopology).obj E) D))) ∧
      Nonempty ((lisseTowerFixedRealization (U.hom ≫ g) d n).obj
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) U.left).mapDerivedCategory.obj D) ≅
        (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj N) := by
  obtain ⟨D, hDbounded, hDlisse, hcomparison⟩ :=
    lisse_finite_level_etale_model X Y g d U n N E hbounded hfinite hmodels
  have hstalk := lisse_finite_level_etale_stalks X Y g d U n N E D
    hDbounded hDlisse hcomparison hmodels
  exact ⟨D, hDbounded, hDlisse, hstalk, hcomparison⟩

end AlgebraicGeometry.Scheme
