/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Sheaf.Paper.PointReductionUnits
public import Sheaf.Paper.PointSectionsDerivedReduction
public import Sheaf.Paper.PointSectionsFiniteReduction
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.Paper.AdicCoefficientDatum

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.PointProEtaleSectionsExact
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Paper.ConstantModuleSectionProperties
import Mathlib.RingTheory.Flat.Tensor
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel

/-! # Unit normalization of point coefficient reduction

Source: Stacks Project, sites-cohomology.tex Tag 07A6; derived.tex Tags 0FND and 09T5;
sites-modules.tex Tags 093J and 093M; current blueprint integral-model proof, clause (4)
(blueprint: lem-trf-point-reduction-unit-normalization).

## Main statement

* `pointReductionUnitNormalization`: the canonical natural comparisons are uniquely
  characterized by the actual scalar-extension unit equation, in both coefficient cases.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The point-section reduction comparisons are uniquely fixed by the actual scalar units.
Source: Stacks 07A6, 0FND, 09T5, 093J, 093M; blueprint integral-model proof, clause (4)
(blueprint: lem-trf-point-reduction-unit-normalization).

Proof (the ten steps of the node):
1. Restriction leaves sections unchanged. Use the identity-on-elements comparison and
   the normalized ordinary and derived coefficient adjunctions. The adjunct of sections
   of the sheaf unit is the unique map satisfying the asserted unit equation.
   Uses: lem-pur-sheaf-ring-derived-coefficient-adjunction,
   lem-weil-point-proetale-sections-exact, def-pc-sheaf-restrict-scalars.
2. For integral reduction put t = uniformizer^(n+1). The DVR is Noetherian and its
   quotient has the free resolution [V --t--> V]. Completed constant-sheaf reduction
   gives the actual quotient projection. For finite reduction all ideals are powers
   of the uniformizer; constant exactness gives B'=B/tB, without asserting t injective.
   Uses: lem-weil-l-adic-extension-integers-dvr,
   lem-weil-pbc-standard-quotients-perfect, lem-weil-pbc-completed-constant-sheaf-reduction,
   lem-weil-pbc-constant-module-section-properties.
3. Balanced tensor identifies F tensor B' with F/tF. Exact sections preserve images
   and cokernels, giving Gamma(F)/t Gamma(F) = Gamma(F/tF) via the quotient-section map.
   Uses: def-pur-sheaf-tensor-product, lem-weil-point-proetale-sections-exact.
4. Resolve the integral object by a flat-term K-flat complex P. In the finite case
   good truncation and bounded-above flat replacement give such P bounded above.
   In both cases put C=Gamma(P); the sheaf reduction is represented by P/tP.
   Uses: lem-pc-kflat-resolution, lem-pc-kflat-bounded-flat-replacement,
   lem-pc-bounded-above-flat-kflat-site, lem-pur-derived-change-of-rings,
   lem-weil-point-proetale-sections-exact.
5. In the integral case resolve C by a flat-term K-flat Q. Multiplication by t is
   injective on C, Q and the acyclic cone W of Q to C, term by term.
   Uses: lem-pc-kflat-resolution, def-pc-flat-sheaf-modules,
   lem-pur-quasi-iso-cone-acyclic, def-weil-abstract-derived-category.
6. If dz=tw in W, injectivity gives dw=0. Write w=dv, then z-tv is a boundary.
   Thus W/tW is acyclic, so Q/tQ to C/tC is a quasi-isomorphism without bounds.
   Uses: lem-pur-quasi-iso-cone-acyclic.
7. In the finite case test every cyclic ideal (uniformizer^r) against Gamma(P^i).
   Exact sections and flatness give the requisite injection, including r=0 and r=b.
   The finitely generated ideal criterion makes C termwise flat; its bound makes it
   K-flat. Here take Q=C and the identity resolution.
   Uses: lem-weil-pbc-constant-module-section-properties, def-pc-flat-sheaf-modules,
   def-pur-sheaf-tensor-product, lem-weil-point-proetale-sections-exact,
   lem-weil-pbc-flat-fg-ideal-criterion, lem-pc-module-bounded-flat-kflat.
8. The resulting quotient-linear chain quasi-isomorphism Q/tQ to Gamma(P/tP)
   represents an isomorphism between the two derived reductions.
   Uses: lem-pc-derived-tensor-second-factor-functor, lem-pur-derived-change-of-rings,
   lem-weil-point-proetale-sections-exact.
9. Both normalized units are represented by x to 1 tensor x. The chain comparison
   sends its image to the actual quotient section, so its adjunct is exactly that of
   step 1. It satisfies the displayed unit equation for the fixed adjunctions.
   Uses: lem-pur-sheaf-ring-derived-coefficient-adjunction,
   lem-weil-point-proetale-sections-exact.
10. Naturality of units and of the Hom bijection gives naturality in derived morphisms.
    Injectivity of the Hom bijection gives uniqueness, independently of resolutions.
    Uses: lem-pur-sheaf-ring-derived-coefficient-adjunction.
-/
theorem pointReductionUnitNormalization (hl : l ≠ D.p) :
    (∀ n : ℕ, ∃! χ : pointReductionTensorSections D l E n ≅
          pointReductionSectionsTensor D l E n,
      Functor.whiskerLeft ((sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
          (pointIntegralSections l E D.k).mapDerivedCategory)
          (pointUnitIntegralModuleUnit l E n) ≫
        Functor.whiskerRight χ.hom (pointUnitIntegralDerivedRestriction l E n) =
      Functor.whiskerRight (Functor.whiskerLeft (sfIntegralConstructible l E (Spec (.of D.k))).ι
          (pointUnitIntegralSheafUnit D l E n))
          (pointIntegralSections l E D.k).mapDerivedCategory ≫
        Functor.whiskerLeft ((sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
          scalarReductionDerivedExtension l E (Spec (.of D.k)) n)
          (pointUnitIntegralDerivedSectionsRestrictionIso D l E n).hom) ∧
    ∀ (n j : ℕ) (hn : 1 ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n),
      ∃! χ :
          (pointFiniteReductionBoundedAbove D.k l E n).ι ⋙
              pointFiniteReductionSections D.k l E n ⋙
              pointFiniteReductionModuleTensor l E n j hjn ≅
            (pointFiniteReductionBoundedAbove D.k l E n).ι ⋙
              pointFiniteReductionSheafTensor D.k l E n j hjn ⋙
              pointFiniteReductionSections D.k l E j,
        Functor.whiskerLeft ((pointFiniteReductionBoundedAbove D.k l E n).ι ⋙
            pointFiniteReductionSections D.k l E n)
            (pointUnitFiniteModuleUnit l E n j hjn) ≫
          Functor.whiskerRight χ.hom (pointUnitFiniteDerivedModuleRestriction l E n j hjn) =
        Functor.whiskerRight (Functor.whiskerLeft (pointFiniteReductionBoundedAbove D.k l E n).ι
            (pointUnitFiniteSheafUnit D l E n j hjn))
            (pointFiniteReductionSections D.k l E n) ≫
          Functor.whiskerLeft ((pointFiniteReductionBoundedAbove D.k l E n).ι ⋙
            pointFiniteReductionSheafTensor D.k l E n j hjn)
            (pointUnitFiniteDerivedSectionsRestrictionIso D l E n j hjn).hom := by
  sorry

end WeilConjectures
