/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W8
-/
module

public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.DerivedNakayamaResolution
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Sheaf.Paper.ModuleRingedToposDerivedComparison

/-! # Integral direct image and the canonical finite reduction

Source: Stacks 099N and blueprint direct-image-limits, finite-projection and completion clauses.
(blueprint: lem-sfb-internal-integral-direct-image-limits).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Direct image preserves canonical integral completeness and its specified residue mate
is invertible, without a finiteness or properness hypothesis on the scheme morphism.
Source: Stacks 099N; blueprint prop-weil-pbc-direct-image-limits, finite-reduction and
completion-unit clauses.
(blueprint: lem-sfb-internal-integral-direct-image-limits).

Proof: pass from internal modules to sectionwise modules by the exact section-action
 equivalence. The integral coefficient limit identifies the ring with the completed adic
 ring for the lifted ring of integers and the principal uniformizer ideal. Quotient
 isomorphisms are induced by ULift.down and fix all scalar representatives. Each quotient
 is finite and perfect, by its two-term finite free resolution; the residue is torsion.
 These data form the adic coefficient datum of CompletedDirectImageLimits.
 Normalize the finite restriction squares by the identity on underlying sections. Their
 derived left-adjoint comparisons identify the actual finite reductions. The geometric
 adjunction comparisons identify the inverse scalar mate displayed here with the
 coefficient reduction/pullback isomorphism chi. In particular it is invertible.
 The finiteProjection_isIso theorem then identifies its geometric mate, computed as
 the residue homEquiv of inverse chi followed by reduction of the integral counit,
 with the invertible finite projection. This equality follows by the scalar and
 geometric adjunction Hom bijections; it retains the quotient action and fixes the
 displayed morphism rather than choosing an arbitrary isomorphism of cones.
 For completeness, use all positive finite projections, with their quotient transitions.
 Exact equivalences transport products and the signed Roos cone. The theorem push_complete
 applies to the resulting reduction tower. The completion-unit equation in
 towerProjection_properties identifies the transported map with the canonical
 augmentation used by IsDerivedComplete. Thus completeness of K implies completeness
 of its direct image. This argument applies to unbounded complexes, arbitrary scheme
 morphisms, empty schemes and zero complexes. -/
theorem internal_integral_direct_image_limits
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    let χ :
        (CondensedRing.upperStar (DerivedNakayama.integerRing l E) j).mapDerivedCategory ⋙
            AdicCompletion.derivedReduction l E U 0 ⟶
          AdicCompletion.derivedReduction l E X 0 ⋙
            (CondensedRing.upperStar (DerivedNakayama.quotientRing l E 1) j).mapDerivedCategory :=
      ((mateEquiv
          (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X 0))
          (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E U 0))).symm
            (TwoSquare.mk _ _ _ _
              (CondensedRing.derivedComapUpperStarIso (DerivedNakayama.reductionRing l E 1) j).inv)
          ).natTrans
    ∃ hχ : IsIso χ, letI := hχ; ∀ K : DerivedCategory (AdicCompletion.Modules l E U),
      (IsDerivedComplete l E U K → IsDerivedComplete l E X
        ((CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) j).obj
          K)) ∧
      IsIso (((CondensedRing.derivedUpperStarLowerStarAdjunction
        (DerivedNakayama.quotientRing l E 1) j).ofNatIsoLeft
          (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (DerivedNakayama.quotientRing l E 1) j)).homEquiv _ _
        (inv (χ.app ((CondensedRing.moduleObjectDerivedPushforward
            (DerivedNakayama.integerRing l E) j).obj K)) ≫
          (AdicCompletion.derivedReduction l E U 0).map
            (((CondensedRing.derivedUpperStarLowerStarAdjunction
              (DerivedNakayama.integerRing l E) j).ofNatIsoLeft
                (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
                  (DerivedNakayama.integerRing l E) j)).counit.app K))) := by
  sorry

end AlgebraicGeometry.ProEtale
