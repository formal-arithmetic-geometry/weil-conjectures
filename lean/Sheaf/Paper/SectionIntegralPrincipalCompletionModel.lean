/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module
public import Sheaf.Paper.StrictCompletionRestrictionData
public import Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel

/-! # Comparing the integral section presentation to principal quotient completion
Source: Bhatt--Scholze, Lemma 3.4.12, Proposition 3.5.1; Stacks Tags 06YS, 0941.
-/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local instance 10000]
  AlgebraicGeometry.ProEtale.StrictCompletionRestriction.smallSiteLocalEquivalences
namespace AlgebraicGeometry.ProEtale.StrictCompletionRestriction

/-- The normalized integral section presentation and principal quotient completion have
exactly the same complete locus, with a regular scalar on the actual section-ring sheaf.

Source: Bhatt--Scholze, Lemma 3.4.12 and Proposition 3.5.1; Stacks Tags 06YS and 0941.
(blueprint: lem-sfb-section-integral-principal-completion-model)

Proof: Unpack IsSectionIntegral. Its scalar is the sectionwise action of the pulled-back
uniformizer from its canonical cone datum. Pullback regularity and the section-action
exact equivalence show that multiplication by this section is monic. Its positive-power
cokernels are the specified finite quotient ring sheaves: the coefficient resolution and
its section-action comparison identify both quotient projections and consecutive quotient
maps. Principal quotient completion has a universal Model, computed on K-flat complexes.
The SectionReductionModels tensor comparisons identify its levels with those of the
integral presentation on each K-flat representative. Their unit and step equations give
one strict map of augmented towers. Product projections identify the Roos comparison on
both coordinates, with the shifted coordinate zero, so it carries the specified unit to
the quotient unit. K-flat computation makes that comparison invertible. Every derived
object admits a K-flat representative; naturality transports the invertibility equivalence
along its representative isomorphism. The construction also applies to zero rings,
empty schemes, and torsion complexes; regularity is imposed only on the coefficient ring.
-/
theorem section_integral_principal_completion_model
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (T : Presentation.{u + 2, u + 1, u + 1}
      (ModuleObjectRingedComparison.Modules (DerivedNakayama.integerRing l E) X))
    (hT : IsSectionIntegral l E X T) :
    ∃ (a : (SheafOfModules.unit
        (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X)
        (ModuleObjectRingedComparison.ring (DerivedNakayama.integerRing l E) X))).sections)
      (_ha : Mono (CategoryTheory.globalSectionMultiplication.{u + 1, u, u + 1}
        (ModuleObjectRingedComparison.ring (DerivedNakayama.integerRing l E) X) a))
      (F : PrincipalQuotientCompletion.Model.{u + 1, u, u + 1, u + 1}
        (ModuleObjectRingedComparison.ring (DerivedNakayama.integerRing l E) X) a),
      ∀ K : DerivedCategory
          (ModuleObjectRingedComparison.Modules (DerivedNakayama.integerRing l E) X),
        IsIso (T.unit.app K) ↔ IsIso (F.unit.app K) := by sorry

end AlgebraicGeometry.ProEtale.StrictCompletionRestriction
