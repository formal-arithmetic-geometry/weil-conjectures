/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.AlgebraicGeometry.SfClassFullCohomologicalDimension
public import Sheaf.AlgebraicGeometry.SfFullCohomologicalDimension
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived
import Sheaf.Paper.ComparisonBoundZero
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.SfFullcdEtaleOrigin
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian

/-!
# Cohomological dimension and closure of the etale-origin coefficient class

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-fullcd-etale-origin,
order 1796 (blueprint: thm-sf-fullcd-used-class).

The class is the recorded essential image of comparison inverse image, in fixed-scalar
module coordinates. The canonical intrinsic realization and its derived comparison identify
these coordinates with modules over the constant ring sheaf. The positive level is `n + 1`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The class-restricted bound `2d`, uniform over the small pro-etale site of the target,
and inverse-image, extension and colimit closure of that same essential-image class.
The final two clauses retain constant coefficients and every etale-origin sheaf.
Source: Weil blueprint, order 1796; Stacks Tags 095T, 09A6, 099T, 099V and 09B1
(blueprint: thm-sf-fullcd-used-class).

Proof:
1. Choose an etale-origin witness F ≅ ν*G (def-sf-fullcd-used-class). The positive-level
coefficient quotient is finite (def-weil-l-adic-coefficient-extension), so a positive
integer annihilates 1 and hence every section of G. Its underlying abelian sheaf is torsion.
2. The absolute clause of thm-sf-fullcd-etale-origin gives vanishing above 2d on Y.
3. Properness is preserved under every base change (lem-weil-pbc-proper-base-change).
Proper maps are separated and finite type (def-weil-proper-morphism), hence qcqs:
finite type implies quasi-compact, and the closed-immersion diagonal is quasi-compact
(def-weil-finite-type-morphism, def-weil-closed-immersion,
def-weil-quasi-separated-morphism). No finite-type hypothesis on the site object is needed.
4. Apply prop-weil-pbc-comparison-direct-image to p and G[0]. Exact comparison pullback
commutes with cohomology, and its invertible unit reflects zero objects
(prop-weil-pbc-site-comparison-finite-level). Thus the etale higher direct images vanish.
5. Use lem-weil-pbc-etale-constant-ring-module-equivalence, retaining underlying abelian
sheaves, and lem-sbc-higher-direct-image-forget-comparison. Proper base change for the
torsion sheaf G (thm-weil-pbc-bounded-below) gives vanishing after every V → Y, because
inverse image is exact (prop-weil-pbc-inverse-image-exact). Module pullback commutes with
forgetting (lemma-weil-pbc-etale-pullback-forget-modules); exact faithful forgetting
reflects zero objects (lem-weil-pbc-module-sheaves-colimits-forgetful).
6. Pullback commutes with comparison (lem-weil-pbc-comparison-pullback). Apply the qcqs
comparison-direct-image theorem to p_V, then exactness of comparison pullback to the
vanishing in step 5. This gives the relative clause at the unchanged bound 2d.
The canonical realization identifies this with the intrinsic FullCD clauses restricted
to the class (def-weil-full-cohomological-dimension).
7. For h:T' → T, the comparison-pullback isomorphism carries h*ν*G to ν*h*G;
etale module inverse image exists and is exact (prop-weil-pbc-inverse-image-modules-exact).
This supplies the new origin witness.
8. For an extension 0 → ν*G' → F → ν*G'' → 0, use enough injectives in module sheaves
(lem-pur-ringed-site-grothendieck-abelian, lem-sp-grothendieck-enough-injectives).
The long exact sequence (lem-weil-pbc-derived-functor-long-exact), left exactness of ν_*,
and prop-sf-comparison-bound-zero give 0 → G' → ν_*F → G'' → 0.
9. Pull this sequence back by exact ν*. The counit compares it to the original sequence.
Its end maps are inverse to the pulled-back units by the adjunction triangle identities
(def-weil-pbc-site-comparison-morphism). The short five lemma
(lem-weil-pbc-short-five-lemma) makes the middle counit invertible, witnessing origin of F.
10. For a diagram of origin sheaves, the counits ν*ν_*H_j → H_j are isomorphisms,
by the unit isomorphism, triangle identities and counit naturality. They form a natural
isomorphism of diagrams. Take the etale colimit of ν_*H and use preservation of colimits
by the left adjoint ν* (lem-weil-pbc-left-adjoint-preserves-colimits) to obtain an origin
witness for the pro-etale colimit. This includes the empty diagram.
For arbitrary index universes, one need not assume an etale colimit exists: origin
objects B are precisely those for which Hom(B, ε_Z) is bijective for every counit
ε_Z : ν*ν_*Z → Z. One direction follows from adjunction and the invertible unit.
For the converse, surjectivity at Z = B gives a section s of ε_B; injectivity of
Hom(ν*ν_*B, ε_B) gives ε_B followed by s equal to the identity, so ε_B is invertible.
The colimit universal property carries these Hom bijections from every H_j to its
colimit, proving origin for every colimit cocone quantified in the statement.
11. The constant coefficient module sheaf represents global sections: a linear map out
of it is determined by the image of 1. Comparison adjunction identifies its pullback
with the pro-etale constant module, since restriction retains the terminal scheme.
Every etale-origin sheaf is in the class by the defining essential-image witness. -/
theorem sfFullcdUsedClass
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (p : X ⟶ Y) [p.IsOver (Spec (CommRingCat.of D.k))] [IsProper p]
    (d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    sfClassFullCohomologicalDimension p (Padic.coefficientExtensionRing l E (n + 1))
        (2 * d) ∧
    (∀ (T T' : Over (Spec (CommRingCat.of D.k)))
        [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
        [LocallyOfFiniteType T'.hom] [QuasiCompact T'.hom]
        (h : T' ⟶ T)
        (F : Sheaf (ProEt.topology T.left) (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))),
      (comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) T.left).essImage F →
        (comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) T'.left).essImage
          ((upperStar (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) h.left).obj F)) ∧
    ∀ (T : Over (Spec (CommRingCat.of D.k)))
        [LocallyOfFiniteType T.hom] [QuasiCompact T.hom],
      (comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
          T.left).essImage.IsClosedUnderExtensions ∧
      (∀ (J : Type w) [Category.{v} J]
          (H : J ⥤ Sheaf (ProEt.topology T.left) (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))))
          (c : Cocone H), IsColimit c →
        (∀ j : J, (comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) T.left).essImage
            (H.obj j)) →
          (comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) T.left).essImage c.pt) ∧
      (comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) T.left).essImage
        ((constantSheaf (ProEt.topology T.left) (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))).obj
          (ModuleCat.of
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ∧
      ∀ F : Sheaf (ProEt.topology T.left) (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))),
        (∃ G : Sheaf T.left.smallEtaleTopology (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))),
          Nonempty ((comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) T.left).obj G ≅ F)) →
            (comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) T.left).essImage F := by
  sorry

end AlgebraicGeometry.ProEtale
