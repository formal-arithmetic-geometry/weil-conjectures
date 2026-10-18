/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.AlgebraicGeometry.SupportTriangleCompatibility
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.PurSupportExact
import Sheaf.AlgebraicGeometry.EtaleComparison
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Localization for the ambient bounded-below exceptional inverse image

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
`lem-pur-support-localization-triangle` (blueprint: lem-pur-support-localization-triangle).
The categories are all constant-coefficient module sheaves, as in
`def-pur-flasque-support`; there is no constructibility condition. The right derived
functors below are the existing ordinary injective-derived functors on `D⁺`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X Z U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X)
  [hs : IsClosedImmersion s] [hj : IsOpenImmersion j] [hqc : QuasiCompact j]
  (hPair : IsCompl (Set.range s) (Set.range j))

/-- The termwise-induced closed direct image on D⁺, using its exactness, rather than
an independently chosen functor. Source: blueprint lem-pur-support-localization-triangle
(blueprint: lem-pur-support-localization-triangle). -/
noncomputable def supportClosedDerivedPlus :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  letI := preservesFiniteColimits_lowerStar_of_isCompl (R := Λ) s j hPair
  (lowerStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus

/-- A model in the stated class is K-injective.
Source: Stacks Tag 070J; blueprint lem-pur-support-localization-triangle, step 1
(blueprint: lem-pur-support-localization-triangle).
Proof: choose a lower bound from hI. Its terms are injective by hI. Apply
CochainComplex.isKInjective_of_injective with that bound. -/
theorem supportModelKInjective (I : SupportComplex Λ X)
    (hI : IsSupportInjectiveModel Λ I) : I.IsKInjective := by
  sorry

include hj in
/-- Open restriction of a bounded below injective model is K-injective.
Source: Stacks Tag 08FI; blueprint lem-pur-support-localization-triangle, step 4
(blueprint: lem-pur-support-localization-triangle).
Proof: identify open inverse image with the slice restriction by
lem-weil-proetale-weakly-etale-localization. Its exact left adjoint, extension by
zero, implies that it preserves injectives (lem-weil-pbc-proetale-restriction-injectives).
It preserves the lower bound since it is additive. Apply Stacks Tag 070J. -/
theorem supportOpenModelKInjective (I : SupportComplex Λ X)
    (hI : IsSupportInjectiveModel Λ I) :
    CochainComplex.IsKInjective
      (((upperStar (ModuleCat.{u + 1} Λ) j).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  sorry

/-- The canonical computation of Rs^! on the chosen model, normalized by the derived
functor unit and by the bounded/unbounded comparison; no model isomorphism is chosen.
Source: blueprint lem-pur-support-localization-triangle, steps 1 and 3
(blueprint: lem-pur-support-localization-triangle). -/
noncomputable def supportShriekModelComparison
    (I : SupportComplex Λ X) (hI : IsSupportInjectiveModel Λ I)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (eB : DerivedCategory.Q.obj I ≅ K.obj) :
    DerivedCategory.Q.obj
        (((finiteClosedUpperShriek Λ s j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      ((finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlus.obj K).obj :=
  letI := supportModelKInjective Λ I hI
  ((finiteClosedUpperShriek Λ s j).rightDerivedFunctorObjQIso I).symm ≪≫
    (finiteClosedUpperShriek Λ s j).rightDerivedFunctor.mapIso eB ≪≫
    ((finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlusCompatibility.app K).symm

/-- The canonical first-term comparison, using termwise exact s_* and the preceding
unit-normalized computation of Rs^!.
Source: blueprint lem-pur-support-localization-triangle, step 5
(blueprint: lem-pur-support-localization-triangle). -/
noncomputable def supportFirstModelComparison
    (I : SupportComplex Λ X) (hI : IsSupportInjectiveModel Λ I)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (eB : DerivedCategory.Q.obj I ≅ K.obj) :
    DerivedCategory.Q.obj (supportedSectionsComplex Λ s j hPair I) ≅
      ((supportClosedDerivedPlus Λ s j hPair).obj
        ((finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlus.obj K)).obj :=
  letI := preservesFiniteColimits_lowerStar_of_isCompl (R := Λ) s j hPair
  ((lowerStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryFactors.app
    (((finiteClosedUpperShriek Λ s j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).symm ≪≫
    (lowerStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategory.mapIso
      (supportShriekModelComparison Λ s j I hI K eB) ≪≫
    ((lowerStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlusCompatibility.app
      ((finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlus.obj K)).symm

/-- The canonical third-term comparison, using injectivity after open restriction,
the derived functor unit, and the ordinary bounded/unbounded comparison for Rj_*.
Source: blueprint lem-pur-support-localization-triangle, steps 4 and 5
(blueprint: lem-pur-support-localization-triangle). -/
noncomputable def supportThirdModelComparison
    (I : SupportComplex Λ X) (hI : IsSupportInjectiveModel Λ I)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (eB : DerivedCategory.Q.obj I ≅ K.obj) :
    DerivedCategory.Q.obj (supportCComplex Λ j I) ≅
      ((lowerStar (ModuleCat.{u + 1} Λ) j).rightDerivedFunctorPlus.obj
        ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K)).obj :=
  letI := supportOpenModelKInjective Λ j I hI
  ((lowerStar (ModuleCat.{u + 1} Λ) j).rightDerivedFunctorObjQIso
    (((upperStar (ModuleCat.{u + 1} Λ) j).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I)).symm ≪≫
    (lowerStar (ModuleCat.{u + 1} Λ) j).rightDerivedFunctor.mapIso
      (((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryFactors.app I).symm ≪≫
        (upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.mapIso eB ≪≫
        ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlusCompatibility.app K).symm) ≪≫
    ((lowerStar (ModuleCat.{u + 1} Λ) j).rightDerivedFunctorPlusCompatibility.app
      ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K)).symm

/-- On every bounded below injective model the specified cone quotient is invertible,
and its specified triangle is distinguished.
Source: Stacks Tag 0152; blueprint lem-pur-support-localization-triangle, step 5
(blueprint: lem-pur-support-localization-triangle).
Proof: injective terms are flasque for the open restriction. Indeed the free module
sheaf on the open fibre product embeds in the free module sheaf on each test object;
an arrow to an injective extends across this embedding. The open unit is therefore
surjective on sections and epic. Its kernel is canonically s_*s^!I via the supported
unit comparison. Degreewise this gives the short exact sequence A→I→C of
lem-pur-support-exact. The explicit cone-to-quotient map q is a quasi-isomorphism
by lem-pc-cone-short-exact-quasi-iso, hence Q(q) is invertible. Transporting the
mapping-cone distinguished triangle along it gives precisely supportModelTriangle,
whose boundary is the negative shifted projection after Q(q) inverse. -/
theorem supportInjectiveConeDistinguished (I : SupportComplex Λ X)
    (hI : IsSupportInjectiveModel Λ I) :
    (supportModelSequence Λ s j hPair I).ShortExact ∧
      ∃ hq : IsIso (DerivedCategory.Q.map (supportConeQuotient Λ s j hPair I)),
        supportModelTriangle Λ s j hPair I hq ∈
          distTriang (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) := by
  sorry

/-- The same specified cone starts from an actual bounded below input complex and
an injective-resolution arrow, rather than only an abstract derived object.
Source: Stacks Tags 013K, 070J and 0152; blueprint
lem-pur-support-localization-triangle, steps 1 and 5
(blueprint: lem-pur-support-localization-triangle).
Proof: enough injectives gives a bounded below injective representative I of QK.
K-injectivity and the derived Hom bijection lift the representing isomorphism to
r:K→I. Since Qr is invertible, r is a quasi-isomorphism. Apply the specified cone
construction and supportInjectiveConeDistinguished. -/
theorem supportResolutionCone (K : SupportComplex Λ X) (hK : ∃ n : ℤ, K.IsStrictlyGE n) :
    ∃ (I : SupportComplex Λ X) (r : K ⟶ I),
      IsSupportInjectiveModel Λ I ∧ QuasiIso r ∧
      ∃ hq : IsIso (DerivedCategory.Q.map (supportConeQuotient Λ s j hPair I)),
        supportModelTriangle Λ s j hPair I hq ∈
          distTriang (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) := by
  sorry

/-- The injective cone is the ambient localization triangle with its actual adjunction
arrows. Rs^! is the right derived functor of the recorded sheaf supported-kernel functor.
Any other right adjoint to this same s_* on D⁺ has the unique counit-compatible
identification. The final conjunct gives resolution independence, derived functoriality,
and etale base change of this specified triangle, including the boundary.

Source: blueprint lem-pur-support-localization-triangle; Stacks Tags 013K, 070J,
05TI, 09AA, 09AH, 09AG, 09BN, 08FI, 0152 and 015F
(blueprint: lem-pur-support-localization-triangle).

Proof, following the eight steps of the node:
1. The module-sheaf categories on the compatible small sites are Grothendieck abelian,
hence have enough injectives. Every D⁺ object has a bounded below injective model I.
The derived Hom theorem realizes its comparison isomorphism by a quasi-isomorphism
from any bounded below input complex. Right derivation of s^! is computed by s^!I.
2. A map s_*N→M has zero open restriction. It factors uniquely through the kernel
G_Z(M) of the open unit. The canonical comparison G_Z(M)≅s_*s^!M and full
faithfulness of s_* give s_*⊣s^!, with counit the specified inverse-comparison inclusion.
3. Exactness of s_* makes s^! preserve injectives. The termwise adjunction descends
to homotopy categories. Derived Hom into the bounded below injective models then
gives s_*⊣Rs^! on D⁺, with that same counit. Uniqueness of a right adjoint gives
the displayed unique natural isomorphism with any other right adjoint.
4. Open restriction preserves injectives and lower bounds. Thus j^*I computes j^*K,
and j_*j^*I computes Rj_*j^*K. The derived open unit is its termwise unit.
The bounded-below and unbounded right derived direct images agree on these models.
5. Apply supportInjectiveConeDistinguished. Its three terms represent s_*Rs^!K,
K, and Rj_*j^*K. Their canonical comparison isomorphisms carry the first two
arrows to the exceptional counit and open unit, respectively.
6. Every derived morphism between injective models has a unique homotopy class of
chain representatives. Apply the three additive functors to such a representative.
Naturality gives a map of the short exact sequences; the diagonal cone map satisfies
q' t = c q and p' t = a[1] p. Inverting q and q' gives the boundary square.
Additive functors preserve homotopies. Identity and composition follow componentwise;
comparison maps representing the identity are invertible and satisfy the cocycle law.
7. Etale inverse image is restriction to the localized site and preserves injectives.
On a test object V over X', the open direct images both evaluate at V×_X U.
The canonical base-change mate identifies these evaluations and their open units.
Exact pullback identifies their kernels, and hence their first terms via the supported
unit comparisons. This gives the specified short-complex isomorphism.
8. Exact pullback carries the cone differential, quotient and negative projection
to those of the primed cone. It preserves the inverse of Q(q). Hence the full
triangle isomorphism has the specified three components and boundary square.
Comparison with any other injective model uses step 6. -/
theorem supportLocalizationTriangle :
    ∃ adj : supportClosedDerivedPlus Λ s j hPair ⊣
        (finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlus,
      (∀ (G : DerivedCategory.Plus
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ⥤
          DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)))
        (adj' : supportClosedDerivedPlus Λ s j hPair ⊣ G),
        ∃! e : (finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlus ≅ G,
          ∀ K : DerivedCategory.Plus
              (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)),
            (supportClosedDerivedPlus Λ s j hPair).map (e.hom.app K) ≫
            adj'.counit.app K = adj.counit.app K) ∧
      (∀ K : DerivedCategory.Plus
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)),
        ∃ (I : SupportComplex Λ X) (hI : IsSupportInjectiveModel Λ I)
          (hq : IsIso (DerivedCategory.Q.map (supportConeQuotient Λ s j hPair I)))
          (eB : DerivedCategory.Q.obj I ≅ K.obj),
          supportModelTriangle Λ s j hPair I hq ∈
              distTriang (DerivedCategory
                (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) ∧
          DerivedCategory.Q.map (supportModelSequence Λ s j hPair I).f ≫ eB.hom =
            (supportFirstModelComparison Λ s j hPair I hI K eB).hom ≫
              DerivedCategory.Plus.ι.map (adj.counit.app K) ∧
          DerivedCategory.Q.map (supportModelSequence Λ s j hPair I).g ≫
              (supportThirdModelComparison Λ j I hI K eB).hom =
            eB.hom ≫ DerivedCategory.Plus.ι.map
              ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) j).unit.app K)) ∧
      supportTriangleMeaning Λ s j hPair := by
  sorry

end AlgebraicGeometry.ProEtale
