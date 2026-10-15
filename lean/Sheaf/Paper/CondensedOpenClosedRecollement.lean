/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import Sheaf.AlgebraicGeometry.ProEtaleOperations
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.Algebra.Homology.FunctorialBoundedInjectiveResolution

import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.Paper.ProfinitePointPullback
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse
import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction

/-!
# Recollement with arbitrary condensed coefficients

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, (3.3), (3.4),
Lemma 3.4 and the proof of Lemma 5.3(2); Stacks, Tags 09AH, 09BM, 09AA, 09BN
(blueprint: lem-weil-pbc-condensed-open-closed-recollement).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Open-closed recollement on ordinary bounded below derived categories.
Source: Hemo--Richarz--Scholbach, (3.3), (3.4), Lemma 3.4 and Lemma 5.3(2);
Stacks, Tags 09AH, 09BM, 09AA, 09BN
(blueprint: lem-weil-pbc-condensed-open-closed-recollement).
Proof:
1. Identify the coefficients by the monoidal composition comparison. The ringed
open-closed theorem gives exact closed pushforward, its invertible counit and the
zero open restriction. Open site localization gives exact extension by zero and
its adjunction. Both inverse images are exact and left adjoint to direct image.
2. The kernel of F → j_*j^*F has zero open restriction, so the closed inverse
image of that kernel is right adjoint to i_*. Every map i_*G → F factors uniquely
through the kernel; use full faithfulness to obtain the adjunction. It is additive
and left exact, and preserves injectives because i_* is exact.
3. Use functorial injective embeddings and bounded injective resolutions. For a
common cohomological bound a, first take the canonical good truncation at a, then
resolve; this is natural in chain maps and keeps all terms below a zero.
4. Descend exact functors termwise and right derive the two left exact functors.
Derived adjunction gives the four displayed adjunctions. On injective complexes
zero below a the two right derived images are still zero below a. The closed
counit stays invertible, proving full faithfulness.
5. Apply the sheaf short exact sequence degreewise. The generic complex short
exact sequence triangle gives the first triangle with its counit and unit maps.
6. On a functorial injective model form Cone(I → j_*j^*I)[-1]. Its open restriction
vanishes since the open counit is invertible, hence the first triangle identifies
it with a closed pushforward.
7. Hom from i_*B into the cone triangle and its rotation, in degrees zero and
minus one, identifies this fibre with i_*Ri^!K, by uniqueness of right adjoints.
This identifies its first arrow with the exceptional counit.
8. Functorial cones descend through homotopy equivalences of injective models.
Resolution comparisons supply shift compatibility; units and counits come from
termwise adjunctions and respect shifts. The connecting arrows use the standard
shift signs of distinguished triangles.
9. The two inverse images preserve small colimits by their sheaf adjunctions.
The common-bound resolutions in step 3 compute both right derived functors.

DAG inputs by step: (1) lem-weil-pbc-profinite-point-pullback,
lem-weil-pbc-proetale-ringed-open-closed, lem-weil-proetale-weakly-etale-localization,
lem-pur-site-restriction-module-adjunction-exact, def-weil-pbc-proetale-operations;
(2) lem-weil-pbc-proetale-ringed-open-closed and def-weil-pbc-proetale-operations;
(3) prop-pur-kinjective-resolutions-exist,
lem-weil-pbc-grothendieck-functorial-injective-embedding,
lem-weil-pbc-functorial-bounded-injective-resolution,
lem-weil-pbc-dplus-injective-representative;
(4) lem-weil-pbc-exact-functor-derived-factorization,
lem-weil-pbc-kinjective-total-derived, lem-pc-pre-derived-adjoint-functors-general;
(5) lem-weil-pbc-complex-ses-triangle;
(6) lem-weil-pbc-right-adjoint-preserves-kinjective, lem-weil-pbc-kinjective-hom-derived;
(7) lem-weil-pbc-hom-into-triangle-exact and the derived adjunction from (4);
(8) lem-pc-right-derived-functor-triangulated, lem-sf-triangle-morphism-iso;
(9) def-weil-pbc-proetale-operations and the resolution inputs of (3). -/
theorem condensed_open_closed_recollement
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ) :
    Exists fun [hclosed : PreservesFiniteColimits (lowerStar Λ i)] ↦
    PreservesFiniteLimits (upperStar Λ j) ∧
    PreservesFiniteColimits (upperStar Λ j) ∧
    PreservesFiniteLimits (upperStar Λ i) ∧
    PreservesFiniteColimits (upperStar Λ i) ∧
    PreservesFiniteLimits (openImmersionLowerShriek Λ j) ∧
    PreservesFiniteColimits (openImmersionLowerShriek Λ j) ∧
    PreservesFiniteLimits (lowerStar Λ i) ∧
    PreservesColimitsOfSize.{u + 1, u + 1} (upperStar Λ j) ∧
    PreservesColimitsOfSize.{u + 1, u + 1} (upperStar Λ i) ∧
    (lowerStar Λ i).Full ∧ (lowerStar Λ i).Faithful ∧
    Nonempty (lowerStar Λ i ⋙ upperStar Λ i ≅ 𝟭 _) ∧
    ∃ (ishriek : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)),
      Exists fun [hadd : ishriek.Additive] ↦
      Exists fun [hleft : PreservesFiniteLimits ishriek] ↦
      ∃ (ash : lowerStar Λ i ⊣ ishriek)
      (aj : D+(openImmersionLowerShriek Λ j) ⊣ D+(upperStar Λ j))
      (bj : D+(upperStar Λ j) ⊣ (lowerStar Λ j).rightDerivedFunctorPlus)
      (ai : D+(upperStar Λ i) ⊣ D+(lowerStar Λ i))
      (bi : D+(lowerStar Λ i) ⊣ ishriek.rightDerivedFunctorPlus),
      Exists fun [hjshift : (lowerStar Λ j).rightDerivedFunctorPlus.CommShift ℤ] ↦
      Exists fun [hishift : ishriek.rightDerivedFunctorPlus.CommShift ℤ] ↦
      aj = derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus Λ j ∧
      bj = derivedUpperStarLowerStarAdjunctionPlus Λ j ∧
      ai = (upperStarLowerStarAdjunction Λ i).mapDerivedCategoryPlusAdjunction ∧
      bi = ash.derivedPlus ∧
      aj.CommShift ℤ ∧ bj.CommShift ℤ ∧ ai.CommShift ℤ ∧ bi.CommShift ℤ ∧
      (D+(lowerStar Λ i)).Full ∧ (D+(lowerStar Λ i)).Faithful ∧
      (∀ K, IsIso (ai.counit.app K)) ∧
      (∀ (K : DerivedCategory.Plus
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
        (a : ℤ), K.IsGE a → (ishriek.rightDerivedFunctorPlus.obj K).IsGE a) ∧
      ∃ (δ : D+(upperStar Λ i) ⋙ D+(lowerStar Λ i) ⟶
          D+(upperStar Λ j) ⋙ D+(openImmersionLowerShriek Λ j) ⋙ shiftFunctor _ (1 : ℤ))
        (ε : D+(upperStar Λ j) ⋙ (lowerStar Λ j).rightDerivedFunctorPlus ⟶
          ishriek.rightDerivedFunctorPlus ⋙ D+(lowerStar Λ i) ⋙ shiftFunctor _ (1 : ℤ)),
        NatTrans.CommShift δ ℤ ∧ NatTrans.CommShift ε ℤ ∧
        (∀ K, Triangle.mk (aj.counit.app K) (ai.unit.app K) (δ.app K) ∈ distTriang _) ∧
        (∀ K, Triangle.mk (bi.counit.app K) (bj.unit.app K) (ε.app K) ∈ distTriang _) ∧
        (∀ a : ℤ, ∃
          (I : CochainComplex.Plus
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ⥤
            CochainComplex.Plus
              (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
          (α : CochainComplex.Plus.ι _ ⟶ I ⋙ CochainComplex.Plus.ι _),
          (∀ K, K.obj.IsGE a → QuasiIso (α.app K)) ∧
          (∀ K, (I.obj K).obj.IsStrictlyGE a) ∧
          (∀ (K) (n : ℤ), Injective ((I.obj K).obj.X n)) ∧
          (∀ K, IsIso (ishriek.rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient _).obj (I.obj K))))) ∧
        (∀ a : ℤ, ∃
          (I : CochainComplex.Plus
            (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) ⥤
            CochainComplex.Plus
              (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)))
          (α : CochainComplex.Plus.ι _ ⟶ I ⋙ CochainComplex.Plus.ι _),
          (∀ K, K.obj.IsGE a → QuasiIso (α.app K)) ∧
          (∀ K, (I.obj K).obj.IsStrictlyGE a) ∧
          (∀ (K) (n : ℤ), Injective ((I.obj K).obj.X n)) ∧
          (∀ K, IsIso ((lowerStar Λ j).rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient _).obj (I.obj K))))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
