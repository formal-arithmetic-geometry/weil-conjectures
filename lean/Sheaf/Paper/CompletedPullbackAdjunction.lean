/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Paper.ConstantCompletionEquivalence
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import Sheaf.CategoryTheory.RingedKoszulCompletionReflector
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
import Sheaf.Paper.LocalHomTowerCriterion
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Sheaf.CategoryTheory.RingedToposMorphism
import Sheaf.CategoryTheory.RingedSiteCompleteElementsIdeal
import Sheaf.CategoryTheory.LevelwiseKInjectiveTowerImage
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.WeilCompletedTensorReflector
import Sheaf.Targets.SliceRestrictionStrictDerivedLimit

/-!
# Completed pullback is left adjoint to direct image

Source: Stacks Project, `proetale.tex`, Tags 099M and 099N (1), (2), and
`algebraization.tex`, Tag 099K
(blueprint: lem-sp-completed-pullback-adjunction).

All coefficient sheaves, local-completeness predicates and quotient-tower completions
are the constructions of `ConstantCompletionEquivalence`. Positive exponents are n+1.
The existential witnesses below specify geometric module direct image and its total
right derived functor by their underlying maps and universal comparisons. In particular
no preservation or adjunction on complete objects is an assumption.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ConstantCompletion

/-- For arbitrary small sites and Noetherian coefficients, quotient-tower completion is
left adjoint to inclusion of the locally derived-complete objects. Derived direct image
preserves these objects, and completed inverse image is its left adjoint. The ordinary
module Hom equivalence is normalized by the given geometric adjunction and insertion
of 1 in scalar extension. Its derived version is normalized on K-flat source and
K-injective target representatives. Finally the complete Hom equivalence is exactly
completion-unit precomposition followed by this ordinary derived Hom equivalence.

Source: Stacks Project, Tags 099M, 099N (1), (2), 099K, and 07A6
(blueprint: lem-sp-completed-pullback-adjunction).

Proof:
1. Apply lem-weil-pbc-ringed-topoi-module-adjunction to the geometric adjunction and
   its canonical identification of constant rings. Its tensor pullback is `pull F
   (constantMap F A)`. Inverse image is exact. Functorial K-injective resolutions
   (prop-pur-kinjective-resolutions-exist) and preservation of K-injectives by the
   right adjoint (lem-weil-pbc-right-adjoint-preserves-kinjective) give the total
   derived direct image. The termwise adjunction descends to the ordinary derived
   adjunction, by lem-weil-pbc-kinjective-hom-derived. This yields its normalization.
2. Noetherianness gives finitely many ideal generators, including the empty list for
   I=0. Apply lem-weil-pbc-ringed-koszul-completion-reflector on both sites. The
   unit-preserving Koszul/quotient comparison of
   lem-weil-pbc-constant-completion-equivalence identifies the reflectors with the
   actual strict quotient-tower completions and their specified units.
3. For any scalar a form the constant strict multiplication tower on a representative
   of H. Exact slice restriction has an exact left adjoint by
   lem-pur-site-restriction-module-adjunction-exact. Levelwise restriction therefore
   preserves K-injective tower complexes and commutes with ordinary inverse limits.
   Consequently it commutes with the strict derived limit. By
   lem-weil-pbc-local-hom-tower-criterion, vanishing of that multiplication-tower
   limit is equivalent to the local RHom vanishing condition on every slice. The
   converse is detected by the cohomology sheaves on all slice terminal objects.
4. For complete N apply lem-weil-ringed-tower-pushforward-limit-comparison to each
   generator's multiplication tower. On a K-injective representative J, comparison
   with a K-injective tower resolution is levelwise a quasi-isomorphism between
   K-injectives: evaluation has the exact left adjoint supported at positions up to
   n. Such maps are homotopy equivalences, so additive direct image preserves them.
   This identifies the whole image tower, including scalar transitions, with the
   multiplication tower of RF(N). Its limit vanishes. Step 3 and
   lem-weil-pbc-ringed-derived-complete-elements-ideal give vanishing for every local
   section of I times the constant ring sheaf. Thus RF preserves completeness.
5. For complete M,N, precompose a map completion(LF(M)) → N with the completion
   unit, then use the ordinary derived Hom equivalence. Both bijections are natural;
   fullness identifies them with the actual Hom sets of the complete categories.
6. The resulting unit is the ordinary unit followed by RF of the completion unit.
   Its counit is the unique extension of the ordinary counit across the completion
   unit. Naturality follows from the two Hom bijections; their inverse identities
   give the triangle identities. The last equation fixes precisely these choices. -/
theorem completedPullbackAdjunction
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology E)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (V : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : L ⊣ V) [PreservesFiniteLimits L] :
    ∃ (F : InverseImageData L)
      (G : Mod (constant JD A) ⥤+ Mod (constant JC A))
      (eG : G.obj ⋙ underlying (constant JC A) ≅ underlying (constant JD A) ⋙ V)
      (aM : pull F (constantMap F A) ⊣ G.obj),
      (∀ (M : Mod (constant JC A)) (N : Mod (constant JD A))
        (f : (pull F (constantMap F A)).obj M ⟶ N),
        (underlying (constant JC A)).map (aM.homEquiv M N f) ≫ eG.hom.app N =
          adj.homEquiv ((underlying (constant JC A)).obj M)
            ((underlying (constant JD A)).obj N)
            (pullInsertion F (constantMap F A) M ≫
              (underlying (constant JD A)).map f)) ∧
      PreservesFiniteLimits (pull F (constantMap F A)) ∧
      PreservesFiniteColimits (pull F (constantMap F A)) ∧
      ∃ (RF : D (constant JD A) ⥤ D (constant JC A))
        (ηG : G.obj.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q (constant JC A) ⟶
          Q (constant JD A) ⋙ RF),
        RF.IsRightDerivedFunctor ηG
            (HomologicalComplex.quasiIso (Mod (constant JD A)) (ComplexShape.up ℤ)) ∧
        (∀ J : Cx (constant JD A), J.IsKInjective → IsIso (ηG.app J)) ∧
        ∃ aD : (derivedPull F V adj (constantMap F A)).functor ⊣ RF,
          (∀ (P : Cx (constant JC A)) (J : Cx (constant JD A)),
            P.IsAcyclicTensorKFlat → (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) → J.IsKInjective →
            ∀ f : ((pull F (constantMap F A)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P ⟶ J,
              aD.homEquiv ((Q (constant JC A)).obj P) ((Q (constant JD A)).obj J)
                ((derivedPull F V adj (constantMap F A)).comparison.app P ≫
                  (Q (constant JD A)).map f) =
                (Q (constant JC A)).map
                  ((aM.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv P J f) ≫
                    ηG.app J) ∧
          ∃ (hC : ∀ M : D (constant JC A),
              IsComplete (quotient JC A I 0) ((completion JC A I false).obj M))
            (hD : ∀ M : D (constant JD A),
              IsComplete (quotient JD A I 0) ((completion JD A I false).obj M))
            (hG : ∀ N : D (constant JD A), IsComplete (quotient JD A I 0) N →
              IsComplete (quotient JC A I 0) (RF.obj N))
            (aC : ObjectProperty.lift (IsComplete (quotient JC A I 0))
              (completion JC A I false) hC ⊣
              ObjectProperty.ι (IsComplete (quotient JC A I 0)))
            (aDCompletion : ObjectProperty.lift (IsComplete (quotient JD A I 0))
              (completion JD A I false) hD ⊣ ObjectProperty.ι (IsComplete (quotient JD A I 0))),
            (∀ (M : D (constant JC A))
              (N : ObjectProperty.FullSubcategory (IsComplete (quotient JC A I 0)))
              (f : (ObjectProperty.lift (IsComplete (quotient JC A I 0))
                (completion JC A I false) hC).obj M ⟶ N),
              aC.homEquiv M N f = (completionUnit JC A I false).app M ≫ f.hom) ∧
            (∀ (M : D (constant JD A))
              (N : ObjectProperty.FullSubcategory (IsComplete (quotient JD A I 0)))
              (f : (ObjectProperty.lift (IsComplete (quotient JD A I 0))
                (completion JD A I false) hD).obj M ⟶ N),
              aDCompletion.homEquiv M N f =
                (completionUnit JD A I false).app M ≫ f.hom) ∧
            ∃ aComplete :
              ObjectProperty.lift (IsComplete (quotient JD A I 0))
                (ObjectProperty.ι (IsComplete (quotient JC A I 0)) ⋙
                  (derivedPull F V adj (constantMap F A)).functor ⋙ completion JD A I false)
                (fun M ↦ hD ((derivedPull F V adj (constantMap F A)).functor.obj M.obj)) ⊣
              ObjectProperty.lift (IsComplete (quotient JC A I 0))
                (ObjectProperty.ι (IsComplete (quotient JD A I 0)) ⋙ RF)
                (fun N ↦ hG N.obj N.property),
              ∀ (M : ObjectProperty.FullSubcategory (IsComplete (quotient JC A I 0)))
                (N : ObjectProperty.FullSubcategory (IsComplete (quotient JD A I 0)))
                (f : (completion JD A I false).obj
                  ((derivedPull F V adj (constantMap F A)).functor.obj M.obj) ⟶ N.obj),
                (aComplete.homEquiv M N (ObjectProperty.homMk f)).hom =
                  aD.homEquiv M.obj N.obj
                    ((completionUnit JD A I false).app
                      ((derivedPull F V adj (constantMap F A)).functor.obj M.obj) ≫ f) := by
  sorry

end CategoryTheory.ConstantCompletion
