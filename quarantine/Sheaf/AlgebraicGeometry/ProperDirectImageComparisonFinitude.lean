/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import Sheaf.AlgebraicGeometry.GeometricFiberFinite
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImages
import Sheaf.AlgebraicGeometry.ProperConstructibleHigherDirectImages
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFiniteStalks
import Sheaf.AlgebraicGeometry.Sites.FibrewiseCohomologicalDimension
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFiniteStalks

/-!
# Comparison and finitude of proper direct images

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/obl-fin-comparison.md`,
statement and proof (blueprint: obl-fin-comparison).

The geometric-stalk comparison uses exactly the endpoint presentations and degree-q
base-change map recorded by `Etale.geometricFiber_finite_stalk_formula`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Proper direct images of constructible finite-coefficient etale sheaves: comparison
at every geometric point, finite fibre cohomology, constructible higher direct images,
and vanishing above twice the geometric fibre dimension bound.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/obl-fin-comparison.md`, clauses (i)-(ii)
(blueprint: obl-fin-comparison).

Proof:
1. Properness includes finite type (def-weil-pbc-scheme-conventions). Compose finite
   affine covers of S over k and of X over S to see X is finite type over k. Since N
   is invertible in k, it is invertible on X and S. Apply
   thm-fin-proper-constructibility-complete and unfold def-finrepair-property-c:
   every nonnegative higher direct image is constructible.
2. By lem-weil-pbc-constructible-module-finite-stalks, F has finite geometric stalks,
   hence satisfies def-constructible-finite. Apply cor-weil-pbc-geometric-fiber-finite
   to get the specified stalk comparison. Apply the finite-stalk lemma to each
   constructible higher direct image and transport finiteness through the comparison
   to get finite fibre cohomology as a Lambda-module.
3. A geometric fibre is proper over the algebraically closed field by
   lem-weil-pbc-proper-fp-permanence, hence finite type. Its dimension is at most d,
   and N stays invertible. The restricted sheaf is constructible by
   prop-constructible-pullback. Apply fin4-lem-fibrewise-cohomological-dimension to
   obtain vanishing above 2d. The comparison makes all the corresponding stalks zero.
4. By lemma-weil-pbc-geometric-stalk-conservative, the map from the zero sheaf to
   the higher direct image is an isomorphism after forgetting to abelian sheaves.
   Its inverse is Lambda-linear: apply the original injective linear map to check
   compatibility with each scalar. Thus the module sheaf is zero in these degrees. -/
theorem properDirectImage_comparison_finitude
    (k : Type u) [Field k] (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hcoeff : IsSmoothBaseChangeCoefficients N Λ (Spec (.of k)))
    {X S : Scheme.{u}} [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (f : X ⟶ S) [IsProper f] (d : ℕ)
    (hfib : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim ↥(pullback f s) ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    (∀ (q : ℕ) (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      (∃ (sourceIso :
          (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            ((baseChangeSourceFunctor Λ s f q).obj F) ≅
          ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
            (higherDirectImage Λ f q F))
        (targetIso :
          (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            ((baseChangeTargetFunctor Λ (pullback.fst f s) (pullback.snd f s) q).obj F) ≅
          (cohomology (ModuleCat.{u + 1} Λ) (pullback f s) q).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj
              ((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f s)).obj F))),
        IsIso (sourceIso.inv ≫
          (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
            (baseChangeHomologyMap Λ (IsPullback.of_hasPullback f s) q F) ≫ targetIso.hom)) ∧
      Finite ((cohomology (ModuleCat.{u + 1} Λ) (pullback f s) q).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f s)).obj F))) ∧
      (2 * d < q → IsZero ((cohomology (ModuleCat.{u + 1} Λ) (pullback f s) q).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f s)).obj F))))) ∧
    (∀ q : ℕ,
      Scheme.IsConstructibleEtaleModuleSheaf (higherDirectImage Λ f q F) ∧
      (2 * d < q → IsZero (higherDirectImage Λ f q F))) := by
  sorry

end AlgebraicGeometry.Etale
