/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.Paper.InternalSectionDerivedTensorComparison
public import Sheaf.Paper.InternalSectionTotalComparison
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Sheaf.Paper.InternalSliceDerivedHomComparison
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus

import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Internal-module and ringed-site derived Hom

Source: Stacks Project, Tags 08J9, 08JA and 08JB; blueprint module objects and
derived tensor--Hom (blueprint: lem-sfb-module-object-ringed-site-derived-comparison).

## Main statements

* `moduleObject_ringedSite_derived_comparison`: naturality, evaluation and slices.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open scoped CategoryTheory.Obj
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.InternalAbelianSheafModule WeilConjectures

namespace AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

universe u₀ v₀

private theorem globalNativeMonoidal_eq_localization
    (C : Type u₀) [Category.{v₀} C] [Abelian C] [IsGrothendieckAbelian.{v₀} C]
    [HasDerivedCategory.{v₀} C] [MonoidalCategory C] [MonoidalClosed C]
    [MonoidalPreadditive C] [BraidedCategory C]
    [(DerivedCategory.Qh (C := C)).HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (.up ℤ))] :
    DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory C =
      DerivedMonoidal.instMonoidalCategory DerivedCategory.Qh
        (HomotopyCategory.quasiIso C (.up ℤ)) := by
  rfl


/-- The native derived tensor uses the K-flat localization monoidal structure.
Source: blueprint derived tensor--Hom, Stacks 06YS
(blueprint: lem-sfb-module-object-ringed-site-derived-comparison).
Proof: unfold the module-derived tensor and the native derived monoidal instance.
Both are induced from the same K-flat left derivability structure and total tensor;
the localization construction therefore gives the same monoidal data. -/
theorem internalMonoidal_eq_localization :
    (inferInstance : MonoidalCategory (DerivedCategory (Internal Λ X))) =
      DerivedMonoidal.instMonoidalCategory DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Internal Λ X) (.up ℤ)) := by
  exact globalNativeMonoidal_eq_localization (Internal Λ X)

/-- The actual derived Koszul braiding, transported along the preceding equality.
Source: Stacks 06YL (blueprint: lem-sfb-module-object-ringed-site-derived-comparison). -/
instance internalBraiding : BraidedCategory (DerivedCategory (Internal Λ X)) :=
  Eq.mp (congrArg (fun m ↦ @BraidedCategory (DerivedCategory (Internal Λ X)) _ m)
    (internalMonoidal_eq_localization Λ X).symm)
    (DerivedMonoidal.braidedCategory' DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Internal Λ X) (.up ℤ)))

/-- Comparison of the module-object right adjoint with the K-injective sheaf-Hom
model, including its evaluation and all localized-site comparisons.

Source: Stacks Project, Tags 08J9, 08JA, 08JB, and the module-object definitions
in the blueprint (blueprint: lem-sfb-module-object-ringed-site-derived-comparison).

Proof, following the five steps of the DAG:
1. Apply def-weil-pbc-internal-abelian-sheaf-module-equivalence and
   lem-pe-internal-section-tensor-comparison. The equivalence is exact, fixes
   underlying sheaves and maps, and preserves and reflects K-flatness. Local pure
   tensors determine the total-complex comparison. Localize its K-flat restriction
   to obtain TensorComparison, with the displayed normalization square.
2. Transport the parametrized adjunction sk-def-sfb-derived-tensor-hom through
   this derived equivalence and tensor comparison. Its counit is precisely the
   transported module-object evaluation.
3. For the ringed-site K-injective model, lem-pur-rhom-global-sections and the
   currying of lem-weil-pbc-ringed-internal-hom-exact-restriction identify
   Hom(A,H(K,N)) with Hom(A tensor K,N). Ordinary evaluation on K-flat and
   K-injective representatives supplies S and T with their representative model.
4. The two right adjoints are uniquely isomorphic by Yoneda. Their Hom bijections
   make the isomorphism natural in the contravariant and covariant variables and
   identify the counits. Use the Koszul exchange to write evaluation with the
   tensor order of CoefficientClosedStructure.
5. Repeat on every slice, restricting the actual coefficient monoid and its
   module objects. The section equivalence for B restricted to U is exact and
   leaves sections unchanged. Apply the ordinary pure-tensor comparison and
   its sum-total characterization to B restricted to U. Localize on K-flat
   representatives to obtain tU for the native local derived tensor. The native
   MonoidalClosed.internalHom is already given by the framework. Uniqueness of
   parametrized right adjoints identifies it with the ringed K-injective Hom;
   the identification respects the native counit, using its Koszul exchange.
   Restriction preserves K-injectives, and its normalized Hom comparison rho_U
   is the identity on local families of maps (08JB). Full faithfulness uniquely
   lifts (theta_U)^(-1) rho_U theta|_U to the module-object restriction isomorphism.
   The compatibility field states precisely that square, including the canonical
   section/restriction counits. For V to U the occurrences of theta_U cancel;
   the cocycle for rho gives the cocycle for the module-side restriction. This
   includes the identity slice, with no completion, boundedness or perfectness. -/
theorem moduleObject_ringedSite_derived_comparison :
    ∃ (S : CoefficientClosedStructure (hom Λ X))
      (T : CoefficientTensorModels.{u, u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (ring Λ X) S)
      (t : TensorComparison Λ X S T)
      (θ : Functor.uncurry.obj (CondensedRing.derivedHom Λ X) ⋙ forward Λ X ≅
        ((forward Λ X).op.prod (forward Λ X)) ⋙ hom Λ X),
      (∀ K N : DerivedCategory (Internal Λ X),
        (forward Λ X).map
          ((@BraidedCategory.braiding _ _ _ (internalBraiding Λ X)
              (((CondensedRing.derivedHom Λ X).obj (op K)).obj N) K).hom ≫
            (CondensedRing.derivedTensorHomAdjunction Λ K).counit.app N) =
          (t.iso.hom.app (((CondensedRing.derivedHom Λ X).obj (op K)).obj N, K)) ≫
            S.tensor.map
              (X := ((forward Λ X).obj (((CondensedRing.derivedHom Λ X).obj (op K)).obj N),
                (forward Λ X).obj K))
              (Y := ((hom Λ X).obj (op ((forward Λ X).obj K), (forward Λ X).obj N),
                (forward Λ X).obj K))
              (θ.hom.app (op K, N), 𝟙 ((forward Λ X).obj K)) ≫
            S.evaluation ((forward Λ X).obj K) ((forward Λ X).obj N)) ∧
      (∀ U : X.ProEt,
        ∃ (SU : CoefficientClosedStructure
            (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
              ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U)))
          (TU : CoefficientTensorModels.{u, u + 1, u, u + 1}
            ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U) SU)
          (tU : SliceTensorComparison Λ X U SU TU)
          (d : RingedSliceEvaluationComparisons (hom Λ X)
            (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
              ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U))
            (ringedSliceDerivedRestriction.{u + 1, u, u, u + 1, u + 1}
              (Scheme.ProEt.topology X) (ring Λ X) U) S SU
            (RingedSliceFlatRestriction.{u + 1, u, u}
              (Scheme.ProEt.topology X) (ring Λ X) U)),
          RingedSliceEvaluationNormalized.{u + 1, u, u, u + 1, u + 1}
            (Scheme.ProEt.topology X) (ring Λ X) U S T SU TU d ∧
          Nonempty (SliceHomComparison Λ X U S SU TU tU d θ)) := by
  sorry

end AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
