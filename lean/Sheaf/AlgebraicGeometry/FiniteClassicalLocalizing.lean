/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.SixFunctors.ClassicalDefinition
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.SixFunctors.IntegralModelsGenerators
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.AlgebraicGeometry.ClassicalModuleWeakSerre
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import Sheaf.Paper.CohomologyInWeakSerreSubcategory
import Sheaf.Paper.FiniteDiscreteCondensedRing
import Sheaf.Paper.FiniteDiscreteSchemeRing
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison

/-! # Classical cohomology is localizing and stable under inverse image

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-ctf-finite-proper/sk-prop-ctf-finite-proper-localizing.proof.md, Transfer
(blueprint: lem-sfb-finite-classical-localizing).

The first clauses use intrinsic modules over the ordinary constant ring sheaf.
The final clause uses the recorded internal-module presentation of `Dctf`.
For finite discrete coefficients the canonical ring identifications
`finiteDiscreteCondensedRing_constant` and `finiteDiscreteSchemeRing_constant`
identify this presentation with the same ordinary constant-coefficient category.
The final clause uses the existing canonical `integralModelIntrinsicRealization`
on each cohomology sheaf, making the coefficient identification explicit.
No completed derived category occurs. Finite rings are represented in `Type 0`,
without restricting their isomorphism classes; the ordinary ring is lifted to `Type u`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The full replete subcategory with classical cohomology is triangulated, closed under
small ambient coproducts and canonical truncations, and stable under every scheme inverse
image. Cohomology and both truncations preserve ambient coproducts; inverse image commutes
with truncation, with its canonical inclusion and projection. On qcqs schemes the localizing
closure of the recorded bounded constructible finite-Tor category has classical cohomology.

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-ctf-finite-proper/sk-prop-ctf-finite-proper-localizing.proof.md, Transfer
(blueprint: lem-sfb-finite-classical-localizing).

Proof plan, following the six steps of the node:
1. Classical module sheaves contain zero and are closed under kernels, cokernels and
   extensions (det-pe-classical-derived-weak-serre). Apply
   lem-sbc-cohomology-in-weak-serre-subcategory to obtain triangulated closure.
   The good truncation formulas (def-kun-truncations) retain cohomology or replace it by zero.
2. Classical sheaves are exactly the essential image of comparison inverse image
   (det-pe-classical-sheaves-modules). Its adjunction
   (def-weil-pbc-site-comparison-morphism) identifies the inverse image of an etale sum
   with the ambient sum, including the empty sum; module sums exist by
   lem-weil-pbc-module-sheaves-colimits-forgetful.
3. The module category is Grothendieck (lem-weil-pbc-ring-sheaves-grothendieck).
   Sums are filtered colimits of finite sums, hence exact. Termwise sums compute ambient
   derived sums (lem-kun-grothendieck-derived-coproducts). Exactness commutes with kernels,
   images and cokernels, hence with cohomology and the good truncations. Step 2 gives closure.
4. Constant-coefficient inverse image is exact (def-weil-pbc-proetale-operations).
   Its cohomology is the inverse image of cohomology. The unrestricted inverse-image square
   of sk-thm-pe-direct-image-comparison preserves classical sheaves. Exactness also preserves
   good truncations and their canonical maps. No qcqs assumption is imposed on the map.
5. The finite-discrete ring identifications
   (lem-weil-pbc-finite-discrete-condensed-ring-constant and
   lem-weil-pbc-finite-discrete-scheme-ring-constant) identify internal and ordinary constant
   modules, preserving cohomology and sums. A finite ring is Noetherian. On qcqs schemes the
   heart clause of sk-thm-pe-constructible-comparison makes every constructible cohomology
   sheaf classical. Thus Dctf lies in the classical class; its Tor bound is not needed here.
6. By steps 1 and 3 this class is one of the full replete triangulated, coproduct-closed
   classes intersected in sk-def-localizing-closure. Step 5 therefore gives the inclusion.
   The zero ring, empty scheme, empty coproduct and unbounded complexes are included. -/
theorem finite_classical_localizing (ell : ℕ) [Fact ell.Prime]
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    [IsTopologicalRing A] (_hA : ∃ n : ℕ, 1 ≤ n ∧ (ell ^ n : A) = 0)
    (T : Scheme.{u}) :
    HasCoproducts.{u + 1} (Scheme.proEtaleDerivedCategory T (ULift.{u, 0} A)) ∧
    IsLocalizingSubcategoryOfSize.{u + 1}
      (fun K : Scheme.proEtaleDerivedCategory T (ULift.{u, 0} A) ↦
        IsClassicalModuleComplex K) ∧
    (∀ (K : Scheme.proEtaleDerivedCategory T (ULift.{u, 0} A)),
      IsClassicalModuleComplex K → ∀ a : ℤ,
        IsClassicalModuleComplex ((DerivedCategory.TStructure.t.truncLE a).obj K) ∧
        IsClassicalModuleComplex ((DerivedCategory.TStructure.t.truncGE a).obj K)) ∧
    (∀ (I : Type (u + 1))
      (K : I → Scheme.proEtaleDerivedCategory T (ULift.{u, 0} A)),
      (∀ i : I, IsClassicalModuleComplex (K i)) →
      ∀ (c : Cofan K), IsColimit c → ∀ q : ℤ,
        Nonempty (IsColimit ((DerivedCategory.homologyFunctor
          (Scheme.proEtaleRingModules T
            (Scheme.proEtaleConstantRing T (ULift.{u, 0} A))) q).mapCocone c)) ∧
        Nonempty (IsColimit ((DerivedCategory.TStructure.t.truncLE q).mapCocone c)) ∧
        Nonempty (IsColimit ((DerivedCategory.TStructure.t.truncGE q).mapCocone c))) ∧
    (∀ (W : Scheme.{u}) (r : W ⟶ T),
      (∀ K : Scheme.proEtaleDerivedCategory T (ULift.{u, 0} A),
        IsClassicalModuleComplex K →
          IsClassicalModuleComplex
            ((Scheme.proEtaleConstantRingDerivedPullback (ULift.{u, 0} A) r).obj K)) ∧
      ∀ a : ℤ,
        ∃ eLE : DerivedCategory.TStructure.t.truncLE a ⋙
            Scheme.proEtaleConstantRingDerivedPullback (ULift.{u, 0} A) r ≅
          Scheme.proEtaleConstantRingDerivedPullback (ULift.{u, 0} A) r ⋙
            DerivedCategory.TStructure.t.truncLE a,
        ∃ eGE : DerivedCategory.TStructure.t.truncGE a ⋙
            Scheme.proEtaleConstantRingDerivedPullback (ULift.{u, 0} A) r ≅
          Scheme.proEtaleConstantRingDerivedPullback (ULift.{u, 0} A) r ⋙
            DerivedCategory.TStructure.t.truncGE a,
        eLE.hom ≫ Functor.whiskerLeft
            (Scheme.proEtaleConstantRingDerivedPullback (ULift.{u, 0} A) r)
            (DerivedCategory.TStructure.t.truncLEι a) =
          Functor.whiskerRight (DerivedCategory.TStructure.t.truncLEι a)
            (Scheme.proEtaleConstantRingDerivedPullback (ULift.{u, 0} A) r) ∧
        Functor.whiskerRight (DerivedCategory.TStructure.t.truncGEπ a)
            (Scheme.proEtaleConstantRingDerivedPullback (ULift.{u, 0} A) r) ≫ eGE.hom =
          Functor.whiskerLeft
            (Scheme.proEtaleConstantRingDerivedPullback (ULift.{u, 0} A) r)
            (DerivedCategory.TStructure.t.truncGEπ a)) ∧
    (∀ [CompactSpace T] [QuasiSeparatedSpace T]
      (K : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj A) T))),
      localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible (Profinite.continuousMapRingObj A) T ⊓
          fun L ↦ DerivedCategory.finiteTorAmplitude _ L) K →
      ∀ q : ℤ, IsClassicalModuleSheaf
        ((WeilConjectures.SixFunctors.integralModelIntrinsicRealization T A).obj
          ((DerivedCategory.homologyFunctor _ q).obj K))) := by
  sorry

end AlgebraicGeometry.ProEtale
