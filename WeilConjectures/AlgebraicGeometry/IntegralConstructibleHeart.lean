/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelHeart
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.RingTheory.Finiteness.Small
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.AlgebraicGeometry.IntegralHeartLocalDualityDescent
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableShortExact
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.RingTheory.DiscreteValuationRing.DerivedQuotientDuality
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Structure of the integral constructible heart

Source: blueprint latest,
`part-six-operations/sec-constructibility-upper-shriek/sec-ladic-summary/sec-i-heart/
sk-lem-int-integral-heart/_section.md`,
clauses (1)--(3) and its proof (blueprint: sk-lem-int-integral-heart).

The statement uses the condensed integral coefficient ring, the finite scalar local-model
predicate, and the ambient derived tensor and internal-hom structures supplied by the
recorded dependencies. Clause (1) records the bounded triangulated category and its
standard truncations together with the degree-zero constructible heart. Clause (2)
records finite stratified scalar models. Clause (3) records dualizability and the two
Tor-amplitude intervals on each stratum.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The integral constructible derived category has the bounded triangulated structure,
its constructible degree-zero heart, finite scalar local models on a common finite
stratification, and the local dual/Tor bounds.

Source: blueprint latest,
`part-six-operations/sec-constructibility-upper-shriek/sec-ladic-summary/sec-i-heart/
sk-lem-int-integral-heart/_section.md`, clauses (1)--(3),
and `sk-lem-int-integral-heart.proof.md` (blueprint: sk-lem-int-integral-heart).
Proof:
1. Finite type over a field gives a Noetherian scheme. The integral criterion
   characterizes constructibility by derived completeness and bounded constructible
   first reduction. Completion preserves shifts and triangles, derived reduction is
   exact, and constructibility for finite residue coefficients is triangulated.
   The zero object and cones therefore give the full triangulated subcategory.
2. The integral local-structure theorem gives bounded finite free scalar complexes
   on a finite stratification. Their cohomology modules are finitely presented over
   the DVR. Exact scalar realization identifies their cohomology with that of the
   realized complexes, giving constructible cohomology and the finite-module models.
3. Standard truncations keep or kill the cohomology sheaves, so preserve bounded
   constructibility. Degree-zero concentration and the fully faithful single functor
   identify the heart. Cone cohomology gives ambient kernels and cokernels; triangles
   from short exact sequences give extension closure and the abelian subcategory.
4. Scalar finite presentations become local finite presentations. The constructible
   module smallness theorem on the quasi-compact locally Noetherian scheme gives
   essential smallness from finite stratifications, presentations and descent data.
5. Apply the local-model statement to C[0]. Over the DVR, each finite scalar module
   has a length-one finite free resolution. Exact realization gives a resolution in
   degrees [-1,0], and dualizing gives degrees [0,1]. Local evaluation and coevaluation
   descend, identify the dual with derived internal Hom into the unit, and establish
   the two triangle identities and both Tor bounds on these same strata. For a
   quotient by a uniformizer power, its dual is the quotient shifted by [-1]. -/
theorem integralConstructibleHeart
    (k : Type u) [Field k]
    (ell : ℕ) [Fact ell.Prime] (hell : IsUnit (ell : k))
    (E : Type v) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    let Λ := integralHeartCoefficientRingObj ell E
    ObjectProperty.IsClosedUnderIsomorphisms
        (constantModelBoundedConstructible Λ X) ∧
      ObjectProperty.IsTriangulated
        (constantModelBoundedConstructible Λ X) ∧
      (∀ K, constantModelBoundedConstructible Λ X K →
        DerivedCategory.TStructure.t.bounded K ∧
          ∀ n : ℤ,
            constantModelBoundedConstructible Λ X
                ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
            constantModelBoundedConstructible Λ X
                ((DerivedCategory.TStructure.t.truncGE n).obj K)) ∧
      (ObjectProperty.ι (IsConstantModelConstructible Λ X) ⋙
          DerivedCategory.singleFunctor _ 0).Full ∧
      (ObjectProperty.ι (IsConstantModelConstructible Λ X) ⋙
          DerivedCategory.singleFunctor _ 0).Faithful ∧
      (∀ K, (ObjectProperty.ι (IsConstantModelConstructible Λ X) ⋙
          DerivedCategory.singleFunctor _ 0).essImage K ↔
        constantModelBoundedConstructible Λ X K ∧
          DerivedCategory.TStructure.t.le 0 K ∧
          DerivedCategory.TStructure.t.ge 0 K) ∧
      Nonempty (Abelian (ConstantModelConstructible Λ X)) ∧
      ObjectProperty.IsClosedUnderKernels
        (IsConstantModelConstructible Λ X) ∧
      ObjectProperty.IsClosedUnderCokernels
        (IsConstantModelConstructible Λ X) ∧
      ObjectProperty.IsClosedUnderExtensions
        (IsConstantModelConstructible Λ X) ∧
      EssentiallySmall.{u + 1} (ConstantModelConstructible Λ X) ∧
      (∀ C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X),
        IsConstantModelConstructible Λ X C →
          ∃ S : Scheme.FiniteLocallyClosedStratification X,
            (∀ a : Fin S.n,
              HasFiniteConstantLocalModel Λ (S.domain a)
                ((CondensedRing.upperStar Λ (S.immersion a)).obj C)) ∧
            (∀ a : Fin S.n,
              let M := (CondensedRing.upperStar Λ (S.immersion a)).obj C
              IsDualizable ((DerivedCategory.singleFunctor _ 0).obj M) ∧
              DerivedCategory.torAmplitudeIn _ (-1) 0
                ((DerivedCategory.singleFunctor _ 0).obj M) ∧
              DerivedCategory.torAmplitudeIn _ 0 1
                (((CondensedRing.derivedHom Λ (S.domain a)).obj
                    (op ((DerivedCategory.singleFunctor _ 0).obj M))).obj
                  (𝟙_ _)))) := by
  sorry

end AlgebraicGeometry.ProEtale
