/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleFiniteStratifiedPerfect
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartOrderedRefinement
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.EtaleDomainPullbackCalculus
import WeilConjectures.AlgebraicGeometry.EtaleLisseCtfPerfectLocalModel
import WeilConjectures.AlgebraicGeometry.RefinementPreservesFiniteLisse
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison

/-! # Local and triangulated calculus for finite stratified-perfect etale complexes

Source: Bhatt--Scholze, Definition 6.3.1, Remark 6.3.2, Lemmas 6.3.4 and
6.3.8--6.3.11, pp. 45--47; Stacks Project, Tag 09BI
(blueprint: lem-per-etale-stratified-perfect-calculus).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Finite stratified-perfect complexes are exactly bounded constructible complexes
of finite Tor amplitude, and form a replete thick triangulated subcategory. The
remaining clauses give finite Zariski locality, arbitrary geometric inverse image,
quasi-compact open extension by zero, arbitrary finite coefficient extension,
tensoring with a locally constant free rank-one sheaf, and all integer shifts.
Source: Bhatt--Scholze, Definition 6.3.1, Remark 6.3.2, Lemmas 6.3.4 and
6.3.8--6.3.11, pp. 45--47; Stacks Project, Tag 09BI
(blueprint: lem-per-etale-stratified-perfect-calculus).

Proof:
1. Every stratum of a Noetherian scheme is quasi-compact. Etale images are open,
so choose finitely many covering members on each stratum. Their bounded finite
projective models have a common degree interval. Exact inverse image commutes
with derived tensor. Tensoring any degree-zero sheaf with these models and
checking vanishing on all strata gives finite Tor amplitude. The same local
models give bounded constructibility.
2. Conversely, refine the finitely many nonzero constructible cohomology
stratifications to connected locally closed strata. Exact inverse image preserves
cohomology, constructibility and the Tor interval. On each stratum the cohomology
is finite lisse. Apply the connected perfect-local-model theorem of Stacks 09BI.
Those strata and their local models witness finite stratified-perfectness. This
argument does not use closure under cones.
3. Bounded constructible complexes are replete and triangulated. Tensor a
triangle with any degree-zero sheaf and apply its long exact cohomology sequence
to obtain finite Tor bounds for the third term. Constructible sheaves are a Serre
subcategory, so cohomology of a retract is constructible. Tensor and cohomology
preserve retracts, so finite Tor amplitude also passes to retracts.
4. Restriction preserves local models. Conversely, refine a finite open cover
and its finite local stratifications by successive differences and intersections.
This gives a finite constructible locally closed stratification of the whole
scheme with the given restricted local perfect models.
5. Exact geometric inverse image preserves bounded constructibility and every
Tor interval, by lem-coef-etale-domain-pullback-calculus. Use the equivalence in
steps 1--2 to obtain preservation of the stratified-perfect subcategories.
6. For a quasi-compact open immersion, adjoin the reduced closed complement to
a witnessing stratification of the open. Exact extension by zero restricts to the
original complex on the open, by its unit isomorphism; on the complement it is
zero, by the extension-by-zero stalk formula. Use the original local perfect
models and the zero perfect model on the complement.
7. Under any finite coefficient map, tensor each bounded finite-projective
model termwise with the target ring. It remains bounded finite-projective.
The canonical scalar/pullback comparison identifies this with restriction of
derived scalar extension. The derived-change-of-rings construction is computed
on these K-flat models; no flatness of the coefficient map is required.
8. Trivialize the locally constant free rank-one sheaf on an etale cover refining
the local models. Tensoring the models with a free rank-one module preserves
perfectness. Integer shifts translate the bounded local models and preserve the
same stratification and covers.
-/
theorem etaleStratifiedPerfect_calculus
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    [IsLocallyNoetherian T] [CompactSpace T] :
    (∀ K : DerivedCategoryModule A T,
      IsFiniteStratifiedPerfectEtaleComplex A T K ↔
        DerivedCategory.isBoundedConstructible A T K ∧
          ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A T a b K) ∧
    (IsFiniteStratifiedPerfectEtaleComplex A T).IsClosedUnderIsomorphisms ∧
    (IsFiniteStratifiedPerfectEtaleComplex A T).IsTriangulated ∧
    (∀ K L : DerivedCategoryModule A T, Retract K L →
      IsFiniteStratifiedPerfectEtaleComplex A T L →
      IsFiniteStratifiedPerfectEtaleComplex A T K) ∧
    (∀ (n : ℕ) (U : Fin n → T.Opens), (⨆ i, U i) = ⊤ →
      ∀ K : DerivedCategoryModule A T,
        IsFiniteStratifiedPerfectEtaleComplex A T K ↔
          ∀ i : Fin n, IsFiniteStratifiedPerfectEtaleComplex A (U i).toScheme
            ((upperStar (ModuleCat.{u + 1} A) (U i).ι).mapDerivedCategory.obj K)) ∧
    (∀ (T' : Scheme.{u}) [IsLocallyNoetherian T'] [CompactSpace T']
      (f : T' ⟶ T) (K : DerivedCategoryModule A T),
      IsFiniteStratifiedPerfectEtaleComplex A T K →
      IsFiniteStratifiedPerfectEtaleComplex A T'
        ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)) ∧
    (∀ (U : Scheme.{u}) [IsLocallyNoetherian U] [CompactSpace U]
      (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
      (K : DerivedCategoryModule A U),
      IsFiniteStratifiedPerfectEtaleComplex A U K →
      IsFiniteStratifiedPerfectEtaleComplex A T
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K)) ∧
    (∀ (B : Type (u + 1)) [CommRing B] [Finite B] (φ : A →+* B)
      (K : DerivedCategoryModule A T),
      IsFiniteStratifiedPerfectEtaleComplex A T K →
      IsFiniteStratifiedPerfectEtaleComplex B T ((scalarExtension φ T).obj K)) ∧
    (∀ (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
      (∃ V : Scheme.Cover.{u} Scheme.etalePrecoverage T, ∀ i : V.I₀,
        Nonempty ((upperStar (ModuleCat.{u + 1} A) (V.f i)).obj L ≅
          (constantSheaf (V.X i).smallEtaleTopology
            (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))) →
      ∀ K : DerivedCategoryModule A T,
        IsFiniteStratifiedPerfectEtaleComplex A T K →
        IsFiniteStratifiedPerfectEtaleComplex A T
          (((derivedTensor (ModuleCat.{u + 1} A) T).obj K).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj L))) ∧
    (∀ (K : DerivedCategoryModule A T) (n : ℤ),
      IsFiniteStratifiedPerfectEtaleComplex A T K →
      IsFiniteStratifiedPerfectEtaleComplex A T (K⟦n⟧)) := by
  sorry

end AlgebraicGeometry.Etale
