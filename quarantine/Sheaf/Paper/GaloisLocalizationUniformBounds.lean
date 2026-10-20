/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Paper.GaloisPartitionModules
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Paper.DualizingLocallyClosedInheritance
public import Sheaf.AlgebraicGeometry.EtaleInternalHomLocalization
public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Data.ZMod.Basic
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.AlgebraicGeometry.GaloisPartitionExactRefinement
import Sheaf.AlgebraicGeometry.NoetherianConstructibleGaloisPartition
import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
import Sheaf.Paper.LisseTensorScalarExtension
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.SixFunctors.GeometricInverseImageConstantModule
import Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageColimits
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit
import WeilConjectures.ConstructibleSheaf.Pullback
import Sheaf.Paper.DirectedGaloisFiniteTensorGenerators

/-!
# Uniform Galois-partition bounds for open image and closed support

Source: ILO, Travaux de Gabber, Expose XVII, Propositions 7.6.3, 7.6.5, 7.6.7
and Corollary 7.6.6, printed pp. 311--313
(blueprint: lem-per-galois-localization-uniform-bounds).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Uniform localization bounds, allowing arbitrary stalk modules in each partition class.
The prime-field duality hypothesis uses the transpose of signed evaluation. Closed support
is the right derived functor of i* ker(id -> j*j*), with the actual adjunction unit.

Source: ILO XVII, 7.6.3--7.6.7, pp. 311--313; arbitrary algebra coefficients as in 7.6.10
(blueprint: lem-per-galois-localization-uniform-bounds).

Proof:
1. Open and closed subschemes of X are Noetherian. Use
   lem-per-galois-partition-exact-refinement to replace input partitions by directed
   refinements; lem-per-directed-galois-finite-tensor-generators gives a finite list C_a
   of prime-field tensor generators, independent of coefficient modules.
2. Pullback preserves constructibility (prop-constructible-pullback). Choose a partition
   trivializing the finite list of pullbacks (lem-per-noetherian-constructible-galois-partition).
   Exact inverse image preserves filtrations and filtered colimits
   (lem-pe-constant-left-module-inverse-image, lem-weil-pbc-inverse-image-preserves-colimits,
   lem-weil-pbc-module-sheaves-colimits-forgetful), as well as constant modules
   (lem-sfb-geometric-inverse-image-constant-module). Hence it preserves partition classes
   with a single output partition, constructibility, and all cohomological bounds.
3. Set Q_U=j*Q. Exact extension by zero preserves bounded constructibility by its stalk
   formula (lem-weil-pbc-extension-by-zero-exact, lem-weil-pbc-extension-by-zero-stalks).
   Localized-site restriction commutes with internal Hom
   (lem-weil-pbc-etale-site-localization-open,
   lem-weil-pbc-ringed-internal-hom-exact-restriction). Apply this to j!M to see Q_U is
   dualizing. Restriction preserves evaluation, signed symmetry, and its transpose.
4. Apply lem-per-etale-internal-hom-localization to j!L and Q. The closed term vanishes,
   giving D_X j!L = Rj_*D_U L by lem-sf-derived-homology-long-exact. Biduality then gives
   Rj_*M = D_X j!D_U M, proving prime-field bounded constructibility.
5. The finitely many C_a have bounded constructible Rj_*C_a. Choose d >= 0 above all
   their nonzero higher images and one partition trivializing these finitely many sheaves.
   Negative higher images vanish by the nonnegative injective resolution. For an empty
   generator list choose d=0 and any partition.
6. For any A-module N the canonical map N_X tensor R^qj_*C -> R^qj_*(N_U tensor C)
   is an isomorphism: choose a prime-field basis of N and express coproducts as filtered
   colimits of finite sums. Use lemma-weil-pbc-direct-image-filtered-colimit and
   lem-sbc-higher-direct-image-forget-comparison. The construction commutes with every
   A-scalar. The open immersion is qcqs and these sheaves are killed by ell.
7. Apply this to C_a. On the chosen covers the outputs are finite sums of N, by
   lem-pod-etale-stalk-tensor-scalar and lem-pod-lisse-tensor-and-scalar-extension;
   lem-weil-pbc-sets-etale-iso-on-geometric-stalks detects the comparison. Exactness,
   extension closure and the higher-image long exact sequence
   (lem-weil-pbc-right-derived-universal-delta-functor) extend the assertion to finite
   filtrations and retracts. Finitely generated N gives constructible outputs.
8. Every partition-class sheaf is a filtered colimit of constructible subobjects by
   lem-per-directed-galois-finite-tensor-generators. Higher images commute with these
   colimits by the same continuity and forgetful comparisons. Exact-refinement closure
   retains the one partition and d, with no finite-generation restriction.
9. Use finite canonical truncation triangles (lem-weil-pbc-truncation-cohomology,
   lem-weil-pbc-truncation-triangle). Triangulated direct image
   (lem-weil-pbc-derived-direct-image-triangulated) and the long exact sequence carry
   [a,b] into [a,b+d]. This proves (1), including the constructible clause.
10. For (2), first restrict the fixed input partition to U by Step 2; apply (1) and take
   a directed common refinement on X. Step 2 for i gives a single partition on Z for
   both i*K and i*Rj_*j*K. All choices precede K.
11. Apply internal-Hom localization with first argument A_X[0]. Hom from the unit is
   the identity and inverse image preserves constants. Apply exact i* and i*i_*=id
   (lem-trf-oriented-closed-base-localization,
   lem-weil-pbc-exact-functor-derived-factorization) to obtain the triangle
   Ri!K -> i*K -> i*Rj_*j*K -> (Ri!K)[1].
12. Its long exact cohomology sequence expresses H^q(Ri!K) as an extension of a
   cokernel by a kernel in the chosen Z class. Exact-refinement closure gives membership
   and constructibility. The interval [a,n] maps into [a,n+d+1], so d_i=d+1 works.
   Empty schemes use empty partitions and zero sheaves; identities allow bound zero.
-/
theorem galois_localization_uniform_bounds
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A] [Algebra (ZMod ℓ) A]
    (_hdual : ∃ Q : DerivedCategoryModule (ULift.{u + 1} (ZMod ℓ)) X,
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) X Q ∧
      ∀ M : DerivedCategoryModule (ULift.{u + 1} (ZMod ℓ)) X,
        DerivedCategory.boundedConstructible
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) X M →
        DerivedCategory.boundedConstructible
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) X
          (((derivedHom (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) X).obj (op M)).obj Q) ∧
        IsIso (etaleEvaluationBiduality (ULift.{u + 1} (ZMod ℓ)) X Q M))
    {Z U : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j]
    (_hij : Set.range i.base = (Set.range j.base)ᶜ) :
    ((∀ P : Scheme.GaloisPartition U,
      ∃ (Q : Scheme.GaloisPartition X) (d : ℕ),
        ∀ K : DerivedCategoryModule A U, P.boundedDerived A K →
          Q.boundedDerived A ((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor.obj K) ∧
          ∀ n : ℤ, _root_.DerivedCategory.IsLE K n →
            _root_.DerivedCategory.IsLE
              ((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor.obj K) (n + (d : ℤ))) ∧
      (∀ K : DerivedCategoryModule A U,
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) U K →
          DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X
            ((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor.obj K))) ∧
    ((∀ P : Scheme.GaloisPartition X,
      ∃ (PZ : Scheme.GaloisPartition Z) (PU : Scheme.GaloisPartition U) (d : ℕ),
        ∀ K : DerivedCategoryModule A X, P.boundedDerived A K →
          PZ.boundedDerived A ((perEtaleClosedSupport A i j).rightDerivedFunctor.obj K) ∧
          PU.boundedDerived A ((perEtalePull A j).obj K) ∧
          (∀ n : ℤ, _root_.DerivedCategory.IsLE K n →
            _root_.DerivedCategory.IsLE
              ((perEtaleClosedSupport A i j).rightDerivedFunctor.obj K) (n + (d : ℤ))) ∧
          (∀ n : ℤ,
            (_root_.DerivedCategory.IsLE K n →
              _root_.DerivedCategory.IsLE ((perEtalePull A j).obj K) n) ∧
            (_root_.DerivedCategory.IsGE K n →
              _root_.DerivedCategory.IsGE ((perEtalePull A j).obj K) n))) ∧
      (∀ K : DerivedCategoryModule A X,
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K →
          DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Z
            ((perEtaleClosedSupport A i j).rightDerivedFunctor.obj K) ∧
          DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) U
            ((perEtalePull A j).obj K))) := by
  sorry

end AlgebraicGeometry.Etale
