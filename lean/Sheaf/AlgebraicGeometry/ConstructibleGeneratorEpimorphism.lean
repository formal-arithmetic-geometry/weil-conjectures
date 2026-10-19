/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import WeilConjectures.AlgebraicGeometry.AffineEtaleRankOneSeparating
import WeilConjectures.AlgebraicGeometry.GeometricStalkColimits
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFiniteStalks
import Sheaf.AlgebraicGeometry.ConstructibleModuleSurjectivityLocus
import Sheaf.AlgebraicGeometry.EtaleLowerShriekConstantConstructible
import Sheaf.Topology.SpectralConstructibleFiniteIntersection
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFiniteStalks

/-!
# Finite free etale generators lifting an epimorphism

Source: Stacks Project, Etale Cohomology, Tag 095N, proof of the finite surjection,
applied to the composite of a free cover with the given epimorphism; Modules on
Sites, Tag 093B(2), in Situation 0937
(blueprint: lem-trf-constructible-generator-epimorphism).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Finite sums of rank-one extensions by zero lift epimorphisms onto constructible
module sheaves. The finite sum also identifies with extension by zero of the rank-one
constant sheaf on the finite disjoint union, including an empty union.

Source: Stacks Project, Tag 095N, proof of the finite surjection, and Tag 093B(2)
(blueprint: lem-trf-constructible-generator-epimorphism).

Proof, following the node:
1. Take all maps from affine etale rank-one extensions to M. Their coproduct maps
   epimorphically to M by the separating-family theorem
   `lem-weil-pbc-affine-etale-rank-one-separating` and existence of colimits
   `lem-weil-pbc-module-sheaves-colimits-forgetful`: right cancellation is checked
   on the coprojections. Each affine source is separated, and its etale map to the
   Noetherian base is quasi-compact and locally of finite type by
   `lem-weil-pbc-affine-source-morphism-separated`,
   `lem-weil-pbc-locally-noetherian-quasi-separated` and
   `lem-weil-pbc-qcqs-morphism-permanence`.
2. For each finite subfamily compose its sum with p to get a map to C. Its source is
   constructible by `lem-weil-pbc-etale-free-sheaf-constructible` and
   `thm-constructible-serre`. The failure-of-surjectivity locus of this map at the
   algebraic-closure points is constructible by
   `lem-weil-pbc-constructible-module-surjectivity-locus`.
3. Geometric stalks are exact (`prop-weil-pbc-geometric-stalks-exact`) and commute
   with coproducts (`lem-kun-stalks-commute-colimits`). A finite generating set of
   the target stalk (`lem-weil-pbc-constructible-module-finite-stalks`) lifts through
   p and the free cover, using only finitely many summands. Thus the intersection
   of all finite-subfamily failure loci is empty. The exact forgetful comparison
   is `lem-weil-pbc-module-sheaves-colimits-forgetful`.
4. The base is spectral by `lem-weil-pbc-qcqs-scheme-spectral`. Constructible-topology
   compactness (`lem-weil-pbc-spectral-constructible-finite-intersection`) gives a
   finite collection of these failure loci with empty intersection. Taking the
   union of their index sets gives one finite subfamily with empty failure locus.
5. The corresponding composite to C is epic: its cokernel has zero stalk at the
   algebraic-closure point of each scheme point, hence is zero by
   `lemma-weil-pbc-geometric-stalk-conservative`, stalk exactness and the faithful
   exact forgetful functor. Restriction of the original free cover gives e to M.
6. Form the finite disjoint union using `lem-weil-pbc-scheme-coproduct-family`.
   Its structure morphism is separated, etale and of finite type componentwise.
   A lift into the disjoint union partitions its source into clopen inverse images
   of the components. The sum-over-lifts formula of
   `def-weil-pbc-etale-sum-extension` therefore identifies its rank-one extension
   with the finite sum of the component extensions, after sheafification.
-/
theorem exists_constructible_generator_epimorphism
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {M C : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (p : M ⟶ C) [Epi p] (hC : IsConstructibleEtaleModuleSheaf C) :
    ∃ (n : ℕ) (U : Fin n → X.Etale),
      (∀ i, IsSeparated (U i).hom ∧ LocallyOfFiniteType (U i).hom ∧
        QuasiCompact (U i).hom) ∧
      (∃ e : (∐ fun i : Fin n ↦
          (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) (U i).hom inferInstance).obj
            ((constantSheaf (U i).left.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
              (ModuleCat.of A A))) ⟶ M,
        Epi (e ≫ p)) ∧
      ∃ h : Etale (Sigma.desc (fun i : Fin n ↦ (U i).hom)),
        IsSeparated (Sigma.desc (fun i : Fin n ↦ (U i).hom)) ∧
        LocallyOfFiniteType (Sigma.desc (fun i : Fin n ↦ (U i).hom)) ∧
        QuasiCompact (Sigma.desc (fun i : Fin n ↦ (U i).hom)) ∧
        Nonempty ((∐ fun i : Fin n ↦
          (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) (U i).hom inferInstance).obj
            ((constantSheaf (U i).left.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
              (ModuleCat.of A A))) ≅
          (Etale.etaleLowerShriek (ModuleCat.{u + 1} A)
            (Sigma.desc (fun i : Fin n ↦ (U i).hom)) h).obj
              ((constantSheaf (∐ fun i : Fin n ↦ (U i).left).smallEtaleTopology
                (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))) := by
  sorry

end AlgebraicGeometry.Scheme
