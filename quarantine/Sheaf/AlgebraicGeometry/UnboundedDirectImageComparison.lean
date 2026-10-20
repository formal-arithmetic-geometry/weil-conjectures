/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
public import Sheaf.AlgebraicGeometry.UnboundedDirectImageComparisonMap
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

import Sheaf.AlgebraicGeometry.UnboundedDirectImageBoundedBelow
import Sheaf.AlgebraicGeometry.UnboundedDirectImageTruncationStability
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Unbounded direct-image comparison

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-pe-unbounded-classical/sk-prop-pe-unbounded-classical-direct-image.md
(blueprint: lem-sfb-unbounded-direct-image-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The canonical comparison is invertible on every unbounded etale complex over a finite
primary ring. Fixed-ring module sheaves are the ordinary constant-ring module sheaves;
the finiteCoefficientRealization of def-weil-pbc-proetale-modules identifies their
pro-etale realization with the continuous-function coefficient presentation.
Source: blueprint, sk-prop-pe-unbounded-classical-direct-image.md and its proof
(blueprint: lem-sfb-unbounded-direct-image-comparison).

Proof:
1. Finite type over a field makes X locally Noetherian, hence g is quasi-separated.
2. Finiteness of A makes every underlying module sheaf torsion. The classical uniform
   higher-direct-image bound and the canonical module/abelian comparison give
   cohomological dimension d=2 dim(X)+1 for etale direct image. Its total derived
   functor raises upper bounds by at most d; exact comparison preserves these bounds.
3. On each lower truncation, the proved bounded-below canonical mate identifies the
   target with the source, so the same upper bound holds on all target truncations.
   Exact comparison commutes with truncation. Pro-etale module sheaves have exact
   countable products, and derived direct image is a right adjoint. The existing
   left-completeness lemma therefore raises the uniform bound by at most one on
   the unbounded target. This avoids sectionwise coefficient transport entirely.
4. For each m choose N=m-d-2. Apply the two functors to the standard truncation triangle.
   Their lower-tail homology vanishes in degrees m and m+1. The long exact sequences
   make both truncation maps invertible on H^m.
5. Naturality of the specified mate identifies the resulting square with the bounded-below
   comparison at tau_{>=N} K. Cancel the target truncation isomorphism to obtain
   invertibility of H^m of the mate. Homology detects isomorphisms in D.
No k-linearity of g, lower bound on K, nonzero ring, or nonempty scheme is used.
-/
theorem unboundedDirectImageComparison
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ)))
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, (ℓ : A) ^ n = 0)
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    (g : X ⟶ Y)
    [LocallyOfFiniteType g] [QuasiCompact g]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsIso (unboundedDirectImageComparisonMap A g K) := by
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k))
  let : QuasiSeparated g := inferInstance
  apply (DerivedCategory.isIso_iff _ _).2
  intro m
  obtain ⟨N, hS, hT⟩ := unboundedDirectImage_truncation_stability
    k hbase hℓ A hA g K m
  let t := (CategoryTheory.Triangulated.TStructure.truncGEπ
    DerivedCategory.TStructure.t N).app K
  let L := (CategoryTheory.Triangulated.TStructure.truncGE
    DerivedCategory.TStructure.t N).obj K
  have : L.IsGE N := inferInstance
  have : IsIso (unboundedDirectImageComparisonMap A g L) :=
    unboundedDirectImageComparison_boundedBelow A g L N
  let H := DerivedCategory.homologyFunctor
    (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) m
  have hn := congrArg H.map (unboundedDirectImageComparisonMap_naturality A g t)
  simp only [Functor.map_comp, Functor.id_obj] at hn
  have := hS
  have := hT
  have hi : IsIso (H.map (unboundedDirectImageComparisonMap A g K) ≫
      H.map ((ProEtale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.map
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map t))) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (H.map ((ProEtale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.map
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map t)))

end AlgebraicGeometry.ProEtale
