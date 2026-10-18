/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
public import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
public import Sheaf.Paper.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Defs.Filter
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.SiteFlatOpcyclesTorCriterion
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
import Mathlib.Algebra.Homology.BifunctorShift

/-!
# Noetherian finite-Tor comparison

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-cor-pe-finite-tor-comparison/sk-cor-pe-finite-tor-comparison-noetherian.md
(blueprint: det-pe-finite-tor-comparison-noetherian).

We use the same coefficient-sized small site models, constant ring sheaves and standard
localizations as `constructibleComparison`. The Tor predicates test all module sheaves in
degree zero using K-flat representatives. The equivalence retains all ambient derived
morphisms and is identified with the specified comparison inverse image.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Comparison preserves and reflects the exact Tor interval for bounded constructible
complexes over a discrete Noetherian ring and restricts to the finite-Tor equivalence.
The first natural isomorphism characterizes the derived comparison by its action on all
complexes; the final one identifies the forward restricted equivalence with that functor.

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-cor-pe-finite-tor-comparison/sk-cor-pe-finite-tor-comparison-noetherian.md;
Stacks Tags 05VD, 07A4, 06YQ, 08G0 and 08G1
(blueprint: det-pe-finite-tor-comparison-noetherian).

Proof, following the node's seven steps:
1. Let R be the etale constant ring, S its comparison inverse image and F = nu*.
   det-pe-classical-sheaves-modules makes F exact and fully faithful. Regard it as the
   module pullback of def-weil-pbc-site-comparison-morphism with structural map the
   constant-ring identification. By lem-weil-pbc-ringed-topos-flat-module-pullback, F
   preserves flat module sheaves. Work on the equivalent small models in the common
   larger universe of def-weil-size-convention.
2. Exactness identifies H^q(FC) with F(H^q C), so F preserves quasi-isomorphisms and
   descends to D, with the stated localization factorization. Apply
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback to identify
   F(K tensor^L N) with FK tensor^L FN. Faithfulness reflects zero objects: if F(M)=0,
   faithfulness applied to the identity and zero of M gives id_M=0.
3. If K has amplitude [a,b], testing against R bounds its cohomology in [a,b]. Use
   def-sbc-standard-tstructure-derived-category for a representative zero above b.
   lem-pc-kflat-bounded-flat-replacement gives a flat replacement P zero above b;
   lem-pc-bounded-above-flat-kflat-site makes it K-flat. Thus def-kun-derived-tensor
   computes every tensor by P tensor N, which is exact in degree a-1 for every N.
4. By lem-weil-pbc-site-flat-opcycles-tor-criterion the cokernel of P^(a-1) to P^a
   is flat. Symmetry with N in degree zero has sign one and gives the needed order
   of tensor factors. By def-kun-truncations the good truncation at a is a flat
   complex supported in [a,b], quasi-isomorphic to P since H^q(P)=0 for q<a.
5. Apply F termwise. Its exactness and preservation of flat sheaves give a flat
   representative of FK supported in [a,b], hence K-flat by
   lem-pc-bounded-above-flat-kflat-site. Tensor with ANY pro-etale module sheaf,
   using def-weil-derived-tensor and def-pc-tensor-complex-sheaves: its terms,
   hence cohomology, vanish outside [a,b]. No classicality of this test is imposed.
6. Conversely test FK against FN for any etale module N. The tensor comparison
   from step 2 and exactness show F(H^q(K tensor^L N))=0 outside [a,b]. Faithfulness
   reflects this vanishing. This proves the reverse implication with the same interval.
7. sk-thm-pe-constructible-comparison gives the bounded constructible equivalence.
   The preceding implications identify the existence of a common finite Tor interval
   on both sides. Restriction to the full subcategories is fully faithful. For a
   finite-Tor pro-etale object choose a bounded constructible etale antecedent; its
   Tor interval is reflected by step 6, giving essential surjectivity. This is the
   discrete constant-ring presentation of det-def-sfb-constructible-tor-amplitude. -/
theorem finiteTorComparisonNoetherian (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] :
    ∃ D : ConstantCompletion.D (ConstantCompletion.constant
        (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
          ConstantCompletion.D (ConstantCompletion.constant
            (Scheme.coefficientProEtaleModelTopology.{u, v} X) A),
      Nonempty (ConstantCompletion.Q _ ⋙ D ≅
        constructibleComparisonComplexPullback X A ⋙ ConstantCompletion.Q _) ∧
      (∀ K : ConstantCompletion.D (ConstantCompletion.constant
          (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A),
        Scheme.IsCoefficientBoundedConstructibleEtale X A K →
          ∀ a b : ℤ, a ≤ b →
            (HasCoefficientModelTorAmplitude _ K a b ↔
              Scheme.HasCoefficientProEtaleTorAmplitude X A (D.obj K) a b)) ∧
      ∃ e : ObjectProperty.FullSubcategory
          (fun K ↦ Scheme.IsCoefficientBoundedConstructibleEtale X A K ∧
            ∃ a b : ℤ, HasCoefficientModelTorAmplitude _ K a b) ≌
          ObjectProperty.FullSubcategory
            (fun K ↦ coefficientBoundedConstructibleProEtale X A K ∧
              Scheme.HasFiniteCoefficientProEtaleTorAmplitude X A K),
        Nonempty (e.functor ⋙ ObjectProperty.ι
            (fun K ↦ coefficientBoundedConstructibleProEtale X A K ∧
              Scheme.HasFiniteCoefficientProEtaleTorAmplitude X A K) ≅
          ObjectProperty.ι
            (fun K ↦ Scheme.IsCoefficientBoundedConstructibleEtale X A K ∧
              ∃ a b : ℤ, HasCoefficientModelTorAmplitude _ K a b) ⋙ D) := by
  sorry

end AlgebraicGeometry.ProEtale
