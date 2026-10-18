/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.Topology.NoetherianSpace
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.SixFunctors.GeometricInverseImageConstantModule

/-!
# Affine-local and global constructibility on Noetherian schemes

Source: Stacks Project, etale-cohomology.tex, Tag 095E,
lemma-constructible-quasi-compact-quasi-separated; proetale.tex, Tag 09AJ,
definition-constructible; topology.tex, Tag 005L
(blueprint: lem-sfb-noetherian-global-constructibility).

The two statements treat the small etale and small pro-etale sites separately. Equivalent
coefficient-sized site models keep the coefficient universe independent of the scheme
universe. The sheaf is an intrinsic module over the constant coefficient ring sheaf.
Finite generation on the etale side is equivalent to finite presentation because the
coefficient ring is Noetherian; it never means finiteness of the underlying set.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- On the small etale site, affine-local constructibility is equivalent to a single
finite constructible locally closed immersed stratification with locally constant
finitely presented module values. Finite generation in the existing local-constancy
predicate is equivalent to finite presentation over `R`.
Source: Stacks Project, Tag 095E, Noetherian module version; Tags 03RW(3) and 005L
(blueprint: lem-sfb-noetherian-global-constructibility).

Proof plan:
1. Choose a finite affine Noetherian cover of X. The underlying spaces of its members
are Noetherian (lem-sc-affine-noetherian-underlying-space), so their finite union is
Noetherian (lem-kun-finite-union-noetherian). Every subset is quasi-compact, including
X and every open (lem-sfb-noetherian-space-compact-subsets); this includes the empty cover.
2. The same cover makes X locally Noetherian (pqf-def-locnoeth), hence quasi-separated
(lem-weil-pbc-locally-noetherian-quasi-separated). Every open in any open subspace is
retrocompact, so every locally closed part is constructible (def-weil-constructible-subset).
3. Pull back trivializing etale coverings using lem-weil-pbc-etale-covering-base-change.
Finite limits of site base change (lem-weil-pbc-etale-base-change-finite-limits) and
lem-weil-pbc-left-exact-site-inverse-image-tensor give geometric inverse image and its
composition comparisons. Equivalences to the coefficient-sized sites preserve these data.
4. The scalar identifications and localized composition are
lem-pe-constant-left-module-inverse-image. Apply
lem-sfb-geometric-inverse-image-constant-module to each pulled-back local model: the
same module M gives a constant model, with its finite presentation unchanged. Over R,
Module.finitePresentation_of_finite and the converse instance identify the recorded
finite-generation predicate with finitely presented values.
5. Under affine-local constructibility, take the partitions on the finite affine cover.
lem-weil-pbc-etale-stratification-local-gluing-core supplies a global immersed refinement
and actual morphisms from its strata to local strata. Pull back their local models by
steps 3-4 to prove the right side; image containment alone is not used as factorization.
6. Conversely, lemma-constructible-pullback-stratification pulls a global partition back
to any affine open, including the empty one. Step 2 gives constructibility of its parts,
and steps 3-4 give their locally constant finitely presented models. No step needs R or M
to be finite as a set. -/
theorem etale_noetherian_global_constructibility
    (X : Scheme.{u}) [IsNoetherian X]
    (R : Type (max v (u + 1))) [CommRing R] [IsNoetherianRing R]
    (F : CategoryTheory.ConstantCompletion.Mod
      (CategoryTheory.ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X)
        R)) :
    IsCoefficientConstructibleEtaleModule X R F ↔
      ∃ S : LocallyClosedStratification X,
        (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
        ∀ a : Fin S.n, IsCoefficientModelLocallyConstantFinite
          (smallModelComparisonEtaleTopology.{u, v} (S.domain a)) R
          ((coefficientEtaleFixedPullback.{u, v} (S.immersion a) R).obj
            ((coefficientModelFixedScalars _ R).obj F)) := by
  sorry

/-- On the small pro-etale site, the same affine-local/global equivalence holds with
finitely presented constant module values, without finiteness of the coefficient set.
Source: Stacks Project, Tag 095E, finite-refinement proof; proetale.tex,
Tag 09AJ, definition-constructible; topology.tex, Tag 005L
(blueprint: lem-sfb-noetherian-global-constructibility).

Proof plan:
1. A finite affine cover by Noetherian rings has Noetherian members
(lem-sc-affine-noetherian-underlying-space), hence Noetherian union
(lem-kun-finite-union-noetherian). By lem-sfb-noetherian-space-compact-subsets every
subset is quasi-compact, also for the empty scheme and the empty cover.
2. The scheme is locally Noetherian (pqf-def-locnoeth), hence quasi-separated by
lem-weil-pbc-locally-noetherian-quasi-separated. Every open of every open subspace is
retrocompact, so locally closed parts are constructible (def-weil-constructible-subset).
3. det-pe-topos-functoriality-inverse-image supplies preservation of pro-etale covers,
finite limits and composition comparisons for inverse image. Transporting by the
coefficient-sized site equivalences preserves all these operations and coverings.
4. Use lem-pe-constant-left-module-inverse-image for scalar and localized composition
comparisons, then lem-sfb-geometric-inverse-image-constant-module on each member of a
pulled-back trivializing cover. The same finitely presented R-module is the new constant
value. Thus every scheme pullback preserves these local models.
5. Apply lem-weil-pbc-etale-stratification-local-gluing-core to the partitions on a
finite affine cover. It is a geometric refinement statement independent of sheaves and
coefficients, and it supplies actual factorization morphisms into the local immersed
strata. Step 4 pulls the locally constant finitely presented models to the global strata.
6. Conversely, base change a global partition to an arbitrary affine open using
lemma-constructible-pullback-stratification. The parts are constructible by step 2,
and their local models pull back by step 4. This gives the left side, also on the empty
open, and proves the equivalence without set-finiteness hypotheses. -/
theorem proEtale_noetherian_global_constructibility
    (X : Scheme.{u}) [IsNoetherian X]
    (R : Type (max v (u + 1))) [CommRing R] [IsNoetherianRing R]
    (F : CategoryTheory.ConstantCompletion.Mod
      (CategoryTheory.ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X)
        R)) :
    IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X R F ↔
      ∃ S : LocallyClosedStratification X,
        (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
        ∀ (a : Fin S.n) (V : coefficientProEtaleSiteModel.{u, v} (S.domain a)),
          ∃ T : Sieve V, T ∈ coefficientProEtaleModelTopology.{u, v} (S.domain a) V ∧
            ∀ (W : coefficientProEtaleSiteModel.{u, v} (S.domain a)) (f : W ⟶ V), T f →
              ∃ M : ModuleCat.{max v (u + 1)} R, Module.FinitePresentation R M ∧
                Nonempty
                  ((((coefficientProEtaleFixedModulePullback.{u, v} (S.immersion a) R).obj
                      ((coefficientModelFixedScalars _ R).obj F)).over W) ≅
                    (constantSheaf
                      ((coefficientProEtaleModelTopology.{u, v} (S.domain a)).over W)
                      (ModuleCat.{max v (u + 1)} R)).obj M) := by
  sorry

end AlgebraicGeometry.Scheme
