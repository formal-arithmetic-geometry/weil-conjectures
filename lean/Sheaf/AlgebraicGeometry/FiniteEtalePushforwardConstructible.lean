/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.EtalePullbackForgetModules
import Sheaf.Paper.FiniteEtaleEtaleLocalSplit
import Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings
import Sheaf.Paper.DirectImageSplitCoverProduct
import WeilConjectures.ConstructibleSheaf.Pullback
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleQcqsAffineLocal
import Sheaf.AlgebraicGeometry.ConstructibleSurjectivePullback

/-!
# Finite etale pushforward preserves constructibility of module sheaves

Source: Stacks Project, Etale Cohomology, Tag 095H, lemma-pushforward-constructible,
module clause for finite coefficient rings
(blueprint: lem-weil-pbc-finite-etale-pushforward-constructible).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Direct image along a finite etale morphism of qcqs schemes preserves the finite
constructible-stratification predicate for sheaves over a finite commutative ring.

Source: Stacks Project, Tag 095H, lemma-pushforward-constructible, module clause
(blueprint: lem-weil-pbc-finite-etale-pushforward-constructible).

Proof:
1. By lem-weil-pbc-constructible-qcqs-affine-local, work on an affine open A of U.
   Use lem-weil-pbc-etale-inverse-image-restriction and
   lemma-weil-pbc-etale-pullback-forget-modules to identify restriction with inverse
   image. Naturality for multiplication by every scalar makes these identifications
   module-linear; sections of the constant ring are locally constant scalars.
2. Apply lem-weil-pbc-finite-etale-etale-local-split at each point of A and pull the
   splitting back to A. By lem-weil-pbc-etale-qcqs-cofinal-finite-coverings choose a
   finite affine etale cover B_b of A subordinate to these neighbourhoods. Base change
   preserves etaleness and each splitting. Form B as their finite disjoint union using
   lem-weil-pbc-scheme-coproduct-family. Its map to A is surjective and etale by
   lem-weil-pbc-etale-local-on-source. Each component is affine and hence qcqs by
   lem-weil-pbc-affine-scheme-qcqs; intersections are a component or empty, so B is
   qcqs by lem-weil-pbc-quasi-separated-affine-cover-criterion. Sheet numbers may vary.
3. On B_b, evaluate direct image on an etale W: the fibre products W ×_U V and
   W ×_{B_b} (B_b ×_U V) are canonically isomorphic, naturally in W and compatibly
   with scalars. Thus restriction commutes with direct image. The splitting gives
   a finite product of restrictions of G by lem-weil-pbc-direct-image-split-cover-product.
   The sheet composites are etale by lem-weil-pbc-etale-scheme-base-change and
   lem-weil-pbc-etale-composition-cancellation. Each factor is constructible by
   prop-constructible-pullback and lem-weil-pbc-constructible-etale-module-sheaf-comparison.
4. A finite product is constructible by induction using clause (2) of
   thm-constructible-serre. The empty product is the zero module sheaf with finite
   constant value zero. The induction step uses the split exact sequence
   0 → P → P × H → H → 0. Transport the finite-stratum witnesses along the module
   isomorphisms in step 3.
5. The affine-local criterion makes the pullback to B constructible. Descend along
   B → A using lem-weil-pbc-etale-constructible-surjective-pullback, since B and A
   are qcqs. Apply the affine-local criterion on U to finish with precisely the
   global finite constructible-stratification predicate. -/
theorem isConstructibleEtaleModuleSheaf_lowerStar_of_finite_etale
    {V U : Scheme.{u}} [CompactSpace V] [QuasiSeparatedSpace V]
    [CompactSpace U] [QuasiSeparatedSpace U] (h : V ⟶ U) [IsFinite h] [Etale h]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (G : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : IsConstructibleEtaleModuleSheaf G) :
    IsConstructibleEtaleModuleSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) h).obj G) := by
  sorry

end AlgebraicGeometry.Scheme
