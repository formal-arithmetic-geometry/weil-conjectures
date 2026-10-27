/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.StackSpaceEtaleComparisons
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange

import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction

/-! # Small étale comparison calculus on algebraic-space tests of a stack

Source: Stacks Project, stacks-sheaves.tex, Tags 075D, 076R and 0GQC;
stacks-cohomology.tex, Tag 0762
(blueprint: lem-sfb-stack-small-etale-comparison-calculus).

Restrictions are actual precomposition, with the canonical regular-function transport.
The tensor-section normalization characterizes comparisons and the pullback unitors and
compositors, so none of the coherence assertions concerns an arbitrary map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w m

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

namespace CategoryTheory

/-- Small étale comparisons on algebraic-space tests, including flat compatibility.
The comparison's defining normalization above is its agreement on every scheme chart;
its natural-transformation type is naturality in H. The identity and composition
clauses explicitly prescribe the identity and pasted two-isomorphisms. They therefore
apply in particular to the canonical two-isomorphisms of a groupoid presentation.
The scheme-test local-presentation hypothesis is equivalently the associated étale
sheaf of a quasi-coherent Zariski module, by the Zariski/étale equivalence.

Source: Stacks 075D, 076R, 0GQC and 0762
(blueprint: lem-sfb-stack-small-etale-comparison-calculus).

Proof:
1. Apply lem-sfb-fibred-fppf-space-module-comparisons to C and its module H.
   The restriction is literal evaluation on z(T), and the adjoint restriction map
   is the uniquely tensor-normalized comparison above. Naturality, identity,
   composition, scheme-chart agreement and étale invertibility follow from that
   theorem, without requiring H to be quasi-coherent on the big site.
2. Under scheme-test quasi-coherence, every étale scheme chart e:E to V identifies
   e-star H_z with H_ze by Step 1. The scheme Zariski/étale quasi-coherent equivalence
   gives local free presentations on E_et. These are the same presentations on the
   localized site of V_et; composing their covers proves quasi-coherence of H_z.
3. For flat a:V to W choose surjective étale scheme atlases E to V and T to W.
   P=E times_W T is a scheme by lem-trf-space-representable-etale-scheme-tests.
   By lem-trf-space-fibre-products-etale-covers its map d to E is surjective étale,
   so r=e d is a surjective étale chart of V. The map f:P to T is flat by the
   chart definition of MapIsFlat. This uses no scheme representability of a.
4. Equip the tests on P and T with the pasted two-isomorphism. Composition gives
   c_r r-star(c_a) = c_f f-star(c_t). The chart comparisons c_r,c_t are invertible;
   c_f is invertible by flat scheme-test compatibility. Therefore r-star(c_a)
   is invertible. The étale tensor-restriction theorem identifies r-star with
   ordinary restriction. On every test A to V, use the surjective étale cover
   A times_V P to A. The local inverses agree on overlaps by uniqueness of inverse.
   The sheaf axiom glues them, and uniqueness gives naturality in A. Hence c_a
   is invertible on V_et.
5. The universal quantification over tests and prescribed two-isomorphisms includes
   the canonical ones from any groupoid presentation. No flatness of an arbitrary
   presentation map is asserted. -/
theorem stack_smallEtale_comparison_calculus {S : Scheme.{u}}
    (C : BasedCategory.{v, w} (Over S)) (hC : IsAlgebraicModuliStack C) :
    (∀ (V : AlgebraicSpace S) (z : BasedFunctor (discreteModuli V.obj.obj) C)
      (theta : ModuliTwoIso z ((discreteModuliMap (𝟙 (V.obj.obj))).comp z)),
      (∀ T : (discreteModuli V.obj.obj).obj,
        theta.val.hom.app T = z.map (CostructuredArrow.homMk (𝟙 T.left)
          (by simp))) →
      ∀ H : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC.1.1),
        (stackSpaceComparison hC.1.1 (𝟙 V) z z theta).app H =
          (stackSpaceTensorId.{u, max v w} V).hom.app
            ((stackSpaceRestriction hC.1.1 z).obj H)) ∧
    (∀ (V W B : AlgebraicSpace S) (a : V ⟶ W) (b : W ⟶ B)
      (z : BasedFunctor (discreteModuli V.obj.obj) C)
      (t : BasedFunctor (discreteModuli W.obj.obj) C)
      (r : BasedFunctor (discreteModuli B.obj.obj) C)
      (theta : ModuliTwoIso z ((discreteModuliMap a.hom.hom).comp t))
      (eta : ModuliTwoIso t ((discreteModuliMap b.hom.hom).comp r))
      (gamma : ModuliTwoIso z ((discreteModuliMap (a ≫ b).hom.hom).comp r)),
      (∀ T : (discreteModuli V.obj.obj).obj,
        gamma.val.hom.app T = theta.val.hom.app T ≫
          eta.val.hom.app ((discreteModuliMap a.hom.hom).obj T) ≫
            r.map (eqToHom (CostructuredArrow.map_comp
              (f := a.hom.hom) (f' := b.hom.hom) (h := T)).symm)) →
      ∀ H : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC.1.1),
        (stackSpaceTensorComp.{u, max v w} a b).hom.app
            ((stackSpaceRestriction hC.1.1 r).obj H) ≫
          (stackSpaceComparison hC.1.1 (a ≫ b) z r gamma).app H =
        (AmbientCoefficients.moduleTensorPullback.{u, max v w} a).map
            ((stackSpaceComparison hC.1.1 b t r eta).app H) ≫
          (stackSpaceComparison hC.1.1 a z t theta).app H) ∧
    (∀ (V W : AlgebraicSpace S) (a : V ⟶ W)
      (z : BasedFunctor (discreteModuli V.obj.obj) C)
      (t : BasedFunctor (discreteModuli W.obj.obj) C)
      (theta : ModuliTwoIso z ((discreteModuliMap a.hom.hom).comp t))
      (H : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC.1.1)),
      IsChartwiseEtale a → IsIso ((stackSpaceComparison hC.1.1 a z t theta).app H)) ∧
    (∀ H : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC.1.1),
      (∀ (T : Over S) (z : BasedFunctor (discreteModuli (schemeSpace T).obj.obj) C),
        ((stackSpaceRestriction hC.1.1 z).obj H).IsQuasicoherent) →
      (∀ (V : AlgebraicSpace S) (z : BasedFunctor (discreteModuli V.obj.obj) C),
        ((stackSpaceRestriction hC.1.1 z).obj H).IsQuasicoherent) ∧
      ((∀ (U T : Over S) (a : U ⟶ T)
        (z : BasedFunctor (discreteModuli (schemeSpace U).obj.obj) C)
        (t : BasedFunctor (discreteModuli (schemeSpace T).obj.obj) C)
        (theta : ModuliTwoIso z ((discreteModuliMap (yoneda.map a)).comp t)),
        Flat a.left → IsIso ((stackSpaceComparison hC.1.1
          (stackSpaceSchemeMap a) z t theta).app H)) →
        ∀ (V W : AlgebraicSpace S) (a : V ⟶ W)
          (z : BasedFunctor (discreteModuli V.obj.obj) C)
          (t : BasedFunctor (discreteModuli W.obj.obj) C)
          (theta : ModuliTwoIso z ((discreteModuliMap a.hom.hom).comp t)),
          MapIsFlat a → IsIso ((stackSpaceComparison hC.1.1 a z t theta).app H))) := by
  sorry

end CategoryTheory
