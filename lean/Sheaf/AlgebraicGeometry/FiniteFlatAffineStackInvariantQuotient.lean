/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Ring.Subring.Basic
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.EtaleSmoothAtlasFppfDescent
import WeilConjectures.AlgebraicGeometry.FinitePushforwardLocallyFree
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.AffineGroupoidIntegralInvariants
import Sheaf.AlgebraicGeometry.AffineGroupoidOrbitFibres
import WeilConjectures.Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Sheaf.AlgebraicGeometry.StackPointTopology
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Sheaf.AlgebraicGeometry.UniversallyHomeomorphIntegral
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.EtaleSpaceLocallyQuasiFinite
import Sheaf.AlgebraicGeometry.AffineGroupoidEtaleInvariantComparison

/-! # Invariant-ring quotient of a stack with a finite flat affine cover

Source: Stacks Project, stacks-more-morphisms.tex, Tags 0DUM, 0DUP, 0DUR and 0DUG
(blueprint: lem-sfb-finite-flat-affine-stack-invariant-quotient).

The relation is the actual 2-fibre product, with both projection comparisons.
The invariant ring is the equalizer on global functions. Its spectrum receives
an S-structure, which need not be an affine morphism to S.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w v' w'

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- The invariant spectrum of a finite flat affine stack cover is a separated,
quasi-compact uniform categorical quotient and a universal homeomorphism.
Source: Stacks Project, Tags 0DUM, 0DUP, 0DUR and 0DUG
(blueprint: lem-sfb-finite-flat-affine-stack-invariant-quotient).

Proof (the eleven steps of the DAG node):
1. By lem-sfb-stack-chartwise-smooth-etale-calculus and
lem-sfb-etale-smooth-atlas-fppf-descent the DM stack is an fppf stack.
The two projections of its cover relation are finite flat and locally finitely
presented, hence finite locally free (def-pc-finite-locally-free). Finiteness makes
the relation affine. By lem-sc-finite-pushforward-locally-free and
lem-pc-finite-flat-affine-sections-projective its affine coordinate modules are
finite projective. Groupoid operations are identity, inverse and composition
of isomorphisms in the fibre groupoids.
2. Using the S-structure constructed in step 11, descend the invariant atlas map
along the finite flat cover. For every object, maps to an algebraic space glue
uniquely over its fppf scheme of lifts. Maps to an affine target correspond to
ring maps into the equalizer, proving affine categoricality.
3. By lem-weil-pbc-fibre-product-affine-spectra and
lem-a1-affine-groupoid-basechange-polynomial-norm the relation and cover commute
with base change. Apply lem-weil-pbc-flat-tensor-exact to the equalizer sequence:
invariants commute with every flat affine base change. Step 2 applies there.
4. By lem-a1-affine-groupoid-integral-invariants the atlas ring is integral over
its invariants. Integral base change and closedness give a closed atlas map.
By lem-a1-affine-groupoid-orbit-fibres and lem-sc-finite-nonempty-point,
geometric objects lift to the atlas and their isomorphism classes are exactly
the orbits. Thus every stack base change gives a bijection on point classes.
5. A closed subset pulls back to a closed subset of the atlas, whose image is
closed by step 4. Thus affine scheme base changes are homeomorphisms. Use
lem-sfb-algebraic-stack-fibre-products and lem-sfb-stack-point-topology to descend
closedness through a smooth atlas for arbitrary algebraic-stack tests. Affine
pullbacks of the finite cover also prove quasi-compactness; finitely many affine
opens handle each quasi-compact open in a scheme test.
6. The relative diagonal pulls back along the fppf cover U times_M U to the map
R to U times_M U. Its composite to U is finite and proper. The target is separated
over U, so lemma-nagata-proper-to-separated-target makes this map proper.
Apply lem-sfb-representable-proper-fppf-target-test to descend properness of the
diagonal, proving separatedness.
7. The equalizer of two maps M to a space is a scheme monomorphism. If they agree
after q, step 5 makes that monomorphism a universal homeomorphism, hence integral
and affine by lem-trf-universally-homeomorph-integral. Affine categoricality gives
an inverse, proving uniqueness. The argument works after flat affine base change.
8. For a map to a space choose an affine etale chart of that space. Its pullback
to U is separated etale and locally quasi-finite. The finite orbit lies in an
affine open by lem-sfb-separated-lqf-affine-finite-set; then
lem-sfb-locally-free-groupoid-invariant-affine gives an invariant affine open W.
9. The restricted groupoid has cartesian endpoint and stabilizer squares.
By lem-sfb-affine-groupoid-etale-invariant-comparison its invariant spectrum N is
etale over M and W equals U times_M N. Affine categoricality factors the map to
the chosen chart through N; fppf descent identifies its pullback with the given map.
10. Such N cover M. Step 7 makes the maps agree on their affine etale overlaps;
the algebraic-space sheaf axiom glues them uniquely. Step 3 gives the same result
after flat affine base change. Affine etale covers and their overlaps then prove
the stated bijection for every flat algebraic-space base change.
11. Construct the S-structure without using steps 2--10. The atlas-to-invariant-
spectrum map is integral, closed, surjective, and has the groupoid orbits as its
fibres. The inverse image of an affine open of S is saturated, hence descends to
an open of M. On each principal affine open in that open, flat localization of
the equalizer identifies invariant functions with the localized invariant ring.
The structural ring map therefore factors uniquely through it. Injectivity into
the localized atlas ring gives agreement on overlaps. Glue these maps to M to S;
the resulting structural map has the required atlas composite. -/
theorem finiteFlatAffineStack_invariant_quotient {S : Scheme.{u}}
    (A : BasedCategory.{v, w} (Over S)) (hA : IsDeligneMumfordModuliStack A)
    (U : Over S) (hU : IsAffine U.left)
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) A)
    (ha : ModuliSchemeTest
      (fun _ _ p ↦ IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p) a) :
    ∃ (R : Over S) (s t : R ⟶ U)
      (e : BasedFunctor (discreteModuli (yoneda.obj R)) (moduliTwoFiberProduct a a)),
      IsAffine R.left ∧ e.toFunctor.IsEquivalence ∧
      Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberFst a a))
        (discreteModuliMap (yoneda.map s))) ∧
      Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberSnd a a))
        (discreteModuliMap (yoneda.map t))) ∧
      s.left.IsFiniteLocallyFree ∧ t.left.IsFiniteLocallyFree ∧
      ∃ C : Subring Γ(U.left, ⊤),
        C = RingHom.eqLocus s.left.appTop.hom t.left.appTop.hom ∧
        ∃ (σ : Spec (.of C) ⟶ S) (φ : U ⟶ Over.mk σ),
          φ.left = U.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom C.subtype) ∧
          ∃ q : BasedFunctor A (discreteModuli (yoneda.obj (Over.mk σ))),
            Nonempty (ModuliTwoIso (a.comp q) (discreteModuliMap (yoneda.map φ))) ∧
            (∀ (M₁ : AlgebraicSpace S) (b : M₁.obj.obj ⟶ yoneda.obj (Over.mk σ)),
              (∀ (T : Over S) (c : yoneda.obj T ⟶ M₁.obj.obj),
                AlgebraicSpace.IsEtale c → Flat (yoneda.preimage (c ≫ b)).left) →
              ∀ Z : AlgebraicSpace S,
                Function.Bijective (fun g : M₁.obj.obj ⟶ Z.obj.obj ↦
                  (moduliTwoFiberFst (discreteModuliMap b) q).comp
                    (discreteModuliMap g))) ∧
            ModuliSchemeTest @IsProper (moduliRelativeDiagonal q) ∧
            IsQuasiCompactModuliMap q ∧
            ∀ (T : BasedCategory.{max u v v', max (u + 1) w w'} (Over S))
              (b : BasedFunctor T (discreteModuli (yoneda.obj (Over.mk σ)))),
              IsAlgebraicModuliStack T →
                IsHomeomorph (moduliPointMap (moduliTwoFiberFst b q)) := by
  sorry

end CategoryTheory
