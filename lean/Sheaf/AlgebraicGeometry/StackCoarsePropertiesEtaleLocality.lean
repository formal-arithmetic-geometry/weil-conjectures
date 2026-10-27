/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.UniversalHomeomorphismModuliMap
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.DMIsomSpaceUnramified
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts

/-! # Étale locality and base change of coarse-morphism properties

Source: Stacks Project, Morphisms of Stacks, Tags 050F, 06TZ, 050V, 0DTL, 0CI8 and 0DTQ
(blueprint: lem-sfb-stack-coarse-properties-etale-locality).

Separatedness is properness of the relative diagonal. For DM stacks, the existing
quasi-compactness predicate using affine tests and compact étale atlases is equivalent
to compactness of inverse images of quasi-compact scheme opens. Universal homeomorphisms
are tested against arbitrary algebraic stacks, with their smooth-atlas point topology.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open AlgebraicGeometry

namespace CategoryTheory

/-- Each of separatedness, quasi-compactness and universal homeomorphism is étale local
on the target and stable under arbitrary DM base change. No representability assumption
is imposed on the original morphism or on the arbitrary DM base-change map.
Source: Stacks Project, Morphisms of Stacks, Tags 050F, 06TZ, 050V, 0DTL, 0CI8 and 0DTQ
(blueprint: lem-sfb-stack-coarse-properties-etale-locality).

Proof:
1. Equal image point classes admit representatives and an isomorphism over a common
field extension, hence a point of the 2-fibre product. Thus its points surject onto
the fibre product of point sets; jointly surjective families stay so after base change
(def-sfb-stable-pointed-moduli-groupoids; Stacks 04XH). No injectivity is asserted.
2. The diagonal of a base change is the pullback of the original relative diagonal:
both fibres classify isomorphisms of the same two objects inducing the same specified
comparison. The relative diagonal is representable by spaces, since its scheme fibres
are fibres of the map of Isom spaces (lem-sfb-dm-isom-space-unramified and
lem-trf-space-fibre-products-etale-covers). Proper DM diagonals have finite scheme tests.
3. Properness of these diagonal tests survives base change. Conversely, after a scheme
test of the diagonal, pull back the covering family and choose étale scheme atlases of
its algebraic-space pullbacks. This is an fppf cover; the diagonal tests become proper
by the hypotheses and step 2. Properness descends by
lem-sfb-space-flat-proper-fp-locality, using lem-a1-space-affine-etale-cover,
lem-sfb-stack-chartwise-smooth-etale-calculus and def-pc-fppf-site.
4. Scheme-test quasi-compactness survives base change by reassociating 2-fibre products.
These products are DM with étale atlases (lem-sfb-dm-etale-atlas-calculus), and their
point topologies agree (lem-sfb-stack-point-topology-flat-lfp-open).
5. To descend quasi-compactness, fix a quasi-compact open V of a scheme test. Refine
the pullbacks of W_i by affine étale scheme charts. Their maps to V are open and
jointly surjective by step 1 and lem-sfb-stack-chartwise-smooth-etale-calculus.
Compactness of V chooses finitely many covering images. Each chosen affine is compact
(lem-a1-space-affine-etale-cover, lem-weil-pbc-affine-opens-basis,
lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact).
6. Over each selected affine U, quasi-compactness of the corresponding local morphism
gives a compact point space of A ×_B U. Its continuous image covers part of A ×_B V;
step 1 says these finitely many images cover all of it. A finite union of compact images
is compact (lem-sfb-stack-point-topology-flat-lfp-open). This proves the scheme tests,
equivalently the existing affine-test compact-atlas predicate for DM stacks.
7. Universal homeomorphisms survive base change by reassociation, even when the final
test Z is an arbitrary algebraic stack. For descent, form Z_i = Z ×_B W_i and choose
smooth surjective scheme atlases U_i of them (lem-sfb-algebraic-stack-fibre-products).
The maps U_i → Z are jointly surjective and open, by step 1,
lem-sfb-stack-chartwise-smooth-etale-calculus and
lem-sfb-stack-point-topology-flat-lfp-open. Each A ×_B U_i → U_i is a homeomorphism
on points by the local hypothesis. Neither Z nor Z_i is assumed DM.
8. For h : |A ×_B Z| → |Z|, lift a point of Z to some U_i to obtain surjectivity.
If two points have equal image, step 1 lifts both together with the same point of U_i;
injectivity on that pullback makes them equal. For an open O upstairs, its inverse
images O_i have open images in U_i, and their open images in Z have union h(O), again
by step 1. Thus h is continuous, bijective and open, hence a homeomorphism. Since Z
was arbitrary, this proves universal homeomorphism descent and finishes all clauses. -/
theorem stack_coarse_properties_etale_locality {S : Scheme.{u}}
    {A B : BasedCategory.{max u v, max (u + 1) w} (Over S)}
    (hA : IsDeligneMumfordModuliStack A) (hB : IsDeligneMumfordModuliStack B)
    (f : BasedFunctor A B) (I : Type z) (W : I → Over S)
    (q : ∀ i : I, BasedFunctor (discreteModuli (yoneda.obj (W i))) B)
    (hqrep : ∀ i : I, IsRepresentableByAlgebraicSpaces (q i))
    (hqet : ∀ i : I, IsEtaleModuliMap (q i))
    (hqsurj : ∀ y : ModuliPoints B, ∃ (i : I)
      (x : ModuliPoints (discreteModuli (yoneda.obj (W i)))), moduliPointMap (q i) x = y) :
    (ModuliSchemeTest @IsProper (moduliRelativeDiagonal f) ↔
      ∀ i : I, ModuliSchemeTest @IsProper
        (moduliRelativeDiagonal (moduliTwoFiberFst (q i) f))) ∧
    (IsQuasiCompactModuliMap f ↔
      ∀ i : I, IsQuasiCompactModuliMap (moduliTwoFiberFst (q i) f)) ∧
    (IsUniversalHomeomorphismModuliMap f ↔
      ∀ i : I, IsUniversalHomeomorphismModuliMap (moduliTwoFiberFst (q i) f)) ∧
    (∀ (B' : BasedCategory.{max u v, max (u + 1) w} (Over S)),
      IsDeligneMumfordModuliStack B' → ∀ g : BasedFunctor B' B,
        (ModuliSchemeTest @IsProper (moduliRelativeDiagonal f) →
          ModuliSchemeTest @IsProper (moduliRelativeDiagonal (moduliTwoFiberFst g f))) ∧
        (IsQuasiCompactModuliMap f → IsQuasiCompactModuliMap (moduliTwoFiberFst g f)) ∧
        (IsUniversalHomeomorphismModuliMap f →
          IsUniversalHomeomorphismModuliMap (moduliTwoFiberFst g f))) := by
  sorry

end CategoryTheory
