/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.StackUniversalHomeomorphism
public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Sheaf.AlgebraicGeometry.AlgebraicStackQuasicompactSurjection
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCompactFppfLocal
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.RelativeInertiaSecondDiagonalGeometry
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Target-étale locality of qcqs and universal homeomorphisms

Source: Stacks Project, stacks-morphisms.tex, Tags 06TZ, 0DTL, 0DTQ, 050F, 050V, 0CI8
(blueprint: lem-sfb-stack-etale-local-qcqs-homeomorphism).

Each of the three properties is tested separately. The arbitrary-base-change assertion
has no covering-family hypothesis. In particular its target need not admit an étale
algebraic-space cover, and no DM condition is imposed on either endpoint.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃ v₄ w₄ z

open AlgebraicGeometry

namespace CategoryTheory

/-- Quasi-compactness, quasi-separatedness and universal homeomorphism are separately
local on the target for a small jointly surjective representable étale space family.
Joint surjectivity retains the field extension and the isomorphism of the actual objects.
Source: Stacks Project, stacks-morphisms.tex, Tags 06TZ, 0DTL and 0DTQ, family version
(blueprint: lem-sfb-stack-etale-local-qcqs-homeomorphism).

Proof, following the eight steps of the DAG node:
1. Fibre products are algebraic by lem-sfb-algebraic-stack-fibre-products. Reassociate
triples in the 2-fibre product to see that quasi-compactness and universal homeomorphism
are stable under base change, giving their forward implications.
2. For a quasi-compact test Z, choose an affine smooth atlas C by
lem-sfb-algebraic-stack-quasicompact-surjection. The spaces C ×_B W_i have disjoint-affine
étale atlases by lem-a1-space-affine-etale-cover. Their images cover C by field-extension
lifting and are open by lem-sfb-stack-point-topology-flat-lfp-open and
lem-sfb-stack-chartwise-smooth-etale-calculus. Affine quasi-compactness selects finitely
many affine charts V_j; the W_i themselves need not be quasi-compact.
3. Each A ×_B V_j is quasi-compact by the assumed local property. Choose affine smooth
atlases H_j. Their finite coproduct is affine by lem-weil-pbc-finite-affine-coproduct-spectrum
and quasi-compact by lem-weil-pbc-affine-scheme-qcqs. It surjects onto A ×_B Z by successive
field lifts. The quasi-compact surjection criterion proves the reverse implication.
4. For spaces, the diagonal after base change is the pullback of the old diagonal.
Apply lem-sfb-space-quasicompact-fppf-local to that diagonal. This proves base-change
stability and jointly surjective flat-lfp descent of space quasi-separatedness; the same
node supplies the corresponding quasi-compactness assertions.
5. Put D = A ×_B A. By lem-sfb-relative-inertia-second-diagonal-geometry the relative
diagonal is representable. The triple identities of
lem-sfb-groupoid-diagonal-two-pullback-identities identify each local diagonal with its
base change to D ×_B W_i. Apply step 4 to every scheme test of D: its inverse images of
the W_i form a jointly surjective étale space family. Thus both quasi-compactness and
quasi-separatedness of the diagonal descend. The same scheme-test argument proves
base-change stability of stack quasi-separatedness.
6. For an arbitrary Z → B, take smooth scheme atlases U_i of W_i ×_B Z. Reassociation
identifies P_i = (A ×_B Z) ×_Z U_i → U_i with a base change of the local map, so its point
map h_i is a homeomorphism. The projections to Z and P = A ×_B Z are smooth and jointly
surjective, by lem-sfb-stack-chartwise-smooth-etale-calculus.
7. Their point maps are open by lem-sfb-stack-point-topology-flat-lfp-open: for the
projection with stack source first take a smooth scheme atlas and use its surjectivity.
All point maps are continuous by lem-sfb-stack-point-topology.
8. The map h:|P| → |Z| is surjective by lifting to some U_i. For injectivity, represent
two points with equal image over a common field extension, lift that common target to
some U_i, and use injectivity of h_i. For open O in |P| its image is the union of the
images of h_i(p_i⁻¹(O)) under the open maps |U_i| → |Z|. Thus h is an open continuous
bijection, hence a homeomorphism. Empty families and empty tests are included. -/
theorem stack_etale_local_qcqs_homeomorphism {S : Scheme.{u}}
    (A : BasedCategory.{v₁, w₁} (Over S)) (B : BasedCategory.{v₂, w₂} (Over S))
    (f : BasedFunctor A B) (hA : IsAlgebraicModuliStack A) (hB : IsAlgebraicModuliStack B)
    (I : Type z) (W : I → AlgebraicSpace S)
    (a : ∀ i : I, BasedFunctor (discreteModuli (W i).obj.obj) B)
    (ha : ∀ i : I, IsEtaleModuliMap (a i))
    (hsurj : ∀ (K : Type u) [Field K] (b : Spec (.of K) ⟶ S)
      (y : BasedFunctor (discreteModuli (yoneda.obj (Over.mk b))) B),
      ∃ (i : I) (L : Type u) (_ : Field L) (j : K →+* L)
        (x : BasedFunctor
          (discreteModuli (yoneda.obj (Over.mk (Spec.map (CommRingCat.ofHom j) ≫ b))))
          (discreteModuli (W i).obj.obj)),
        Nonempty (ModuliTwoIso (x.comp (a i))
          ((discreteModuliMap (yoneda.map
            (Over.homMk (Spec.map (CommRingCat.ofHom j))))).comp y))) :
    (IsQuasiCompactAlgebraicModuliMap.{u, _, _, _, _, v₃, w₃} f ↔
      ∀ i : I, IsQuasiCompactAlgebraicModuliMap.{u, _, _, _, _, v₃, w₃}
        (moduliTwoFiberFst (a i) f)) ∧
    (IsQuasiSeparatedAlgebraicModuliMap f ↔
      ∀ i : I, IsQuasiSeparatedAlgebraicModuliMap (moduliTwoFiberFst (a i) f)) ∧
    (IsUniversalHomeomorphismAlgebraicModuliMap.{u, _, _, _, _, v₃, w₃} f ↔
      ∀ i : I, IsUniversalHomeomorphismAlgebraicModuliMap.{u, _, _, _, _, v₃, w₃}
        (moduliTwoFiberFst (a i) f)) := by
  sorry

/-- Each of the three properties is preserved by arbitrary algebraic-stack base change,
without any covering, representability, DM, inertia or finite-type hypothesis.
Source: Stacks Project, stacks-morphisms.tex, Tags 050V, 050F and 0CI8
(blueprint: lem-sfb-stack-etale-local-qcqs-homeomorphism).

Proof: DAG step 1 reassociates the explicit triples and their comparison isomorphisms.
A further quasi-compact test of a base change is therefore a quasi-compact test of f;
a further point map is one already tested by universal homeomorphism of f. For
quasi-separatedness, DAG steps 4 and 5 identify the new relative diagonal with the base
change of the old one (lem-sfb-groupoid-diagonal-two-pullback-identities). Its scheme
base changes remain spaces by lem-sfb-relative-inertia-second-diagonal-geometry, and
space quasi-compactness and quasi-separatedness are preserved by step 4, using
lem-sfb-space-quasicompact-fppf-local on the diagonal. Transport the actual projections
through these equivalences. Algebraicity is lem-sfb-algebraic-stack-fibre-products. -/
theorem stack_qcqs_homeomorphism_baseChange {S : Scheme.{u}}
    (A : BasedCategory.{v₁, w₁} (Over S)) (B : BasedCategory.{v₂, w₂} (Over S))
    (C : BasedCategory.{v₃, w₃} (Over S))
    (f : BasedFunctor A B) (g : BasedFunctor C B)
    (hA : IsAlgebraicModuliStack A) (hB : IsAlgebraicModuliStack B)
    (hC : IsAlgebraicModuliStack C) :
    (IsQuasiCompactAlgebraicModuliMap.{u, _, _, _, _, v₄, w₄} f →
      IsQuasiCompactAlgebraicModuliMap.{u, _, _, _, _, v₄, w₄}
        (moduliTwoFiberFst g f)) ∧
    (IsQuasiSeparatedAlgebraicModuliMap f →
      IsQuasiSeparatedAlgebraicModuliMap (moduliTwoFiberFst g f)) ∧
    (IsUniversalHomeomorphismAlgebraicModuliMap.{u, _, _, _, _, v₄, w₄} f →
      IsUniversalHomeomorphismAlgebraicModuliMap.{u, _, _, _, _, v₄, w₄}
        (moduliTwoFiberFst g f)) := by
  sorry

end CategoryTheory
