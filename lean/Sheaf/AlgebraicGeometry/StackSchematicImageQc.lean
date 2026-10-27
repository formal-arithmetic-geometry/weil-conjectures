/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Sheaf.AlgebraicGeometry.AlgebraicStackQuasicompactSurjection
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealClosedSubspaceCorrespondence
import Sheaf.AlgebraicGeometry.StackPointTopology

/-! # Schematic images of quasi-compact stack morphisms

Source: Stacks Project, stacks-morphisms.tex, Tags 0CPU, 0CMK and 0CML;
spaces-morphisms.tex, Tags 03MB, 082X and 082Z
(blueprint: lem-sfb-stack-schematic-image-qc).

Closed subspaces and their quasi-coherent ideals are the existing subobjects. The kernel
is specified on every etale scheme chart using the canonical direct-image structure map.
The epimorphism onto the closed subspace's direct image expresses the quotient sheaf.
Flat base change is expressed by a cartesian closed subspace with the same minimality
property. After etale base change, joint detection of functions on all comma objects is
exactly injectivity into the compatible-family direct image, without a choice of atlas.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- A quasi-compact algebraic-stack map to an algebraic space has a smallest closed
factorization, with its quasi-coherent kernel ideal, quotient sheaf, topological closure,
schematic dominance, flat base change, and etale-local schematic dominance.
Source: Stacks Project, Tags 0CPU, 0CMK, 0CML, 03MB, 082X and 082Z
(blueprint: lem-sfb-stack-schematic-image-qc).

Proof:
1. On an affine etale chart V of Y, choose an affine smooth surjective atlas U of X_V
using lem-sfb-algebraic-stack-fibre-products and
lem-sfb-algebraic-stack-quasicompact-surjection. A compatible function family vanishing
on U vanishes everywhere: pull the atlas back to each object and use its etale-local
sections (lem-sfb-smooth-space-cover-etale-sections), then the sheaf condition. This uses
lem-sfb-stack-chartwise-smooth-etale-calculus and def-sfb-stack-quasi-coherent-algebra,
and remains valid after base change. No quasi-compactness of the atlas map is needed.
2. The affine scheme-image kernel theorem lem-weil-pbc-scheme-image-qc-kernel gives
Z = Spec(Gamma(V)/J), where J is the kernel for U to V. By
lemma-nagata-scheme-image-ideal-qc the map U to Z is schematically dominant. Both schemes
are affine, so lemma-nagata-dense-flat-pullback applies to this qcqs map and proves that
Z pulls back to the image after every flat affine base change. Only affine scheme maps
are required to be quasi-separated.
3. Step 1 identifies the intrinsic structure-map kernel on every affine etale V' over V
with the affine kernel of step 2, namely J O(V'). Thus the kernel is quasi-coherent.
lem-sfb-space-ideal-closed-subspace-correspondence constructs W with this ideal and
quotient structure sheaf; W times_Y V is Z. The construction is independent of the atlas.
4. For any object T of X, etale-local sections of the pulled-back atlas show that the
pulled-back ideal vanishes locally, hence on T. The closed-subspace factorization
criterion gives its unique map to W. These maps respect arrows and define q. Any other
closed factorization has ideal contained in the kernel, hence contains W by the
inclusion-reversing ideal correspondence. Point-set containment alone is not used.
5. By lem-sfb-stack-point-topology, U surjects onto the points of X_V. The scheme image
has support equal to the closure of the image of U. Given w in W and an open
neighbourhood in Y, lift w to Z in an etale chart; the lifted neighbourhood meets U.
Thus w belongs to the image closure. The converse follows from the closed factorization.
6. For flat Y' to Y choose compatible affine etale charts V' to V. Their map is flat.
The pulled-back atlas and steps 1--2 identify the new kernel with J O(V'). The
closed-subspace correspondence identifies the image with W times_Y Y'. Quasi-compactness
of the new stack map follows from def-sfb-stack-qcqs-morphism. No flat base-change theorem
for the entire direct image is needed.
7. The map q is quasi-compact since W to Y is a monomorphism. Its kernel cuts out a
closed subspace W0 of W through which q factors. Its composite is closed in Y, so
minimality forces W0 = W and the kernel is zero. Apply step 6 to q: after every flat
base change, in particular every etale base change, its image is still the whole target.
The same zero-kernel argument gives injectivity there. All steps include empty sources,
identity maps, nonreduced targets, and stacks without quasi-separatedness. -/
theorem exists_stack_schematicImage_of_quasiCompact {S : Scheme.{u}}
    (X : BasedCategory.{v, w} (Over S)) (hX : IsAlgebraicModuliStack X)
    (Y : AlgebraicSpace S) (f : BasedFunctor X (discreteModuli Y.obj.obj))
    (hf : IsQuasiCompactAlgebraicModuliMap.{u, v, w, u, u + 1, 0, 0} f) :
    ∃ (W : ClosedSubspace Y)
      (q : BasedFunctor X (discreteModuli (W.val : AlgebraicSpace S).obj.obj))
      (I : QuasiCoherentIdeal Y),
      Nonempty (f ≅ q.comp (discreteModuliMap W.val.arrow.hom.hom)) ∧
      (∀ (D : ClosedSubspace Y)
        (a : BasedFunctor X (discreteModuli (D.val : AlgebraicSpace S).obj.obj)),
        Nonempty (f ≅ a.comp (discreteModuliMap D.val.arrow.hom.hom)) → W.val ≤ D.val) ∧
      I.val = kernelSubobject (moduleStructureMap W.val.arrow) ∧
      Epi (moduleStructureMap W.val.arrow) ∧
      (∀ (T : Y.EtaleSite) (r : Y.structureSheaf.obj.obj (op T)),
        (∃ s : (I.val : Y.Modules).val.obj (op T), I.val.arrow.val.app (op T) s = r) ↔
          moduliStructureMapApp hX.1.1 Y f T r = 0) ∧
      Set.range (moduliPointMap (discreteModuliMap W.val.arrow.hom.hom)) =
        closure (Set.range (moduliPointMap f)) ∧
      (∀ T : (W.val : AlgebraicSpace S).EtaleSite,
        Function.Injective (moduliStructureMapApp hX.1.1 (W.val : AlgebraicSpace S) q T)) ∧
      (∀ (Y' : AlgebraicSpace S) (g : Y' ⟶ Y), MapIsFlat g →
        ∃ (W' : ClosedSubspace Y')
          (a : (W'.val : AlgebraicSpace S) ⟶ (W.val : AlgebraicSpace S))
          (q' : BasedFunctor (moduliTwoFiberProduct f (discreteModuliMap g.hom.hom))
            (discreteModuli (W'.val : AlgebraicSpace S).obj.obj)),
          IsPullback a W'.val.arrow W.val.arrow g ∧
          Nonempty (moduliTwoFiberSnd f (discreteModuliMap g.hom.hom) ≅
            q'.comp (discreteModuliMap W'.val.arrow.hom.hom)) ∧
          ∀ (D : ClosedSubspace Y')
            (b : BasedFunctor (moduliTwoFiberProduct f (discreteModuliMap g.hom.hom))
              (discreteModuli (D.val : AlgebraicSpace S).obj.obj)),
            Nonempty (moduliTwoFiberSnd f (discreteModuliMap g.hom.hom) ≅
              b.comp (discreteModuliMap D.val.arrow.hom.hom)) → W'.val ≤ D.val) ∧
      (∀ (W' : AlgebraicSpace S) (g : W' ⟶ (W.val : AlgebraicSpace S)),
        IsEtale g.hom.hom → ∀ (T : W'.EtaleSite) (r : W'.structureSheaf.obj.obj (op T)),
          (∀ i : ModuliPushforwardIndex W'
              (moduliTwoFiberSnd q (discreteModuliMap g.hom.hom)) T,
            (Scheme.Γ.map (moduliChartSchemeMap W'
              (moduliTwoFiberSnd q (discreteModuliMap g.hom.hom)) T i).op) r = 0) →
          r = 0) := by
  sorry

end CategoryTheory
