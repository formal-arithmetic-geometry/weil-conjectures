/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.ReducedCurveDualizingModule
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact

/-! # Nonzero ideal-twisted H¹ forces a low-degree subcurve

Source: Stacks Project, curves.tex, Tag 0E3E, lemma-vanishing-on-gorenstein,
including its connected-component reduction before the Euler calculation.
(blueprint: lem-sfb-curve-ideal-h1-subcurve-obstruction).

The bound uses the Euler-characteristic degree and the actual global sections of the
scheme-theoretic intersection. Its scalar action is induced by the structure morphism.
The dimension-at-most-zero convention includes the empty closed subscheme.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

/-- Nonvanishing of ideal-twisted first cohomology on a proper reduced connected curve
forces a reduced connected closed subcurve with the stated degree bound.

Source: Stacks Project, curves.tex, Tag 0E3E, lemma-vanishing-on-gorenstein.
(blueprint: lem-sfb-curve-ideal-h1-subcurve-obstruction).

Proof (the node's seven steps):
1. By lem-trf-proper-field-invertible-coherent, X is Noetherian and L and O_X are
   coherent. Quasi-coherent ideals are locally finitely generated, hence coherent by
   pqf-lem-coherent-ft-locnoeth. Tensoring by L preserves exactness and coherence.
   There are finitely many components. A zero-dimensional component would be clopen;
   connectedness and dimension one exclude it, so X has pure dimension one.
2. By lem-sfb-reduced-curve-dualizing-module, nonzero H^1 supplies a nonzero map
   phi : I_Z tensor L -> omega_X. A nonzero vector space has a nonzero functional,
   by extending a nonzero vector to a basis. Let Y be the reduced union of components
   where the generic stalk map is nonzero. Generic detection makes Y nonempty.
3. If J defines Y, phi kills J I_Z L: on Y, J is generically zero, and off Y, phi
   is generically zero. Generic detection kills the image. Thus phi factors through
   the restriction to Y and into the annihilator of J in omega_X. Closed immersions
   preserve properness by lem-weil-pbc-closed-immersion-proper. The identification in
   lem-sfb-closed-subcurve-dualizing-adjunction gives a map to omega_Y, generically
   nonzero on every component.
4. Put T = Z times_X Y, L_Y = L|Y and I' = ker(O_Y -> O_T). Locally the natural
   surjection I_Z/J I_Z -> (I_Z + J)/J has generically zero kernel, since Z has
   dimension at most zero. Kernels and cokernels are coherent by
   lem-weil-pbc-coherent-modules-kernel-cokernel-sum. The generic-detection theorem
   kills the image of that kernel in omega_Y, giving alpha : I' L_Y -> omega_Y.
   Its component-generic maps are isomorphisms of one-dimensional vector spaces.
5. The kernel of alpha is a submodule of L_Y with zero generic stalks. On a reduced
   affine trivialization, a section vanishing at all minimal-prime localizations is
   zero. Hence alpha is injective. Its coherent cokernel Q is generically zero and
   therefore has zero-dimensional support on the Noetherian pure curve Y.
6. Choose a connected component B of Y. It is nonempty, reduced, clopen in Y and
   closed in X, and has dimension one. Restrict the exact sequence to B. Extending
   coherent modules by zero to the other clopen components identifies the restricted
   dualizing pair with omega_B by lem-sfb-reduced-curve-dualizing-module. This yields
   0 -> I_B L_B -> omega_B -> Q_B -> 0, with I_B the ideal of Z times_X B.
7. By lem-pc-chi-zero-dim-support, the quotient O_B/I_B tensored with L_B has Euler
   characteristic dim_k Gamma(Z times_X B, O), while chi(Q_B) is nonnegative.
   Additivity from lem-pc-euler-additive and def-pc-degree-line-bundle gives
   chi(I_B L_B) = deg(L_B) + chi(O_B) - dim_k Gamma(Z times_X B, O).
   Duality gives chi(omega_B) = -chi(O_B), so the second exact sequence gives
   0 <= chi(Q_B) = -2 chi(O_B) - deg(L_B) + dim_k Gamma(Z times_X B, O).
   Rearrange to obtain the bound. The same argument includes empty Z or intersection.
-/
theorem exists_subcurve_degree_le_of_ideal_h1_nonzero
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [IsReduced X] [ConnectedSpace X]
    (hdim : topologicalKrullDim X = 1)
    (L : X.Modules) [L.IsInvertible]
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
    (hZ : topologicalKrullDim Z ≤ 0)
    (hH : ¬ Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj
      (i.ker.toModules ⊗ L : X.Modules))) :
    ∃ (B : Scheme.{u}) (b : B ⟶ X),
      IsClosedImmersion b ∧ IsReduced B ∧ ConnectedSpace B ∧
      topologicalKrullDim B = 1 ∧
      @Scheme.Modules.degree k _ B ⟨b ≫ X ↘ Spec (.of k)⟩
          ((Scheme.Modules.tensorPullback b).obj L) ≤
        -2 * @Scheme.Modules.eulerChar k _ B ⟨b ≫ X ↘ Spec (.of k)⟩
          (SheafOfModules.unit B.ringCatSheaf) +
        (@Module.finrank k Γ(pullback i b, ⊤) _ _
          (Module.compHom Γ(pullback i b, ⊤)
            (((Scheme.ΓSpecIso (.of k)).inv ≫
              (pullback.fst i b ≫ i ≫ X ↘ Spec (.of k)).appTop).hom)) : ℤ) := by
  sorry

end AlgebraicGeometry
