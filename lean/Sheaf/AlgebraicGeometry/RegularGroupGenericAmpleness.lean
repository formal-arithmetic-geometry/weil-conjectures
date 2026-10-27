module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
public import WeilConjectures.AlgebraicGeometry.Ample

import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Sheaf.AlgebraicGeometry.NoetherianFibreAmpleNeighbourhood
import Sheaf.TraceFormula.SchemeRelativeAmpleAffineCover
import Sheaf.AlgebraicGeometry.RigidifiedLineExtension

/-! # Generic ampleness of a symmetric line on a regular-base group scheme

Source: Deligne, Le lemme de Gabber, Proposition 4.3 and Section 4.8, pp. 142, 144;
the scheme criterion cited there is Raynaud, Faisceaux amples, XI Theorem 1.13.
The general regular-base formulation is the agent-extracted supporting criterion
recorded in the DAG, rather than the literal Picard-specific Proposition 4.3.
(blueprint: lem-sfb-regular-group-generic-ampleness)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonObj

namespace AlgebraicGeometry

/-- A symmetric invertible module on a smooth separated commutative group scheme
with semiabelian geometric fibres over a regular locally Noetherian base is relatively
ample if it is ample on every component's generic fibre, provided the group is proper
on a dense base open. Relative ampleness means absolute ampleness over every affine
base open; all module restrictions use tensor inverse image.

Source: Deligne, Le lemme de Gabber, Proposition 4.3 and Section 4.8, pp. 142, 144;
Raynaud, Faisceaux amples, XI Theorem 1.13, as extracted in the DAG.
(blueprint: lem-sfb-regular-group-generic-ampleness)

Proof plan, following the six DAG steps:
1. Trivialize the identity pullback of L on an affine base cover. By
   rem-pc-regular-normal, refine to normal integral regular Noetherian affine pieces T.
   The trivialization rigidifies L on each piece, and V meets T densely.
2. The identity section makes every fibre nonempty. Apply
   lem-trf-smooth-connected-fibre-normal-integrality to obtain geometrically integral
   fibres. Inside the proper open V, apply lem-trf-noetherian-fibre-ample-neighbourhood
   at T's generic point. Obtain an affine dense open U on whose inverse image L is
   ample; lem-trf-scheme-relative-ample-affine-cover gives relative ampleness there.
3. Apply lem-sfb-symmetric-ample-power-extension to the rigidified symmetric line
   on G_U. Obtain an affine cover T_i, positive n_i and relatively ample rigidified
   lines B_i agreeing, by specified rigidified isomorphisms, with L to the n_i-th
   tensor power over U intersect T_i. All semiabelian and proper-open assumptions
   are inherited from G and V.
4. By lem-sfb-regular-group-rigidified-line-extension, full faithfulness extends each
   specified comparison to B_i isomorphic to the n_i-th power of L on all G_{T_i}.
   Use geometric integrality from step 2 and regularity of T_i.
5. Since T_i is affine, B_i is absolutely ample. A section of a positive m-th power
   of B_i becomes a section of the positive (n_i*m)-th power of L with the same
   affine nonvanishing open. The definition def-weil-pbc-ample-invertible-module
   therefore gives ampleness of L on G_{T_i}, including its quasi-compactness.
6. Finite presentation makes the structure map quasi-compact. Apply
   lem-trf-scheme-relative-ample-affine-cover to this affine cover to get ampleness
   over every affine base open. For the empty base the same conclusion holds.
-/
theorem regularGroupGenericAmpleness
    {S : Scheme.{u}} (hS : IsRegularScheme S)
    (G : Grp (Over S)) [IsCommMonObj G.X]
    [Smooth G.X.hom] [IsSeparated G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [GeometricallyConnected G.X.hom]
    (hG : HasSemiabelianGeometricFibres G)
    (V : S.Opens) (hV : Dense (V : Set S))
    (hproper : IsProper (G.X.hom ∣_ V))
    (L : G.X.left.Modules) [L.IsInvertible]
    (symmetry : (Scheme.Modules.tensorPullback ι[G.X].left).obj L ≅ L)
    (hgeneric : ∀ (C : Set S), C ∈ irreducibleComponents S →
      ∀ ξ : S, IsGenericPoint ξ C →
        @Scheme.Modules.IsAmple (G.X.hom.fiber ξ)
          ((Scheme.Modules.tensorPullback (G.X.hom.fiberι ξ)).obj L)
          ((Scheme.Modules.invertible_pullback_tensor (G.X.hom.fiberι ξ)).1 L).2) :
    ∀ (W : S.Opens), IsAffineOpen W →
      @Scheme.Modules.IsAmple (G.X.hom ⁻¹ᵁ W).toScheme
        ((Scheme.Modules.tensorPullback (G.X.hom ⁻¹ᵁ W).ι).obj L)
        ((Scheme.Modules.invertible_pullback_tensor (G.X.hom ⁻¹ᵁ W).ι).1 L).2 := by
  sorry

end AlgebraicGeometry
