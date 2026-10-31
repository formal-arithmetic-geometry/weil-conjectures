/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemiabelianGeometricFibres
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor

/-! # Local prolongation of a tensor power of a symmetric line

Source: Moret-Bailly, Pinceaux de varietes abeliennes, II 3.3.3, opening
power-prolongation input (Raynaud, Faisceaux amples, XI 1.13), agent-formulated
local non-positive version. The local originals are WANTED in the DAG source.
(blueprint: lem-sfb-symmetric-line-power-prolongation)

The intersection of two base restrictions is realized by their fibre product over
G. No positivity, rigidification or cubical structure on the extension is asserted.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory MonObj

namespace AlgebraicGeometry

/-- A positive tensor power of a rigidified symmetric line on a dense open base
extends on an affine open covering of the normal integral locally Noetherian base.
All pullbacks of modules use the explicit tensor inverse-image functor.

Source: Moret-Bailly, Pinceaux de varietes abeliennes, II 3.3.3, opening
power-prolongation input (Raynaud, Faisceaux amples, XI 1.13), agent-formulated
local non-positive version; local originals WANTED.
(blueprint: lem-sfb-symmetric-line-power-prolongation)

Proof plan:
1. On a nonempty affine base open take the generic fibre. By
   lem-sfb-algebraic-group-ample-difference, write the generic line as A tensor B-dual
   with A and B ample. Symmetrization and the given symmetry identify the quotient
   of their symmetrizations with the square of the generic line. The tensor and
   pullback rules are lem-weil-pbc-invertible-pullback-tensor.
2. Apply lem-sfb-raynaud-generic-ample-symmetrization to A and B. Refine both affine
   coverings. If their powers extend with exponents a,b, their tensor quotient
   with exponents b,-a extends the generic power d=2ab, which is positive.
3. Tensor the extension with the pullback of the dual of its identity restriction.
   This rigidifies it. Normalize the generic comparison by its value at the identity.
   The quotient with the given d-th power is now rigidified, generically trivial,
   with generic trivialization equal to one along the identity.
4. Spread that trivialization to a dense base open. On a finite affine cover
   trivializing the quotient, clear the finitely many denominators of its section,
   inverse and overlap identities. Noetherian finiteness is supplied by
   lem-weil-pbc-finite-type-over-noetherian. The identity value remains one.
5. Apply lem-sfb-normal-group-vertical-cartier-descent on U. Semiabelian fibres are
   geometrically connected: the torus torsor over a connected abelian variety is
   open and surjective with connected fibres. The comparison's vertical Cartier
   divisor is pulled back from the identity, where it is zero, and hence is zero.
   The rational section is therefore everywhere invertible. This gives the desired
   comparison on all of the overlap, with no structure imposed on the extension. -/
theorem symmetricLinePowerProlongation
    {S : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (G : Grp (Over S)) [IsCommMonObj G.X]
    [Smooth G.X.hom] [IsSeparated G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    (hG : HasSemiabelianGeometricFibres G)
    (U : S.Opens) (hU : Dense (U : Set S))
    (N : ((Over.pullback U.ι).mapGrp.obj G).X.left.Modules) [N.IsInvertible]
    (rigidification :
      (Scheme.Modules.tensorPullback η[((Over.pullback U.ι).mapGrp.obj G).X].left).obj N ≅
        𝟙_ U.toScheme.Modules)
    (symmetry :
      (Scheme.Modules.tensorPullback ι[((Over.pullback U.ι).mapGrp.obj G).X].left).obj N ≅ N) :
    ∃ (I : Type u) (W : I → S.Opens), (⨆ i, W i) = ⊤ ∧
      (∀ i, IsAffineOpen (W i)) ∧
      ∀ i, Nonempty (W i) →
        ∃ (d : ℕ), 1 ≤ d ∧
          ∃ (P : (pullback G.X.hom (W i).ι).Modules), P.IsInvertible ∧
            Nonempty
              ((Scheme.Modules.tensorPullback
                (pullback.fst (pullback.fst G.X.hom (W i).ι)
                  (pullback.fst G.X.hom U.ι))).obj P ≅
                (Scheme.Modules.tensorPullback
                  (pullback.snd (pullback.fst G.X.hom (W i).ι)
                    (pullback.fst G.X.hom U.ι))).obj (N.tensorPow d)) := by
  sorry

end AlgebraicGeometry
