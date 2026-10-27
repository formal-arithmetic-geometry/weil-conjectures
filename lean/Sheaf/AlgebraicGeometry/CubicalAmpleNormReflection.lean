/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CubicalRigidifiedLine
public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.AmplePullback

/-! # Ampleness reflected by the inversion norm of a cubical line

Source: agent-formulated norm-reflection input to the cubical ampleness argument,
using Raynaud, Faisceaux amples sur les schemas en groupes, XI, and Moret-Bailly,
Pinceaux de varietes abeliennes, I §§2, 5. This is not a numbered assertion of Raynaud.
(blueprint: lem-sfb-cubical-ample-norm-reflection)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- Absolute ampleness of the supplied global inversion norm implies ampleness of the
cubical rigidified line on the whole group scheme.

Source: the agent-formulated norm-reflection input supported by Raynaud, Faisceaux
amples, XI, and Moret-Bailly, Pinceaux, I §§2, 5; original ampleness chapters WANTED.
(blueprint: lem-sfb-cubical-ample-norm-reflection)

Proof plan:
1. Put D = P tensor (inversion pullback P) dual. Apply
`lem-sfb-cubical-antisymmetric-frame-extension`: its frame scheme q : E -> G is a
smooth separated commutative group of finite presentation with semiabelian geometric
fibres. The map q is affine, faithfully flat of finite presentation, with kernel G_m,
and its tautological frame trivializes q*D over the unchanged normal integral base.
2. Rank-one evaluation gives P squared isomorphic to N tensor D, where
N = P tensor inversion pullback P. By `lem-weil-pbc-invertible-pullback-tensor`,
pullback commutes with tensor products, so q*(P squared) is isomorphic to q*N.
Evaluation is multiplication in a local frame and agrees on overlaps.
3. Since q is affine and N is ample on all of G,
`lem-weil-pbc-pullback-ample-invertible` makes q*N ample on all of E. Transporting
sections through the isomorphism preserves their values and nonvanishing loci.
4. Apply `lem-sfb-semiabelian-gm-extension-ample-reflection` to q and P squared.
Step 1 supplies its group-extension and base hypotheses, and step 3 its absolute
ampleness hypothesis. Thus P squared is ample on G.
5. By `def-weil-pbc-ample-invertible-module`, the affine nonvanishing section loci
for positive powers of P squared cover G, which is quasi-compact. Reassociate their
sections as sections of P to the positive power 2n; their loci do not change. This
is precisely the same absolute ampleness criterion for P. -/
theorem CubicalRigidifiedLine.isAmple_of_isAmple_inversionNorm
    {S : Scheme.{u}} [IsIntegral S] [IsNoetherian S] [IsAffine S]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (G : Over S) [CommGrpObj G] [Smooth G.hom] [IsSeparated G.hom]
    [LocallyOfFinitePresentation G.hom] [QuasiCompact G.hom]
    (hG : HasSemiabelianGeometricFibres (Grp.mk G)) (P : CubicalRigidifiedLine G)
    (hN : ∃ h : (P.line ⊗
        (Scheme.Modules.tensorPullback (ι[G]).left).obj P.line).IsInvertible,
      @Scheme.Modules.IsAmple G.left
        (P.line ⊗ (Scheme.Modules.tensorPullback (ι[G]).left).obj P.line) h) :
    @Scheme.Modules.IsAmple G.left P.line P.invertible := by
  sorry

end AlgebraicGeometry
