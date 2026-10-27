/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q89
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Group.Smooth

import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.AlgebraicGeometry.LocallyNoetherianComponentsLocallyFinite
import Sheaf.AlgebraicGeometry.IrreducibleProductOverField
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField
import WeilConjectures.AlgebraicGeometry.GroupScheme.Separated

/-!
# Identity components of locally algebraic groups

Source: Stacks Project, Tags 0B7R, 047R, 047P, 047N and 047L
(blueprint: lem-sfb-locally-algebraic-group-identity-component).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

/-- Source: Stacks Project, Tags 0B7R, 047R, 047P, 047N and 047L
(blueprint: lem-sfb-locally-algebraic-group-identity-component).

Proof:
1. Local finite type gives local Noetherianness. The unique minimal prime in each local
ring (lem-sfb-group-local-minimal-prime), the affine component description and localization
prime correspondence show that distinct irreducible components are disjoint.
2. Local finiteness of components makes them clopen. The neutral component is therefore
an irreducible component. Its reduced induced structure is geometrically irreducible by
lem-sfb-group-local-minimal-prime; reduction is a universal homeomorphism, so the open
component itself is geometrically irreducible.
3. Multiplication, inverse and unit factor uniquely through this open component. The
irreducibility of its product implies the multiplication image remains in the component.
The factorizations inherit the group identities from G.
4. Apply lem-sfb-irreducible-group-quasi-compact to this irreducible group. Its open
immersion into G supplies local finite type, hence it is of finite type.
5. After any field extension the clopen decomposition pulls back. Geometric irreducibility
makes the pullback of the neutral component connected, and it contains the identity.
The other clopen piece cannot meet the identity component. Thus the components agree,
and their open-subscheme structures agree.
6. Reduction is connected and irreducible, hence integral, and remains of finite type.
Over the perfect field k, the product of two reduced schemes is reduced. Thus the unit,
inverse and multiplication factor uniquely through the reduction, giving its subgroup
structure (047R).
7. Geometric reducedness over the perfect field and smooth_of_grpObj give smoothness;
047L gives separatedness. The reduction immersion is a homeomorphism, giving the
asserted equality of underlying topological spaces. -/
theorem locallyAlgebraicGroup_identityComponent
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] :
    ∃ U : G.left.Opens,
      (U : Set G.left) = connectedComponent (GrpObj.onePoint G) ∧
      IsClosed (U : Set G.left) ∧
      GeometricallyIrreducible (U.ι ≫ G.hom) ∧
      LocallyOfFiniteType (U.ι ≫ G.hom) ∧ QuasiCompact (U.ι ≫ G.hom) ∧
      (∀ (K : Type u) [Field K] [Algebra k K],
        (pullback.fst G.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ⁻¹'
          (U : Set G.left) =
        connectedComponent (GrpObj.onePoint
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G))) ∧
      ∃ gC : GrpObj (Over.mk (U.ι ≫ G.hom)),
        @IsMonHom _ _ _ _ _ gC.toMonObj _ (Over.homMk (V := G) U.ι) ∧
        Smooth (U.toScheme.nilradical.subschemeι ≫ U.ι ≫ G.hom) ∧
        ConnectedSpace U.toScheme.nilradical.subscheme ∧
        IsIntegral U.toScheme.nilradical.subscheme ∧
        IsSeparated (U.toScheme.nilradical.subschemeι ≫ U.ι ≫ G.hom) ∧
        LocallyOfFiniteType (U.toScheme.nilradical.subschemeι ≫ U.ι ≫ G.hom) ∧
        QuasiCompact (U.toScheme.nilradical.subschemeι ≫ U.ι ≫ G.hom) ∧
        IsHomeomorph U.toScheme.nilradical.subschemeι ∧
        ∃ gR : GrpObj (Over.mk (U.toScheme.nilradical.subschemeι ≫ U.ι ≫ G.hom)),
          @IsMonHom _ _ _ _ _ gR.toMonObj gC.toMonObj
            (Over.homMk U.toScheme.nilradical.subschemeι) := by
  sorry

end AlgebraicGeometry
