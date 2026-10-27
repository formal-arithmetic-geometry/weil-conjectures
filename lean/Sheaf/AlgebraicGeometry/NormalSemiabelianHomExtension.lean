module

public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import Sheaf.AlgebraicGeometry.SemiabelianGeometricPowerIntegrality
import Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Extension of generic homomorphisms of semiabelian schemes

Source: Lan, Structures of semi-abelian schemes, Proposition 3.3.1.5,
quoting Faltings--Chai I, Proposition 2.7 and Raynaud IX 1.4.
(blueprint: lem-sfb-normal-semiabelian-hom-extension)

Restriction is the group-object functor induced by canonical base change to the
residue field of the generic point. All group laws are the given group laws.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- Every homomorphism of the generic fibres of two semiabelian schemes over a
normal integral locally Noetherian base extends uniquely over that base.

Source: Lan, Structures of semi-abelian schemes, Proposition 3.3.1.5,
quoting Faltings--Chai I, Proposition 2.7 and Raynaud IX 1.4.
(blueprint: lem-sfb-normal-semiabelian-hom-extension)

Proof plan:
1. Apply lem-sfb-semiabelian-geometric-power-integrality for n = 1, 2 on the
   geometric fibres of P. The algebraic-closure test for geometric connectedness,
   smooth base change and smooth composition allow application of
   lem-sbc-smooth-connected-generic-geometry-core to P and its relative square.
   They and their generic fibres are integral and normal. Identity sections make
   the families surjective, so their generic points lie over the base generic
   point. Finite presentation and finite-type-over-noetherian make P locally
   Noetherian.
2. Form the scheme-theoretic image of the graph of the prescribed generic map
   in P times Q. The nodes lem-sfb-semiabelian-generic-graph-proper and
   lem-sfb-semiabelian-generic-graph-finite-fibres make its projection to P proper
   with finite fibres. By thm-pqf-finite-iff-proper-finite-fibres it is finite.
3. The graph map gives a section over the generic point of P. Apply
   lem-sfb-finite-normal-generic-section-extension to the finite projection over
   the normal integral P. Compose the resulting section with the second
   projection to obtain an S-map from P to Q.
4. Two maps from an integral scheme to the separated S-scheme Q agreeing over
   its function field are equal: the closed equalizer ideal vanishes in the
   fraction field of each affine domain, hence vanishes. Apply this on the
   generic fibre of P to identify the restriction with the given map, on the
   relative square to prove preservation of multiplication, and on S for the
   identity. Inverses follow from the group axioms. The same equality test on P
   proves uniqueness. -/
theorem normal_semiabelian_hom_extension
    {S : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (P Q : Grp (Over S)) [IsCommMonObj P.X] [IsCommMonObj Q.X]
    [Smooth P.X.hom] [IsSeparated P.X.hom]
    [LocallyOfFinitePresentation P.X.hom] [QuasiCompact P.X.hom]
    [Smooth Q.X.hom] [IsSeparated Q.X.hom]
    [LocallyOfFinitePresentation Q.X.hom] [QuasiCompact Q.X.hom]
    (hP : HasSemiabelianGeometricFibres P)
    (hQ : HasSemiabelianGeometricFibres Q)
    (fη : (Over.pullback (S.fromSpecResidueField (genericPoint S))).mapGrp.obj P ⟶
      (Over.pullback (S.fromSpecResidueField (genericPoint S))).mapGrp.obj Q) :
    ∃! f : P ⟶ Q,
      (Over.pullback (S.fromSpecResidueField (genericPoint S))).mapGrp.map f = fη := by
  sorry

end AlgebraicGeometry
