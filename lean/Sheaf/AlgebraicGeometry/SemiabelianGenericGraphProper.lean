module

public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import Sheaf.AlgebraicGeometry.SemiabelianGeometricPowerIntegrality
import Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore
import Sheaf.TraceFormula.ReducedSchemeImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Sheaf.AlgebraicGeometry.SemiabelianTraitHomExtension
import Sheaf.AlgebraicGeometry.Morphisms.GenericDvrPropernessCriterion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Proper projection of a semiabelian generic graph

Source: Faltings, Finiteness Theorems for Abelian Varieties over Number Fields,
Chapter II, section 2, Lemma 1 proof, printed pages 10-11.
(blueprint: lem-sfb-semiabelian-generic-graph-proper)

The graph map uses the given group homomorphism on the actual scheme fibres.
Its scheme-theoretic image is Mathlib's image, with its canonical closed inclusion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

/-- The fibre graph followed by the projection to the original relative product.
Its first component is the fibre inclusion, and its second is the prescribed
homomorphism followed by the other fibre inclusion. This construction also makes
sense at a nongeneric point.

Source: Faltings, Chapter II, section 2, Lemma 1 proof, graph closure construction.
(blueprint: lem-sfb-semiabelian-generic-graph-proper) -/
noncomputable def semiabelianFibreGraphMap {S : Scheme.{u}} (P Q : Grp (Over S))
    (s : S)
    (u : (Over.pullback (S.fromSpecResidueField s)).mapGrp.obj P ⟶
      (Over.pullback (S.fromSpecResidueField s)).mapGrp.obj Q) :
    P.X.hom.fiber s ⟶ pullback P.X.hom Q.X.hom :=
  pullback.lift (P.X.hom.fiberι s) (u.hom.hom.left ≫ Q.X.hom.fiberι s)
    ((P.X.hom.fiber_fac s).trans
      ((congrArg (fun a => a ≫ S.fromSpecResidueField s) (Over.w u.hom.hom).symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun a => u.hom.hom.left ≫ a) (Q.X.hom.fiber_fac s).symm).trans
            (Category.assoc _ _ _).symm))))

/-- The projection to P of the schematic closure of the generic homomorphism's graph
is proper, even when Q has toric fibres.

Source: Faltings, Chapter II, section 2, Lemma 1 proof, printed pages 10-11.
(blueprint: lem-sfb-semiabelian-generic-graph-proper)

Proof plan from the accepted DAG split:
1. By lem-sfb-semiabelian-geometric-power-integrality with n = 1 the geometric
   fibres of P are connected. The algebraic-closure connectedness test
   lem-weil-geometrically-connected-algebraic-closure and
   lem-sbc-smooth-connected-generic-geometry-core make P and its generic fibre
   integral. The identity section ensures nonemptiness. Finite presentation and
   lem-weil-pbc-finite-type-over-noetherian make P locally Noetherian.
2. The generic graph is a closed immersion into the generic relative product,
   since Q is separated. The generic-point inclusion into S is affine, so the
   graph map to the original product is quasi-compact. By
   lemma-nagata-scheme-image-ideal-qc its image is dense in its scheme image;
   lem-trf-reduced-scheme-image makes this image reduced. The closure of the
   nonempty irreducible generic fibre is irreducible, hence the image is integral.
   Its generic point is the image of the generic point of the generic fibre.
3. By lem-pod-separated-finite-type-base-change the product projects to P by a
   separated finite-type map. Restricting to its closed graph image preserves
   these properties, by affine quotients and pullback of the closed diagonal.
4. The generic-point inclusion is flat (localization on affine charts). Apply
   lem-sfb-scheme-image-flat-base-change, then
   lemma-nagata-scheme-image-of-closed-immersion: the generic fibre of the image
   is exactly the graph of u. Its generic point therefore satisfies a_Q = u(a_P).
5. For each DVR subring A of the image's function field L and extension b to P,
   base change P and Q to Spec A. Smoothness follows from
   lem-pc-proper-base-change; separated finite type follows from
   lem-pod-separated-finite-type-base-change. Finite presentation and the group
   laws persist under base change, as does the geometric semiabelian condition.
   Apply lem-sfb-trait-semiabelian-hom-extension to extend u_L over Spec A.
6. Evaluate the extension on the section induced by b, giving c to Q. The pair
   (b,c) extends the generic graph point. By lemma-nagata-valuation-factor-closed
   it factors through the closed graph image, giving the required DVR lift.
7. The image is integral, P is locally Noetherian, and the projection is separated
   finite type with all the required generic DVR lifts. Apply
   lem-sfb-generic-dvr-properness-criterion to conclude properness. -/
theorem semiabelian_generic_graph_proper
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
    (u : (Over.pullback (S.fromSpecResidueField (genericPoint S))).mapGrp.obj P ⟶
      (Over.pullback (S.fromSpecResidueField (genericPoint S))).mapGrp.obj Q) :
    IsProper ((semiabelianFibreGraphMap P Q (genericPoint S) u).imageι ≫
      pullback.fst P.X.hom Q.X.hom) := by
  sorry

end AlgebraicGeometry
