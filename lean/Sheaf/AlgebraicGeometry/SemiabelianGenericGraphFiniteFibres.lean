module

public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import Sheaf.AlgebraicGeometry.SemiabelianGeometricPowerIntegrality
import Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore
import WeilConjectures.AlgebraicGeometry.NoetherianSpecializationTrait
import Sheaf.AlgebraicGeometry.SemiabelianTraitHomExtension
import WeilConjectures.FieldTheory.CommonExtensionFields
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Topology.NoetherianSpace
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.FinitePresentation
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Finite fibres of a generic semiabelian graph closure

Source: Faltings, Finiteness Theorems for Abelian Varieties over Number Fields,
Chapter II, section 2, Lemma 1 proof, printed pages 10-11.
(blueprint: lem-sfb-semiabelian-generic-graph-finite-fibres)

The graph map and its image projection are canonical constructions. Finiteness
concerns the points of the scheme fibre and imposes no reducedness condition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

/-- The prescribed generic graph followed by the map into the total fibre product.
The two coordinates are the canonical map from the generic fibre of P to P and
u followed by the canonical map from the generic fibre of Q to Q. The counits of
base change supply these coordinates as morphisms over S; their product is then
identified with the chosen scheme fibre product.

Source: Faltings, Chapter II, section 2, Lemma 1 proof, printed pages 10-11.
(blueprint: lem-sfb-semiabelian-generic-graph-finite-fibres) -/
noncomputable def semiabelianGenericGraphMap
    {S : Scheme.{u}} [IsIntegral S] (P Q : Grp (Over S))
    (uη : (Over.pullback (S.fromSpecResidueField (genericPoint S))).mapGrp.obj P ⟶
      (Over.pullback (S.fromSpecResidueField (genericPoint S))).mapGrp.obj Q) :
    ((Over.pullback (S.fromSpecResidueField (genericPoint S))).obj P.X).left ⟶
      pullback P.X.hom Q.X.hom :=
  (prod.lift
    ((Over.mapPullbackAdj (S.fromSpecResidueField (genericPoint S))).counit.app P.X)
    ((Over.map (S.fromSpecResidueField (genericPoint S))).map uη.hom.hom ≫
      (Over.mapPullbackAdj (S.fromSpecResidueField (genericPoint S))).counit.app Q.X)).left ≫
    (Over.prodLeftIsoPullback P.X Q.X).hom

/-- The first projection from the scheme-theoretic image of the generic graph.
Its source is exactly the closed subscheme cut out by the graph map's kernel ideal.

Source: Faltings, Chapter II, section 2, Lemma 1 proof, printed pages 10-11.
(blueprint: lem-sfb-semiabelian-generic-graph-finite-fibres) -/
noncomputable def semiabelianGenericGraphProjection
    {S : Scheme.{u}} [IsIntegral S] (P Q : Grp (Over S))
    (uη : (Over.pullback (S.fromSpecResidueField (genericPoint S))).mapGrp.obj P ⟶
      (Over.pullback (S.fromSpecResidueField (genericPoint S))).mapGrp.obj Q) :
    (semiabelianGenericGraphMap P Q uη).image ⟶ P.X.left :=
  (semiabelianGenericGraphMap P Q uη).imageι ≫ pullback.fst P.X.hom Q.X.hom

/-- Every scheme fibre of the first projection of the generic graph closure has
finitely many underlying points. This includes empty fibres and says nothing
about nilpotents in their local rings.

Source: Faltings, Chapter II, section 2, Lemma 1 proof, printed pages 10-11.
(blueprint: lem-sfb-semiabelian-generic-graph-finite-fibres)

Proof plan from the accepted DAG split:
1. Apply lem-sfb-semiabelian-geometric-power-integrality with n = 1, then
   lem-weil-geometrically-connected-algebraic-closure and
   lem-sbc-smooth-connected-generic-geometry-core. The identity section makes
   P nonempty; its generic fibre is integral, with generic point xi.
2. The finite-type-over-noetherian and affine-noetherian-underlying-space
   results make the ambient product and graph image locally Noetherian and the
   generic source Noetherian. By lem-sfb-noetherian-space-compact-subsets, the
   graph map is quasi-compact. lemma-nagata-scheme-image-ideal-qc identifies
   the image support with the closure of its range; the image y of xi is generic.
3. For two points z_i over a point x of P, use
   lem-sbc-noetherian-specialization-trait to trace y to each z_i by a DVR.
   When z_i = y use its residue field instead. Smooth base change from
   lem-pc-proper-base-change and finite-presentation base change from
   lem-weil-pbc-finite-presentation-base-change-composition preserve the
   hypotheses. Apply lem-sfb-semiabelian-trait-hom-extension over each DVR;
   over a field use the given generic homomorphism itself.
4. The two coordinates of each trait map satisfy q_i = v_i(p_i) generically.
   Their equalizer is closed by separatedness. Its ideal vanishes in the
   fraction field, hence in the DVR, so equality holds on the whole trait.
5. By lem-weil-common-extension-fields, put both closed residue fields over
   kappa(x) inside one field and then its algebraic closure. The two first
   coordinates agree. lem-sfb-semiabelian-trait-specialization-agreement
   identifies the specialized homomorphisms, so the second coordinates agree.
6. The fibre-product universal property and injectivity of the closed image
   immersion give z_1 = z_2. The homeomorphism in def-pc-scheme-fibre identifies
   the scheme fibre's points with this inverse image. A set with at most one
   point is finite. No assertion about reducedness is used or concluded. -/
theorem semiabelian_generic_graph_finite_fibres
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
    (uη : (Over.pullback (S.fromSpecResidueField (genericPoint S))).mapGrp.obj P ⟶
      (Over.pullback (S.fromSpecResidueField (genericPoint S))).mapGrp.obj Q)
    (x : P.X.left) :
    Finite ((semiabelianGenericGraphProjection P Q uη).fiber x) := by
  sorry

end AlgebraicGeometry
