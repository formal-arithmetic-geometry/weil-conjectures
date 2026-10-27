module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
import Mathlib.Topology.Defs.Filter
import Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealClosedSubspaceCorrespondence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleFpDirectedApproximation
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedStructureFinitePresentation

/-! # Closed subspaces as limits of finitely presented closed subspaces

Source: Stacks Project, Limits of Spaces, Tag 0A0U,
lemma-closed-is-limit-closed-and-finite-presentation
(blueprint: lem-sfb-space-closed-subspace-fp-approximation).

The base is Spec Z in the specified universe. The diagram and its limiting cone
are in algebraic spaces over Y, so all structure and compatibility equations
are carried by the over category and the natural transformation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A closed subspace of a qcqs algebraic space is the inverse limit over its target
of a small nonempty directed system of finitely presented closed subspaces.
Both the transitions and the projections from the given closed subspace are closed
immersions. Quasi-compactness is tested by quasi-compact surjective etale atlases.
Source: Stacks Project, Limits of Spaces, Tag 0A0U
(blueprint: lem-sfb-space-closed-subspace-fp-approximation).

Proof, following the accepted six-step DAG split:
1. A quasi-compact surjective etale atlas makes the point space of Y quasi-compact:
   pull back an open cover, choose a finite subcover, and use surjectivity. The
   diagonal hypothesis gives the other input to module approximation, using
   def-a1-space-point-topology and def-weil-pbc-quasi-compact-scheme.
2. By lem-sfb-space-ideal-closed-subspace-correspondence let I be the kernel ideal
   defining X in Y. By lem-sfb-space-module-fp-directed-approximation write I as a
   filtered colimit of finitely presented quasi-coherent modules F_j, with maps u_j,
   in all module sheaves.
3. Index by finite-type quasi-coherent subideals of I. The zero ideal is an index;
   the sum gives a common upper bound. Images of the u_j are such subideals, and
   each u_j factors through its image. These assertions use
   lem-sfb-space-qcoh-kernels-colimits and lem-sfb-space-qcoh-affine-chart-calculus.
   The index is small by def-weil-size-convention; a finite affine etale atlas
   bounds finite-type subideals by finite lists of sections, allowing a u-small index.
4. Define X_a by its subideal, using the ideal/closed-subspace correspondence.
   By lem-sfb-space-closed-structure-finite-presentation its map to Y is finitely
   presented, since its defining ideal is of finite type.
5. Inclusion of ideals gives unique transitions X_b to X_a and maps X to X_a.
   These maps are base changes of the closed immersions into Y, by
   lem-trf-space-fibre-products-etale-covers and def-weil-closed-immersion.
   Uniqueness gives the functor identities, cone compatibility and triangles over Y.
6. For any algebraic space T over Y a compatible cone kills every subideal.
   The canonical map I to h_* O_T therefore vanishes after each u_j, since u_j
   factors through its finite-type image. The module-colimit universal property
   makes that map zero. The factorization criterion in
   lem-sfb-space-ideal-closed-subspace-correspondence gives the unique map T to X.
   Its projections are the prescribed cone maps by uniqueness into each subspace.
   This is the limit universal property in algebraic spaces over Y. -/
theorem exists_closedImmersion_finitePresentation_limit
    {X Y : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))} (i : X ⟶ Y)
    (hYqc : IsQuasiCompact Y.obj)
    (hYqs : IsQuasiCompactPresheafMap (prod.lift (𝟙 Y.obj.obj) (𝟙 Y.obj.obj)))
    (hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : Iᵒᵖ ⥤ Over Y)
      (q : (Functor.const Iᵒᵖ).obj (Over.mk i) ⟶ D),
      (∀ a : Iᵒᵖ,
        IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
          (D.obj a).hom.hom.hom ∧
        IsQuasiCompactPresheafMap (D.obj a).hom.hom.hom ∧
        IsQuasiCompactPresheafMap (pullback.diagonal (D.obj a).hom.hom.hom) ∧
        MapIsLocallyOfFinitePresentation (D.obj a).hom) ∧
      (∀ (a b : Iᵒᵖ) (f : a ⟶ b),
        IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
          (D.map f).left.hom.hom) ∧
      (∀ a : Iᵒᵖ,
        IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
          (q.app a).left.hom.hom) ∧
      Nonempty (IsLimit (Cone.mk (Over.mk i) q)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
