module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.SpaceDerivedPullback
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.AlgebraicGeometry.PerfectAffineBoundedProjective
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
import Sheaf.AlgebraicGeometry.SpacePerfectUniformTor
import Sheaf.AlgebraicGeometry.SpaceQcqsDistinguishedSquareInduction
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.RingTheory.FilteredColimitAlgebrasUnderlyingModule
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # Perfect-source Hom continuity for affine limits of algebraic spaces

Source: Stacks Project, spaces-perfect.tex, Tag 09RI(1), Situation 09RH
(blueprint: lem-sfb-space-perfect-source-hom-continuity).

The tail Hom diagram and its cocone use the normalized composition comparisons of
unbounded derived tensor pullback. ULift only places the Hom sets and the indexing
colimit in one common universe; it does not change their elements or the comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Pullback comparison for a specified commuting triangle, with its actual maps.
Source: Stacks, 09RI, transition identifications; 0D6D, derived pullback composition
(blueprint: lem-sfb-space-perfect-source-hom-continuity). -/
def spaceLimitDerivedComparison {S : Scheme.{u}} {A B C : AlgebraicSpace S}
    [HasDerivedCategory.{w} A.SmallModules] [HasDerivedCategory.{w} B.SmallModules]
    [HasDerivedCategory.{w} C.SmallModules]
    (f : B ⟶ A) (g : C ⟶ B) (p : C ⟶ A) (h : g ≫ f = p) :
    spaceDerivedPullback p ≅ spaceDerivedPullback f ⋙ spaceDerivedPullback g :=
  eqToIso (congrArg spaceDerivedPullback h.symm) ≪≫ spaceDerivedPullbackComp f g

variable {S : Scheme.{u}} {I : Type u} [Preorder I]
  (D : Iᵒᵖ ⥤ AlgebraicSpace S)
  [∀ j : Iᵒᵖ, HasDerivedCategory.{w} (D.obj j).SmallModules]
  (i : I) (P K : (D.obj (op i)).DerivedModules)

/-- The pullback-induced transition between the actual stage Hom sets.
Source: Stacks, 09RI(1), the directed system of Hom groups
(blueprint: lem-sfb-space-perfect-source-hom-continuity). -/
def spaceLimitHomTransition {j k : Set.Ici i} (a : j ⟶ k)
    (v : (spaceDerivedPullback (D.map (homOfLE j.property).op)).obj P ⟶
      (spaceDerivedPullback (D.map (homOfLE j.property).op)).obj K) :
    (spaceDerivedPullback (D.map (homOfLE k.property).op)).obj P ⟶
      (spaceDerivedPullback (D.map (homOfLE k.property).op)).obj K :=
  (spaceLimitDerivedComparison
      (D.map (homOfLE j.property).op) (D.map (homOfLE (leOfHom a : j.val ≤ k.val)).op)
      (D.map (homOfLE k.property).op)
      (D.map_comp (homOfLE (leOfHom a : j.val ≤ k.val)).op
        (homOfLE j.property).op).symm).hom.app P ≫
    (spaceDerivedPullback (D.map (homOfLE (leOfHom a : j.val ≤ k.val)).op)).map v ≫
    (spaceLimitDerivedComparison
      (D.map (homOfLE j.property).op) (D.map (homOfLE (leOfHom a : j.val ≤ k.val)).op)
      (D.map (homOfLE k.property).op)
      (D.map_comp (homOfLE (leOfHom a : j.val ≤ k.val)).op
        (homOfLE j.property).op).symm).inv.app K

/-- Identity law for the canonical tail transition.
Source: Stacks, 09RI, composition identifications, and 0D6D
(blueprint: lem-sfb-space-perfect-source-hom-continuity).
Proof: the derived identity comparison is normalized by ordinary multiplication.
Its triangle law with the composition comparison identifies transport along the
identity arrow with conjugation by the same isomorphism, hence with the identity. -/
theorem spaceLimitHomTransition_id (j : Set.Ici i)
    (v : (spaceDerivedPullback (D.map (homOfLE j.property).op)).obj P ⟶
      (spaceDerivedPullback (D.map (homOfLE j.property).op)).obj K) :
    spaceLimitHomTransition D i P K (𝟙 j) v = v := by
  sorry

/-- Composition law for canonical tail transitions.
Source: Stacks, 09RI, composition identifications, and 0D6D
(blueprint: lem-sfb-space-perfect-source-hom-continuity).
Proof: the associativity pentagon for normalized derived composition follows by
uniqueness with the derived counits: on flat K-flat representatives both routes
send a triple pure tensor to its product. Naturality cancels the middle comparison
on the target of the first map, leaving precisely the composite transition. -/
theorem spaceLimitHomTransition_comp {j k l : Set.Ici i} (a : j ⟶ k) (b : k ⟶ l)
    (v : (spaceDerivedPullback (D.map (homOfLE j.property).op)).obj P ⟶
      (spaceDerivedPullback (D.map (homOfLE j.property).op)).obj K) :
    spaceLimitHomTransition D i P K (a ≫ b) v =
      spaceLimitHomTransition D i P K b (spaceLimitHomTransition D i P K a v) := by
  sorry

/-- The tail diagram of Hom sets, lifted only to accommodate both index and Hom size.
Source: Stacks, 09RI(1) (blueprint: lem-sfb-space-perfect-source-hom-continuity). -/
def spaceLimitHomDiagram : Set.Ici i ⥤ Type (max u w) where
  obj j := ULift.{u}
    ((spaceDerivedPullback (D.map (homOfLE j.property).op)).obj P ⟶
      (spaceDerivedPullback (D.map (homOfLE j.property).op)).obj K)
  map a := TypeCat.ofHom (fun v ↦ ULift.up (spaceLimitHomTransition D i P K a v.down))
  map_id j := congrArg TypeCat.ofHom (funext fun v ↦
    congrArg ULift.up (spaceLimitHomTransition_id D i P K j v.down))
  map_comp a b := congrArg TypeCat.ofHom (funext fun v ↦
    congrArg ULift.up (spaceLimitHomTransition_comp D i P K a b v.down))

variable (c : Cone D) [HasDerivedCategory.{w} c.pt.SmallModules]

/-- Pulling a stage morphism back to the limit, using the cone's commuting triangle.
Source: Stacks, 09RI(1) (blueprint: lem-sfb-space-perfect-source-hom-continuity). -/
def spaceLimitHomToLimit (j : Set.Ici i)
    (v : (spaceDerivedPullback (D.map (homOfLE j.property).op)).obj P ⟶
      (spaceDerivedPullback (D.map (homOfLE j.property).op)).obj K) :
    (spaceDerivedPullback (@id (c.pt ⟶ D.obj (op i)) (c.π.app (op i)))).obj P ⟶
      (spaceDerivedPullback (@id (c.pt ⟶ D.obj (op i)) (c.π.app (op i)))).obj K :=
  (spaceLimitDerivedComparison
      (D.map (homOfLE j.property).op)
      (@id (c.pt ⟶ D.obj (op j.val)) (c.π.app (op j.val)))
      (@id (c.pt ⟶ D.obj (op i)) (c.π.app (op i)))
      (c.w (homOfLE j.property).op)).hom.app P ≫
    (spaceDerivedPullback (@id (c.pt ⟶ D.obj (op j.val)) (c.π.app (op j.val)))).map v ≫
    (spaceLimitDerivedComparison
      (D.map (homOfLE j.property).op)
      (@id (c.pt ⟶ D.obj (op j.val)) (c.π.app (op j.val)))
      (@id (c.pt ⟶ D.obj (op i)) (c.π.app (op i)))
      (c.w (homOfLE j.property).op)).inv.app K

/-- The comparison to the limit respects every canonical transition.
Source: Stacks, 09RI, its canonical Hom comparison, and 0D6D
(blueprint: lem-sfb-space-perfect-source-hom-continuity).
Proof: use the cone equation for a and for the two arrows to i. The normalized
composition pentagon identifies the two iterated pullbacks. Naturality of this
comparison transports v, and its inverse on K cancels, proving the equality. -/
theorem spaceLimitHomToLimit_transition {j k : Set.Ici i} (a : j ⟶ k)
    (v : (spaceDerivedPullback (D.map (homOfLE j.property).op)).obj P ⟶
      (spaceDerivedPullback (D.map (homOfLE j.property).op)).obj K) :
    spaceLimitHomToLimit D i P K c k (spaceLimitHomTransition D i P K a v) =
      spaceLimitHomToLimit D i P K c j v := by
  sorry

/-- The canonical pullback cocone with vertex the limit Hom set.
Source: Stacks, 09RI(1) (blueprint: lem-sfb-space-perfect-source-hom-continuity). -/
def spaceLimitHomCocone : Cocone (spaceLimitHomDiagram D i P K) where
  pt := ULift.{u} ((spaceDerivedPullback (@id (c.pt ⟶ D.obj (op i)) (c.π.app (op i)))).obj P ⟶
    (spaceDerivedPullback (@id (c.pt ⟶ D.obj (op i)) (c.π.app (op i)))).obj K)
  ι :=
    { app := fun j ↦ TypeCat.ofHom (fun v ↦
        ULift.up (spaceLimitHomToLimit D i P K c j v.down))
      naturality := fun _ _ a ↦ congrArg TypeCat.ofHom (funext fun v ↦
        congrArg ULift.up (spaceLimitHomToLimit_transition D i P K c a v.down)) }

/-- The canonical colimit-to-limit Hom map.
Source: Stacks, 09RI(1) (blueprint: lem-sfb-space-perfect-source-hom-continuity). -/
def spaceLimitHomComparison :
    colimit (spaceLimitHomDiagram D i P K) → (spaceLimitHomCocone D i P K c).pt :=
  colimit.desc _ (spaceLimitHomCocone D i P K c)

/-- Hom from a perfect source commutes with affine directed limits of qcqs spaces,
with an arbitrary unbounded target having quasi-coherent cohomology.
Source: Stacks Project, spaces-perfect.tex, Tag 09RI(1), Situation 09RH
(blueprint: lem-sfb-space-perfect-source-hom-continuity).

Proof:
1. Pass to the cofinal directed tail above i. For each qcqs etale T over X_i form
   its base changes T_j and T_infinity. Affine limits and chart pullback calculus
   identify these as a limit with affine transitions. Define the desired property
   simultaneously for all shifts K[n]; local perfect models restrict to T.
2. For affine T all the base changes are affine. Limit sections give A = colim A_j.
   Perfectness gives quasi-coherent cohomology. Unbounded Zariski-etale comparison,
   etale detection of perfectness, and the affine equivalence represent P by a
   bounded finite-projective complex B and K by a flat-term K-flat complex C.
3. Scalar extension and the K-flat tensor comparisons identify the derived maps
   with Hom in K(A_i) from B to (C tensor A_j)[n]. B is K-projective because it is
   bounded above with projective terms. Adjunction for ordinary scalar extension
   respects chain maps, homotopies, transitions and limit projections.
4. Filtered colimits of algebras are their underlying module colimits; tensor
   commutes with them degreewise. Thus C tensor A is the degreewise colimit.
5. Choose finite-free splittings for the finitely many terms of B. A map from
   each term lifts to a stage by lifting finitely many generator images. Equality
   of two such maps at the limit holds at a later stage by eventual equality.
6. Lift finitely many components of a chain map and kill their differential
   defects at one later stage. Lift a homotopy similarly and enforce its finitely
   many equations. This proves surjectivity and injectivity, for every shift,
   without a bound on C or flatness of the transition rings.
7. Derived-Hom Mayer-Vietoris on a distinguished square gives compatible exact
   rows at every stage and at infinity, including their boundary maps. Filtered
   exactness gives a five-term exact diagram for the colimit row.
8. The four outer comparisons are bijective if the property holds on the three
   local pieces. For surjectivity lift the local image, lift it by exactness, then
   correct by a lifted boundary. For injectivity write a class with zero image as
   a boundary, lift its lower preimage from the preceding local pair, and use
   injectivity there to make the boundary zero.
9. The property is invariant under isomorphism. The affine case and this excision
   step give the qcqs distinguished-square induction hypotheses. Apply induction
   to X_i and take n = 0. All comparisons remain the canonical pullback cocone. -/
theorem perfect_source_hom_continuity
    [Nonempty I] [IsDirected I (· ≤ ·)] (hc : IsLimit c)
    (hqc : ∀ j : I, CompactSpace (Point (D.obj (op j)).obj.obj))
    (hqs : ∀ j : I, IsAbsolutelyQuasiSeparated (D.obj (op j)))
    (haff : ∀ (j k : I) (h : j ≤ k), MapIsAffine (D.map (homOfLE h).op))
    (hP : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
      (D.obj (op i)).smallStructureSheaf P)
    (hK : (D.obj (op i)).derivedQCohProperty K) :
    Function.Bijective (spaceLimitHomComparison D i P K c) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
