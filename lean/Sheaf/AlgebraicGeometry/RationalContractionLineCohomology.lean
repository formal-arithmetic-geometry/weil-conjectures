/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.RingTheory.SmoothAtPrimeDifferentialsDimension
import Sheaf.RingTheory.SmoothRationalPointCompletion
import Sheaf.TraceFormula.NodalContractionNormalizationBranches
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre

/-! # Line bundles under a rational-component contraction

Source: Knudsen, The projectivity of the moduli space of stable curves II,
Section 1, Corollary 1.5, printed p.167, and its contraction application pp.167--168;
arbitrary-base finite-presentation form
(blueprint: lem-sfb-rational-contraction-line-cohomology).

The auxiliary records only expand the diagram, exceptional-component hypothesis and
canonical comparisons of this statement. They introduce no alternative module operations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RationalContraction

/-- The two families and their morphism over the same base.
Source: Knudsen II, Corollary 1.5, p.167
(blueprint: lem-sfb-rational-contraction-line-cohomology). -/
structure Diagram where
  T : Scheme.{u}
  X : Scheme.{u}
  Y : Scheme.{u}
  pX : X ⟶ T
  pY : Y ⟶ T
  q : Y ⟶ X
  over : q ≫ pX = pY

namespace Diagram

variable (D : Diagram.{u})

/-- The actual map on a base change, including geometric fibres.
Source: Knudsen II, Corollary 1.5(iii), p.167
(blueprint: lem-sfb-rational-contraction-line-cohomology). -/
def fiberMap {S : Scheme.{u}} (a : S ⟶ D.T) :
    pullback (C := Scheme.{u}) D.pY a ⟶ pullback (C := Scheme.{u}) D.pX a :=
  pullback.map D.pY a D.pX a D.q (𝟙 S) (𝟙 D.T)
    ((Category.comp_id D.pY).trans D.over.symm)
    ((Category.comp_id a).trans (Category.id_comp a).symm)

/-- The reduced projective-line component is contracted to a point, with no other fibre
points over it; outside it the map is an isomorphism. Its boundary consists of one or two
nodes. Since the component is a smooth projective line in a reduced nodal curve, those
boundary nodes are transverse and have one branch on each subcurve. The condition on the
fibre is set theoretic: reducedness of the scheme-theoretic fibre is a proof step, not an
additional hypothesis.
Source: Knudsen II, contraction application of Corollary 1.5, pp.167--168
(blueprint: lem-sfb-rational-contraction-line-cohomology). -/
def Exceptional {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (a : Spec (.of Ω) ⟶ D.T)
    (i : ProjectiveLine (Spec (.of Ω)) ⟶ pullback (C := Scheme.{u}) D.pY a) : Prop :=
  IsClosedImmersion i ∧ Set.range i ∈ irreducibleComponents (pullback (C := Scheme.{u}) D.pY a) ∧
  i ≫ pullback.snd D.pY a = (ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω)) ∧
  (∃ (x : pullback (C := Scheme.{u}) D.pX a)
      (hx : IsClosed ({x} : Set (pullback (C := Scheme.{u}) D.pX a))),
    D.fiberMap a ⁻¹' {x} = Set.range i ∧
    IsIso (pullback.snd (D.fiberMap a)
      (Scheme.Opens.ι (X := pullback (C := Scheme.{u}) D.pX a) ⟨{x}ᶜ, hx.isOpen_compl⟩))) ∧
  ((Set.range i ∩ closure ((Set.range i)ᶜ)).encard = 1 ∨
    (Set.range i ∩ closure ((Set.range i)ᶜ)).encard = 2) ∧
  ∀ y : pullback (C := Scheme.{u}) D.pY a, y ∈ Set.range i ∩ closure ((Set.range i)ᶜ) →
    ¬ ∃ U : (pullback (C := Scheme.{u}) D.pY a).Opens,
      y ∈ U ∧ Smooth (U.ι ≫ pullback.snd D.pY a)

/-- Each geometric fibre map is an isomorphism or contracts exactly one indicated
projective-line component with the prescribed one- or two-node boundary.
Source: Knudsen II, pp.167--168
(blueprint: lem-sfb-rational-contraction-line-cohomology). -/
def IsElementary : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ D.T),
    IsIso (D.fiberMap a) ∨
      ∃ i : ProjectiveLine (Spec (.of Ω)) ⟶ pullback (C := Scheme.{u}) D.pY a, D.Exceptional a i

/-- The Euler-characteristic degree bound on every contracted geometric component, using
its actual pullback line bundle on the standard projective line. Quantification over every
parametrization avoids choosing component coordinates.
Source: Knudsen II, Corollary 1.5 and its contraction application, pp.167--168
(blueprint: lem-sfb-rational-contraction-line-cohomology). -/
def DegreeAtLeast (L : D.Y.Modules) (d : ℤ) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ D.T)
    (i : ProjectiveLine (Spec (.of Ω)) ⟶ pullback (C := Scheme.{u}) D.pY a),
    D.Exceptional a i → d ≤
      Scheme.Modules.degree Ω ((Scheme.Modules.tensorPullback
        (i ≫ pullback.fst D.pY a)).obj L)

/-- An arbitrary cartesian change of the common base and both curves. Isomorphisms of
entire diagrams are included, even with identity base map and nonidentity curve maps.
Source: Knudsen II, Corollary 1.5(iii), p.167
(blueprint: lem-sfb-rational-contraction-line-cohomology). -/
structure Change (D' : Diagram.{u}) where
  base : D'.T ⟶ D.T
  x : D'.X ⟶ D.X
  y : D'.Y ⟶ D.Y
  squareX : IsPullback x D'.pX D.pX base
  squareY : IsPullback y D'.pY D.pY base
  squareQ : y ≫ D.q = D'.q ≫ x

variable {D}

/-- The existing section-normalized canonical comparison, rather than a chosen isomorphism.
Source: Knudsen II, Corollary 1.5(iii), p.167; Stacks Tag 08HY
(blueprint: lem-sfb-rational-contraction-line-cohomology). -/
def Change.comparison {D' : Diagram.{u}} (A : D.Change D') (L : D.Y.Modules) :
    (Scheme.Modules.tensorPullback A.x).obj ((Scheme.Modules.pushforward D.q).obj L) ⟶
      (Scheme.Modules.pushforward D'.q).obj ((Scheme.Modules.tensorPullback A.y).obj L) :=
  Scheme.Modules.moduleBaseChangeMap D.q D'.q A.x A.y A.squareQ L

/-- The same canonical comparison for the composite change, written without choosing an
iterated-fibre-product identification. Source: Knudsen II, Corollary 1.5(iii), p.167
(blueprint: lem-sfb-rational-contraction-line-cohomology). -/
def Change.compositeComparison {D' D'' : Diagram.{u}} (A : D.Change D')
    (B : D'.Change D'') (L : D.Y.Modules) :
    (Scheme.Modules.tensorPullback (B.x ≫ A.x)).obj
        ((Scheme.Modules.pushforward D.q).obj L) ⟶
      (Scheme.Modules.pushforward D''.q).obj
        ((Scheme.Modules.tensorPullback (B.y ≫ A.y)).obj L) :=
  Scheme.Modules.moduleBaseChangeMap D.q D''.q (B.x ≫ A.x) (B.y ≫ A.y)
    ((Category.assoc B.y A.y D.q).trans
      ((congrArg (fun k ↦ B.y ≫ k) A.squareQ).trans
        ((Category.assoc B.y D'.q A.x).symm.trans
          ((congrArg (fun k ↦ k ≫ A.x) B.squareQ).trans
            (Category.assoc D''.q B.x A.x))))) L

variable (D)

/-- Composition and naturality in line-bundle isomorphisms for the actual comparisons.
The composition equation also covers all changes that are diagram isomorphisms, giving
naturality under their identifications. Source: Knudsen II, pp.167--168
(blueprint: lem-sfb-rational-contraction-line-cohomology). -/
def Compatible (L : D.Y.Modules) : Prop :=
  (∀ (D' D'' : Diagram.{u}) (A : D.Change D') (B : D'.Change D''),
    A.compositeComparison B L =
      (Scheme.Modules.tensorPullbackSectionComp B.x A.x).hom.app
          ((Scheme.Modules.pushforward D.q).obj L) ≫
        (Scheme.Modules.tensorPullback B.x).map (A.comparison L) ≫
        B.comparison ((Scheme.Modules.tensorPullback A.y).obj L) ≫
        (Scheme.Modules.pushforward D''.q).map
          ((Scheme.Modules.tensorPullbackSectionComp B.y A.y).inv.app L)) ∧
  (∀ (D' : Diagram.{u}) (A : D.Change D') (M : D.Y.Modules) (e : L ≅ M),
    (Scheme.Modules.tensorPullback A.x).map ((Scheme.Modules.pushforward D.q).map e.hom) ≫
        A.comparison M =
      A.comparison L ≫
        (Scheme.Modules.pushforward D'.q).map
          ((Scheme.Modules.tensorPullback A.y).map e.hom))

/-- Vanishing, finite presentation, base-flatness, arbitrary base change and generation
for an invertible module under a single rational-component contraction.
Source: Knudsen II, Section 1, Corollary 1.5(i)--(iv), printed p.167, and pp.167--168;
arbitrary-base finite-presentation form
(blueprint: lem-sfb-rational-contraction-line-cohomology).

Proof, following the six steps of the DAG node:
1. Properness of X/T makes it separated. Proper-to-separated-target
   (lemma-nagata-proper-to-separated-target) makes q proper. Invertibility makes L
   quasi-coherent, finitely presented and T-flat, using flatness of Y/T.
2. The geometric fibres of q are points or the exceptional projective line as schemes.
   At a smooth image point, smooth-over-field-dimension-differentials and
   smooth-rational-point-completion give the one-variable power-series completion.
   At a node the completion has two axes. Apply
   lem-trf-nodal-contraction-normalization-branches in its ordinary one- or two-fold
   case to prove the entire scheme-theoretic exceptional fibre reduced; no thickening
   is silently removed. Proper-fp-permanence supplies the geometric properness.
3. Projective-line-invertible-classification writes the restriction as O(d).
   Projective-space-twist-cohomology gives chi(O(d))=d+1 and chi(O)=1, hence degree=d.
   H1 vanishes for d >= -1, including d=-1 where both H0 and H1 vanish. Point fibres
   have no positive cohomology. These are lem-sfb-projective-line-invertible-classification,
   lem-pc-projective-space-twist-cohomology and def-pc-degree-line-bundle.
4. Apply lem-sfb-relative-acyclic-direct-image to (T,Y,X,q,L). It gives finite
   presentation, quasi-coherence, T-flatness, R1=0 and all base-change isomorphisms.
   No Noetherian hypothesis or flatness of q or of the base change is used.
5. In nonnegative degree the two homogeneous monomials x0^d and x1^d generate O(d)
   on its two charts (def-sc-p1-standard); for d=0 use 1. Point fibres are generated
   too. The generation conclusion of the same relative criterion gives surjectivity
   of the adjunction counit. Degree -1 is deliberately excluded from this clause.
6. Locally the canonical comparison sends b tensor s to b times the pulled-back s.
   A further change sends b'' tensor (b' tensor s) to b'' h*(b') times the composite
   pullback of s, independently of the path. Replacing s by its line-bundle
   isomorphism gives naturality. This proves the compatibility equations, including
   all diagram isomorphisms, with the normalized comparisons of def-pc-module-pullback.
-/
theorem line_cohomology
    (D : Diagram.{u}) [IsProper D.pX] [IsProper D.pY] [Flat D.pX] [Flat D.pY]
    [LocallyOfFinitePresentation D.pX] [LocallyOfFinitePresentation D.pY]
    (hX : HasNodalGeometricFibres D.pX) (hY : HasNodalGeometricFibres D.pY)
    (hXpure : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ D.T),
      IsReduced (pullback (C := Scheme.{u}) D.pX a) ∧
        (pullback (C := Scheme.{u}) D.pX a).IsPureDimension 1)
    (hYpure : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ D.T),
      IsReduced (pullback (C := Scheme.{u}) D.pY a) ∧
        (pullback (C := Scheme.{u}) D.pY a).IsPureDimension 1)
    (hq : D.IsElementary)
    (L : D.Y.Modules) [L.IsInvertible] (hdegree : D.DegreeAtLeast L (-1)) :
    ((Scheme.Modules.pushforward D.q).obj L).IsQuasicoherent ∧
    ((Scheme.Modules.pushforward D.q).obj L).IsFinitePresentation ∧
    ((Scheme.Modules.pushforward D.q).obj L).IsFlatOver D.pX ∧
    IsZero ((Scheme.Modules.higherDirectImage D.q 1).obj L) ∧
    (∀ (D' : Diagram.{u}) (A : D.Change D'), IsIso (A.comparison L)) ∧
    (D.DegreeAtLeast L 0 →
      Epi ((Scheme.Modules.tensorPullbackSectionAdjunction D.q).counit.app L)) ∧
    D.Compatible L := by
  sorry

end Diagram
end AlgebraicGeometry.RationalContraction
