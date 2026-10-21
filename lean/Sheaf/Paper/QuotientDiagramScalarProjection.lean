/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.StrictQuotientScalarBalancing
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.ProjectionFormulaBaseChangeNaturality
import Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.Paper.CompletedConstantAlgebraFlatQuotients
import Sheaf.Paper.ReductionPullbackDerivedTower
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # Scalar compatibility of the strict quotient projection morphism

Source: main-20261015, sec-proper-base-change/sk-thm-properbasechange,
lemma-weil-pbc-completed-exchange-coherence.proof.md, second paragraph,
strict coefficient supplement old Step 5; Stacks 0B56 and 0FND.
(blueprint: lem-weil-pbc-quotient-diagram-scalar-projection).

Use the published small pro-etale model, its actual completed coefficient limit and
its strict derived reductions. Index n denotes the positive exponent n+1. Direct images
are specified as right adjoints of the normalized derived inverse images. Right adjoints
with their adjunctions determine the ordinary unbounded derived operations up to unique
adjunction-preserving isomorphism. The scalar comparisons are their specified right mates,
exactly the normalization of flat-ringed-diagram-restriction. Projection is the mate of
the inverse pullback/reduction comparison, hence the adjunct of counit tensored with identity
under the diagonal direct-image identification. All equalities occur before evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ConstantCompletion

namespace AlgebraicGeometry.Scheme.StrictScalarBalancing

variable {A : Type (u + 1)} [CommRing A]

/-- The strict projection transformation, defined by the actual adjunction Hom bijection.
At K its adjunct is the inverse of tau at RK followed by reduction of the ordinary counit.
Thus it is the counit-tensor projection of Stacks 0B56 under the normalized diagonal
identification, rather than a map chosen by its evaluations.
Source: completed-exchange-coherence proof, second paragraph, strict supplement Step 5;
Stacks 0B56 (blueprint: lem-weil-pbc-quotient-diagram-scalar-projection). -/
def quotientProjection {X Y : Scheme.{u}} (f : X ⟶ Y) (d : AdicCoefficientDatum A)
    (b : Bool) (p : PullModel f d b)
    (R : D (ring X d b) ⥤ D (ring Y d b))
    (H : TD (ring X d b) ⥤ TD (ring Y d b))
    (ordinaryAdj : p.ordinary ⊣ R) (diagramAdj : p.diagrams ⊣ H)
    (tau : p.ordinary ⋙ reduction X d b ≅ reduction Y d b ⋙ p.diagrams) :
    R ⋙ reduction Y d b ⟶ reduction X d b ⋙ H :=
  (mateEquiv ordinaryAdj diagramAdj (TwoSquare.mk _ _ _ _ tau.inv)).natTrans

/-- The ordinary direct-image scalar comparison is the right mate of a inverse.
Its normalization is the adjunct identity of flat-ringed-diagram-restriction.
Source: strict supplement Step 5, scalar-counit calculation; Stacks 0FND
(blueprint: lem-weil-pbc-quotient-diagram-scalar-projection). -/
def ordinaryScalarDirect {X Y : Scheme.{u}} (f : X ⟶ Y) (d : AdicCoefficientDatum A)
    (bal : Balancing d) (p : PullCompatibility f d (bal.ρ Y) (bal.ρ X))
    (Ra : D (ring X d true) ⥤ D (ring Y d true))
    (R0 : D (ring X d false) ⥤ D (ring Y d false))
    (adjA : p.completed.ordinary ⊣ Ra) (adj0 : p.constant.ordinary ⊣ R0) :
    Ra ⋙ dres (scalar Y d) ⟶ dres (scalar X d) ⋙ R0 :=
  (mateEquiv adjA adj0 (TwoSquare.mk _ _ _ _ p.a.inv)).natTrans

/-- The strict-diagram direct-image scalar comparison is the right mate of p inverse.
This is the normalized d of flat-ringed-diagram-restriction, including all transitions.
Source: strict supplement Step 5, strict-diagram adjunct identity; Stacks 0FND
(blueprint: lem-weil-pbc-quotient-diagram-scalar-projection). -/
def diagramScalarDirect {X Y : Scheme.{u}} (f : X ⟶ Y) (d : AdicCoefficientDatum A)
    (bal : Balancing d) (p : PullCompatibility f d (bal.ρ Y) (bal.ρ X))
    (Ha : TD (ring X d true) ⥤ TD (ring Y d true))
    (H0 : TD (ring X d false) ⥤ TD (ring Y d false))
    (adjA : p.completed.diagrams ⊣ Ha) (adj0 : p.constant.diagrams ⊣ H0) :
    Ha ⋙ tdres (scalar Y d) ⟶ tdres (scalar X d) ⋙ H0 :=
  (mateEquiv adjA adj0 (TwoSquare.mk _ _ _ _ p.p.inv)).natTrans

/-- Scalar restriction carries the completed-coefficient strict projection to the
constant-coefficient strict projection. The two direct scalar comparisons are invertible.
Every displayed map is a component of a natural transformation, and K ranges over the
entire unbounded ambient derived category.

Source: main-20261015, completed-exchange-coherence proof, second paragraph,
strict coefficient supplement old Step 5; Stacks 0B56 and 0FND.
(blueprint: lem-weil-pbc-quotient-diagram-scalar-projection).

Proof:
1. Completed-constant-algebra-flat-quotients gives flatness of the completed ring over
constant A. Profinite-coefficient-inverse-image identifies completed and finite rings,
preserving the quotient projections. Constant-left-module-inverse-image identifies
constant A even if A is infinite. Check scalar compatibility after every finite
projection: both adjuncts send a constant x to its residue. Joint determination by the
projections gives the scalar square. Flat-ringed-diagram-restriction, first for ordinary
modules and then for strict diagrams, gives the normalized comparisons and their
invertibility. Diagram-site-realization places them in the strict derived categories.
2. Write B for reduction. Augmented-diagram-projection-mate identifies each projection
with the adjunct of s at RK followed by B of the ordinary counit, where s is tau inverse.
Constant-tower-pushforward-normalization supplies the strict counit equation, identifying
this with counit tensored with identity under the diagonal direct-image comparison.
3. The ordinary scalar adjunct identity gives r(epsilonA) after a inverse equal to
G(chi) followed by epsilon0. This also follows directly from the right-mate formula.
4. Apply strict-quotient-scalar-balancing to M = Ra K. Its pullback equation identifies
rho after r(sA) and p inverse with G(rho) followed by s0 and B(a inverse).
Reduction-pullback-derived-tower and ringed-topoi-derived-tensor-pullback identify these
s maps: both are the termwise tensor comparison on flat-term K-flat representatives.
5. Apply naturality of rho to epsilonA, substitute the equations of steps 4 and 3,
and use naturality of s0 at chi. The result is the identity of the two adjuncts:
r(tA), corrected by p inverse and rho, equals G(B(chi) after rho) followed by t0.
6. The strict scalar adjunct identity identifies the first side with the adjunct of
the left displayed composite. Naturality of the Hom bijection identifies the other
side with the adjunct of the right displayed composite. Injectivity proves equality.
7. Counits, reassociations, balancing and right mates are natural. Thus the equality
holds naturally for every K. Every calculation takes place in the derived category of
strict towers, so no faithfulness of derived evaluation, properness, completeness or
witness hypothesis is used. -/
theorem quotientDiagramScalarProjection
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : AdicCoefficientDatum A)
    (bal : Balancing d) (p : PullCompatibility f d (bal.ρ Y) (bal.ρ X))
    (Ra : D (ring X d true) ⥤ D (ring Y d true))
    (R0 : D (ring X d false) ⥤ D (ring Y d false))
    (Ha : TD (ring X d true) ⥤ TD (ring Y d true))
    (H0 : TD (ring X d false) ⥤ TD (ring Y d false))
    (ordinaryAdjA : p.completed.ordinary ⊣ Ra)
    (ordinaryAdj0 : p.constant.ordinary ⊣ R0)
    (diagramAdjA : p.completed.diagrams ⊣ Ha)
    (diagramAdj0 : p.constant.diagrams ⊣ H0) :
    IsIso (ordinaryScalarDirect f d bal p Ra R0 ordinaryAdjA ordinaryAdj0) ∧
      IsIso (diagramScalarDirect f d bal p Ha H0 diagramAdjA diagramAdj0) ∧
      ∀ K : D (ring X d true),
        (tdres (scalar Y d)).map
            ((quotientProjection f d true p.completed Ra Ha ordinaryAdjA diagramAdjA p.τ).app K) ≫
          (diagramScalarDirect f d bal p Ha H0 diagramAdjA diagramAdj0).app
            ((reduction X d true).obj K) ≫ H0.map ((bal.ρ X).hom.app K) =
        (bal.ρ Y).hom.app (Ra.obj K) ≫
          (reduction Y d false).map
            ((ordinaryScalarDirect f d bal p Ra R0 ordinaryAdjA ordinaryAdj0).app K) ≫
          (quotientProjection f d false p.constant R0 H0 ordinaryAdj0 diagramAdj0
            p.constantReassociation).app ((dres (scalar X d)).obj K) := by
  sorry

end AlgebraicGeometry.Scheme.StrictScalarBalancing
