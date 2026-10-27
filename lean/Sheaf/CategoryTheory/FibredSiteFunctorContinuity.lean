/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
public import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Sites.Continuous

/-! # Functoriality of inherited sites of fibred groupoids

Source: Stacks Project, Tags 06NU and 06NW
(blueprint: lem-sfb-fibred-site-functor-continuity).

The covering families retain their indices. The base and total categories have
independent object and morphism universes; their common bound is used for covering
indices and for sets of sections. All arrows are strongly cartesian, so preserving
cartesian arrows imposes no additional condition on a functor over the base.

`IsSiteForCoveringFamilies` retains the actual indexed families needed for this
inherited-site construction. `coveringFamiliesPrecoverage` forgets their indices
only when forming the topology for sheaves. The existing presieve site interface
is imported from `SiteCoveringAxioms` and its dependency record is retained.
-/

@[expose] public section

set_option autoImplicit false

universe w u v ub vb ux vx uy vy

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The three site axioms and closure under bijective reindexing for actual indexed
families. Pullbacks need exist only for covering arrows, and some choice of the
pullback family must cover, as in the clarification after 00VH(3).
Source: Stacks Project, Sites, Definition 00VH
(blueprint: lem-sfb-fibred-site-functor-continuity). -/
def IsSiteForCoveringFamilies {C : Type u} [Category.{v} C]
    (Cov : ∀ X : C, Set (PreZeroHypercover.{w} X)) : Prop :=
  (∀ (X Y : C) (f : Y ⟶ X), IsIso f → Cov X (.singleton f)) ∧
  (∀ (X : C) (E : PreZeroHypercover.{w} X)
    (D : ∀ i : E.I₀, PreZeroHypercover.{w} (E.X i)),
    Cov X E → (∀ i, Cov (E.X i) (D i)) → Cov X (E.bind D)) ∧
  (∀ (X : C) (E : PreZeroHypercover.{w} X), Cov X E →
    ∀ (Y : C) (g : Y ⟶ X),
      ∃ (P : E.I₀ → C) (a : ∀ i, P i ⟶ Y) (b : ∀ i, P i ⟶ E.X i),
        (∀ i, IsPullback (a i) (b i) g (E.f i)) ∧ Cov Y ⟨E.I₀, P, a⟩) ∧
  (∀ (X : C) (E : PreZeroHypercover.{w} X) (I : Type w) (e : I ≃ E.I₀),
    Cov X E → Cov X (E.reindex e))

/-- Forget the indexing only when generating the topology used for sheaves. An actual
covering family witnesses membership of its underlying presieve.
Source: Stacks Project, Sites, Definitions 00VH, 00VM, 00VR
(blueprint: lem-sfb-fibred-site-functor-continuity). -/
def coveringFamiliesPrecoverage {C : Type u} [Category.{v} C]
    (Cov : ∀ X : C, Set (PreZeroHypercover.{w} X)) : Precoverage C where
  coverings X := {R | ∃ E : PreZeroHypercover.{w} X, Cov X E ∧ E.presieve₀ = R}

/-- A family in the total category covers exactly when its image family covers in
its base. For a fibred groupoid the strongly cartesian condition in 06NU is automatic.
Source: Stacks Project, Tag 06NU, remark following the proof
(blueprint: lem-sfb-fibred-site-functor-continuity). -/
def inheritedCoveringFamilies {B : Type ub} [Category.{vb} B]
    {X : Type ux} [Category.{vx} X]
    (Cov : ∀ b : B, Set (PreZeroHypercover.{w} b)) (p : X ⥤ B)
    (x : X) : Set (PreZeroHypercover.{w} x) :=
  {E | Cov (p.obj x) (E.map p)}

/-- The inherited indexed families give sites, and every functor over the base between
fibred groupoids preserves covers and covering pullbacks, is continuous and
cocontinuous, and lifts a cover with the same index set up to isomorphism over its target.
Source: Stacks Project, Tags 06NU and 06NW
(blueprint: lem-sfb-fibred-site-functor-continuity).

Proof: (1) Isomorphism covers, composition and bijective reindexing descend to the
base-site axioms (def-weil-pbc-sites-and-cohomology).
(2) Pull back a base covering along the image of an arbitrary total-category arrow.
Lift its pullback projections cartesianly. The cartesian universal properties give
pullback squares upstairs (lem-sfb-cartesian-lift-pullback-square, Stacks 06N4),
so these lifted projections form the required covering pullback. Apply this to both
projections p and r to obtain the inherited sites.
(3) The equality F ⋙ r = p gives cover preservation. The image of a covering
pullback square is again the pullback square over the same base pullback, by the
same cartesian universal property in Y. Hence the canonical comparison is invertible.
These are the two conditions of Stacks continuity.
(4) Given a covering of F(x), lift its base arrows to arrows x_i → x. Each F(x_i) → F(x)
and the corresponding given arrow are cartesian lifts of the same base arrow.
Their universal properties give mutually inverse comparison arrows, over the identity
in the base and commuting with their maps to F(x). This gives the stated isomorphisms
and hence the refinement required for cocontinuity
(def-weil-pbc-special-cocontinuous-functor, condition (1)).
(5) The equalizer diagram for a sheaf on Y and the image covering is the diagram
for its precomposition on X, using the pullback comparisons of (3). Thus
precomposition preserves sheaves, also for the empty covering (Stacks 00WW). -/
theorem fibredSiteFunctor_continuity
    {B : Type ub} [Category.{vb} B]
    {X : Type ux} [Category.{vx} X] {Y : Type uy} [Category.{vy} Y]
    (Cov : ∀ b : B, Set (PreZeroHypercover.{max w ub vb ux vx uy vy} b))
    (hCov : IsSiteForCoveringFamilies Cov)
    (p : X ⥤ B) (r : Y ⥤ B) [p.IsPreFibered] [r.IsPreFibered]
    (hp : ∀ (x' x : X) (a : x' ⟶ x), p.IsStronglyCartesian (p.map a) a)
    (hr : ∀ (y' y : Y) (a : y' ⟶ y), r.IsStronglyCartesian (r.map a) a)
    (F : X ⥤ Y) (hF : F ⋙ r = p) :
    IsSiteForCoveringFamilies (inheritedCoveringFamilies Cov p) ∧
    IsSiteForCoveringFamilies (inheritedCoveringFamilies Cov r) ∧
    (∀ (x : X) (E : PreZeroHypercover.{max w ub vb ux vx uy vy} x),
      inheritedCoveringFamilies Cov p x E →
        inheritedCoveringFamilies Cov r (F.obj x) (E.map F)) ∧
    (∀ (x : X) (E : PreZeroHypercover.{max w ub vb ux vx uy vy} x),
      inheritedCoveringFamilies Cov p x E →
        ∀ (i : E.I₀) (t : X) (g : t ⟶ x), PreservesLimit (cospan (E.f i) g) F) ∧
    F.IsContinuous
      (coveringFamiliesPrecoverage (inheritedCoveringFamilies Cov p)).toGrothendieck
      (coveringFamiliesPrecoverage (inheritedCoveringFamilies Cov r)).toGrothendieck ∧
    F.IsCocontinuous
      (coveringFamiliesPrecoverage (inheritedCoveringFamilies Cov p)).toGrothendieck
      (coveringFamiliesPrecoverage (inheritedCoveringFamilies Cov r)).toGrothendieck ∧
    (∀ G : Sheaf
      (coveringFamiliesPrecoverage (inheritedCoveringFamilies Cov r)).toGrothendieck
        (Type (max w ub vb ux vx uy vy)),
      Presheaf.IsSheaf
        (coveringFamiliesPrecoverage (inheritedCoveringFamilies Cov p)).toGrothendieck
        (F.op ⋙ G.obj)) ∧
    (∀ (x : X) (E : PreZeroHypercover.{max w ub vb ux vx uy vy} (F.obj x)),
      inheritedCoveringFamilies Cov r (F.obj x) E →
        ∃ (U : E.I₀ → X) (a : ∀ i, U i ⟶ x) (e : ∀ i, F.obj (U i) ≅ E.X i),
          inheritedCoveringFamilies Cov p x ⟨E.I₀, U, a⟩ ∧
            ∀ i, (e i).hom ≫ E.f i = F.map (a i)) := by
  sorry

end CategoryTheory
