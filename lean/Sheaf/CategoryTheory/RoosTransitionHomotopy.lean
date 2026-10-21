/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionDefs
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.Homotopy

/-!
# The forward arithmetic Roos transition and its specified homotopy

Source: Stacks Project, sites-cohomology.tex, Tag 0941, lemma-derived-limit-is-ok,
and algebra.tex, Tag 00LR, lemma-homotopic-equal-homology. The coordinate calculations
are the ten-step agent proof of (blueprint: lem-weil-roos-transition-homotopy).

We reuse `roosF` and the arithmetic restriction, selection and block constructions.
Index `n : ℕ` denotes positive index `n+1`; its dilate is `e*(n+1)-1`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w uC vC r

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.StrictTowerArithmetic

namespace CategoryTheory.RoosTransition

variable {D : Type u} [Category.{v} D] [Abelian D] [HasCountableProducts D]

/-- The product transition T from the arithmetic subsequence to the original tower.
Source: Tag 0941, explicit forward-transition refinement, proof step 1
(blueprint: lem-weil-roos-transition-homotopy). -/
def forward (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (e : ℕ) (he : 0 < e) :
    roosP ((complexRestriction D e).obj X) ⟶ roosP X :=
  Pi.lift (fun n ↦ Pi.π
    (fun i : ℕ ↦ ((complexRestriction D e).obj X).asFunctor.obj (op i)) n ≫
      X.asFunctor.map (homOfLE (Nat.le_sub_one_of_lt
        ((Nat.lt_succ_self n).trans_le (Nat.le_mul_of_pos_left (n + 1) he)))).op)

/-- The finite telescoping sum h, including the empty interval when e=1.
Source: Tag 0941, explicit forward-transition refinement, proof steps 4-5
(blueprint: lem-weil-roos-transition-homotopy). -/
def telescope (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (e : ℕ) : roosP X ⟶ roosP X :=
  Pi.lift (fun n ↦ ∑ k ∈ Finset.range (e * (n + 1) - 1 - n),
    Pi.π (fun i : ℕ ↦ X.asFunctor.obj (op i)) (n + k) ≫
      X.asFunctor.map (homOfLE (Nat.le_add_right n k)).op)

/-- The endomorphism phi, with coordinate T_(n,en) x_en.
Source: Tag 0941, explicit forward-transition refinement, proof step 3
(blueprint: lem-weil-roos-transition-homotopy). -/
def phi (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (e : ℕ) (he : 0 < e) : roosP X ⟶ roosP X :=
  selection e X.asFunctor ≫ forward X e he

/-- The endomorphism psi, with coordinate sum_(en ≤ i < e(n+1)) T_(n,i) y_i.
Source: Tag 0941, explicit forward-transition refinement, proof step 3
(blueprint: lem-weil-roos-transition-homotopy). -/
def psi (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (e : ℕ) (he : 0 < e) : roosP X ⟶ roosP X :=
  block e X.asFunctor ≫ forward X e he

/-- The complete coordinate, homotopy, localization and naturality assertion.
The witnesses are simultaneous over all strict towers, so the naturality clauses
refer to the same maps and the same explicitly normalized homotopy.
Source: Tag 0941, explicit forward-transition refinement, proof steps 1-10
(blueprint: lem-weil-roos-transition-homotopy). -/
def TransitionHomotopy (D : Type u) [Category.{v} D] [Abelian D]
    [HasCountableProducts D] [HasDerivedCategory.{w} D] : Prop :=
  ∀ (e : ℕ) (he : 0 < e),
    ∃ (res : ∀ X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ,
        roosF.obj X ⟶ roosF.obj ((complexRestriction D e).obj X))
      (delta : ∀ X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ,
        roosF.obj ((complexRestriction D e).obj X) ⟶ roosF.obj X)
      (H : ∀ X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ,
        Homotopy (𝟙 (roosF.obj X)) (res X ≫ delta X)),
      (∀ X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ,
        (roosU X ≫ block e X.asFunctor =
          selection e X.asFunctor ≫ roosU ((complexRestriction D e).obj X)) ∧
        (roosU ((complexRestriction D e).obj X) ≫ forward X e he =
          forward X e he ≫ roosU X) ∧
        (∀ p : ℤ,
          (res X).f (p + 1) ≫ (roosχ ((complexRestriction D e).obj X) p).hom =
            (roosχ X p).hom ≫
              biprod.map ((block e X.asFunctor).f p) ((selection e X.asFunctor).f (p + 1))) ∧
        (∀ p : ℤ,
          (delta X).f (p + 1) ≫ (roosχ X p).hom =
            (roosχ ((complexRestriction D e).obj X) p).hom ≫
              biprod.map ((forward X e he).f p) ((forward X e he).f (p + 1))) ∧
        (∀ p : ℤ,
          (res X ≫ delta X).f (p + 1) ≫ (roosχ X p).hom =
            (roosχ X p).hom ≫ biprod.map ((psi X e he).f p) ((phi X e he).f (p + 1))) ∧
        (roosU X ≫ telescope X e = 𝟙 _ - phi X e he) ∧
        (telescope X e ≫ roosU X = 𝟙 _ - psi X e he) ∧
        (∀ p : ℤ,
          (H X).hom (p + 1 + 1) (p + 1) ≫ (roosχ X p).hom =
            (roosχ X (p + 1)).hom ≫
              biprod.lift 0 (-(biprod.fst ≫ (telescope X e).f (p + 1)))) ∧
        QuasiIso (delta X) ∧ QuasiIso (res X) ∧
        (∃ i : DerivedCategory.Q.{w}.obj (roosF.obj X) ≅
            DerivedCategory.Q.{w}.obj (roosF.obj ((complexRestriction D e).obj X)),
          i.hom = DerivedCategory.Q.{w}.map (res X) ∧
          i.inv = DerivedCategory.Q.{w}.map (delta X))) ∧
      (∀ (X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (a : X ⟶ Y),
        (roosF.map a ≫ res Y = res X ≫ roosF.map ((complexRestriction D e).map a)) ∧
        (roosF.map ((complexRestriction D e).map a) ≫ delta Y = delta X ≫ roosF.map a) ∧
        (roosPmap a ≫ selection e Y.asFunctor = selection e X.asFunctor ≫
          roosPmap ((complexRestriction D e).map a)) ∧
        (roosPmap a ≫ block e Y.asFunctor = block e X.asFunctor ≫
          roosPmap ((complexRestriction D e).map a)) ∧
        (roosPmap ((complexRestriction D e).map a) ≫ forward Y e he =
          forward X e he ≫ roosPmap a) ∧
        (roosPmap a ≫ telescope Y e = telescope X e ≫ roosPmap a) ∧
        (roosPmap a ≫ phi Y e he = phi X e he ≫ roosPmap a) ∧
        (roosPmap a ≫ psi Y e he = psi X e he ≫ roosPmap a) ∧
        (∀ p : ℤ, (H X).hom (p + 1) p ≫ (roosF.map a).f p =
          (roosF.map a).f (p + 1) ≫ (H Y).hom (p + 1) p))

/-- The forward Roos transition is the inverse of the finite-block restriction, with
exactly the displayed telescoping homotopy. This holds for constant A-coefficients
and for every sheaf of commutative A-algebras, with all arrows and homotopies linear
in that module category. The algebra clause imposes no exact-product hypothesis.

Source: sites-cohomology.tex, Tag 0941, lemma-derived-limit-is-ok, Roos model;
algebra.tex, Tag 00LR, lemma-homotopic-equal-homology. Explicit agent refinement
(blueprint: lem-weil-roos-transition-homotopy).

Proof, following the node's ten steps:
1. Product projections and composites of transitions define all maps. The tower law
   gives fT=Tf_e, hence the diagonal forward map is a chain map.
2. The block sum telescopes to b_e f=f_e a_e, giving the restriction chain map.
3. The two composite coordinates are T b_e=psi and T a_e=phi.
4. Telescoping [n,en) gives hf=1-phi, also for the empty interval e=1.
5. Subtracting [n,en) and [n+1,e(n+1)) gives fh=1-psi.
6. Since dh=hd, H(y,x)=(0,-hy) gives dH+Hd=(fhy,hfx)=1-delta res,
   with the stated shifted-cone signs (def-weil-abstract-derived-category).
7. For the subsequence tower L_n=K_en, the other composite has the same phi/psi
   formulas for L. Repeating the finite-sum calculation gives the opposite homotopy.
8. A null-homotopy induces zero on ker(d)/im(d), so the two maps induce inverse
   cohomology isomorphisms (Tag 00LR).
9. Localization through the homotopy category gives the specified inverse equality.
10. A strict tower morphism commutes with every composite transition, proving all
    naturality identities. Products of R-modules are sectionwise products with
    coordinatewise action and gluing; projections, sums and transitions are linear.
    Steps 1-9 apply there without needing products to be exact. -/
theorem roos_transition_homotopy
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J RingCat.{max uC vC r}]
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (A : Type (max uC vC r)) [CommRing A]
    [HasDerivedCategory.{w}
      (ringedSiteModules.{max uC vC r} ((constantSheaf J RingCat).obj (RingCat.of A)))]
    [HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{max uC vC r} ((constantSheaf J RingCat).obj (RingCat.of A)))] :
    TransitionHomotopy.{_, _, w}
      (ringedSiteModules.{max uC vC r} ((constantSheaf J RingCat).obj (RingCat.of A))) ∧
    ∀ (R : Sheaf J RingCat.{max uC vC r})
      (_algebra : (constantSheaf J RingCat).obj (RingCat.of A) ⟶ R)
      (_comm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
      [HasDerivedCategory.{w} (ringedSiteModules.{max uC vC r} R)],
      TransitionHomotopy.{_, _, w} (ringedSiteModules.{max uC vC r} R) := by
  sorry

end CategoryTheory.RoosTransition
