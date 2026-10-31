/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SheafDgHomotopySystem
public import Mathlib.CategoryTheory.Monoidal.Bimod

/-! # Balanced tensor and internal Hom for sheaf dg bimodules

Source: Stacks Project, `sdga.tex`, graded tensor and internal Hom constructions
and Tag 0FRS (blueprint: def-sf-sheaf-dg-bimodule-models).

The existing monoidal category of unbounded complexes of module sheaves supplies
both the coefficient sheaf tensor and its signed direct-sum totalization. Universal
properties specify the constructions without choosing any data from a postponed proof.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.RingedSiteDg

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O : Sheaf J CommRingCat.{u}}

/-- The first balancing arrow acts on the right module.
Source: Stacks `sdga.tex`, tensor products (blueprint: def-sf-sheaf-dg-bimodule-models). -/
def bimoduleBalanceLeft {A B : Algebra O} (N : Bimod A B) (M : Module A) :
    ((underlying A).obj M ⊗ A.X) ⊗ N.X ⟶ (underlying A).obj M ⊗ N.X :=
  action M ▷ N.X

/-- The second balancing arrow acts on the left of the bimodule.
Source: Stacks `sdga.tex`, tensor products (blueprint: def-sf-sheaf-dg-bimodule-models). -/
def bimoduleBalanceRight {A B : Algebra O} (N : Bimod A B) (M : Module A) :
    ((underlying A).obj M ⊗ A.X) ⊗ N.X ⟶ (underlying A).obj M ⊗ N.X :=
  (α_ _ _ _).hom ≫ ((underlying A).obj M ◁ N.actLeft)

/-- The ordinary balanced sheaf tensor functor is characterized by its coequalizer
and induced right action, naturally on all chain maps. The ambient tensor is already
sheafified, with direct-sum total grading and the signed tensor differential.
Source: Stacks `sdga.tex`, tensor products and 0FRS
(blueprint: def-sf-sheaf-dg-bimodule-models). -/
structure SheafBalancedTensorModel {A B : Algebra O} (N : Bimod A B)
    (F : Module A ⥤ Module B) where
  π (M : Module A) : (underlying A).obj M ⊗ N.X ⟶ (underlying B).obj (F.obj M)
  balance (M : Module A) : bimoduleBalanceLeft N M ≫ π M =
    bimoduleBalanceRight N M ≫ π M
  colimit (M : Module A) : Nonempty (IsColimit (Cofork.ofπ (π M) (balance M)))
  naturality {M M' : Module A} (f : M ⟶ M') :
    ((underlying A).map f ▷ N.X) ≫ π M' = π M ≫ (underlying B).map (F.map f)
  right_action (M : Module A) :
    ((underlying A).obj M ◁ N.actRight) ≫ π M =
      (α_ _ _ _).inv ≫ (π M ▷ B.X) ≫ action (F.obj M)

/-- Right B-linearity of an evaluation map, with no sign in the right-module convention.
Source: Stacks `sdga.tex`, internal Hom (blueprint: def-sf-sheaf-dg-bimodule-models). -/
def IsBimoduleEvaluation {A B : Algebra O} (N : Bimod A B)
    (X : Complex O) (L : Module B) (e : X ⊗ N.X ⟶ (underlying B).obj L) : Prop :=
  (α_ X N.X B.X).hom ≫ (X ◁ N.actRight) ≫ e =
    (e ▷ B.X) ≫ action L

/-- The full internal Hom complex is specified by universal B-linear evaluation,
against every test complex of module sheaves. This determines its terms and differential:
locally the degree-r term is the product of degree-r right graded B-linear maps,
and d(f) = d_L f - (-1)^r f d_N. Tests include arbitrary sheaves placed in each degree,
so this is internal sheaf Hom, rather than merely the complex of global maps.
The right A-action is precomposition with the left action on N, without a braiding.
Source: Stacks `sdga.tex`, internal Hom and 0FRS
(blueprint: def-sf-sheaf-dg-bimodule-models). -/
structure SheafBimoduleHomModel {A B : Algebra O} (N : Bimod A B)
    (G : Module B ⥤ Module A) where
  evaluation (L : Module B) : (underlying A).obj (G.obj L) ⊗ N.X ⟶ (underlying B).obj L
  right_linear (L : Module B) :
    IsBimoduleEvaluation N ((underlying A).obj (G.obj L)) L (evaluation L)
  universal (L : Module B) (X : Complex O)
      (e : X ⊗ N.X ⟶ (underlying B).obj L) (he : IsBimoduleEvaluation N X L e) :
    ∃! f : X ⟶ (underlying A).obj (G.obj L), (f ▷ N.X) ≫ evaluation L = e
  action_eq (L : Module B) :
    (action (G.obj L) ▷ N.X) ≫ evaluation L =
      (α_ _ _ _).hom ≫ (((underlying A).obj (G.obj L)) ◁ N.actLeft) ≫ evaluation L
  naturality {L L' : Module B} (f : L ⟶ L') :
    ((underlying A).map (G.map f) ▷ N.X) ≫ evaluation L' =
      evaluation L ≫ (underlying B).map f

/-- An ordinary adjunction is the specified tensor-Hom currying exactly when evaluation
of its transpose is the original map on the balanced tensor. This is the sheaf-map equation
Phi(f)(m)(n) = f(m tensor n), including all local homogeneous pure tensors.
Source: Stacks `sdga.tex`, Tag 0FRS (blueprint: def-sf-sheaf-dg-bimodule-models). -/
def IsSheafBimoduleCurrying {A B : Algebra O} (N : Bimod A B)
    {F : Module A ⥤ Module B} {G : Module B ⥤ Module A}
    (t : SheafBalancedTensorModel N F) (h : SheafBimoduleHomModel N G)
    (adj : F ⊣ G) : Prop :=
  ∀ (M : Module A) (L : Module B) (f : F.obj M ⟶ L),
    ((underlying A).map (adj.homEquiv M L f) ▷ N.X) ≫ h.evaluation L =
      t.π M ≫ (underlying B).map f

end CategoryTheory.RingedSiteDg
