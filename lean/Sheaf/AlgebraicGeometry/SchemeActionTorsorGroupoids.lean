/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Sites.Over
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack

/-! # Scheme actions, their action groupoid, and equivariant scheme torsors

Source: Stacks Project, examples-stacks.tex, Situation 04WL and Proposition 04WM
(blueprint: def-sfb-scheme-action-torsor-groupoids).

The acting group and its actions are Mathlib's internal group and module objects.
Torsors are actual schemes locally equivariantly isomorphic to the trivial torsor.
Total arrows are cartesian equivariant scheme maps, so the projection remembers
fibre-product pullback rather than only isomorphism classes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.SchemeAction

variable {S : Scheme.{u}} (G V : Over S) [GrpObj G] [ModObj G V]

/-- An object of the action groupoid over a variable test scheme.
Source: Stacks 04WM (blueprint: def-sfb-scheme-action-torsor-groupoids). -/
structure ActionObject (G V : Over S) where
  base : Over S
  point : base ⟶ V

/-- A base arrow and a group element taking the source point to the target point.
Source: Stacks 04WM (blueprint: def-sfb-scheme-action-torsor-groupoids). -/
@[ext]
structure ActionHom (X Y : ActionObject G V) where
  base : X.base ⟶ Y.base
  label : X.base ⟶ G
  equation : label • X.point = base ≫ Y.point

/-- Composition multiplies the second label, restricted to the first base, on the left.
Source: Stacks 04WM (blueprint: def-sfb-scheme-action-torsor-groupoids). -/
instance : Category (ActionObject G V) where
  Hom := ActionHom G V
  id X := ⟨𝟙 X.base, 1, by simp⟩
  comp a b := ⟨a.base ≫ b.base, (a.base ≫ b.label) * a.label, by
    rw [mul_smul, a.equation, ← ModObj.comp_smul, b.equation, Category.assoc]⟩
  id_comp a := by
    apply ActionHom.ext <;> simp
  comp_id a := by
    apply ActionHom.ext <;> simp
  assoc a b c := by
    apply ActionHom.ext <;> simp [MonObj.comp_mul, Category.assoc, mul_assoc]

/-- The action groupoid as a category over the big site.
Source: Stacks 04WM (blueprint: def-sfb-scheme-action-torsor-groupoids). -/
def actionGroupoid : BasedCategory (Over S) :=
  BasedCategory.ofFunctor
    { obj := fun X : ActionObject G V ↦ X.base
      map := fun {X Y} (a : ActionHom G V X Y) ↦ a.base }

/-- The local trivialization condition, on an arbitrary covering sieve. A map from
`G × W` to `P` is an isomorphism to the base change precisely when its square is
cartesian. The displayed equality is equivariance on all test schemes.
Source: Stacks 04WL (blueprint: def-sfb-scheme-action-torsor-groupoids). -/
def IsLocallyTrivial (T P : Over S) [ModObj G P] (p : P ⟶ T) : Prop :=
  ∃ R : Sieve T, R ∈ (Scheme.fppfTopology.over S) T ∧
    ∀ (W : Over S) (b : W ⟶ T), R b →
      ∃ q : G ⊗ W ⟶ P,
        IsPullback q (snd G W) p b ∧
        ∀ (Z : Over S) (g h : Z ⟶ G) (w : Z ⟶ W),
          lift (g * h) w ≫ q = g • (lift h w ≫ q)

/-- A scheme torsor with an equivariant map to the action scheme. The invariance
of the projection is an equation, rather than a further action on the base.
Source: Stacks 04WL (blueprint: def-sfb-scheme-action-torsor-groupoids). -/
structure TorsorObject where
  base : Over S
  space : Over S
  action : ModObj G space
  projection : space ⟶ base
  invariant : ∀ (W : Over S) (g : W ⟶ G) (p : W ⟶ space),
    (lift g p ≫ action.smul) ≫ projection = p ≫ projection
  local_trivial : @IsLocallyTrivial S G _ base space action projection
  map : space ⟶ V
  equivariant : ∀ (W : Over S) (g : W ⟶ G) (p : W ⟶ space),
    (lift g p ≫ action.smul) ≫ map = g • (p ≫ map)

attribute [instance] TorsorObject.action

/-- Total arrows are equivariant maps whose base square is cartesian and whose
map to `V` is preserved. Over an identity these are exactly equivariant isomorphisms.
Source: Stacks 04WL (blueprint: def-sfb-scheme-action-torsor-groupoids). -/
@[ext]
structure TorsorHom (X Y : TorsorObject G V) where
  base : X.base ⟶ Y.base
  map : X.space ⟶ Y.space
  cartesian : IsPullback map X.projection Y.projection base
  equivariant : ∀ (W : Over S) (g : W ⟶ G) (p : W ⟶ X.space),
    (g • p) ≫ map = g • (p ≫ map)
  commutes : map ≫ Y.map = X.map

/-- Composition is ordinary scheme composition with pasting of cartesian squares.
Source: Stacks 04WL (blueprint: def-sfb-scheme-action-torsor-groupoids). -/
instance : Category (TorsorObject G V) where
  Hom := TorsorHom G V
  id X := ⟨𝟙 X.base, 𝟙 X.space, IsPullback.of_id_fst, by intros; simp, by simp⟩
  comp a b := ⟨a.base ≫ b.base, a.map ≫ b.map, a.cartesian.paste_horiz b.cartesian,
    by intros; simp only [← Category.assoc, a.equivariant, b.equivariant],
    by rw [Category.assoc, b.commutes, a.commutes]⟩
  id_comp a := by
    apply TorsorHom.ext <;> simp
  comp_id a := by
    apply TorsorHom.ext <;> simp
  assoc a b c := by
    apply TorsorHom.ext <;> simp [Category.assoc]

/-- The torsor groupoid with its actual base projection.
Source: Stacks 04WL (blueprint: def-sfb-scheme-action-torsor-groupoids). -/
def torsorGroupoid : BasedCategory (Over S) :=
  BasedCategory.ofFunctor
    { obj := fun X : TorsorObject G V ↦ X.base
      map := fun {X Y} (a : TorsorHom G V X Y) ↦ a.base }


/-- The actual left-translation map on a product with a test scheme.
Source: Stacks 04WL (blueprint: def-sfb-scheme-action-torsor-groupoids). -/
def trivialActionMap (T : Over S) : G ⊗ (G ⊗ T) ⟶ G ⊗ T :=
  lift (fst G (G ⊗ T) * (snd G (G ⊗ T) ≫ fst G T))
    (snd G (G ⊗ T) ≫ snd G T)

/-- Unitality and associativity of the specified left-translation map.
Source: Stacks 04WL (blueprint: def-sfb-scheme-action-torsor-groupoids).
Proof: compose with both product projections. The first projection gives
`1h=h` and `(gh)j=g(hj)` in the group of test points of `G`; the second
projection is unchanged. Yoneda and the universal property of products finish. -/
theorem trivial_action_laws (T : Over S) :
    (MonObj.one (X := G) ▷ (G ⊗ T)) ≫ trivialActionMap G T = (λ_ (G ⊗ T)).hom ∧
    (MonObj.mul (X := G) ▷ (G ⊗ T)) ≫ trivialActionMap G T =
      (α_ G G (G ⊗ T)).hom ≫ G ◁ trivialActionMap G T ≫ trivialActionMap G T := by
  sorry

/-- Left translation on the first factor of a trivial torsor.
Source: Stacks 04WL (blueprint: def-sfb-scheme-action-torsor-groupoids). -/
@[instance_reducible]
def trivialAction (T : Over S) : ModObj G (G ⊗ T) where
  smul := trivialActionMap G T
  one_smul := (trivial_action_laws G T).1
  mul_smul := (trivial_action_laws G T).2

/-- The specified projection and map of a trivial torsor satisfy the object laws.
Source: Stacks 04WL and 04WM (blueprint: def-sfb-scheme-action-torsor-groupoids).
Proof: on test points the action is `(g,(h,t)) ↦ (gh,t)`, so its projection is
invariant. For each base arrow `W → T`, the map `(h,w) ↦ (h,b(w))` is a
cartesian equivariant trivialization; take the maximal covering sieve. Finally
`(gh)·x = g·(h·x)` is the associativity law of the given action on `V`. -/
theorem trivial_object_laws (T : Over S) (x : T ⟶ V) :
    (∀ (W : Over S) (g : W ⟶ G) (p : W ⟶ G ⊗ T),
      (lift g p ≫ (trivialAction G T).smul) ≫ snd G T = p ≫ snd G T) ∧
    @IsLocallyTrivial S G _ T (G ⊗ T) (trivialAction G T) (snd G T) ∧
    (∀ (W : Over S) (g : W ⟶ G) (p : W ⟶ G ⊗ T),
      (lift g p ≫ (trivialAction G T).smul) ≫
          (lift (fst G T) (snd G T ≫ x) ≫ ModObj.smul (M := G) (X := V)) =
        g • (p ≫ (lift (fst G T) (snd G T ≫ x) ≫ ModObj.smul (M := G) (X := V)))) := by
  sorry

/-- The trivial scheme torsor and its actual orbit map.
Source: Stacks 04WM (blueprint: def-sfb-scheme-action-torsor-groupoids). -/
def trivialObject (X : ActionObject G V) : TorsorObject G V where
  base := X.base
  space := G ⊗ X.base
  action := trivialAction G X.base
  projection := snd G X.base
  invariant := (trivial_object_laws G V X.base X.point).1
  local_trivial := (trivial_object_laws G V X.base X.point).2.1
  map := lift (fst G X.base) (snd G X.base ≫ X.point) ≫ ModObj.smul (M := G) (X := V)
  equivariant := (trivial_object_laws G V X.base X.point).2.2

/-- The actual inverse-right-translation map of trivial torsor schemes.
Source: Stacks 04WM (blueprint: def-sfb-scheme-action-torsor-groupoids). -/
def trivialArrowMap {X Y : ActionObject G V} (a : ActionHom G V X Y) :
    (trivialObject G V X).space ⟶ (trivialObject G V Y).space :=
  lift (fst G X.base * (snd G X.base ≫ a.label)⁻¹) (snd G X.base ≫ a.base)

/-- Right translation by the inverse label is cartesian, equivariant and preserves
the orbit maps, and the formulas preserve identity and composition.
Source: Stacks 04WM (blueprint: def-sfb-scheme-action-torsor-groupoids).
Proof: over the source base, the inverse is right translation by the label, so the
base square is cartesian. Left and right multiplications commute. The equation
`g·x=y` gives `f_y(hg⁻¹)=h·x`. For successive labels `g,b`, the composite label
is `bg`, and right translations compose as `hg⁻¹b⁻¹=h(bg)⁻¹`. Restriction of
labels along base arrows gives the same identity over different test schemes. -/
theorem trivial_arrow_laws :
    (∀ {X Y : ActionObject G V} (a : ActionHom G V X Y),
      IsPullback (trivialArrowMap G V a) (trivialObject G V X).projection
        (trivialObject G V Y).projection a.base ∧
      (∀ (W : Over S) (g : W ⟶ G) (p : W ⟶ (trivialObject G V X).space),
        (g • p) ≫ trivialArrowMap G V a = g • (p ≫ trivialArrowMap G V a)) ∧
      trivialArrowMap G V a ≫ (trivialObject G V Y).map = (trivialObject G V X).map) ∧
    (∀ X : ActionObject G V, trivialArrowMap G V (𝟙 X) = 𝟙 _) ∧
    (∀ {X Y Z : ActionObject G V} (a : X ⟶ Y) (b : Y ⟶ Z),
      trivialArrowMap G V (a ≫ b) = trivialArrowMap G V a ≫ trivialArrowMap G V b) := by
  sorry

/-- The canonical functor from the action groupoid to scheme torsors, including
its inverse-right-translation convention on arrows. Its base projection is unchanged.
Source: Stacks 04WM (blueprint: def-sfb-scheme-action-torsor-groupoids). -/
def trivialTorsorFunctor : BasedFunctor (actionGroupoid G V) (torsorGroupoid G V) where
  obj := trivialObject G V
  map a :=
    ⟨a.base, trivialArrowMap G V a, (trivial_arrow_laws G V).1 a |>.1,
      (trivial_arrow_laws G V).1 a |>.2.1, (trivial_arrow_laws G V).1 a |>.2.2⟩
  map_id X := TorsorHom.ext rfl ((trivial_arrow_laws G V).2.1 X)
  map_comp a b := TorsorHom.ext rfl ((trivial_arrow_laws G V).2.2 a b)
  w := rfl

end AlgebraicGeometry.SchemeAction
