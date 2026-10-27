module

public import Sheaf.CategoryTheory.SheafDgFreeClosedGenerators
public import Sheaf.CategoryTheory.RingedToposMorphism

/-! # Geometric scalar extension of right sheaf dg modules

Source: Stacks Project, sdga.tex, 0FSF--0FSG and definition-pullback
(blueprint: def-sfb-sheaf-dg-geometric-scalar-extension).

The inverse image need not come from a functor between sites. Maps from its
homogeneous pieces are therefore maps of sheaves, with operations transported
on generalized elements. The tensor product is specified by its balanced universal
property: a map out is a semilinear dg map out of the pulled-back source. This fixes
both the object up to its unique unit-preserving isomorphism and the canonical map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uC vC uD vD w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.SheafDg

set_option quotPrecheck false in
set_option hygiene false in
/-- The underlying sheaf of sets of a coefficient module (forget the module structure),
written inline from Mathlib's `SheafOfModules.toSheaf`.
Source: Stacks, Modules on Sites, 03CY
(blueprint: def-sfb-sheaf-dg-geometric-scalar-extension). -/
local notation "𝔘[" R "]" =>
  SheafOfModules.toSheaf (rings R) ⋙ sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{w})

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {S : Sheaf J CommRingCat.{w}} {T : Sheaf K CommRingCat.{w}}

/-- Degreewise maps out of inverse-image sheaves, without any linearity assumption.
Source: Stacks, sdga.tex, definition-pullback
(blueprint: def-sfb-sheaf-dg-geometric-scalar-extension). -/
abbrev PulledFamily (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (P : Complex S) (M : Complex T) :=
  ∀ n : ℤ, L.obj ((𝔘[S]).obj (P.X n)) ⟶
    (𝔘[T]).obj (M.X n)

/-- Additivity after inverse image is tested on all generalized triples x,y,x+y.
This is a diagram identity, not a condition only on global sections.
Source: Stacks, Modules on Sites, 03D2
(blueprint: def-sfb-sheaf-dg-geometric-scalar-extension). -/
def IsPulledAdditive (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (P : ringedSiteModules.{w} (rings S)) (M : ringedSiteModules.{w} (rings T))
    (a : L.obj ((𝔘[S]).obj P) ⟶
      (𝔘[T]).obj M) : Prop :=
  ∀ (Z : Sheaf J (Type w)) (x y z : Z ⟶ (𝔘[S]).obj P),
    (∀ (U : Cᵒᵖ) (t : Z.obj.obj U),
      z.hom.app U t = @Add.add (P.val.obj U) inferInstance
        (x.hom.app U t) (y.hom.app U t)) →
    ∀ (V : Dᵒᵖ) (t : (L.obj Z).obj.obj V),
      ((L.map z) ≫ a).hom.app V t = @Add.add (M.val.obj V) inferInstance
        (((L.map x) ≫ a).hom.app V t) (((L.map y) ≫ a).hom.app V t)

/-- Additive degreewise maps commuting with all differentials.
Source: Stacks, sdga.tex, definition-pullback
(blueprint: def-sfb-sheaf-dg-geometric-scalar-extension). -/
def IsPulledComplexMap (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (P : Complex S) (M : Complex T) (a : PulledFamily L P M) : Prop :=
  (∀ n : ℤ, IsPulledAdditive L (P.X n) (M.X n) (a n)) ∧
    ∀ p q : ℤ, L.map ((𝔘[S]).map (P.d p q)) ≫ a q =
      a p ≫ (𝔘[T]).map (M.d p q)

/-- A map f^{-1}A to B of associative unital dg algebras. Multiplication and
unit are specified on generalized sections; no graded commutativity is required.
Source: Stacks, sdga.tex, final paragraph of 0FSG
(blueprint: def-sfb-sheaf-dg-geometric-scalar-extension). -/
structure PulledAlgebraMap (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (A : Algebra S) (B : Algebra T) where
  map : PulledFamily L A.X B.X
  chain : IsPulledComplexMap L A.X B.X map
  mul : ∀ (p q : ℤ) (Z : Sheaf J (Type w))
    (x : Z ⟶ (𝔘[S]).obj (A.X.X p))
    (y : Z ⟶ (𝔘[S]).obj (A.X.X q))
    (z : Z ⟶ (𝔘[S]).obj (A.X.X (p + q))),
    (∀ (U : Cᵒᵖ) (t : Z.obj.obj U), z.hom.app U t =
      actionSection A (regular A) p q U (x.hom.app U t) (y.hom.app U t)) →
    ∀ (V : Dᵒᵖ) (t : (L.obj Z).obj.obj V),
      ((L.map z) ≫ map (p + q)).hom.app V t =
        actionSection B (regular B) p q V
          (((L.map x) ≫ map p).hom.app V t) (((L.map y) ≫ map q).hom.app V t)
  one : ∀ (Z : Sheaf J (Type w))
    (x : Z ⟶ (𝔘[S]).obj (A.X.X 0)),
    (∀ (U : Cᵒᵖ) (t : Z.obj.obj U), x.hom.app U t = oneSection A U) →
    ∀ (V : Dᵒᵖ) (t : (L.obj Z).obj.obj V),
      ((L.map x) ≫ map 0).hom.app V t = oneSection B V

/-- A semilinear right dg map after geometric inverse image. The action relation
is the balanced relation a(pa)=a(p)phi(a), transported on generalized elements.
Source: Stacks, sdga.tex, tensor products and definition-pullback
(blueprint: def-sfb-sheaf-dg-geometric-scalar-extension). -/
def IsPulledModuleMap {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)}
    {A : Algebra S} {B : Algebra T} (φ : PulledAlgebraMap L A B)
    (P : RightModule A) (M : RightModule B)
    (a : PulledFamily L ((rightUnderlying A).obj P) ((rightUnderlying B).obj M)) : Prop :=
  IsPulledComplexMap L ((rightUnderlying A).obj P) ((rightUnderlying B).obj M) a ∧
    ∀ (p q : ℤ) (Z : Sheaf J (Type w))
      (x : Z ⟶ (𝔘[S]).obj (((rightUnderlying A).obj P).X p))
      (y : Z ⟶ (𝔘[S]).obj (A.X.X q))
      (z : Z ⟶ (𝔘[S]).obj
        (((rightUnderlying A).obj P).X (p + q))),
      (∀ (U : Cᵒᵖ) (t : Z.obj.obj U), z.hom.app U t =
        rightActionSection A P p q U (x.hom.app U t) (y.hom.app U t)) →
      ∀ (V : Dᵒᵖ) (t : (L.obj Z).obj.obj V),
        ((L.map z) ≫ a (p + q)).hom.app V t = rightActionSection B M p q V
          (((L.map x) ≫ a p).hom.app V t) (((L.map y) ≫ φ.map q).hom.app V t)

/-- Postcomposition of a pulled-back family by an actual target dg module map.
Source: Stacks, sdga.tex, definition-pullback
(blueprint: def-sfb-sheaf-dg-geometric-scalar-extension). -/
def pulledPost {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)}
    {A : Algebra S} {B : Algebra T} {P : RightModule A} {M N : RightModule B}
    (a : PulledFamily L ((rightUnderlying A).obj P) ((rightUnderlying B).obj M))
    (g : M ⟶ N) :
    PulledFamily L ((rightUnderlying A).obj P) ((rightUnderlying B).obj N) :=
  fun n ↦ a n ≫ (𝔘[T]).map (((rightUnderlying B).map g).f n)

/-- Precomposition of a pulled-back family by the inverse image of a source map.
Source: Stacks, sdga.tex, definition-pullback
(blueprint: def-sfb-sheaf-dg-geometric-scalar-extension). -/
def pulledPre {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)}
    {A : Algebra S} {B : Algebra T} {P Q : RightModule A} {M : RightModule B}
    (g : P ⟶ Q)
    (a : PulledFamily L ((rightUnderlying A).obj Q) ((rightUnderlying B).obj M)) :
    PulledFamily L ((rightUnderlying A).obj P) ((rightUnderlying B).obj M) :=
  fun n ↦ L.map ((𝔘[S]).map
    (((rightUnderlying A).map g).f n)) ≫ a n

/-- The universal property of f^{-1}P tensor_{f^{-1}A} B, including its unit
p mapped to p tensor 1. It tests all semilinear dg maps and their unique
B-linear factorizations. Thus this is the balanced tensor, with its actual
universal map, rather than a freely supplied comparison between objects.
Source: Stacks, sdga.tex, tensor products and definition-pullback
(blueprint: def-sfb-sheaf-dg-geometric-scalar-extension). -/
def IsGeometricScalarExtension {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)}
    {A : Algebra S} {B : Algebra T} (φ : PulledAlgebraMap L A B)
    (P : RightModule A) (M : RightModule B)
    (a : PulledFamily L ((rightUnderlying A).obj P) ((rightUnderlying B).obj M)) : Prop :=
  IsPulledModuleMap φ P M a ∧
    (∀ (N : RightModule B) (g : M ⟶ N), IsPulledModuleMap φ P N (pulledPost a g)) ∧
    ∀ (N : RightModule B)
      (b : PulledFamily L ((rightUnderlying A).obj P) ((rightUnderlying B).obj N)),
      IsPulledModuleMap φ P N b → ∃! g : M ⟶ N, pulledPost a g = b

/-- Apply inverse image to each fibre of a graded set sheaf. Finite-limit
preservation and preservation of coproducts identify these with the fibres of
f^{-1}S to the constant integer sheaf on the target.
Source: Stacks, sdga.tex, 0FSF--0FSG
(blueprint: def-sfb-sheaf-dg-geometric-scalar-extension). -/
def pulledGradedSets (L : Sheaf J (Type w) ⥤ Sheaf K (Type w)) :
    GradedObject ℤ (Sheaf J (Type w)) ⥤ GradedObject ℤ (Sheaf K (Type w)) where
  obj E n := L.obj (E n)
  map e n := L.map (e n)
  map_id _ := by funext n; exact L.map_id _
  map_comp _ _ := by funext n; exact L.map_comp _ _

/-- The generator normalization for the geometric free-module comparison.
Source: Stacks, sdga.tex, final display of 0FSG
(blueprint: def-sfb-sheaf-dg-geometric-scalar-extension). -/
def IsFreeBaseChangeUnit {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)}
    {A : Algebra S} {B : Algebra T} (E : GradedObject ℤ (Sheaf J (Type w)))
    (a : PulledFamily L ((rightUnderlying A).obj (freeRight A E))
      ((rightUnderlying B).obj (freeRight B ((pulledGradedSets L).obj E)))) : Prop :=
  ∀ n : ℤ, L.map (freeGenerator A E n) ≫ a n =
    freeGenerator B ((pulledGradedSets L).obj E) n

end CategoryTheory.SheafDg
