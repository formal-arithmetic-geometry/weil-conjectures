module

public import Sheaf.Algebra.Homology.OpenTotalTensorCoefficientNormalization

/-! # Strict coefficient interchange for open total tensor

Source: Stacks Project, Modules on Sites, Tag 0E8I, and Cohomology on Sites,
Tag 0GL1; agent coefficient refinement
(blueprint: def-sf-open-total-tensor-coefficient-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


attribute [local irreducible] SheafOfModules.monoidalCategory

universe c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules.LocalizedStrictTensor
namespace SheafOfModules.OpenTotalTensorCoefficient

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r}) (V : C)
  [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- The interchange equation, its generator value and its strict naturality.
The transition formulas specify the canonical transitions rather than arbitrary
maps: on the source they replace its scalar, on the target both scalar entries.
Source: Stacks 0E8I and 0GL1, agent coefficient refinement
(blueprint: def-sf-open-total-tensor-coefficient-coherence). -/
structure StrictCoherence (e : Comparisons.{c, v, r} R V) where
  equation : ∀ (A : Under R)
    (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R),
    (e.left R V A Q F).hom = (e.right R V A Q F).hom
  generator : ∀ (A : Under R)
    (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R)
    (p q n : ℤ) (h : p + q = n) (W : C) (f : W ⟶ V)
    (x : (Q.X p).val.obj (op (Over.mk f))) (y : (F.X q).val.obj (op W))
    (a : A.right.obj.obj (op W)),
    (((e.left R V A Q F).hom.f n).val.app (op W))
        (sourceSection.{c, v, r} R V A Q F p q n h W f x y a) =
      targetSection.{c, v, r} R V A Q F p q n h W f x y a 1
  generator_inverse : ∀ (A : Under R)
    (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R)
    (p q n : ℤ) (h : p + q = n) (W : C) (f : W ⟶ V)
    (x : (Q.X p).val.obj (op (Over.mk f))) (y : (F.X q).val.obj (op W))
    (a b : A.right.obj.obj (op W)),
    (((e.left R V A Q F).inv.f n).val.app (op W))
        (targetSection.{c, v, r} R V A Q F p q n h W f x y a b) =
      sourceSection.{c, v, r} R V A Q F p q n h W f x y (a * b)
  sourceFamily : ∀ (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R),
    StrictFamily.{c, v, r} R (fun A ↦ source.{c, v, r} R V A Q F)
  targetFamily : ∀ (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R),
    StrictFamily.{c, v, r} R (fun A ↦ target.{c, v, r} R V A Q F)
  source_transition : ∀ {A B : Under R} (a : A ⟶ B)
    (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R)
    (p q n : ℤ) (h : p + q = n) (W : C) (f : W ⟶ V)
    (x : (Q.X p).val.obj (op (Over.mk f))) (y : (F.X q).val.obj (op W))
    (s : A.right.obj.obj (op W)),
    (((sourceFamily Q F).map a).f n).val.app (op W)
        (sourceSection.{c, v, r} R V A Q F p q n h W f x y s) =
      sourceSection.{c, v, r} R V B Q F p q n h W f x y (a.right.hom.app (op W) s)
  target_transition : ∀ {A B : Under R} (a : A ⟶ B)
    (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R)
    (p q n : ℤ) (h : p + q = n) (W : C) (f : W ⟶ V)
    (x : (Q.X p).val.obj (op (Over.mk f))) (y : (F.X q).val.obj (op W))
    (s t : A.right.obj.obj (op W)),
    (((targetFamily Q F).map a).f n).val.app (op W)
        (targetSection.{c, v, r} R V A Q F p q n h W f x y s t) =
      targetSection.{c, v, r} R V B Q F p q n h W f x y
        (a.right.hom.app (op W) s) (a.right.hom.app (op W) t)
  left_strict : ∀ (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R),
    IsStrict.{c, v, r} R (sourceFamily Q F) (targetFamily Q F) (fun A ↦ e.left R V A Q F)
  right_strict : ∀ (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R),
    IsStrict.{c, v, r} R (sourceFamily Q F) (targetFamily Q F) (fun A ↦ e.right R V A Q F)
  tower_equation : ∀ (S : AlgebraTowers.{c, v, r} R)
    (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R),
    Functor.whiskerLeft S
        (strictIso.{c, v, r} R (sourceFamily Q F) (targetFamily Q F)
          (fun A ↦ e.left R V A Q F) (left_strict Q F)).hom =
      Functor.whiskerLeft S
        (strictIso.{c, v, r} R (sourceFamily Q F) (targetFamily Q F)
          (fun A ↦ e.right R V A Q F) (right_strict Q F)).hom
  localized_equation : ∀ (S : AlgebraTowers.{c, v, r} R)
    (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R),
    (localizeTower.{c, v, r} R).map ((transpose.{c, v, r} R).map (Functor.whiskerLeft S
        (strictIso.{c, v, r} R (sourceFamily Q F) (targetFamily Q F)
          (fun A ↦ e.left R V A Q F) (left_strict Q F)).hom)) =
      (localizeTower.{c, v, r} R).map ((transpose.{c, v, r} R).map (Functor.whiskerLeft S
        (strictIso.{c, v, r} R (sourceFamily Q F) (targetFamily Q F)
          (fun A ↦ e.right R V A Q F) (right_strict Q F)).hom))
  natural : ∀ (A : Under R)
    (Q Q' : Complex.{max c v, v, r} (R.over V)) (F F' : Complex.{c, v, r} R)
    (u : Q ⟶ Q') (v : F ⟶ F'),
    sourceMap.{c, v, r} R V A u v ≫ (e.left R V A Q' F').hom =
      (e.left R V A Q F).hom ≫ targetMap.{c, v, r} R V A u v


end SheafOfModules.OpenTotalTensorCoefficient
