module

public import Sheaf.Algebra.Homology.OpenTotalTensorCoefficientNormalization

/-! # Homogeneous coefficient comparison calculations

Source: Stacks Project, Modules on Sites, Tag 0E8I, and Cohomology on Sites,
Tag 0GL1; agent coefficient refinement
(blueprint: lem-sf-open-total-generator-calculus).
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

/-- The normalized composites have the indicated values and complex naturality.
Source: Stacks Modules on Sites, Tag 0E8I, lemma-j-shriek-and-tensor;
Tag 03EL; agent refinement of steps 2, 3, 5 and 7 of the interchange argument.
(blueprint: lem-sf-open-total-generator-calculus).

Proof: the balanced comparison sends the scalar a to the first tensor factor and
inserts 1 in the second. The coefficient-linear comparison moves a into the
extension summand, and gamma moves the tensor into that summand. Thus the left
composite has the displayed value. In the right composite gamma acts first,
linear moves the scalar into the extension summand, and the slice balanced map
again distributes a and 1; restrictionCoefficient identifies the second factor
by its normalized formula. For the inverse, reverse gamma and linear, then use
the inverse balanced comparison, which multiplies the two scalar entries.
All formulas preserve (p,q). Naturality in chain maps follows from naturality of
the module comparisons, their uniquely prescribed generator formulas and the
coproduct universal property in each total degree. No coefficient-transition or
interchange equation is assumed. -/
theorem normalized_composite_values (e : Comparisons.{c, v, r} R V)
    (hg : GammaNormalization.{c, v, r} R V e)
    (hl : LinearNormalization.{c, v, r} R V e)
    (hr : RestrictionNormalization.{c, v, r} R V e) :
    (∀ (A : Under R)
      (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R)
      (p q n : ℤ) (h : p + q = n) (W : C) (f : W ⟶ V)
      (x : (Q.X p).val.obj (op (Over.mk f))) (y : (F.X q).val.obj (op W))
      (a : A.right.obj.obj (op W)),
      (((e.left R V A Q F).hom.f n).val.app (op W))
          (sourceSection.{c, v, r} R V A Q F p q n h W f x y a) =
        targetSection.{c, v, r} R V A Q F p q n h W f x y a 1) ∧
    (∀ (A : Under R)
      (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R)
      (p q n : ℤ) (h : p + q = n) (W : C) (f : W ⟶ V)
      (x : (Q.X p).val.obj (op (Over.mk f))) (y : (F.X q).val.obj (op W))
      (a : A.right.obj.obj (op W)),
      (((e.right R V A Q F).hom.f n).val.app (op W))
          (sourceSection.{c, v, r} R V A Q F p q n h W f x y a) =
        targetSection.{c, v, r} R V A Q F p q n h W f x y a 1) ∧
    (∀ (A : Under R)
      (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R)
      (p q n : ℤ) (h : p + q = n) (W : C) (f : W ⟶ V)
      (x : (Q.X p).val.obj (op (Over.mk f))) (y : (F.X q).val.obj (op W))
      (a b : A.right.obj.obj (op W)),
      (((e.left R V A Q F).inv.f n).val.app (op W))
          (targetSection.{c, v, r} R V A Q F p q n h W f x y a b) =
        sourceSection.{c, v, r} R V A Q F p q n h W f x y (a * b)) ∧
    (∀ (A : Under R)
      (Q Q' : Complex.{max c v, v, r} (R.over V)) (F F' : Complex.{c, v, r} R)
      (u : Q ⟶ Q') (v : F ⟶ F'),
      sourceMap.{c, v, r} R V A u v ≫ (e.left R V A Q' F').hom =
        (e.left R V A Q F).hom ≫ targetMap.{c, v, r} R V A u v) := by sorry

end SheafOfModules.OpenTotalTensorCoefficient
