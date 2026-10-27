module

public import Mathlib.RingTheory.Extension.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! # Square-zero algebra extension classes

Source: Stacks Project, examples-defos.tex, notation preceding Tag 0DZ4.
(blueprint: def-sfb-square-zero-algebra-classes)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

namespace Algebra.SquareZeroClasses

variable (R B N : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup N] [Module B N]

/-- An extension with its specified additive kernel and quotient action.
Source: Stacks notation before 0DZ4 (blueprint: def-sfb-square-zero-algebra-classes). -/
structure Extension where
  extension : Algebra.Extension.{u} R B
  i : N →+ extension.Ring
  injective : Function.Injective i
  exact : ∀ x : extension.Ring, algebraMap extension.Ring B x = 0 ↔ ∃ n, i n = x
  square_zero : ∀ n m : N, i n * i m = 0
  action : ∀ (x : extension.Ring) (n : N),
    x * i n = i ((algebraMap extension.Ring B x) • n)

variable {R B N}

/-- The specified quotient algebra map.
Source: Stacks notation before 0DZ4 (blueprint: def-sfb-square-zero-algebra-classes). -/
def Extension.p (E : Extension R B N) : E.extension.Ring →ₐ[R] B :=
  IsScalarTower.toAlgHom R E.extension.Ring B

/-- Isomorphisms fix both the kernel marking and quotient.
Source: Stacks notation before 0DZ4 (blueprint: def-sfb-square-zero-algebra-classes). -/
def Isomorphic (E F : Extension R B N) : Prop :=
  ∃ e : E.extension.Ring ≃ₐ[R] F.extension.Ring,
    (∀ x, F.p (e x) = E.p x) ∧ ∀ n, e (E.i n) = F.i n

/-- The quotient by extension isomorphism. `Quot` takes the equivalence closure;
isomorphism already is an equivalence relation, so these are precisely isomorphism classes.
Source: Stacks notation before 0DZ4 (blueprint: def-sfb-square-zero-algebra-classes). -/
def Classes (R B N : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup N] [Module B N] :=
  Quot (Isomorphic (R := R) (B := B) (N := N))

/-- The class of an actual extension.
Source: Stacks notation before 0DZ4 (blueprint: def-sfb-square-zero-algebra-classes). -/
def classOf (E : Extension R B N) : Classes R B N := Quot.mk _ E

/-- The algebra fibre product of two extensions over their specified quotient.
Source: Stacks notation before 0DZ4 (blueprint: def-sfb-square-zero-algebra-classes). -/
def fiber (E F : Extension R B N) :
    Subalgebra R (E.extension.Ring × F.extension.Ring) :=
  AlgHom.equalizer (E.p.comp (AlgHom.fst R E.extension.Ring F.extension.Ring))
    (F.p.comp (AlgHom.snd R E.extension.Ring F.extension.Ring))

/-- The graph of Baer addition: push out the fibre product along kernel addition.
The displayed algebra map is automatically the coefficient pushout, since both rows
are extensions and its kernel map is addition.
Source: Stacks notation before 0DZ4 (blueprint: def-sfb-square-zero-algebra-classes). -/
def IsBaerSum (E F G : Extension R B N) : Prop :=
  ∃ b : fiber E F →ₐ[R] G.extension.Ring,
    (∀ x, G.p (b x) = E.p x.val.1) ∧
    ∀ (n m : N) (x : fiber E F), x.val = (E.i n, F.i m) → b x = G.i (n + m)

/-- The graph of scalar pushout along multiplication by an element of the base ring.
Source: Stacks notation before 0DZ4 (blueprint: def-sfb-square-zero-algebra-classes). -/
def IsScalarPushout (a : R) (E F : Extension R B N) : Prop :=
  ∃ f : E.extension.Ring →ₐ[R] F.extension.Ring,
    (∀ x, F.p (f x) = E.p x) ∧
    ∀ n, f (E.i n) = F.i ((algebraMap R B a) • n)

/-- An additive module structure is the natural one precisely when its operations
are Baer sum and scalar pushout on representatives.
Source: Stacks notation before 0DZ4 (blueprint: def-sfb-square-zero-algebra-classes). -/
def IsNaturalModule [AddCommGroup (Classes R B N)] [Module R (Classes R B N)] : Prop :=
  (∀ E F G : Extension R B N, classOf E + classOf F = classOf G ↔ IsBaerSum E F G) ∧
  ∀ (a : R) (E F : Extension R B N), a • classOf E = classOf F ↔ IsScalarPushout a E F

end Algebra.SquareZeroClasses
