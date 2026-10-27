module

public import Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory
public import Mathlib.CategoryTheory.Core
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.TensorProduct.Basic

/-! # Marked flat algebra deformation groupoids

Source: Stacks Project, examples-defos.tex, Example 0DY1 (example-rings),
and Tag 0DYV (lemma-completion)
(blueprint: def-sfb-marked-flat-algebra-deformations).

The special-fibre marking is represented by its surjection with prescribed kernel.
The core of the category of factorizations retains exactly marked algebra isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct

namespace Algebra.FlatDeformation

open AlgebraicGeometry.ArtinDeformation

variable {k : Type u} [Field k] (B : Type u) [CommRing B] [Algebra k B]

/-- The residue-marked map from the test algebra to the special fibre.
Source: Stacks, example-rings and Tag 0DYV
(blueprint: def-sfb-marked-flat-algebra-deformations). -/
def specialArrow (A : TestCategory k k) : Over (CommAlgCat.of k B) :=
  Over.mk (CommAlgCat.ofHom ((Algebra.ofId k B).comp (residue A)))

/-- Flat factorizations whose reduction map is the specified special-fibre quotient.
Source: Stacks, example-rings and Tag 0DYV
(blueprint: def-sfb-marked-flat-algebra-deformations). -/
def IsMarkedFlat (A : TestCategory k k) (X : Under (specialArrow B A)) : Prop :=
  X.hom.left.hom.toRingHom.Flat ∧ Function.Surjective X.right.hom.hom ∧
    RingHom.ker X.right.hom.hom.toRingHom =
      (IsLocalRing.maximalIdeal (ring A)).map X.hom.left.hom.toRingHom

/-- Marked flat deformations over A, with precisely the marked isomorphisms as arrows.
Source: Stacks, example-rings and Tag 0DYV
(blueprint: def-sfb-marked-flat-algebra-deformations). -/
abbrev Groupoid (A : TestCategory k k) :=
  Core (ObjectProperty.FullSubcategory (IsMarkedFlat B A))

variable {B} {A : TestCategory k k}

/-- The actual algebra of a marked deformation.
Source: Stacks, Tag 0DYV (blueprint: def-sfb-marked-flat-algebra-deformations). -/
abbrev algebra (Q : Groupoid B A) : CommAlgCat.{u} k := Q.of.obj.right.left

/-- The coefficient-algebra map of a deformation.
Source: Stacks, Tag 0DYV (blueprint: def-sfb-marked-flat-algebra-deformations). -/
abbrev scalar (Q : Groupoid B A) : ring A →ₐ[k] algebra Q := Q.of.obj.hom.left.hom

/-- The specified special-fibre quotient, retaining the marking rather than its class.
Source: Stacks, Tag 0DYV (blueprint: def-sfb-marked-flat-algebra-deformations). -/
abbrev marking (Q : Groupoid B A) : algebra Q →ₐ[k] B := Q.of.obj.right.hom.hom

/-- The underlying algebra map of a marked isomorphism.
Source: Stacks, Tag 0DYV (blueprint: def-sfb-marked-flat-algebra-deformations). -/
abbrev hom {Q Q' : Groupoid B A} (f : Q ⟶ Q') : algebra Q →ₐ[k] algebra Q' :=
  f.iso.hom.hom.right.left.hom

/-- The inverse image of the ideal of the special fibre.
Source: Stacks, Tag 0DYV (blueprint: def-sfb-marked-flat-algebra-deformations). -/
def ideal (J : Ideal B) (Q : Groupoid B A) : Ideal (algebra Q) :=
  J.comap (marking Q).toRingHom

/-- Exact finite-quotient characterization of the map induced on completions by f.
This characterization determines g uniquely and uses every level, including level zero.
Source: Stacks, Tag 0DYV, the quotientwise completion construction
(blueprint: def-sfb-marked-flat-algebra-deformations). -/
def IsCompletionMap {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (g : AdicCompletion I R →+* AdicCompletion J S) : Prop :=
  ∀ (n : ℕ) (x : AdicCompletion I R) (r : R),
    AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) r →
      AdicCompletion.evalₐ J n (g x) = Ideal.Quotient.mk (J ^ n) (f r)

/-- A marked map over a change of Artinian base. Its kernel marking is kept literally.
Source: Stacks, example-rings and Tag 0DYV
(blueprint: def-sfb-marked-flat-algebra-deformations). -/
def IsMarkedMap {A' : TestCategory k k} (f : A ⟶ A')
    (Q : Groupoid B A) (Q' : Groupoid B A') (i : algebra Q →ₐ[k] algebra Q') : Prop :=
  i.comp (scalar Q) = (scalar Q').comp (map f) ∧
    (marking Q').comp i = marking Q

/-- The actual tensor-product base change, with its comparison fixed on simple tensors.
The scalar structures on the tensor factors are the given coefficient maps.
Source: Stacks, Tag 0DYV and algebra.tex, Tag 00MA
(blueprint: def-sfb-marked-flat-algebra-deformations). -/
def IsBaseChange {A' : TestCategory k k} (f : A ⟶ A')
    (Q : Groupoid B A) (Q' : Groupoid B A') (i : algebra Q →ₐ[k] algebra Q') : Prop :=
  letI : Algebra (ring A) (algebra Q) := (scalar Q).toRingHom.toAlgebra
  letI : Algebra (ring A) (ring A') := (map f).toRingHom.toAlgebra
  IsMarkedMap f Q Q' i ∧
    ∃ e : (algebra Q ⊗[ring A] ring A') ≃+* algebra Q',
      ∀ (q : algebra Q) (a : ring A'), e (q ⊗ₜ[ring A] a) = i q * scalar Q' a

end Algebra.FlatDeformation
