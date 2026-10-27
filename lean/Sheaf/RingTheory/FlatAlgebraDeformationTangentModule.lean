module

public import Sheaf.RingTheory.MarkedFlatAlgebraDeformations
public import Sheaf.AlgebraicGeometry.MarkedStackDeformations

/-! # Canonical operations on the tangent set of flat algebra deformations

Source: Stacks Project, examples-defos.tex, Tag 0DY3 (lemma-rings-TI), and
formal-defos.tex, tangent-space operations
(blueprint: def-sfb-flat-algebra-deformation-tangent-module).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry.ArtinDeformation

namespace Algebra.FlatDeformation

variable {k : Type u} [Field k] (B : Type u) [CommRing B] [Algebra k B]

/-- The isomorphism classes of the actual marked flat dual-number deformations.
Source: Stacks, Tag 0DY3 (blueprint: def-sfb-flat-algebra-deformation-tangent-module). -/
abbrev Tangent :=
  Quotient (isIsomorphicSetoid (Groupoid B (squareZeroTest (R := k) (k := k) k)))

/-- The class of a marked dual-number deformation.
Source: Stacks, Tag 0DY3 (blueprint: def-sfb-flat-algebra-deformation-tangent-module). -/
def tangentClass (Q : Groupoid B (squareZeroTest (R := k) (k := k) k)) : Tangent (k := k) B :=
  Quotient.mk _ Q

/-- A class is induced by the actual square-zero base change along a linear map.
Source: Stacks, Tag 0DY3 (blueprint: def-sfb-flat-algebra-deformation-tangent-module). -/
def InducesTangent {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : V →ₗ[k] k) (Q : Groupoid B (squareZeroTest (R := k) (k := k) V))
    (x : Tangent (k := k) B) : Prop :=
  ∃ (D : Groupoid B (squareZeroTest (R := k) (k := k) k))
    (i : algebra Q →ₐ[k] algebra D),
    IsBaseChange (AlgebraicGeometry.StackDeformation.squareZeroTransport f) Q D i ∧
      tangentClass (k := k) B D = x

/-- The deformation operations, fixed by square-zero scalar maps and by gluing over
k followed by addition of the two square-zero directions. The biconditionals prevent
an unrelated vector-space structure from satisfying the predicate.
Source: Stacks, Tag 0DY3 and formal-defos.tex, tangent-space operations
(blueprint: def-sfb-flat-algebra-deformation-tangent-module). -/
def IsCanonicalTangentModule [AddCommGroup (Tangent (k := k) B)]
    [Module k (Tangent (k := k) B)] : Prop :=
  (∀ (Q : Groupoid B (squareZeroTest (R := k) (k := k) k)) (c : k) (y : Tangent (k := k) B),
    c • tangentClass (k := k) B Q = y ↔
      InducesTangent (k := k) B (c • (LinearMap.id : k →ₗ[k] k)) Q y) ∧
  (∀ x y z : Tangent (k := k) B,
    x + y = z ↔
      ∃ Q : Groupoid B (squareZeroTest (R := k) (k := k) (k × k)),
        InducesTangent (k := k) B (LinearMap.fst k k k) Q x ∧
        InducesTangent (k := k) B (LinearMap.snd k k k) Q y ∧
        InducesTangent (k := k) B (LinearMap.fst k k k + LinearMap.snd k k k) Q z)

end Algebra.FlatDeformation
