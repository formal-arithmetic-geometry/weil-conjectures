/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q131
-/
module

public import Sheaf.AlgebraicGeometry.ConormalGradedAlgebra
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalFunctorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage
import WeilConjectures.AlgebraicGeometry.ModulePullbackIdealQuotient
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Quotient
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction

/-!
# Flat base change of the conormal graded algebra

Source: Stacks Project, Divisors, Tags 0634 and 0635, closed immersion case
(blueprint: lem-pur-conormal-algebra-flat-base-change).

## Main definitions

* `adjointPiece`: the adjoint of a homogeneous comparison, on the ambient schemes.
* `IsBaseChangeMap`: the graded algebra comparison specified by its affine tensor formula.

## Main statements

* `existsUnique_baseChangeMap`: existence, uniqueness, surjectivity, and flat isomorphism.

An algebra map out of a tensor pullback is encoded by its underlying module map and
its adjoint ring-sheaf map over the structure-sheaf map. This is the usual universal
property of algebra scalar extension; the homogeneous maps specify its grading.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

noncomputable section

namespace AlgebraicGeometry.ConormalGradedAlgebra

variable {X Z X' Z' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
  [IsClosedImmersion i] [IsClosedImmersion i']
  (g : X ⟶ X') (f : Z ⟶ Z') (h : i ≫ g = f ≫ i')

/-- The adjoint homogeneous comparison, with the commutative square implementing the
identification of the two pushforwards. The adjunction units send a representative to
its pure tensor with one. Source: Stacks Project, Divisors, Tag 0634
(blueprint: lem-pur-conormal-algebra-flat-base-change). -/
def adjointPiece (n : ℕ) (d : (tensorPullback f).obj (piece i' n) ⟶ piece i n) :
    power i' n ⟶ (pushforward (i ≫ g)).obj (piece i n) :=
  (Classical.choose (exists_tensorPullbackAdjunction i')).unit.app (power i' n) ≫
    (pushforward i').map
      ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app (piece i' n) ≫
        (pushforward f).map d) ≫
    (pushforwardComp f i').hom.app (piece i n) ≫
    (pushforwardCongr h.symm).hom.app (piece i n)

/-- Specification of the canonical conormal-algebra comparison. A ring-sheaf adjoint
makes the module map an algebra map; homogeneous maps make it graded. The affine formula
uses ideal-power representatives and arbitrary scalar factors, hence says precisely
`[a] tensor r` maps to `[g-sharp(a) * r]` under the recorded conormal identifications.
The last two equations normalize degrees zero and one using the existing canonical maps.
Source: Stacks Project, Divisors, Tags 0634 and 0635
(blueprint: lem-pur-conormal-algebra-flat-base-change). -/
def IsBaseChangeMap (A : Presentation i) (A' : Presentation i')
    (c : (tensorPullback f).obj A'.algebra.toModule ⟶ A.algebra.toModule) : Prop :=
  ∃ (ρ : A'.algebra.right ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj A.algebra.right)
    (d : ∀ n : ℕ, (tensorPullback f).obj (piece i' n) ⟶ piece i n),
    (A'.algebra.hom ≫ ρ =
      (⟨f.c⟩ : Z'.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Z.sheaf) ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).map A.algebra.hom) ∧
    (∀ (V : Z'.Opens) (a : A'.algebra.right.obj.obj (op V)),
      c.val.app (op (f ⁻¹ᵁ V))
        (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app
          A'.algebra.toModule).val.app (op V) a) = ρ.hom.app (op V) a) ∧
    (∀ n : ℕ, (tensorPullback f).map (A'.inclusion n) ≫ c = d n ≫ A.inclusion n) ∧
    (∀ (U : X.affineOpens) (U' : X'.affineOpens) (H : U.1 ≤ g ⁻¹ᵁ U'.1)
      (n : ℕ) (a : (power i' n).val.obj (op U'.1)) (r : Γ(X, U.1)),
      ∃ b : (power i n).val.obj (op U.1),
        (powerInclusion i n).val.app (op U.1) b =
          g.appLE U'.1 U.1 H ((powerInclusion i' n).val.app (op U'.1) a) * r ∧
        i.app U.1 r •
          (piece i n).val.map (homOfLE (i.preimage_mono H)).op
            ((adjointPiece i i' g f h n (d n)).val.app (op U'.1) a) =
          representative i n U.1 b) ∧
    (d 0 ≫ tensorPullbackObjUnitToUnit i =
      (tensorPullback f).map (tensorPullbackObjUnitToUnit i') ≫
        tensorPullbackObjUnitToUnit f) ∧
    d 1 = Classical.choose ((Classical.choose_spec
      (closedImmersion_conormal_functorial i i' g f h).2).2)

/-- The canonical comparison of conormal graded algebras exists uniquely. Its underlying
module map is an epimorphism, and it is an isomorphism when the ambient base change is flat.
Here `Epi` is sheaf surjectivity, equivalently surjectivity on stalks; it makes no assertion
of surjectivity on sections of arbitrary non-affine opens.
Source: Stacks Project, Divisors, Tags 0634 and 0635
(blueprint: lem-pur-conormal-algebra-flat-base-change).

Proof:
1. Compatible affine pairs cover X, and their inverse images cover Z. The Cartesian
   ideal-image theorem and modulePullbackIdealQuotient identify I with I'R on every pair.
2. The conormal presentation identifies the homogeneous sections with J^n/J^(n+1).
   Pullback preserves quasi-coherence and its affine-sections theorem gives tensor
   products. Since J annihilates these quotients, tensoring over A/J with B/JB is
   canonically the same as tensoring over A with B, fixing pure tensors.
3. The equality (JB)^n = J^n B, including n=0, shows that [a] tensor b maps to
   [phi(a)b]. Changing a by J^(n+1) changes the result by (JB)^(n+1); balancing
   follows from phi(ra)b = phi(a)phi(r)b. Thus each homogeneous map is well defined.
4. Use the affine tilde adjunction to obtain local sheaf maps. On principal refinements
   both restrictions send [a]/s^r tensor b to [phi(a)b]/phi(s)^r. Refine arbitrary
   overlaps by such opens, then apply existsUnique_hom_of_cover degreewise. This also
   proves the formula on every compatible pair, without affine intersections.
5. On pure tensors both multiplication composites send ([a] tensor b)([a'] tensor b')
   to [phi(aa')bb']; the unit goes to [1]. The graded coproduct property and preservation
   of coproducts by the tensor-pullback left adjoint give c and its ring adjoint rho.
   The same local generators prove uniqueness of c from its affine formula.
6. The degree-zero formula is the canonical structure-sheaf identification. Degree one
   agrees with closedImmersion_conormal_functorial on every ideal representative;
   uniqueness identifies the two maps.
7. Every class in (JB)^n/(JB)^(n+1) is a finite sum [phi(a_l)b_l], so has a preimage.
   Locally a section of the graded sheaf is a finite sum of homogeneous sections.
   Lift these on a compatible affine refinement: c is locally surjective, hence epi.
8. Under Flat g each affine B is flat over A. Tensor the injection
   J^n/J^(n+1) into A/J^(n+1) with B. The tensor-quotient comparison identifies its
   target with B/(JB)^(n+1), and the resulting injection factors through c_n followed
   by (JB)^n/(JB)^(n+1) into B/(JB)^(n+1). Thus c_n is injective in every degree.
9. The bijective affine maps give local inverses by the affine tilde equivalence.
   Their inverses agree on overlaps and glue. Extend them to the graded coproduct;
   multiplication and unit follow by applying the injective c. Thus c is an algebra
   isomorphism, detected by its underlying module map. -/
theorem existsUnique_baseChangeMap (hc : IsLimit (PullbackCone.mk i f h))
    (A : Presentation i) (A' : Presentation i') :
    (∀ (U : X.affineOpens) (U' : X'.affineOpens) (H : U.1 ≤ g ⁻¹ᵁ U'.1),
      i.ker.ideal U = Ideal.map (g.appLE U'.1 U.1 H).hom (i'.ker.ideal U')) ∧
    (∃! c : (tensorPullback f).obj A'.algebra.toModule ⟶ A.algebra.toModule,
      IsBaseChangeMap i i' g f h A A' c) ∧
    ∀ c : (tensorPullback f).obj A'.algebra.toModule ⟶ A.algebra.toModule,
      IsBaseChangeMap i i' g f h A A' c → Epi c ∧ (Flat g → IsIso c) := by
  sorry

end AlgebraicGeometry.ConormalGradedAlgebra
