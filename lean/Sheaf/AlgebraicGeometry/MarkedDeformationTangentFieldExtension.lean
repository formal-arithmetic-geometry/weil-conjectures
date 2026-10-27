module

public import Sheaf.AlgebraicGeometry.MarkedStackDeformations
public import Sheaf.AlgebraicGeometry.ArtinFamilyLiftingData
public import Sheaf.AlgebraicGeometry.ArtinRSTangentTensor
public import Mathlib.Algebra.Module.TransferInstance
import Sheaf.AlgebraicGeometry.ArtinLocalTestAlgebra
import Sheaf.RingTheory.ArtinianFiniteTypeResidueCriterion
import Sheaf.AlgebraicGeometry.AffineClosedPinchingPushout
import Sheaf.RingTheory.ArtinianFiniteResidueRestriction
import Mathlib.RingTheory.HopkinsLevitzki

/-! # Marked deformation tangent spaces under finite field extension

Source: Stacks Project, artin.tex, Tags 07WU and 07WX; formal-defos.tex, Tag 07WB
(blueprint: lem-sfb-marked-deformation-tangent-field-extension).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w z

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.StackDeformation

variable {R k : Type u} [CommRing R] [IsNoetherianRing R] [Field k]
  [Algebra R k] [Algebra.FiniteType R k]

/-- A coherent presentation of the actual marked categories, with transport tied to
cartesian arrows respecting the marking. The last equation gives naturality on arrows.
Source: Stacks, Tag 07T4 (blueprint: lem-sfb-marked-deformation-tangent-field-extension). -/
def HasMarkedPredeformation
    (F : BasedCategory.{v, w} (Over (Spec (.of R))))
    (x : Functor.Fiber F.p (affine (CommAlgCat.of R k))) : Prop :=
  ∃ (D : ArtinDeformation.CofibredGroupoids.{u, v, max v w} R k)
    (E : ∀ A : ArtinDeformation.TestCategory R k, ArtinDeformation.fibre D A ≌ Marked F x A),
    ArtinDeformation.IsPredeformation D ∧ ArtinDeformation.IsRimSchlessinger D ∧
    ∀ (A B : ArtinDeformation.TestCategory R k) (f : A ⟶ B),
      ∃ b : ∀ Y : ArtinDeformation.fibre D A,
        ((E B).functor.obj ((ArtinDeformation.push D f).obj Y)).obj.right.val ⟶
          ((E A).functor.obj Y).obj.right.val,
        (∀ Y, F.p.IsHomLift (affineMap f.hom.left) (b Y) ∧
          ((E B).functor.obj ((ArtinDeformation.push D f).obj Y)).obj.hom ≫ b Y =
            ((E A).functor.obj Y).obj.hom) ∧
        ∀ (Y Z : ArtinDeformation.fibre D A) (g : Y ⟶ Z),
          (((E B).functor.map ((ArtinDeformation.push D f).map g)).hom.right).val ≫ b Z =
            b Y ≫ (((E A).functor.map g).hom.right).val

/-- The coordinatewise inclusion k[ε] → l[ε], with the prescribed R-actions.
Source: Stacks, Tag 07WB (blueprint: lem-sfb-marked-deformation-tangent-field-extension). -/
def dualNumberFieldMap (l : Type u) [Field l] [Algebra k l]
    [Algebra R l] [IsScalarTower R k l] :
    ArtinDeformation.squareZeroAlgebra (R := R) (k := k) k ⟶
      ArtinDeformation.squareZeroAlgebra (R := R) (k := l) l := by
  letI : Module kᵐᵒᵖ k := Module.compHom k (RingEquiv.toOpposite k).symm.toRingHom
  letI : IsCentralScalar k k := ⟨fun _ _ ↦ rfl⟩
  letI : Module lᵐᵒᵖ l := Module.compHom l (RingEquiv.toOpposite l).symm.toRingHom
  letI : IsCentralScalar l l := ⟨fun _ _ ↦ rfl⟩
  letI : Algebra R (TrivSqZeroExt k k) := Algebra.restrictScalars R k _
  letI : Algebra R (TrivSqZeroExt l l) := Algebra.restrictScalars R l _
  apply CommAlgCat.ofHom
  exact
    { toFun := fun z ↦ ⟨algebraMap k l z.fst, algebraMap k l z.snd⟩
      map_zero' := by ext <;> simp
      map_one' := by ext <;> simp
      map_add' := by intro a b; ext <;> simp
      map_mul' := by
        intro a b
        ext <;> simp
      commutes' := by
        intro r
        change (⟨algebraMap k l (algebraMap R k r), algebraMap k l 0⟩ :
          TrivSqZeroExt l l) = ⟨algebraMap R l r, 0⟩
        exact TrivSqZeroExt.ext (IsScalarTower.algebraMap_apply R k l r).symm (map_zero _) }

/-- The pullback relation across a field extension, including the original marking.
Source: Stacks, Tags 07WX and 07WB
(blueprint: lem-sfb-marked-deformation-tangent-field-extension). -/
def PullsBackField
    (F : BasedCategory.{v, w} (Over (Spec (.of R))))
    (x : Functor.Fiber F.p (affine (CommAlgCat.of R k)))
    (l : Type u) [Field l] [Algebra k l] [Algebra R l] [IsScalarTower R k l]
    [Algebra.FiniteType R l]
    (xl : Functor.Fiber F.p (affine (CommAlgCat.of R l))) (a : xl.val ⟶ x.val)
    (Y : Marked F x (ArtinDeformation.squareZeroTest (R := R) (k := k) k))
    (Z : Marked F xl (ArtinDeformation.squareZeroTest (R := R) (k := l) l)) : Prop :=
  ∃ b : Z.obj.right.val ⟶ Y.obj.right.val,
    F.p.IsHomLift (affineMap (dualNumberFieldMap (R := R) (k := k) l)) b ∧
      Z.obj.hom ≫ b = a ≫ Y.obj.hom

/-- The l-module on T ⊗_k l comes from the right factor, transported along tensor symmetry.
Source: Stacks, Tag 07WB (blueprint: lem-sfb-marked-deformation-tangent-field-extension). -/
abbrev rightTensorModule (l : Type u) [Field l] [Algebra k l]
    (T : Type z) [AddCommGroup T] [Module k T] : Module l (TensorProduct k T l) :=
  (TensorProduct.comm k T l).toAddEquiv.module l

/-- Marked deformations are predeformation categories with (RS). Their tangent
operations are canonical, and finite field extension gives the canonical tensor
isomorphism, with no finite-dimensionality assumption on the tangent space.
Source: Stacks, artin.tex, Tags 07WU, 07WX; formal-defos.tex, Tag 07WB
(blueprint: lem-sfb-marked-deformation-tangent-field-extension).

Proof:
1. Pullback of marked objects has the coherence of F. Over k, (x,id) exists and
there is a unique marking-preserving arrow between any two objects. This gives
IsPredeformation from def-sfb-artin-deformation-test-category.
2. For a surjective test arrow the literal ring fibre product is Artinian local
with residue k by lem-sfb-artin-local-test-algebra. All rings are finite type by
lem-sfb-artinian-finite-type-residue-criterion. The surjective kernel is nilpotent;
lem-sfb-affine-closed-pinching-pushout identifies Spec of the fibre product with
the scheme pushout. Apply the assumed (RS) equivalence.
3. Glue the underlying objects and their markings. Compatibility on the overlap
makes the two resulting markings equal. Full faithfulness glues exactly the
marking-preserving arrows. This proves (RS) for the marked categories. A finite
basis of l/k proves finite type over R, so the same applies to xl.
4. Apply lem-sfb-artin-rs-tangent-tensor. Its product and sum maps give addition,
the constant object gives zero, and ε ↦ cε gives scaling. Pullback of square-zero
algebras commutes with these operations, so the induced rho is k-linear.
5. For B with residue l put C=B ×_l k. By
lem-sfb-artinian-finite-residue-restriction it is an Artinian local k-test.
Use the finite-type criterion, nilpotence, and the affine pushout lemma again.
Taking marked fibres of the gluing equivalence gives F_x(C) ≃ F_xl(B), naturally
in B, by sending a marked triple to its B-component with the induced marking.
6. For a finite-dimensional l-space V, l[V] ×_l k = k[V_k]. The tensor theorem
identifies its marked classes with T_x ⊗_k V_k. Naturality under projections,
addition and multiplication by a in l proves l-linearity at V=l. The map k → l,
1 ↦ 1, identifies the pure tensor v ⊗ 1 with rho(v), hence v ⊗ a with a rho(v).
Only V_k, never T_x, needs finite dimension. Pure tensors generate, so the formula
uniquely specifies the isomorphism, including l=k and zero tangent spaces. -/
theorem markedDeformation_tangent_field_extension
    (F : BasedCategory.{v, w} (Over (Spec (.of R))))
    (hF : IsFibredInGroupoids F)
    (hRS : CategoryTheory.ArtinFamily.IsRimSchlessinger (.of R) F)
    (x : Functor.Fiber F.p (affine (CommAlgCat.of R k))) :
    HasMarkedPredeformation F x ∧
    ∃ (_ : AddCommGroup (Tangent F x)) (_ : Module k (Tangent F x)),
      (∀ t : Tangent F x, IsZeroClass F x t ↔ t = 0) ∧
      (∀ (c : k) (t s : Tangent F x), IsScalarClass F x c t s ↔ s = c • t) ∧
      (∀ t s r : Tangent F x, IsSumClass F x t s r ↔ r = t + s) ∧
      ∀ (l : Type u) [Field l] [Algebra k l] [Algebra R l] [IsScalarTower R k l]
        [FiniteDimensional k l]
        (xl : Functor.Fiber F.p (affine (CommAlgCat.of R l))) (a : xl.val ⟶ x.val),
        F.p.IsHomLift
          (affineMap (CommAlgCat.ofHom (IsScalarTower.toAlgHom R k l))) a →
        ∃ (_ : Algebra.FiniteType R l), HasMarkedPredeformation F xl ∧
        ∃ (_ : AddCommGroup (Tangent F xl)) (_ : Module l (Tangent F xl))
          (_ : Module k (Tangent F xl)) (_ : IsScalarTower k l (Tangent F xl)),
          (∀ t : Tangent F xl, IsZeroClass F xl t ↔ t = 0) ∧
          (∀ (c : l) (t s : Tangent F xl), IsScalarClass F xl c t s ↔ s = c • t) ∧
          (∀ t s r : Tangent F xl, IsSumClass F xl t s r ↔ r = t + s) ∧
          ∃ (rho : Tangent F x →ₗ[k] Tangent F xl)
            (e : @LinearEquiv l l _ _ (RingHom.id l) (RingHom.id l) _ _
              (TensorProduct k (Tangent F x) l) (Tangent F xl) _ _
              (rightTensorModule l (Tangent F x)) _),
            (∀ (Y : Marked F x
                (ArtinDeformation.squareZeroTest (R := R) (k := k) k))
              (Z : Marked F xl
                (ArtinDeformation.squareZeroTest (R := R) (k := l) l)),
              PullsBackField F x l xl a Y Z →
                rho (classOf F x Y) = classOf F xl Z) ∧
            ∀ (t : Tangent F x) (c : l), e (t ⊗ₜ[k] c) = c • rho t := by
  sorry

end AlgebraicGeometry.StackDeformation
