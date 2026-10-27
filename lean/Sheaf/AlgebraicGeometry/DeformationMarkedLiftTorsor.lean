module

public import Sheaf.AlgebraicGeometry.ArtinRSTangentTensor
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.Algebra.Group.Action.Defs

/-! # The canonical tangent action on marked deformation lifts

Source: Stacks Project, Formal Deformation Theory, Tags 06JE, 06JI and 06JJ
(blueprint: lem-sfb-deformation-marked-lift-torsor).

Marked lifts retain their specified arrow to the object being lifted. The action is
characterized by gluing two such lifts and transporting along the literal difference
map. Thus the statement specifies the canonical action, including its functoriality.

## Main definitions and statement

* `MarkedLift`, `markedLiftClasses`: the marked lift category and its classes.
* `IsCanonicalMarkedLiftAction`: the difference-map characterization of the action.
* `DeformationMorphism`: coherent morphisms, allowing different fibre universes.
* `deformation_marked_lift_torsor`: existence, unique translation, and equivariance.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w v' w'

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.ArtinDeformation

variable {k : Type u} [Field k]

/-- Marked lifts, with morphisms preserving the marking. Since the fibres are groupoids,
the marking arrows and all compatible arrows are invertible.
Source: Stacks, Tag 06JE (blueprint: lem-sfb-deformation-marked-lift-torsor). -/
abbrev MarkedLift (F : CofibredGroupoids.{u, v, w} k k)
    {A B : TestCategory k k} (p : B ⟶ A) (x : fibre F A) :=
  CostructuredArrow (push F p) x

/-- Isomorphism classes of marked lifts, rather than unmarked classes of objects.
Source: Stacks, Tag 06JE (blueprint: lem-sfb-deformation-marked-lift-torsor). -/
def markedLiftClasses (F : CofibredGroupoids.{u, v, w} k k)
    {A B : TestCategory k k} (p : B ⟶ A) (x : fibre F A) :=
  Quotient (isIsomorphicSetoid (MarkedLift F p x))

/-- The class of a specified marked lift.
Source: Stacks, Tag 06JE (blueprint: lem-sfb-deformation-marked-lift-torsor). -/
def markedLiftClass {F : CofibredGroupoids.{u, v, w} k k}
    {A B : TestCategory k k} {p : B ⟶ A} {x : fibre F A} (z : MarkedLift F p x) :
    markedLiftClasses F p x := Quotient.mk _ z

/-- The actual kernel, with its k-module structure inherited from the test k-algebra.
Source: Stacks, Tag 06JI (blueprint: lem-sfb-deformation-marked-lift-torsor). -/
abbrev liftKernel {A B : TestCategory k k} (p : B ⟶ A) :=
  LinearMap.ker (map p).toLinearMap

/-- The literal difference function (a,b) ↦ (residue(a),b-a). Its kernel component
is well-defined by the equation defining the ring fibre product.
Source: Stacks, Tag 06JI (blueprint: lem-sfb-deformation-marked-lift-torsor). -/
def markedDifferenceValue {A B : TestCategory k k} (p : B ⟶ A)
    (a : fibreProductAlgebra p p) : squareZeroAlgebra (R := k) (k := k) (liftKernel p) :=
  (residue B a.val.1, ⟨a.val.2 - a.val.1, by
    change map p (a.val.2 - a.val.1) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr a.property.symm⟩)

/-- The vector structure and normalized natural tensor equivalences supplied by
lem-sfb-artin-rs-tangent-tensor, packaged without choosing arbitrary new data.
The formulas characterize the canonical structure: coordinate functionals detect
all square-zero classes and all tensor coordinates.
Source: Stacks, Tags 06IH and 06I8
(blueprint: lem-sfb-deformation-marked-lift-torsor). -/
class MarkedLiftTangentData (F : CofibredGroupoids.{u, v, w} k k) where
  [addCommGroup : AddCommGroup (tangentSet F)]
  [module : Module k (tangentSet F)]
  equiv (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    TensorProduct k (tangentSet F) V ≃ isoClasses F (squareZeroTest (R := k) (k := k) V)
  pure (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (x : tangentSet F) (z : V) :
    equiv V (x ⊗ₜ[k] z) =
      isoClassesMap F (squareZeroMap (LinearMap.toSpanSingleton k V z)) x
  normalization (x : tangentSet F) (a : k) : equiv k (x ⊗ₜ[k] a) = a • x
  naturality (V W : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      [AddCommGroup W] [Module k W] [FiniteDimensional k W] (f : V →ₗ[k] W) :
    isoClassesMap F (squareZeroMap f) ∘ equiv V =
      equiv W ∘ TensorProduct.map (LinearMap.id : tangentSet F →ₗ[k] tangentSet F) f

attribute [instance_reducible] MarkedLiftTangentData.addCommGroup
  MarkedLiftTangentData.module
attribute [instance] MarkedLiftTangentData.addCommGroup MarkedLiftTangentData.module

/-- The action is the one whose translation parameter is obtained by marked gluing
and the difference map. The displayed pullback object retains both markings to x.
Source: Stacks, Tag 06JI, equations (one)--(three)
(blueprint: lem-sfb-deformation-marked-lift-torsor). -/
def IsCanonicalMarkedLiftAction (F : CofibredGroupoids.{u, v, w} k k)
    [T : MarkedLiftTangentData F] {A B : TestCategory k k} (p : B ⟶ A)
    (hs : Function.Surjective (map p))
    [FiniteDimensional k (liftKernel p)] (x : fibre F A)
    (act : AddAction (TensorProduct k (tangentSet F) (liftKernel p))
      (markedLiftClasses F p x)) : Prop :=
  ∃ g : fibreProductTest p p hs ⟶ squareZeroTest (R := k) (k := k) (liftKernel p),
    (∀ a : fibreProductAlgebra p p, map g a = markedDifferenceValue p a) ∧
    ∀ (z w : MarkedLift F p x) (y : fibre F (fibreProductTest p p hs)),
    Nonempty ((comparison F (fibreProductFst p p hs) (fibreProductSnd p p hs) p p
      (fibreProduct_condition p p hs)).obj y ≅
        { fst := z.left, snd := w.left, iso := asIso z.hom ≪≫ (asIso w.hom).symm }) →
    ∀ t : TensorProduct k (tangentSet F) (liftKernel p),
      act.vadd t (markedLiftClass z) = markedLiftClass w ↔
        isoClassesMap F g (Quotient.mk _ y) =
          T.equiv (liftKernel p) t

/-- A morphism of deformation pseudofunctors, with its coherent base-change
isomorphisms. This component presentation permits different universes for the two
families of groupoids. The equations are the unit and composition axioms of a
pseudonatural transformation; naturality in fibre arrows is part of each NatIso.
Source: Stacks, Tags 06GJ and 06JJ
(blueprint: lem-sfb-deformation-marked-lift-torsor). -/
structure DeformationMorphism (F : CofibredGroupoids.{u, v, w} k k)
    (G : CofibredGroupoids.{u, v', w'} k k) where
  app (A : TestCategory k k) : fibre F A ⥤ fibre G A
  baseChange {A B : TestCategory k k} (f : A ⟶ B) :
    app A ⋙ push G f ≅ push F f ⋙ app B
  unit (A : TestCategory k k) (x : fibre F A) :
    (baseChange (𝟙 A)).hom.app x ≫ (app A).map ((unitIso F A).hom.app x) =
      (unitIso G A).hom.app ((app A).obj x)
  comp {A B C : TestCategory k k} (f : A ⟶ B) (g : B ⟶ C) (x : fibre F A) :
    (push G g).map ((baseChange f).hom.app x) ≫
        (baseChange g).hom.app ((push F f).obj x) ≫
          (app C).map ((compIso F f g).hom.app x) =
      (compIso G f g).hom.app ((app A).obj x) ≫ (baseChange (f ≫ g)).hom.app x

/-- Applying a coherent morphism to the object and its marking defines the marked-lift
functor. The base-change constraint identifies G(p)H(z) with H(F(p)z).
Source: Stacks, Tag 06JJ (blueprint: lem-sfb-deformation-marked-lift-torsor). -/
def markedLiftMorphismFunctor {F : CofibredGroupoids.{u, v, w} k k}
    {G : CofibredGroupoids.{u, v', w'} k k}
    (H : DeformationMorphism F G)
    {A B : TestCategory k k} (p : B ⟶ A) (x : fibre F A) :
    MarkedLift F p x ⥤ MarkedLift G p ((H.app A).obj x) :=
  CostructuredArrow.map₂ (H.baseChange p).hom (𝟙 _)

/-- The induced map on marked lift classes.
Source: Stacks, Tag 06JJ (blueprint: lem-sfb-deformation-marked-lift-torsor). -/
def markedLiftMorphism {F : CofibredGroupoids.{u, v, w} k k}
    {G : CofibredGroupoids.{u, v', w'} k k}
    (H : DeformationMorphism F G)
    {A B : TestCategory k k} (p : B ⟶ A) (x : fibre F A) :
    markedLiftClasses F p x →
      markedLiftClasses G p ((H.app A).obj x) :=
  Quotient.map (markedLiftMorphismFunctor H p x).obj (by
    intro z w h
    rcases h with ⟨i⟩
    exact ⟨(markedLiftMorphismFunctor H p x).mapIso i⟩)

/-- The map dH on the exact isomorphism classes over the dual numbers.
Source: Stacks, Tags 06ID and 06JJ
(blueprint: lem-sfb-deformation-marked-lift-torsor). -/
def deformationTangentMap {F : CofibredGroupoids.{u, v, w} k k}
    {G : CofibredGroupoids.{u, v', w'} k k}
    (H : DeformationMorphism F G) : tangentSet F → tangentSet G :=
  Quotient.map
    (H.app (squareZeroTest (R := k) (k := k) k)).obj (by
      intro z w h
      rcases h with ⟨i⟩
      exact ⟨(H.app (squareZeroTest (R := k) (k := k) k)).mapIso i⟩)

/-- Marked lifts have the canonical free and transitive tangent-tensor action, and
all coherent morphisms are equivariant for dH tensor the identity of the kernel.
Source: Stacks, Tags 06JI and 06JJ
(blueprint: lem-sfb-deformation-marked-lift-torsor).

Proof:
1. Use lem-sfb-artin-rs-tangent-tensor for the normalized natural tangent data.
Every k-subspace of the kernel is an ideal, since multiplication acts through the
residue. A strictly descending chain of subspaces would contradict Artinianness,
so the kernel is finite-dimensional, including the zero kernel.
2. Put B2 = B ×_A B. The difference map g(a,b)=(residue(a),b-a) gives an isomorphism
B2 ≅ B ×_k k[I], with inverse (a,(residue(a),i)) ↦ (a,a+i), preserving first
projection. By lem-sfb-rs-marked-lift-pullback-bijections, marked gluing and this
isomorphism give, for every z, a bijection δ_z from lifts to TF tensor I. Forgetting
the unique marking over k identifies the parameter set with F̄(k[I]). This yields
exactly IsCanonicalMarkedLiftAction, independently of representatives.
3. Glue three lifts using (RS). On the triple fibre product the difference maps
satisfy (b-a)+(c-b)=c-a. Apply the tangent tensor lemma's naturality for the two
coordinate projections and the sum map I ⊕ I → I. Thus δ_z(v)=δ_z(w)+δ_w(v).
4. Define t +ᵥ z as the unique w with δ_z(w)=t. Cancellation gives δ_z(z)=0;
the cocycle identity gives the action laws. Bijectivity gives the unique parameter
for every z,w. The construction on an empty lift set is its unique empty action.
5. Naturality in the pseudofunctor of the marked gluing comparisons shows that H
commutes with δ. Scalars and sums on square-zero parameters show dH is k-linear.
For a basis of I, its coordinate projections detect both tensor parameters and
square-zero classes, identifying the parameter map with dH tensor id_I. This
proves the stated equivariance without choosing any initial lift. -/
theorem deformation_marked_lift_torsor
    (F : CofibredGroupoids.{u, v, w} k k)
    (G : CofibredGroupoids.{u, v', w'} k k)
    (hpreF : IsPredeformation F) (hrsF : IsRimSchlessinger F)
    (hpreG : IsPredeformation G) (hrsG : IsRimSchlessinger G)
    {A B : TestCategory k k} (p : B ⟶ A) (hs : Function.Surjective (map p))
    (hk : ∀ b ∈ IsLocalRing.maximalIdeal (ring B),
      ∀ i ∈ RingHom.ker (map p).toRingHom, b * i = 0) :
    ∃ (_ : MarkedLiftTangentData F) (_ : MarkedLiftTangentData G)
      (_ : FiniteDimensional k (liftKernel p))
      (actF : ∀ x : fibre F A,
        AddAction (TensorProduct k (tangentSet F) (liftKernel p)) (markedLiftClasses F p x))
      (actG : ∀ x : fibre G A,
        AddAction (TensorProduct k (tangentSet G) (liftKernel p)) (markedLiftClasses G p x)),
      (∀ x : fibre F A, IsCanonicalMarkedLiftAction F p hs x (actF x)) ∧
      (∀ x : fibre G A, IsCanonicalMarkedLiftAction G p hs x (actG x)) ∧
      (∀ (x : fibre F A) (z w : markedLiftClasses F p x),
        ∃! t, (actF x).vadd t z = w) ∧
      (∀ (x : fibre G A) (z w : markedLiftClasses G p x),
        ∃! t, (actG x).vadd t z = w) ∧
      (∀ H : DeformationMorphism F G,
        ∃ dH : tangentSet F →ₗ[k] tangentSet G,
          (∀ t, dH t = deformationTangentMap H t) ∧
          ∀ (x : fibre F A) (z : markedLiftClasses F p x)
            (t : TensorProduct k (tangentSet F) (liftKernel p)),
            markedLiftMorphism H p x ((actF x).vadd t z) =
              (actG ((H.app A).obj x)).vadd
                (TensorProduct.map dH (LinearMap.id : liftKernel p →ₗ[k] liftKernel p) t)
                (markedLiftMorphism H p x z)) := by
  sorry

end AlgebraicGeometry.ArtinDeformation
