module

public import Sheaf.AlgebraicGeometry.ArtinRSTangentTensor

/-! # Hulls of classical deformation functors

Source: Stacks Project, formal-defos.tex, Tags 06HC, 06HR, 06IG, 06IY and 06JL
(blueprint: def-sfb-classical-deformation-hull).

The test category, pseudofunctor and complete local algebra are the existing
Artin deformation definitions with coefficient ring equal to the residue field.
Natural transformations are recorded componentwise, including their naturality.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry.ArtinDeformation

variable {k : Type u} [Field k]

/-- The vector operations on the tangent set are the square-zero parameter operations.
The addition condition uses both projections from k[k × k], so under (RS) it
specifies the sum of every pair, including the zero-dimensional tangent case.
Source: Stacks, Tags 06IG and 06IH
(blueprint: def-sfb-classical-deformation-hull). -/
def HasClassicalTangentOperations (D : CofibredGroupoids.{u, v, w} k k)
    [tadd : AddCommGroup (tangentSet D)] [Module k (tangentSet D)] : Prop :=
  (∀ (a : k) (x : tangentSet D),
    a • x = isoClassesMap D (squareZeroMap (a • (LinearMap.id : k →ₗ[k] k))) x) ∧
  (∀ z : isoClasses D (squareZeroTest (R := k) (k := k) (k × k)),
    isoClassesMap D (squareZeroMap
      ((LinearMap.fst k k k) + (LinearMap.snd k k k))) z =
      @Add.add (tangentSet D) tadd.toAdd
        (isoClassesMap D (squareZeroMap (LinearMap.fst k k k)) z)
        (isoClassesMap D (squareZeroMap (LinearMap.snd k k k)) z))

/-- The tangent operations on local maps are pointwise operations on their epsilon
coefficients. This characterizes the usual derivation vector space, without choosing
any presentation or basis of the source complete ring.
Source: Stacks, Tag 06IG, tangent space of a prorepresentable functor
(blueprint: def-sfb-classical-deformation-hull). -/
def HasLocalMapTangentOperations (B : CompleteLocalAlgebra k k)
    [AddCommGroup (LocalMap B (squareZeroTest (R := k) (k := k) k))]
    [Module k (LocalMap B (squareZeroTest (R := k) (k := k) k))] : Prop :=
  (∀ (a b : LocalMap B (squareZeroTest (R := k) (k := k) k)) (c : B.ring),
    TrivSqZeroExt.snd ((a + b).hom c) =
      TrivSqZeroExt.snd (a.hom c) + TrivSqZeroExt.snd (b.hom c)) ∧
  (∀ (r : k) (a : LocalMap B (squareZeroTest (R := k) (k := k) k)) (c : B.ring),
    TrivSqZeroExt.snd ((r • a).hom c) = r * TrivSqZeroExt.snd (a.hom c))

/-- A natural map h_B → π₀ D, with h_B the existing type of marked local maps.
Such maps are automatically continuous: locality sends m_B^n into m_A^n, and
some positive power of m_A is zero. The naturality field is written for every
commuting triangle of local maps and hence is precisely ordinary naturality.
Source: Stacks, Tags 06HC and 06HR
(blueprint: def-sfb-classical-deformation-hull). -/
structure ClassicalClassMap (D : CofibredGroupoids.{u, v, w} k k)
    (B : CompleteLocalAlgebra k k) where
  app : ∀ A : TestCategory k k, LocalMap B A → isoClasses D A
  naturality : ∀ (A A' : TestCategory k k) (f : A ⟶ A')
    (a : LocalMap B A) (a' : LocalMap B A'),
    (map f).comp a.hom = a'.hom → isoClassesMap D f (app A a) = app A' a'

/-- A hull is smooth on every surjection and induces the specified linear tangent
isomorphism. The source vector structures must be the epsilon-coefficient operations;
they cannot be transported arbitrarily through a bijection.
Source: Stacks, Tag 06IY, remark-compare-schlessinger-H3, and Tag 06IZ
(blueprint: def-sfb-classical-deformation-hull). -/
def IsClassicalHull {D : CofibredGroupoids.{u, v, w} k k}
    [AddCommGroup (tangentSet D)] [Module k (tangentSet D)]
    {B : CompleteLocalAlgebra k k} (η : ClassicalClassMap D B) : Prop :=
  (∀ (A A' : TestCategory k k) (f : A' ⟶ A), Function.Surjective (map f) →
    ∀ (a : LocalMap B A) (y : isoClasses D A'),
      η.app A a = isoClassesMap D f y →
      ∃ b : LocalMap B A', (map f).comp b.hom = a.hom ∧ η.app A' b = y) ∧
  (∃ (_ : AddCommGroup (LocalMap B (squareZeroTest (R := k) (k := k) k)))
      (_ : Module k (LocalMap B (squareZeroTest (R := k) (k := k) k))),
    HasLocalMapTangentOperations B ∧
      ∃ e : LocalMap B (squareZeroTest (R := k) (k := k) k) ≃ₗ[k] tangentSet D,
        ∀ a : LocalMap B (squareZeroTest (R := k) (k := k) k),
          e a = η.app (squareZeroTest (R := k) (k := k) k) a)

/-- A natural inverse to a componentwise map h_B → π₀ D, including both inverse
identities and naturality of the inverse. Source: Stacks, Tag 06JL
(blueprint: def-sfb-classical-deformation-hull). -/
def IsClassicalClassIso {D : CofibredGroupoids.{u, v, w} k k}
    {B : CompleteLocalAlgebra k k} (η : ClassicalClassMap D B) : Prop :=
  ∃ ι : ∀ A : TestCategory k k, isoClasses D A → LocalMap B A,
    (∀ A : TestCategory k k,
      Function.LeftInverse (ι A) (η.app A) ∧ Function.RightInverse (ι A) (η.app A)) ∧
    (∀ (A A' : TestCategory k k) (f : A ⟶ A') (y : isoClasses D A),
      (map f).comp (ι A y).hom = (ι A' (isoClassesMap D f y)).hom)

/-- The canonical map k → k[epsilon] used to pull back the residue object.
Source: Stacks, formal-defos.tex, section-infinitesimal-automorphisms
(blueprint: def-sfb-classical-deformation-hull). -/
def classicalZeroArrow :
    residueTest (R := k) (k := k) ⟶ squareZeroTest (R := k) (k := k) k :=
  ObjectProperty.homMk (Over.homMk
    (CommAlgCat.ofHom (Algebra.ofId k (ring (squareZeroTest (R := k) (k := k) k))))
    (by ext))

end AlgebraicGeometry.ArtinDeformation
