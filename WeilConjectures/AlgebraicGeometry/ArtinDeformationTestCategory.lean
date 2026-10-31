/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.HopkinsLevitzki

/-! # Artinian deformation tests and formal objects

Source: Stacks Project, Formal Deformation Theory, Tags 06GC, 06GD, 06GS, 06J9,
06H3, 06H5, 06HC and 06HR; Artin's Axioms, Tag 07T4
(blueprint: def-sfb-artin-deformation-test-category).

A residue marking is encoded by its surjective augmentation with maximal kernel.
This retains exactly the specified residue-field algebra isomorphism. The test
category is a full subcategory of the category of augmented commutative algebras.
Transport coherence is Mathlib's pseudofunctor coherence, with groupoid fibres.

## Main definitions

* `TestCategory`: marked Artinian local algebras and residue-preserving local maps.
* `CofibredGroupoids`, `IsPredeformation`, `IsRimSchlessinger`: deformation categories.
* `CompleteLocalAlgebra`, `Level`, `levelLift`: complete marked local algebras, truncations.
* `FormalObject`, `evaluate`, `evaluationRestriction`, `IsVersal`: formal deformations.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ArtinDeformation

variable (R k : Type u) [CommRing R] [IsNoetherianRing R] [Field k] [Algebra R k]
  [Algebra.FiniteType R k]

/-- A marked Artinian local algebra, expressed by its augmentation to the residue field.
Source: Stacks, Tags 06GC and 07T4
(blueprint: def-sfb-artin-deformation-test-category). -/
class IsTestAlgebra {A : CommAlgCat.{u} R} (p : A →ₐ[R] k) : Prop where
  localRing : IsLocalRing A
  artinian : IsArtinianRing A
  surjective : Function.Surjective p
  kernel : RingHom.ker p.toRingHom = @IsLocalRing.maximalIdeal A _ localRing

/-- The category C_{R,k}; its arrows preserve the augmentation, hence are local and
induce the identity on the marked residue field. Source: Stacks, Tags 06GC and 07T4
(blueprint: def-sfb-artin-deformation-test-category). -/
abbrev TestCategory :=
  ObjectProperty.FullSubcategory
    (fun X : Over (CommAlgCat.of R k) ↦ IsTestAlgebra R k X.hom.hom)

variable {R k}

/-- Underlying algebra of a marked test. Source: Stacks, Tag 06GC
(blueprint: def-sfb-artin-deformation-test-category). -/
abbrev ring (A : TestCategory R k) : CommAlgCat.{u} R := A.obj.left

/-- Local structure of a test ring. Source: Stacks, Tag 06GC
(blueprint: def-sfb-artin-deformation-test-category). -/
instance testLocal (A : TestCategory R k) : IsLocalRing (ring A) := A.property.localRing

/-- Artinian structure of a test ring. Source: Stacks, Tag 06GC
(blueprint: def-sfb-artin-deformation-test-category). -/
instance testArtinian (A : TestCategory R k) : IsArtinianRing (ring A) := A.property.artinian

/-- The marked residue map. Source: Stacks, Tag 06GC
(blueprint: def-sfb-artin-deformation-test-category). -/
abbrev residue (A : TestCategory R k) : (ring A) →ₐ[R] k := A.obj.hom.hom

/-- The underlying algebra homomorphism of a test arrow. Source: Stacks, Tag 06GC
(blueprint: def-sfb-artin-deformation-test-category). -/
abbrev map {A B : TestCategory R k} (f : A ⟶ B) : (ring A) →ₐ[R] (ring B) :=
  f.hom.left.hom

/-- A small extension: a surjection with nonzero principal kernel killed by the
maximal ideal. Such a kernel is precisely a one-dimensional marked-residue vector
space. Source: Stacks, Tag 06GD
(blueprint: def-sfb-artin-deformation-test-category). -/
def IsSmallExtension {A B : TestCategory R k} (f : B ⟶ A) : Prop :=
  Function.Surjective (map f) ∧ RingHom.ker (map f).toRingHom ≠ ⊥ ∧
    (RingHom.ker (map f).toRingHom).IsPrincipal ∧
    ∀ b ∈ IsLocalRing.maximalIdeal (ring B), ∀ x ∈ RingHom.ker (map f).toRingHom,
      b * x = 0

/-- The residue field itself is a marked test. Source: Stacks, Tag 06GC
(blueprint: def-sfb-artin-deformation-test-category).
The field is local and Artinian; its identity augmentation is surjective with
zero kernel, which is its maximal ideal. -/
theorem field_isTestAlgebra : IsTestAlgebra R k (A := CommAlgCat.of R k) (AlgHom.id R k) := sorry

/-- The distinguished residue-field test. Source: Stacks, Tag 06GC
(blueprint: def-sfb-artin-deformation-test-category). -/
def residueTest : TestCategory R k :=
  ⟨Over.mk (CommAlgCat.ofHom (AlgHom.id R k)), field_isTestAlgebra⟩

set_option linter.checkUnivs false in
/-- Covariant coherent transport to groupoids, in the chosen transport presentation.
Source: Stacks, Tag 06GJ (blueprint: def-sfb-artin-deformation-test-category). -/
structure CofibredGroupoids (R k : Type u) [CommRing R] [Field k] [Algebra R k] where
  transport : Pseudofunctor (LocallyDiscrete (TestCategory R k)) Cat.{v, w}
  groupoid : ∀ A : TestCategory R k, IsGroupoid (transport.obj ⟨A⟩)

attribute [instance] CofibredGroupoids.groupoid

/-- The groupoid over a test algebra. Source: Stacks, Tag 06GJ
(blueprint: def-sfb-artin-deformation-test-category). -/
abbrev fibre (F : CofibredGroupoids.{u, v, w} R k) (A : TestCategory R k) :=
  F.transport.obj ⟨A⟩

/-- Covariant transport along a marked local map. Source: Stacks, Tag 06GJ
(blueprint: def-sfb-artin-deformation-test-category). -/
abbrev push (F : CofibredGroupoids.{u, v, w} R k) {A B : TestCategory R k}
    (f : A ⟶ B) : fibre F A ⥤ fibre F B :=
  (F.transport.map f.toLoc).toFunctor

/-- The composition comparison, in the direction g_* f_* to (gf)_*.
Source: Stacks, Tag 06GJ (blueprint: def-sfb-artin-deformation-test-category). -/
def compIso (F : CofibredGroupoids.{u, v, w} R k) {A B C : TestCategory R k}
    (f : A ⟶ B) (g : B ⟶ C) : push F f ⋙ push F g ≅ push F (f ≫ g) :=
  (Cat.Hom.toNatIso (F.transport.mapComp f.toLoc g.toLoc)).symm

/-- A predeformation category has a nonempty terminal groupoid at k.
Source: Stacks, Tag 06GS (blueprint: def-sfb-artin-deformation-test-category). -/
def IsPredeformation (F : CofibredGroupoids.{u, v, w} R k) : Prop :=
  Nonempty (fibre F (residueTest (R := R) (k := k))) ∧
    ∀ x y : fibre F (residueTest (R := R) (k := k)), Nonempty (Unique (x ⟶ y))

/-- Isomorphism classes, retaining all groupoid objects before taking the quotient.
Source: Stacks, Tag 06GS (blueprint: def-sfb-artin-deformation-test-category). -/
def isoClasses (F : CofibredGroupoids.{u, v, w} R k) (A : TestCategory R k) :=
  Quotient (isIsomorphicSetoid (fibre F A))

/-- The literal fibre-product algebra, with componentwise operations inherited from
A₁ × A₂. Source: Stacks, Tag 06J2
(blueprint: def-sfb-artin-deformation-test-category). -/
def fibreProductAlgebra {A₁ A₂ A : TestCategory R k} (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A) :
    Subalgebra R (ring A₁ × ring A₂) :=
  AlgHom.equalizer ((map f₁).comp (AlgHom.fst R (ring A₁) (ring A₂)))
    ((map f₂).comp (AlgHom.snd R (ring A₁) (ring A₂)))

/-- The canonical comparison for a commuting test square. The constraints of the
pseudofunctor identify its two composite transports; Mathlib's categorical pullback
has exactly the triples and compatible pairs of arrows of the node.
Source: Stacks, Tag 06J2 (blueprint: def-sfb-artin-deformation-test-category). -/
def comparison (F : CofibredGroupoids.{u, v, w} R k)
    {P A₁ A₂ A : TestCategory R k} (p₁ : P ⟶ A₁) (p₂ : P ⟶ A₂)
    (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A) (h : p₁ ≫ f₁ = p₂ ≫ f₂) :
    fibre F P ⥤ CategoricalPullback (push F f₁) (push F f₂) :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
    (push F f₁) (push F f₂) (fibre F P)).obj
    { fst := push F p₁
      snd := push F p₂
      iso := compIso F p₁ f₁ ≪≫ eqToIso (congrArg (push F) h) ≪≫
        (compIso F p₂ f₂).symm }

/-- The canonical residue augmentation of the literal fibre product.
Source: Stacks, Tag 06J2 (blueprint: def-sfb-artin-deformation-test-category). -/
def fibreProductResidue {A₁ A₂ A : TestCategory R k} (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A) :
    fibreProductAlgebra f₁ f₂ →ₐ[R] k :=
  (residue A₁).comp ((AlgHom.fst R (ring A₁) (ring A₂)).comp
    (fibreProductAlgebra f₁ f₂).val)

/-- The literal fibre product is again a marked Artinian local test when the second
leg is surjective. Source: Stacks, Tag 06J2
(blueprint: def-sfb-artin-deformation-test-category).
A pair is a unit precisely when both components are units. Compatibility of residue
markings therefore makes its nonunits the kernel of the common residue map. This
map is onto, since a lift in the second factor exists by surjectivity. The kernel of
the projection onto A₁ is a submodule of the finite-length A₂-module A₂. The quotient
is A₁, so the fibre product has finite length and is Artinian. -/
theorem fibreProduct_isTestAlgebra {A₁ A₂ A : TestCategory R k}
    (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A) (hs : Function.Surjective (map f₂)) :
    IsTestAlgebra R k (A := CommAlgCat.of R (fibreProductAlgebra f₁ f₂))
      (fibreProductResidue f₁ f₂) := sorry

/-- The actual fibre product in the test category. Source: Stacks, Tag 06J2
(blueprint: def-sfb-artin-deformation-test-category). -/
def fibreProductTest {A₁ A₂ A : TestCategory R k} (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hs : Function.Surjective (map f₂)) : TestCategory R k :=
  ⟨Over.mk (CommAlgCat.ofHom (fibreProductResidue f₁ f₂)),
    fibreProduct_isTestAlgebra f₁ f₂ hs⟩

/-- Compatibility of both fibre-product projections with the residue marking.
Source: Stacks, Tag 06J2 (blueprint: def-sfb-artin-deformation-test-category).
The first equality is the definition. For the second, apply the common residue map
of A to f₁(x₁) = f₂(x₂), and use the marking compatibility of both legs. -/
theorem fibreProduct_projection_residue {A₁ A₂ A : TestCategory R k}
    (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A) :
    (residue A₂).comp ((AlgHom.snd R (ring A₁) (ring A₂)).comp
      (fibreProductAlgebra f₁ f₂).val) = fibreProductResidue f₁ f₂ := sorry

/-- First literal projection of tests. Source: Stacks, Tag 06J2
(blueprint: def-sfb-artin-deformation-test-category). -/
def fibreProductFst {A₁ A₂ A : TestCategory R k} (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hs : Function.Surjective (map f₂)) : fibreProductTest f₁ f₂ hs ⟶ A₁ :=
  ObjectProperty.homMk (Over.homMk (CommAlgCat.ofHom
    ((AlgHom.fst R (ring A₁) (ring A₂)).comp (fibreProductAlgebra f₁ f₂).val)) rfl)

/-- Second literal projection of tests. Source: Stacks, Tag 06J2
(blueprint: def-sfb-artin-deformation-test-category). -/
def fibreProductSnd {A₁ A₂ A : TestCategory R k} (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hs : Function.Surjective (map f₂)) : fibreProductTest f₁ f₂ hs ⟶ A₂ :=
  ObjectProperty.homMk (Over.homMk (CommAlgCat.ofHom
    ((AlgHom.snd R (ring A₁) (ring A₂)).comp (fibreProductAlgebra f₁ f₂).val))
    (congrArg CommAlgCat.ofHom (fibreProduct_projection_residue f₁ f₂)))

/-- The literal projections form a commuting square. Source: Stacks, Tag 06J2
(blueprint: def-sfb-artin-deformation-test-category).
An element of the equalizer is a pair with f₁(x₁) = f₂(x₂); this is exactly the
required equality on elements, and extensionality gives equality of test arrows. -/
theorem fibreProduct_condition {A₁ A₂ A : TestCategory R k}
    (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A) (hs : Function.Surjective (map f₂)) :
    fibreProductFst f₁ f₂ hs ≫ f₁ = fibreProductSnd f₁ f₂ hs ≫ f₂ := sorry

/-- (RS): the canonical functor from the actual fibre product is an equivalence.
Source: Stacks, Tags 06J2 and 06J9
(blueprint: def-sfb-artin-deformation-test-category). -/
def IsRimSchlessinger (F : CofibredGroupoids.{u, v, w} R k) : Prop :=
  ∀ (A₁ A₂ A : TestCategory R k) (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hs : Function.Surjective (map f₂)),
    (comparison F (fibreProductFst f₁ f₂ hs) (fibreProductSnd f₁ f₂ hs) f₁ f₂
      (fibreProduct_condition f₁ f₂ hs)).IsEquivalence

/-- The square-zero algebra with the canonical right action and scalar restriction.
Source: Stacks, Tag 06IG; Mathlib's TrivSqZeroExt
(blueprint: def-sfb-artin-deformation-test-category). -/
def squareZeroAlgebra (V : Type u) [AddCommGroup V] [Module k V] : CommAlgCat.{u} R :=
  letI : Module kᵐᵒᵖ V := Module.compHom V (RingEquiv.toOpposite k).symm.toRingHom
  letI : IsCentralScalar k V := ⟨fun _ _ ↦ rfl⟩
  letI : Algebra R (TrivSqZeroExt k V) := Algebra.restrictScalars R k _
  CommAlgCat.of R (TrivSqZeroExt k V)

/-- The first projection, with the R-structure through k. Source: Stacks, Tag 06IG
(blueprint: def-sfb-artin-deformation-test-category). -/
def squareZeroResidue (V : Type u) [AddCommGroup V] [Module k V] :
    squareZeroAlgebra (R := R) (k := k) V →ₐ[R] k :=
  letI : Module kᵐᵒᵖ V := Module.compHom V (RingEquiv.toOpposite k).symm.toRingHom
  letI : IsCentralScalar k V := ⟨fun _ _ ↦ rfl⟩
  letI : Algebra R (TrivSqZeroExt k V) := Algebra.restrictScalars R k _
  { (TrivSqZeroExt.fstHom k k V).toRingHom with commutes' := fun _ ↦ rfl }

/-- The finite square-zero algebra is a marked Artinian local test.
Source: Stacks, Tag 06IG (blueprint: def-sfb-artin-deformation-test-category).
Its maximal ideal is 0 ⊕ V and has square zero. The quotient is k, and the finite
k-dimension of k ⊕ V makes the ring Artinian. The projection is surjective with
that maximal ideal as kernel. -/
theorem squareZero_isTestAlgebra (V : Type u) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] :
    IsTestAlgebra R k (squareZeroResidue (R := R) (k := k) V) := sorry

/-- k[V], with Mathlib's square-zero multiplication. Source: Stacks, Tag 06IG
(blueprint: def-sfb-artin-deformation-test-category). -/
def squareZeroTest (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    TestCategory R k :=
  ⟨Over.mk (CommAlgCat.ofHom (squareZeroResidue V)), squareZero_isTestAlgebra V⟩

/-- The tangent set F̄(k[ε]); the predeformation condition belongs to its intended use.
Source: Stacks, Tag 06IG (blueprint: def-sfb-artin-deformation-test-category). -/
def tangentSet (F : CofibredGroupoids.{u, v, w} R k) :=
  isoClasses F (squareZeroTest (R := R) (k := k) k)

/-- A complete Noetherian local R-algebra with its specified residue-field isomorphism.
Completeness is `IsAdicComplete` for the maximal ideal, i.e. the canonical map to the
adic completion is bijective. Source: Stacks, Tag 06H5
(blueprint: def-sfb-artin-deformation-test-category). -/
structure CompleteLocalAlgebra (R k : Type u) [CommRing R] [Field k] [Algebra R k] where
  ring : CommAlgCat.{u} R
  localRing : IsLocalRing ring
  noetherian : IsNoetherianRing ring
  complete : IsAdicComplete (IsLocalRing.maximalIdeal ring) ring
  residueEquiv : IsLocalRing.ResidueField ring ≃ₐ[R] k

attribute [instance] CompleteLocalAlgebra.localRing CompleteLocalAlgebra.noetherian
  CompleteLocalAlgebra.complete

/-- The positive-level infinitesimal quotient C / m^(n+1). Source: Stacks, Tag 06H3
(blueprint: def-sfb-artin-deformation-test-category). -/
abbrev Level (C : CompleteLocalAlgebra R k) (n : ℕ) :=
  C.ring ⧸ IsLocalRing.maximalIdeal C.ring ^ (n + 1)

/-- The canonical reduction from a higher positive level. Source: Stacks, Tag 06H3
(blueprint: def-sfb-artin-deformation-test-category). -/
def reduction (C : CompleteLocalAlgebra R k) {m n : ℕ} (h : n ≤ m) :
    Level C m →ₐ[R] Level C n :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- The specified residue map at each level, through the quotient factor map.
Source: Stacks, Tag 06H3 (blueprint: def-sfb-artin-deformation-test-category). -/
def levelResidue (C : CompleteLocalAlgebra R k) (n : ℕ) : Level C n →ₐ[R] k :=
  C.residueEquiv.toAlgHom.comp
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_self (Nat.succ_ne_zero n)))

/-- A map from C kills the (n+1)-st power of its maximal ideal.
Source: Stacks, Tag 06HC (blueprint: def-sfb-artin-deformation-test-category). -/
def KillsLevel (C : CompleteLocalAlgebra R k) {A : Type u}
    [CommRing A] [Algebra R A] (f : C.ring →ₐ[R] A) (n : ℕ) : Prop :=
  ∀ c ∈ IsLocalRing.maximalIdeal C.ring ^ (n + 1), f c = 0

/-- The induced map from a truncation, by the quotient universal property.
Source: Stacks, Tag 06HC (blueprint: def-sfb-artin-deformation-test-category). -/
def levelLift (C : CompleteLocalAlgebra R k) {A : Type u}
    [CommRing A] [Algebra R A] (f : C.ring →ₐ[R] A) (n : ℕ) (h : KillsLevel C f n) :
    Level C n →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ f h

/-- The canonical augmentation on the positive truncation C/m^(n+1) gives a test.
Source: Stacks, Tags 06H3 and 06H5
(blueprint: def-sfb-artin-deformation-test-category).
A positive power of the maximal ideal is proper, so the quotient is local. Its
maximal ideal is nilpotent and it is Noetherian, hence Artinian by the nilpotent
maximal-ideal criterion. The quotient residue is the specified residue of C. -/
theorem level_isTestAlgebra (C : CompleteLocalAlgebra R k)
    (n : ℕ) :
    IsTestAlgebra R k
      (A := CommAlgCat.of R (Level C n))
      (levelResidue C n) := sorry

/-- The actual positive infinitesimal quotient, not an arbitrarily chosen test ring.
Source: Stacks, Tags 06H3 and 06H5
(blueprint: def-sfb-artin-deformation-test-category). -/
def levelTest (C : CompleteLocalAlgebra R k) (n : ℕ) :
    TestCategory R k :=
  ⟨Over.mk (CommAlgCat.ofHom (levelResidue C n)),
    level_isTestAlgebra C n⟩

/-- The reductions preserve the marked residue. Source: Stacks, Tag 06H3
(blueprint: def-sfb-artin-deformation-test-category).
Both composites send a class represented by c to the specified residue of c.
Quotient induction therefore gives equality of these algebra maps. -/
theorem reduction_residue (C : CompleteLocalAlgebra R k)
    {m n : ℕ} (h : n ≤ m) :
    (levelResidue C n).comp
        (reduction C h) =
      levelResidue C m := sorry

/-- The canonical transition between truncation tests. Source: Stacks, Tag 06H3
(blueprint: def-sfb-artin-deformation-test-category). -/
def levelMap (C : CompleteLocalAlgebra R k)
    {m n : ℕ} (h : n ≤ m) : levelTest C m ⟶ levelTest C n :=
  ObjectProperty.homMk
    (Over.homMk (CommAlgCat.ofHom (reduction C h))
      (congrArg CommAlgCat.ofHom (reduction_residue C h)))

/-- The identity comparison of the transport. Source: Stacks, Tag 06GJ
(blueprint: def-sfb-artin-deformation-test-category). -/
def unitIso (F : CofibredGroupoids.{u, v, w} R k) (A : TestCategory R k) :
    push F (𝟙 A) ≅ 𝟭 (fibre F A) :=
  Cat.Hom.toNatIso (F.transport.mapId ⟨A⟩)

/-- The canonical reduction at equal levels is the identity. Source: Stacks, Tag 06H3
(blueprint: def-sfb-artin-deformation-test-category).
The underlying quotient factor sends every representative to itself. Extensionality
of algebra maps, over-category arrows and full-subcategory arrows proves the identity. -/
theorem levelMap_refl (C : CompleteLocalAlgebra R k) (n : ℕ) :
    levelMap C (le_refl n) = 𝟙 (levelTest C n) := sorry

/-- Canonical reductions compose. Source: Stacks, Tag 06H3
(blueprint: def-sfb-artin-deformation-test-category).
All maps send a representative c to its class; quotient induction and extensionality
prove the equality, including the identity cases. -/
theorem levelMap_comp (C : CompleteLocalAlgebra R k)
    {l m n : ℕ} (h : n ≤ m) (h' : m ≤ l) :
    levelMap C h' ≫ levelMap C h = levelMap C (h.trans h') := sorry

/-- Formal objects, with level n meaning the positive exponent n+1. All transitions
are retained, with equations saying they are the composites of successive ones.
This is equivalent to specifying only successive isomorphisms.
Source: Stacks, Tags 06H3 and 06H5
(blueprint: def-sfb-artin-deformation-test-category). -/
structure FormalObject (F : CofibredGroupoids.{u, v, w} R k)
    (C : CompleteLocalAlgebra R k) where
  obj : ∀ n : ℕ, fibre F (levelTest C n)
  transition : ∀ {m n : ℕ} (h : n ≤ m), (push F (levelMap C h)).obj (obj m) ≅ obj n
  transition_id : ∀ n : ℕ,
    (transition (le_refl n)).hom =
      eqToHom (congrArg (fun f ↦ (push F f).obj (obj n)) (levelMap_refl C n)) ≫
        (unitIso F (levelTest C n)).hom.app (obj n)
  transition_comp : ∀ {l m n : ℕ} (h : n ≤ m) (h' : m ≤ l),
    (push F (levelMap C h)).map (transition h').hom ≫ (transition h).hom =
      (compIso F (levelMap C h') (levelMap C h)).hom.app (obj l) ≫
        eqToHom (congrArg (fun f ↦ (push F f).obj (obj l)) (levelMap_comp C h h')) ≫
          (transition (h.trans h')).hom

/-- Arrows over the fixed complete ring C commute with its transitions.
Source: Stacks, Tag 06H3 (blueprint: def-sfb-artin-deformation-test-category). -/
structure FormalHom {F : CofibredGroupoids.{u, v, w} R k}
    {C : CompleteLocalAlgebra R k}
    (ξ η : FormalObject F C) where
  app : ∀ n : ℕ, ξ.obj n ⟶ η.obj n
  comm : ∀ {m n : ℕ} (h : n ≤ m),
    (push F (levelMap C h)).map (app m) ≫ (η.transition h).hom =
      (ξ.transition h).hom ≫ app n

/-- A marked local R-map from a complete algebra to a test algebra.
Source: Stacks, Tags 06GC and 06HC
(blueprint: def-sfb-artin-deformation-test-category). -/
structure LocalMap (C : CompleteLocalAlgebra R k)
    (A : TestCategory R k) where
  hom : C.ring →ₐ[R] ring A
  localHom : IsLocalHom hom
  marked : ∀ c : C.ring,
    residue A (hom c) = C.residueEquiv (IsLocalRing.residue C.ring c)

/-- A positive nilpotence exponent exists. Source: Stacks, Tag 00J8
(blueprint: def-sfb-artin-deformation-test-category).
The recorded Artinian local nilpotence criterion gives a nilpotent maximal ideal.
If its vanishing exponent is zero, increase it by one; any larger power still vanishes. -/
theorem nilpotence_exists (A : TestCategory R k) :
    ∃ n : ℕ, IsLocalRing.maximalIdeal (ring A) ^ (n + 1) = ⊥ := sorry

/-- The least positive vanishing exponent, encoded by its predecessor.
Source: Stacks, Tag 06HC (blueprint: def-sfb-artin-deformation-test-category). -/
def nilpotenceIndex (A : TestCategory R k) : ℕ := Nat.find (nilpotence_exists A)

/-- A local marked map kills the indicated power of the source maximal ideal.
Source: Stacks, Tag 06HC (blueprint: def-sfb-artin-deformation-test-category).
Locality maps the maximal ideal into the target maximal ideal, hence does the same
for its powers. At the least nilpotence exponent of A, the target power is zero. -/
theorem evaluation_kills {C : CompleteLocalAlgebra R k}
    {A : TestCategory R k} (a : LocalMap C A) :
    KillsLevel C a.hom (nilpotenceIndex A) := sorry

/-- The actual induced quotient map at the least nilpotence exponent.
Source: Stacks, Tag 06HC (blueprint: def-sfb-artin-deformation-test-category). -/
def evaluationAlgebraMap {C : CompleteLocalAlgebra R k}
    {A : TestCategory R k} (a : LocalMap C A) :
    Level C (nilpotenceIndex A) →ₐ[R] ring A :=
  levelLift C a.hom (nilpotenceIndex A) (evaluation_kills a)

/-- The induced quotient map retains the marking. Source: Stacks, Tag 06HC
(blueprint: def-sfb-artin-deformation-test-category).
Evaluate both sides on a representative c and apply the marking equation of a. -/
theorem evaluation_residue {C : CompleteLocalAlgebra R k}
    {A : TestCategory R k} (a : LocalMap C A) :
    (residue A).comp (evaluationAlgebraMap a) =
      levelResidue C (nilpotenceIndex A) := sorry

/-- The canonical map from the fixed truncation, as an arrow of tests.
Source: Stacks, Tag 06HC (blueprint: def-sfb-artin-deformation-test-category). -/
def evaluationMap {C : CompleteLocalAlgebra R k}
    {A : TestCategory R k} (a : LocalMap C A) : levelTest C (nilpotenceIndex A) ⟶ A :=
  ObjectProperty.homMk (Over.homMk (CommAlgCat.ofHom (evaluationAlgebraMap a))
    (congrArg CommAlgCat.ofHom (evaluation_residue a)))

/-- Evaluation uses exactly the least positive nilpotence exponent of the target.
Source: Stacks, Tag 06HC (blueprint: def-sfb-artin-deformation-test-category). -/
def evaluate {F : CofibredGroupoids.{u, v, w} R k}
    {C : CompleteLocalAlgebra R k} (ξ : FormalObject F C)
    {A : TestCategory R k} (a : LocalMap C A) : fibre F A :=
  (push F (evaluationMap a)).obj (ξ.obj (nilpotenceIndex A))

/-- Evaluation map at a higher level, obtained by the canonical reduction.
Source: Stacks, Tag 06HC (blueprint: def-sfb-artin-deformation-test-category). -/
def evaluationAtMap {C : CompleteLocalAlgebra R k}
    {A : TestCategory R k} (a : LocalMap C A) {m : ℕ} (h : nilpotenceIndex A ≤ m) :
    levelTest C m ⟶ A := levelMap C h ≫ evaluationMap a

/-- The specified identification of higher-level evaluation with the fixed evaluation.
It is the inverse composition constraint followed by the transported tower transition.
Source: Stacks, Tag 06HC (blueprint: def-sfb-artin-deformation-test-category). -/
def evaluationFromHigher {F : CofibredGroupoids.{u, v, w} R k}
    {C : CompleteLocalAlgebra R k} (ξ : FormalObject F C)
    {A : TestCategory R k} (a : LocalMap C A) {m : ℕ} (h : nilpotenceIndex A ≤ m) :
    (push F (evaluationAtMap a h)).obj (ξ.obj m) ≅ evaluate ξ a :=
  (compIso F (levelMap C h) (evaluationMap a)).symm.app (ξ.obj m) ≪≫
    (push F (evaluationMap a)).mapIso (ξ.transition h)

/-- Factor maps through any common higher level respect postcomposition.
Source: Stacks, Tag 06HC (blueprint: def-sfb-artin-deformation-test-category).
Both sides send the class of c to a(c); their equality follows from the assumed
lifting equality f(b(c)) = a(c), quotient induction, and extensionality. -/
theorem evaluationAtMap_comp {C : CompleteLocalAlgebra R k}
    {A B : TestCategory R k} (f : B ⟶ A) (a : LocalMap C A) (b : LocalMap C B)
    (hab : (map f).comp b.hom = a.hom) {m : ℕ}
    (hA : nilpotenceIndex A ≤ m) (hB : nilpotenceIndex B ≤ m) :
    evaluationAtMap b hB ≫ f = evaluationAtMap a hA := sorry

/-- Restriction of evaluations, using the common level max(N_A,N_B), the tower's
transitions and the same pseudofunctor composition constraints as higher evaluation.
Source: Stacks, Tag 06HC (blueprint: def-sfb-artin-deformation-test-category). -/
def evaluationRestriction {F : CofibredGroupoids.{u, v, w} R k}
    {C : CompleteLocalAlgebra R k} (ξ : FormalObject F C)
    {A B : TestCategory R k} (f : B ⟶ A) (a : LocalMap C A) (b : LocalMap C B)
    (hab : (map f).comp b.hom = a.hom) :
    (push F f).obj (evaluate ξ b) ≅ evaluate ξ a :=
  (push F f).mapIso (evaluationFromHigher ξ b (le_max_right _ _)).symm ≪≫
    (compIso F (evaluationAtMap b (le_max_right (nilpotenceIndex A) _)) f).app
      (ξ.obj (max (nilpotenceIndex A) (nilpotenceIndex B))) ≪≫
    eqToIso (congrArg
      (fun g ↦ (push F g).obj (ξ.obj (max (nilpotenceIndex A) (nilpotenceIndex B))))
      (evaluationAtMap_comp f a b hab (le_max_left _ _) (le_max_right _ _))) ≪≫
    evaluationFromHigher ξ a (le_max_left _ _)

/-- Versality retains the specified special-fibre identification, rather than merely
asking for some isomorphism after lifting. Source: Stacks, Tags 06HR and 06HS
(blueprint: def-sfb-artin-deformation-test-category). -/
def IsVersal {F : CofibredGroupoids.{u, v, w} R k}
    {C : CompleteLocalAlgebra R k} (ξ : FormalObject F C) : Prop :=
  ∀ (A B : TestCategory R k) (f : B ⟶ A), Function.Surjective (map f) →
    ∀ (a : LocalMap C A) (y : fibre F B)
      (α : (push F f).obj y ≅ evaluate ξ a),
      ∃ (b : LocalMap C B) (hab : (map f).comp b.hom = a.hom)
        (β : y ≅ evaluate ξ b),
        (push F f).map β.hom ≫ (evaluationRestriction ξ f a b hab).hom = α.hom

end AlgebraicGeometry.ArtinDeformation
