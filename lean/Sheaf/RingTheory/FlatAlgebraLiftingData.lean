module

public import Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory
public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Localization.Algebra

/-!
# Marked flat algebra lifting problems

Source: Stacks Project, cotangent.tex, section-deformations and Tag 08SP;
defos.tex, Tag 08S7 (blueprint: def-sfb-flat-algebra-lifting-data).

A marking is encoded by its surjective reduction map with prescribed kernel.
This is equivalent to a specified algebra isomorphism after scalar reduction.
The quotient below identifies precisely marking-preserving algebra isomorphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct

namespace Algebra.FlatLifting

/-- An augmented finite dimensional local base extension with kernel annihilated
by the maximal ideal. The kernel may be zero or have arbitrary finite dimension.
Source: Stacks, Tag 08SP (blueprint: def-sfb-flat-algebra-lifting-data). -/
structure Base (k : Type u) [Field k] where
  thick : CommAlgCat.{u} k
  thin : CommAlgCat.{u} k
  thickResidue : thick →ₐ[k] k
  thinResidue : thin →ₐ[k] k
  thickTest : AlgebraicGeometry.ArtinDeformation.IsTestAlgebra k k thickResidue
  thinTest : AlgebraicGeometry.ArtinDeformation.IsTestAlgebra k k thinResidue
  thickFinite : FiniteDimensional k thick
  thinFinite : FiniteDimensional k thin
  quotient : thick →ₐ[k] thin
  surjective : Function.Surjective quotient
  residue : thinResidue.comp quotient = thickResidue
  small : ∀ a ∈ @IsLocalRing.maximalIdeal thick _ thickTest.localRing,
    ∀ i ∈ RingHom.ker quotient.toRingHom, a * i = 0

variable {k : Type u} [Field k]

/-- The actual kernel, with its inherited k-vector space structure.
Source: Stacks, Tag 08SP (blueprint: def-sfb-flat-algebra-lifting-data). -/
def ideal (D : Base k) : Submodule k D.thick :=
  (RingHom.ker D.quotient.toRingHom).restrictScalars k

/-- The special fibre k tensor_C B, with the coefficient factor on the left.
Source: Stacks, Tag 08QQ (blueprint: def-sfb-flat-algebra-lifting-data). -/
def fibre (D : Base k) (B : CommAlgCat.{u} D.thin) : CommAlgCat.{u} k :=
  letI : Algebra D.thin k := D.thinResidue.toRingHom.toAlgebra
  letI : IsScalarTower k D.thin k := IsScalarTower.of_algHom D.thinResidue
  CommAlgCat.of k (k ⊗[D.thin] B)

/-- The canonical map from an algebra to its special fibre.
Source: Stacks, Tag 08QQ (blueprint: def-sfb-flat-algebra-lifting-data). -/
def reduction (D : Base k) (B : CommAlgCat.{u} D.thin) : B →+* fibre D B :=
  letI : Algebra D.thin k := D.thinResidue.toRingHom.toAlgebra
  letI : IsScalarTower k D.thin k := IsScalarTower.of_algHom D.thinResidue
  Algebra.TensorProduct.includeRight.toRingHom

/-- Scalar reduction of a morphism of algebras, on tensors c tensor b to c tensor f(b).
Source: Stacks, Tags 08QQ and 08SF (blueprint: def-sfb-flat-algebra-lifting-data). -/
def fibreMap (D : Base k) {B U : CommAlgCat.{u} D.thin} (f : B →ₐ[D.thin] U) :
    fibre D B →ₐ[k] fibre D U :=
  letI : Algebra D.thin k := D.thinResidue.toRingHom.toAlgebra
  letI : IsScalarTower k D.thin k := IsScalarTower.of_algHom D.thinResidue
  Algebra.TensorProduct.map (AlgHom.id k k) f

/-- The coefficient module P tensor_k I, with its ordinary P-module action.
Source: Stacks, Tag 08SP (blueprint: def-sfb-flat-algebra-lifting-data). -/
def coefficient (D : Base k) (B : CommAlgCat.{u} D.thin) : ModuleCat.{u} (fibre D B) :=
  ModuleCat.of (fibre D B) (fibre D B ⊗[k] ideal D)

/-- A marked flat lift. Its reduction map is the marking on generators; surjectivity
and the kernel equation say that it induces precisely E tensor_{C'} C isomorphic to B.
Source: Stacks, Tag 08SP (blueprint: def-sfb-flat-algebra-lifting-data). -/
structure Lift (D : Base k) (B : CommAlgCat.{u} D.thin) where
  ring : CommRingCat.{u}
  structureMap : D.thick →+* ring
  flat : structureMap.Flat
  reduction : ring →+* B
  surjective : Function.Surjective reduction
  square : reduction.comp structureMap = (algebraMap D.thin B).comp D.quotient.toRingHom
  kernel : RingHom.ker reduction = (RingHom.ker D.quotient.toRingHom).map structureMap

/-- Isomorphism over the thick base and inducing the identity on the marked reduction.
Source: Stacks, Tag 08S7 (blueprint: def-sfb-flat-algebra-lifting-data). -/
def Isomorphic {D : Base k} {B : CommAlgCat.{u} D.thin} (E F : Lift D B) : Prop :=
  ∃ e : E.ring ≃+* F.ring,
    e.toRingHom.comp E.structureMap = F.structureMap ∧
      F.reduction.comp e.toRingHom = E.reduction

/-- The actual quotient of marked flat lifts by marking-preserving isomorphism.
The displayed relation is already an equivalence relation; Quot uses its equivalence
closure and hence gives the same classes without choosing representatives.
Source: Stacks, Tag 08S7 (blueprint: def-sfb-flat-algebra-lifting-data). -/
def Classes (D : Base k) (B : CommAlgCat.{u} D.thin) :=
  Quot (Isomorphic (D := D) (B := B))

/-- The class of a specified marked flat lift.
Source: Stacks, Tag 08S7 (blueprint: def-sfb-flat-algebra-lifting-data). -/
def classOf {D : Base k} {B : CommAlgCat.{u} D.thin} (E : Lift D B) : Classes D B :=
  Quot.mk _ E

/-- The ordinary derived cotangent cohomology group Hom(L_{P/k}, N[j]).
Source: Stacks, Tags 08SP and 08QQ (blueprint: def-sfb-flat-algebra-lifting-data). -/
def T [∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (K : CotangentResolution.Coherence.{u}) (D : Base k)
    (B : CommAlgCat.{u} D.thin) (j : ℤ) :=
  letI := (inferInstance : ∀ R : CommRingCat.{u},
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R)) (CommRingCat.of (fibre D B))
  CotangentResolution.cotangentComplex K
      (Arrow.mk (CommRingCat.ofHom (algebraMap k (fibre D B)))) ⟶
    ((DerivedCategory.singleFunctor (ModuleCat.{u} (fibre D B)) 0).obj
      (coefficient D B))⟦j⟧

/-- The additive group structure is exactly addition of derived morphisms.
Source: Stacks, Tag 08SP (blueprint: def-sfb-flat-algebra-lifting-data). -/
instance tAddCommGroup
    [dc : ∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (K : CotangentResolution.Coherence.{u}) (D : Base k)
    (B : CommAlgCat.{u} D.thin) (j : ℤ) : AddCommGroup (T K D B j) :=
  letI := dc (CommRingCat.of (fibre D B))
  inferInstanceAs (AddCommGroup
    (CotangentResolution.cotangentComplex K
        (Arrow.mk (CommRingCat.ofHom (algebraMap k (fibre D B)))) ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (fibre D B)) 0).obj
        (coefficient D B))⟦j⟧))

/-- The coefficient map p tensor i to h(p) tensor i, retaining the source action.
Source: Stacks, Tag 08SF (blueprint: def-sfb-flat-algebra-lifting-data). -/
def coefficientMap (D : Base k) {B U : CommAlgCat.{u} D.thin}
    (f : B →ₐ[D.thin] U) : coefficient D B ⟶
      (ModuleCat.restrictScalars (fibreMap D f).toRingHom).obj (coefficient D U) :=
  letI := (fibreMap D f).toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom (fibreMap D f)
  ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (fibreMap D f).toRingHom).obj (coefficient D U))
    (TensorProduct.AlgebraTensorModule.map
      (Algebra.linearMap (fibre D B) (fibre D U)) (LinearMap.id : ideal D →ₗ[k] ideal D))

/-- Canonical localization of cotangent cohomology, expressed by restriction,
standard cotangent functoriality, and the actual coefficient map. For a localization
there is a unique target class satisfying this equation (08SF and tensor adjunction).
Source: Stacks, Tag 08SF (blueprint: def-sfb-flat-algebra-lifting-data). -/
def IsLocalizedClass
    [dc : ∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (K : CotangentResolution.Coherence.{u}) (D : Base k)
    {B U : CommAlgCat.{u} D.thin} (f : B →ₐ[D.thin] U) (j : ℤ)
    (t : T K D B j) (v : T K D U j) : Prop :=
  letI := dc (CommRingCat.of (fibre D B))
  letI := dc (CommRingCat.of (fibre D U))
  CotangentResolution.cotangentMap K
      (Arrow.homMk' (𝟙 (CommRingCat.of k))
        (CommRingCat.ofHom (fibreMap D f).toRingHom)
        (CommRingCat.hom_ext ((RingHom.comp_id _).trans
          (fibreMap D f).comp_algebraMap.symm))) ≫
    (ModuleCat.restrictScalars (fibreMap D f).toRingHom).mapDerivedCategory.map v ≫
    ((ModuleCat.restrictScalars (fibreMap D f).toRingHom).mapDerivedCategory.commShiftIso
      j).hom.app _ ≫
    ((ModuleCat.restrictScalars (fibreMap D f).toRingHom).mapDerivedCategorySingleFunctor
      0).hom.app (coefficient D U)⟦j⟧' =
    t ≫ ((DerivedCategory.singleFunctor (ModuleCat.{u} (fibre D B)) 0).map
      (coefficientMap D f))⟦j⟧'

/-- Localization of a marked lift, specified by its actual universal localization
map and by the retained reduction. This includes multiplicative sets containing zero.
Source: Stacks, Tag 08SF (blueprint: def-sfb-flat-algebra-lifting-data). -/
def IsLocalizedLift {D : Base k} {B U : CommAlgCat.{u} D.thin}
    (S : Submonoid (fibre D B)) (f : B →ₐ[D.thin] U) (E : Lift D B) (F : Lift D U) : Prop :=
  ∃ l : E.ring →+* F.ring,
    l.comp E.structureMap = F.structureMap ∧
    F.reduction.comp l = f.toRingHom.comp E.reduction ∧
    @IsLocalization E.ring _
      ((S.comap (reduction D B).toMonoidHom).comap E.reduction.toMonoidHom)
      F.ring _ l.toAlgebra

end Algebra.FlatLifting
