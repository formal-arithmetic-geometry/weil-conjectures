/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Affine Hopf action module data

Source: Stacks, Tag 03LF, affine form of the identity and cocycle diagrams.
The target pullback is identified with M tensor_k C. The source uses the algebra
structure induced by rho, rather than the usual inclusion of E into E tensor_k C.
For composable arrows the coordinate ring is E tensor_k C tensor_k C, with maps
p_a(e tensor c)=e tensor c tensor 1, p_b(e tensor c)=rho(e) tensor c, and
p_ab(e tensor c)=e tensor Delta(c). Pullbacks are linear maps on actual balanced scalar
extensions, characterized on
all finite presentations of the image of each generator. Identity and cocycle are
equalities of these pullbacks, with all extension transports normalized on generators.
They are not defined as counitality and coassociativity of the generator map.
(blueprint: def-sfb-hopf-action-module-data)
-/

set_option autoImplicit false

@[expose] public section

universe u v w z z₂ t

open TensorProduct
open scoped TensorProduct

namespace HopfAction

variable (k : Type u) [Field k] (C : Type v) [CommRing C] [HopfAlgebra k C]
variable (E : Type w) [CommRing E] [Algebra k E]
variable (M : Type z) [AddCommGroup M] [Module E M] [Module k M]
variable [IsScalarTower k E M]

/-- Extension along the specified algebra map, with the algebra factor first.
Source: Stacks Tag 03LF, affine pullback. (blueprint: def-sfb-hopf-action-module-data) -/
abbrev Extension (r : E →ₐ[k] E ⊗[k] C) : Type (max v w z) :=
  letI := r.toRingHom.toAlgebra
  letI : Module E (E ⊗[k] C) := r.toRingHom.toAlgebra.toModule
  (E ⊗[k] C) ⊗[E] M

/-- Scalar multiplication in the specified extension.
Source: Stacks Tag 03LF, affine pullback. (blueprint: def-sfb-hopf-action-module-data) -/
def extensionSmul (r : E →ₐ[k] E ⊗[k] C) (l : E ⊗[k] C)
    (x : Extension k C E M r) : Extension k C E M r :=
  letI := r.toRingHom.toAlgebra
  letI : Module E (E ⊗[k] C) := r.toRingHom.toAlgebra.toModule
  l • x

/-- The generating tensor in extension of scalars.
Source: Stacks Tag 03LF, affine pullback. (blueprint: def-sfb-hopf-action-module-data) -/
def extensionTensor (r : E →ₐ[k] E ⊗[k] C) (l : E ⊗[k] C) (m : M) :
    Extension k C E M r :=
  letI := r.toRingHom.toAlgebra
  letI : Module E (E ⊗[k] C) := r.toRingHom.toAlgebra.toModule
  l ⊗ₜ[E] m

/-- The action of E tensor C on M tensor C, using multiplication of C coefficients.
Source: Stacks Tag 03LF, affine target module. (blueprint: def-sfb-hopf-action-module-data) -/
def targetAction : E ⊗[k] C →ₗ[k] (M ⊗[k] C →ₗ[k] M ⊗[k] C) :=
  TensorProduct.lift
    (((TensorProduct.mapBilinear (RingHom.id k) M C M C).comp
      (Algebra.lsmul k k M).toLinearMap).compl₂ (Algebra.lsmul k k C).toLinearMap)

/-- Coassociativity in right-comodule convention.
Source: Stacks Tag 03LF, affine cocycle. (blueprint: def-sfb-hopf-action-module-data) -/
def Coassociative (θ : M →ₗ[k] M ⊗[k] C) : Prop :=
  (TensorProduct.assoc k M C C).toLinearMap ∘ₗ θ.rTensor C ∘ₗ θ =
    (Coalgebra.comul (R := k) (A := C)).lTensor M ∘ₗ θ

/-- Counitality in right-comodule convention.
Source: Stacks Tag 03LF, identity section. (blueprint: def-sfb-hopf-action-module-data) -/
def Counital (θ : M →ₗ[k] M ⊗[k] C) : Prop :=
  (TensorProduct.rid k M).toLinearMap ∘ₗ
    (Coalgebra.counit (R := k) (A := C)).lTensor M ∘ₗ θ = LinearMap.id

/-- A coaction of the coordinate Hopf algebra on the algebra E.
Source: Stacks Tag 03LF, affine action. (blueprint: def-sfb-hopf-action-module-data) -/
structure AlgebraCoaction where
  /-- The given algebra coaction. -/
  map : E →ₐ[k] E ⊗[k] C
  /-- Identity law. -/
  counit : Counital k C E map.toLinearMap
  /-- Composition law. -/
  coassoc : Coassociative k C E map.toLinearMap

/-- Semilinear, counital, coassociative module coaction.
Source: Stacks Tag 03LF, affine equivariance. (blueprint: def-sfb-hopf-action-module-data) -/
structure ModuleCoaction (ρ : AlgebraCoaction k C E) where
  /-- The k-linear coaction. -/
  map : M →ₗ[k] M ⊗[k] C
  /-- Compatibility with the E action. -/
  semilinear : ∀ (e : E) (m : M), map (e • m) = targetAction k C E M (ρ.map e) (map m)
  /-- Identity law. -/
  counit : Counital k C M map
  /-- Composition law. -/
  coassoc : Coassociative k C M map

/-- The k-module structure of the specified scalar extension.
Source: Stacks Tag 03LF, affine pullback. (blueprint: def-sfb-hopf-action-module-data) -/
instance extensionModule (r : E →ₐ[k] E ⊗[k] C) :
    Module k (Extension k C E M r) :=
  letI := r.toRingHom.toAlgebra
  letI : Module E (E ⊗[k] C) := r.toRingHom.toAlgebra.toModule
  inferInstanceAs (Module k ((E ⊗[k] C) ⊗[E] M))

/-- The k-linear generating map into the specified extension.
Source: Stacks Tag 03LF, affine pullback. (blueprint: def-sfb-hopf-action-module-data) -/
def extensionUnit (r : E →ₐ[k] E ⊗[k] C) : M →ₗ[k] Extension k C E M r :=
  letI := r.toRingHom.toAlgebra
  letI : Module E (E ⊗[k] C) := r.toRingHom.toAlgebra.toModule
  (TensorProduct.mk E (E ⊗[k] C) M 1).restrictScalars k

/-- Scalar extension to an arbitrary coordinate algebra along a specified map.
Source: Stacks Tag 03LF, pullbacks. (blueprint: def-sfb-hopf-action-module-data) -/
abbrev ScalarExtension (A : Type t) [CommRing A] [Algebra k A] (r : E →ₐ[k] A) :=
  letI := r.toRingHom.toAlgebra
  letI : Module E A := r.toRingHom.toAlgebra.toModule
  A ⊗[E] M

/-- The coefficient-algebra action on the actual scalar extension.
Source: Stacks Tag 03LF, pullbacks. (blueprint: def-sfb-hopf-action-module-data) -/
instance scalarExtensionModule (A : Type t) [CommRing A] [Algebra k A]
    (r : E →ₐ[k] A) : Module A (ScalarExtension k E M A r) :=
  letI := r.toRingHom.toAlgebra
  letI : Module E A := r.toRingHom.toAlgebra.toModule
  inferInstanceAs (Module A (A ⊗[E] M))

/-- Generating tensors in the actual scalar extension.
Source: Stacks Tag 03LF, pullbacks. (blueprint: def-sfb-hopf-action-module-data) -/
def scalarExtensionTensor (A : Type t) [CommRing A] [Algebra k A]
    (r : E →ₐ[k] A) (a : A) (m : M) : ScalarExtension k E M A r :=
  letI := r.toRingHom.toAlgebra
  letI : Module E A := r.toRingHom.toAlgebra.toModule
  a ⊗ₜ[E] m

/-- The target ring map t-sharp.
Source: Stacks Tag 03LF, affine action. (blueprint: def-sfb-hopf-action-module-data) -/
def targetMap : E →ₐ[k] E ⊗[k] C := Algebra.TensorProduct.includeLeft

/-- The identity-section ring map u_L(e tensor c) = e epsilon(c).
Source: Stacks Tag 03LF, identity. (blueprint: def-sfb-hopf-action-module-data) -/
def identityMap : E ⊗[k] C →ₐ[k] E :=
  Algebra.TensorProduct.productMap (AlgHom.id k E)
    ((Algebra.ofId k E).comp (Bialgebra.counitAlgHom k C))

/-- The first-arrow ring map p_a(e tensor c) = e tensor c tensor 1.
Source: Stacks Tag 03LF, cocycle. (blueprint: def-sfb-hopf-action-module-data) -/
def firstArrowMap : E ⊗[k] C →ₐ[k] (E ⊗[k] C) ⊗[k] C :=
  Algebra.TensorProduct.includeLeft

/-- The second-arrow ring map p_b(e tensor c) = rho(e) tensor c.
Source: Stacks Tag 03LF, cocycle. (blueprint: def-sfb-hopf-action-module-data) -/
def secondArrowMap (ρ : AlgebraCoaction k C E) :
    E ⊗[k] C →ₐ[k] (E ⊗[k] C) ⊗[k] C :=
  Algebra.TensorProduct.map ρ.map (AlgHom.id k C)

/-- The composite-arrow ring map p_ab(e tensor c) = e tensor Delta(c).
Source: Stacks Tag 03LF, cocycle. (blueprint: def-sfb-hopf-action-module-data) -/
def compositeArrowMap : E ⊗[k] C →ₐ[k] (E ⊗[k] C) ⊗[k] C :=
  (Algebra.TensorProduct.assoc k k k E C C).symm.toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id k E) (Bialgebra.comulAlgHom k C))

/-- Characterize the actual pullback p*delta as the A-linear extension of its generator
map. The finite-presentation condition says exactly that delta(1 tensor m) = sum a_i tensor b_i
is sent to sum p(1 tensor b_i) tensor a_i in the target scalar extension.
All presentations, including the empty one, are included; no basis is chosen.
Source: Stacks Tag 03LF, pullback of alpha. (blueprint: def-sfb-hopf-action-module-data) -/
def IsPullback (ρ : AlgebraCoaction k C E)
    (δ : Extension k C E M ρ.map ≃ₗ[k] M ⊗[k] C)
    (A : Type t) [CommRing A] [Algebra k A] (p : E ⊗[k] C →ₐ[k] A)
    (F : ScalarExtension k E M A (p.comp ρ.map) →ₗ[A]
      ScalarExtension k E M A (p.comp (targetMap k C E))) : Prop :=
  ∀ (m : M) (n : ℕ) (a : Fin n → M) (b : Fin n → C),
    δ (extensionTensor k C E M ρ.map 1 m) = ∑ i, a i ⊗ₜ[k] b i →
    F (scalarExtensionTensor k E M A (p.comp ρ.map) 1 m) =
      ∑ i, scalarExtensionTensor k E M A (p.comp (targetMap k C E))
        (p (1 ⊗ₜ[k] b i)) (a i)

/-- Canonical change between two scalar-extension presentations: the coefficient and
module generators are unchanged. This pins the transport uniquely, including when the
underlying algebra maps agree only by the action identities.
Source: Stacks Tag 03LF, extension transports. (blueprint: def-sfb-hopf-action-module-data) -/
def IsExtensionTransport (A : Type t) [CommRing A] [Algebra k A]
    (r s : E →ₐ[k] A)
    (T : ScalarExtension k E M A r ≃ₗ[A] ScalarExtension k E M A s) : Prop :=
  ∀ (a : A) (m : M), T (scalarExtensionTensor k E M A r a m) =
    scalarExtensionTensor k E M A s a m

/-- The actual identity pullback equals the identity after its canonical identifications
with M. Every map is pinned by its generator values; the existential witnesses are proof
fields, not choices of data. No counit law for the generator map is assumed here.
Source: Stacks Tag 03LF, identity diagram. (blueprint: def-sfb-hopf-action-module-data) -/
def IdentityDiagram (ρ : AlgebraCoaction k C E)
    (δ : Extension k C E M ρ.map ≃ₗ[k] M ⊗[k] C) : Prop :=
  ∃ (F : ScalarExtension k E M E ((identityMap k C E).comp ρ.map) →ₗ[E]
        ScalarExtension k E M E ((identityMap k C E).comp (targetMap k C E)))
    (S : ScalarExtension k E M E ((identityMap k C E).comp ρ.map) ≃ₗ[E] M)
    (T : ScalarExtension k E M E
      ((identityMap k C E).comp (targetMap k C E)) ≃ₗ[E] M),
    IsPullback k C E M ρ δ E (identityMap k C E) F ∧
    (∀ (e : E) (m : M),
      S (scalarExtensionTensor k E M E ((identityMap k C E).comp ρ.map) e m) = e • m) ∧
    (∀ (e : E) (m : M), T (scalarExtensionTensor k E M E
      ((identityMap k C E).comp (targetMap k C E)) e m) = e • m) ∧
    T.toLinearMap ∘ₗ F = S.toLinearMap

/-- The actual pullback cocycle over P = (E tensor C) tensor C. The three pullback
maps and all three transports are characterized by their values on generators.
The equation is T_target o p_a*delta o T_middle o p_b*delta = p_ab*delta o T_source.
Thus its source, middle and target modules are the genuine balanced extensions, not
copies of a coassociativity equation.
Source: Stacks Tag 03LF, cocycle diagram. (blueprint: def-sfb-hopf-action-module-data) -/
def CocycleDiagram (ρ : AlgebraCoaction k C E)
    (δ : Extension k C E M ρ.map ≃ₗ[k] M ⊗[k] C) : Prop :=
  ∃ (Fa : ScalarExtension k E M ((E ⊗[k] C) ⊗[k] C)
          ((firstArrowMap k C E).comp ρ.map) →ₗ[(E ⊗[k] C) ⊗[k] C]
        ScalarExtension k E M ((E ⊗[k] C) ⊗[k] C)
          ((firstArrowMap k C E).comp (targetMap k C E)))
    (Fb : ScalarExtension k E M ((E ⊗[k] C) ⊗[k] C)
          ((secondArrowMap k C E ρ).comp ρ.map) →ₗ[(E ⊗[k] C) ⊗[k] C]
        ScalarExtension k E M ((E ⊗[k] C) ⊗[k] C)
          ((secondArrowMap k C E ρ).comp (targetMap k C E)))
    (Fab : ScalarExtension k E M ((E ⊗[k] C) ⊗[k] C)
          ((compositeArrowMap k C E).comp ρ.map) →ₗ[(E ⊗[k] C) ⊗[k] C]
        ScalarExtension k E M ((E ⊗[k] C) ⊗[k] C)
          ((compositeArrowMap k C E).comp (targetMap k C E)))
    (Ts : ScalarExtension k E M ((E ⊗[k] C) ⊗[k] C)
          ((secondArrowMap k C E ρ).comp ρ.map) ≃ₗ[(E ⊗[k] C) ⊗[k] C]
        ScalarExtension k E M ((E ⊗[k] C) ⊗[k] C)
          ((compositeArrowMap k C E).comp ρ.map))
    (Tm : ScalarExtension k E M ((E ⊗[k] C) ⊗[k] C)
          ((secondArrowMap k C E ρ).comp (targetMap k C E)) ≃ₗ[(E ⊗[k] C) ⊗[k] C]
        ScalarExtension k E M ((E ⊗[k] C) ⊗[k] C)
          ((firstArrowMap k C E).comp ρ.map))
    (Tt : ScalarExtension k E M ((E ⊗[k] C) ⊗[k] C)
          ((firstArrowMap k C E).comp (targetMap k C E)) ≃ₗ[(E ⊗[k] C) ⊗[k] C]
        ScalarExtension k E M ((E ⊗[k] C) ⊗[k] C)
          ((compositeArrowMap k C E).comp (targetMap k C E))),
    IsPullback k C E M ρ δ _ (firstArrowMap k C E) Fa ∧
    IsPullback k C E M ρ δ _ (secondArrowMap k C E ρ) Fb ∧
    IsPullback k C E M ρ δ _ (compositeArrowMap k C E) Fab ∧
    IsExtensionTransport k E M _ ((secondArrowMap k C E ρ).comp ρ.map)
      ((compositeArrowMap k C E).comp ρ.map) Ts ∧
    IsExtensionTransport k E M _ ((secondArrowMap k C E ρ).comp (targetMap k C E))
      ((firstArrowMap k C E).comp ρ.map) Tm ∧
    IsExtensionTransport k E M _ ((firstArrowMap k C E).comp (targetMap k C E))
      ((compositeArrowMap k C E).comp (targetMap k C E)) Tt ∧
    Tt.toLinearMap ∘ₗ Fa ∘ₗ Tm.toLinearMap ∘ₗ Fb = Fab ∘ₗ Ts.toLinearMap

/-- An L-linear isomorphism with the actual identity and composable-arrow pullback diagrams.
Source: Stacks Tag 03LF, affine equivariance. (blueprint: def-sfb-hopf-action-module-data) -/
structure Linearization (ρ : AlgebraCoaction k C E) where
  /-- The isomorphism from source pullback to target pullback. -/
  iso : Extension k C E M ρ.map ≃ₗ[k] M ⊗[k] C
  /-- Linearity for all elements of L. -/
  linear : ∀ (l : E ⊗[k] C) (x : Extension k C E M ρ.map),
    iso (extensionSmul k C E M ρ.map l x) = targetAction k C E M l (iso x)
  /-- Pullback along u_L is the identity of M under the canonical transports. -/
  counit : IdentityDiagram k C E M ρ iso
  /-- Pullbacks along p_a, p_b and p_ab satisfy the actual cocycle diagram over P. -/
  cocycle : CocycleDiagram k C E M ρ iso

/-- Base change of a module map along the specified source algebra map.
Source: Stacks Tag 03LF, morphisms. (blueprint: def-sfb-hopf-action-module-data) -/
def extensionMap {N : Type z₂} [AddCommGroup N] [Module E N]
    (r : E →ₐ[k] E ⊗[k] C) (f : M →ₗ[E] N) :
    Extension k C E M r → Extension k C E N r :=
  letI := r.toRingHom.toAlgebra
  letI : Module E (E ⊗[k] C) := r.toRingHom.toAlgebra.toModule
  fun x ↦ LinearMap.baseChange (E ⊗[k] C) f x

/-- Multiplication of the two Hopf coefficients after tensoring over E.
Source: Stacks Tag 03LF, tensor datum. (blueprint: def-sfb-hopf-action-module-data) -/
def tensorCoefficients (N : Type z₂) [AddCommGroup N] [Module E N] [Module k N]
    [IsScalarTower k E N] :
    (M ⊗[k] C) ⊗[k] (N ⊗[k] C) →ₗ[k] (M ⊗[E] N) ⊗[k] C :=
  TensorProduct.map
    (TensorProduct.lift ((TensorProduct.mk E M N).restrictScalars₁₂ k k))
    (LinearMap.mul' k C) ∘ₗ
    (TensorProduct.tensorTensorTensorComm k M C N C).toLinearMap

end HopfAction
