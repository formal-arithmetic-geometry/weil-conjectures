/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Paper.FinitePullbackTensorRepresentativeData

/-! # Composition of the ordinary signed tensor comparison

Source: Stacks 03EL, 07A4 and 00YV.
(blueprint: lem-pur-finite-pullback-tensor-chain-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FinitePullbackTensorRep
attribute [local irreducible] Scheme.residueField finiteIntrinsicClosed
  finiteIntrinsicTensorModels finitePullbackTensorConstruction
attribute [local implicit_reducible] integralCoefficientSheaf
  integralCoefficientCommRingSheaf finiteIntrinsicDerivedTensor
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The ordinary total comparison respects the unit-normalized pullback compositor.
Source: Stacks, Modules on Sites 03EL, Sites 00YV, and Cohomology on Sites 07A4
(blueprint: lem-pur-finite-pullback-tensor-chain-composition).

Proof: first work with two sheaves of modules. The defining unit-section formula
for proEtaleOrdinaryTensorPullback sends the unit of a pure tensor to the tensor
of its two units. The realization maps in moduleComp preserve precisely these
adjunction-unit sections. The fixed-scalar compositor is the comparison of the
composite adjunctions, and inserts their composite unit. Consequently both routes
send a unit section of m tensor n to the tensor of the two iterated unit sections,
with the same fibre-product identification of test objects. Apply the adjunction
hom-equivalence to the two candidate maps out of composite pullback. Maps from
the sheaf tensor are determined by pure tensors: the tensor universal property
proves this before sheafification, and the sheafification adjunction proves it
afterwards. Thus the two module maps agree. For complexes, precompose in degree
k with each direct-sum injection indexed by i+j=k. The definition of comparison
is the inverse ordinary tensor comparison on this summand, while complexComp
is moduleComp degree by degree. The module identity just established gives the
same summand map on both sides. Preservation of the total coproduct by the
left-adjoint pullbacks and coproduct extensionality give equality in every
degree. The signed differentials are already respected by the three existing
chain maps, so homological-complex morphism extensionality proves the equation.
No flatness, boundedness or derived localization is used. -/
theorem chain_composition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Z ⟶ X) (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ) :
    comparison l E (h ≫ f) n P Q ≫
      (totalTensor l E Z n).map (Prod.mkHom
        ((complexComp l E f h n).hom.app P) ((complexComp l E f h n).hom.app Q)) =
    (complexComp l E f h n).hom.app (tensor l E Y n P Q) ≫
      (pull l E h n).map (comparison l E f n P Q) ≫
      comparison l E h n ((pull l E f n).obj P) ((pull l E f n).obj Q) := by
  sorry

end WeilConjectures.FinitePullbackTensorRep
