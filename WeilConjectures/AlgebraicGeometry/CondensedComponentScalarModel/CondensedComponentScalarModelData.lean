/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedScalarRealization
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Irreducible

/-! # Scalar models on reduced irreducible components

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Theorem 4.13,
finite-component reduction (blueprint: def-pod-condensed-component-scalar-model-data).
The component schemes are the actual reduced induced closed subschemes. The model
predicate uses their small pro-etale sites and the original scalar-realization functor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedComponentScalarModel

/-- The reduced induced scheme on an irreducible component, formed from its vanishing ideal.
Source: HRS Theorem 4.13, finite-component reduction
(blueprint: def-pod-condensed-component-scalar-model-data). -/
def component (X : Scheme.{u}) (Z : irreducibleComponents X) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal
    ⟨Z.val, isClosed_of_mem_irreducibleComponents _ Z.property⟩).subscheme

/-- The canonical closed inclusion of the reduced component into the original scheme.
Source: HRS Theorem 4.13, finite-component reduction
(blueprint: def-pod-condensed-component-scalar-model-data). -/
def inclusion (X : Scheme.{u}) (Z : irreducibleComponents X) : component X Z ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal
    ⟨Z.val, isClosed_of_mem_irreducibleComponents _ Z.property⟩).subschemeι

/-- The inclusion is the existing closed immersion of the vanishing-ideal subscheme.
Source: Stacks 01IQ; HRS Theorem 4.13
(blueprint: def-pod-condensed-component-scalar-model-data). -/
instance inclusionClosed (X : Scheme.{u}) (Z : irreducibleComponents X) :
    IsClosedImmersion (inclusion X Z) := by
  unfold inclusion
  infer_instance

/-- Reduced components of an affine scheme are affine, since their inclusions are affine.
Source: Stacks 01IQ; HRS Theorem 4.13
(blueprint: def-pod-condensed-component-scalar-model-data). -/
instance componentAffine (X : Scheme.{u}) [IsAffine X] (Z : irreducibleComponents X) :
    IsAffine (component X Z) := isAffine_of_isAffineHom (inclusion X Z)

/-- The underlying space of the vanishing-ideal subscheme is its irreducible support.
Source: Stacks 004W; HRS Theorem 4.13
(blueprint: def-pod-condensed-component-scalar-model-data). -/
instance componentIrreducible (X : Scheme.{u}) (Z : irreducibleComponents X) :
    IrreducibleSpace (component X Z) :=
  Subtype.irreducibleSpace Z.property.1

/-- The image of the reduced component is precisely the original closed component.
Source: the vanishing-ideal construction; HRS Theorem 4.13
(blueprint: def-pod-condensed-component-scalar-model-data). -/
theorem range_inclusion (X : Scheme.{u}) (Z : irreducibleComponents X) :
    Set.range (inclusion X Z) = Z.val := by
  exact (Scheme.IdealSheafData.vanishingIdeal
    ⟨Z.val, isClosed_of_mem_irreducibleComponents _ Z.property⟩).range_subschemeι

/-- A fixed scalar complex models the restriction on every w-contractible affine test
of a particular reduced component. The inverse image is along the actual composite.
Source: HRS Theorem 4.13, irreducible case and finite-component reduction
(blueprint: def-pod-condensed-component-scalar-model-data). -/
def HasModel (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
    (P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X)))
    (Z : irreducibleComponents X) : Prop :=
  ∀ W : (component X Z).ProEt, IsAffine W.left → IsWContractibleRing Γ(W.left, ⊤) →
    Nonempty ((CondensedRing.upperStar Λ.X (W.hom ≫ inclusion X Z)).mapDerivedCategory.obj K ≅
      (condensedScalarRealization Λ.X W.left).obj P)

/-- Isomorphic scalar complexes give the same component-model predicate. The map is the
image of the specified scalar isomorphism, so it changes neither pullback nor realization.
Source: functoriality of HRS (3.2), Theorem 4.13, finite-component argument
(blueprint: def-pod-condensed-component-scalar-model-data). -/
theorem HasModel.of_iso (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (X : Scheme.{u})
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
    {P Q : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X))}
    {Z : irreducibleComponents X} (h : HasModel Λ X K P Z) (a : P ≅ Q) :
    HasModel Λ X K Q Z := by
  intro W hW hw
  obtain ⟨e⟩ := h W hW hw
  exact ⟨e ≪≫ (condensedScalarRealization Λ.X W.left).mapIso a⟩

end AlgebraicGeometry.ProEtale.CondensedComponentScalarModel
