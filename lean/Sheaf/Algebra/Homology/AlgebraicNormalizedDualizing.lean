/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.Algebra.Homology.RingHomExtensionDefs
public import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus

/-! # Algebraic dualizing complexes and local normalization

Source: Stacks Project, dualizing.tex, Definition 0A7B and Section 0A7M,
opening paragraph (blueprint: def-per-algebraic-normalized-dualizing).

Ordinary modules are encoded on the existing one-object site with bottom topology.
The scalar-action map is the transpose of the left unitor under the existing
representative-normalized tensor--Hom adjunction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

/-- Transport an ordinary module to the one-object bottom-topology ringed site.
Source: Stacks Project, 0A7B, ordinary modules viewed on the one-object ringed site
(blueprint: def-per-algebraic-normalized-dualizing). This is the constant module,
with identity restriction maps; no object is chosen from an existence assertion. -/
def algebraicDualizingModuleSheaf (A : Type u) [CommRing A] (M : ModuleCat.{u} A) :
    RingSiteModules A where
  val :=
    { obj := fun _ ↦ M
      map := fun _ ↦ ModuleCat.ofHom (LinearMap.id : M →ₗ[A] M) }
  isSheaf := Presheaf.isSheaf_bot _

end CategoryTheory

namespace DerivedCategory

/-- The canonical homothety A[0] → RHom(Ω,Ω), as the transpose of scalar evaluation.
Source: Stacks Project, Definition 0A7B
(blueprint: def-per-algebraic-normalized-dualizing).
The evaluation-normalized adjunction sends this unitor to multiplication by a scalar
on a K-flat/K-injective representative, so it specifies the actual scalar-action map. -/
def algebraicDualizingScalarAction (A : Type u) [CommRing A]
    [HasDerivedCategory.{u} (RingSiteModules A)]
    (Ω : DerivedCategory (RingSiteModules A)) :
    𝟙_ (DerivedCategory (RingSiteModules A)) ⟶
      (SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf A) Ω).obj Ω :=
  (SignedRingedHom.adjunction ⊥ (CochainComplex.onePointRingSheaf A) Ω).homEquiv _ _
    (λ_ Ω).hom

/-- An algebraic dualizing complex over a commutative Noetherian ring has a bounded
injective representative, finite cohomology in every degree, and invertible scalar action.
Source: Stacks Project, Definition 0A7B; finite injective dimension as in 0A5R
(blueprint: def-per-algebraic-normalized-dualizing). The bounds are on the terms of
an injective representative, not merely on its cohomology. -/
def IsAlgebraicDualizing (A : Type u) [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{u} (RingSiteModules A)]
    (Ω : DerivedCategory (RingSiteModules A)) : Prop :=
  (∃ I : CochainComplex (RingSiteModules A) ℤ,
    (∀ i : ℤ, Injective (I.X i)) ∧
    (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (I.X i)) ∧
    Nonempty (DerivedCategory.Q.obj I ≅ Ω)) ∧
  (∀ j : ℤ, Module.Finite A
    (((homologyFunctor (RingSiteModules A) j).obj Ω).val.obj (op ⟨PUnit.unit⟩))) ∧
  IsIso (algebraicDualizingScalarAction A Ω)

/-- Local normalization of an algebraic dualizing complex: RHom(κ[0],Ω) ≅ κ[0],
where κ is the residue field with its canonical A-module structure.
Source: Stacks Project, Section 0A7M, opening paragraph
(blueprint: def-per-algebraic-normalized-dualizing). The underlying dualizing
conditions are retained in this predicate. No choice of a residue-field isomorphism
or of an injective resolution is part of its data. -/
def IsNormalizedAlgebraicDualizing (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [HasDerivedCategory.{u} (RingSiteModules A)]
    (Ω : DerivedCategory (RingSiteModules A)) : Prop :=
  IsAlgebraicDualizing A Ω ∧
  Nonempty
    ((SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf A)
      ((DerivedCategory.singleFunctor (RingSiteModules A) 0).obj
        (algebraicDualizingModuleSheaf A (ModuleCat.of A (IsLocalRing.ResidueField A))))).obj Ω ≅
      (DerivedCategory.singleFunctor (RingSiteModules A) 0).obj
        (algebraicDualizingModuleSheaf A (ModuleCat.of A (IsLocalRing.ResidueField A))))

end DerivedCategory
