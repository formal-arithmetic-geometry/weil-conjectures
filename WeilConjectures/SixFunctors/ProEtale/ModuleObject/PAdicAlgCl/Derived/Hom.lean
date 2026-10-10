/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived.Tensor

/-!

# The derived internal hom of module objects over `ℚ̄_ℓ`

Let `ℓ` be a prime and `X` a scheme, so that the derived category
`D(Mod_{ℚ̄_ℓ,X})` of module objects over the coefficient ring object `ℚ̄_ℓ,X` carries
the derived tensor product `- ⊗ᴸ_{ℚ̄_ℓ,X} -` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived.Tensor`. Under the
same hypotheses `D(Mod_{ℚ̄_ℓ,X})` is monoidal closed
(`WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed`), and this file defines the
*derived hom* `RHom_{ℚ̄_ℓ,X}(-, -)` of module objects to be the internal hom of that closed
structure, i.e. the right adjoint of the derived tensor product.

## Main definitions

- `AlgebraicGeometry.ProEtale.PadicAlgClRing.derivedHom` : the derived hom
  `RHom_{ℚ̄_ℓ,X}(-, -) : D(Mod_{ℚ̄_ℓ,X})ᵒᵖ ⥤ D(Mod_{ℚ̄_ℓ,X}) ⥤ D(Mod_{ℚ̄_ℓ,X})`, with scoped
  notation `RHom(X)⟦ℚ̄_ℓ⟧`.

## Main results

- `AlgebraicGeometry.ProEtale.PadicAlgClRing.derivedTensorHomAdjunction₂` : the adjunction
  with parameter `- ⊗ᴸ_{ℚ̄_ℓ,X} - ⊣₂ RHom_{ℚ̄_ℓ,X}(-, -)`.

- `AlgebraicGeometry.ProEtale.PadicAlgClRing.derivedTensorHomAdjunction` : its unary shadow,
  the adjunction `K ⊗ᴸ_{ℚ̄_ℓ,X} - ⊣ RHom_{ℚ̄_ℓ,X}(K, -)` for a fixed `K : D(Mod_{ℚ̄_ℓ,X})`.

## Implementation notes

This is the module-object counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom`. The closedness of
`D(Mod_{ℚ̄_ℓ,X})` is the sorried instance `DerivedCategory.monoidalClosed`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale.PadicAlgClRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})

/-- The derived hom `RHom_{ℚ̄_ℓ,X}(-, -) : D(Mod_{ℚ̄_ℓ,X})ᵒᵖ ⥤ D(Mod_{ℚ̄_ℓ,X}) ⥤ D(Mod_{ℚ̄_ℓ,X})`
on the unbounded derived category of module objects over the coefficient ring object `ℚ̄_ℓ,X`:
the internal hom of the monoidal closed structure on `D(Mod_{ℚ̄_ℓ,X})`, i.e. the right adjoint
of the derived tensor product `- ⊗ᴸ_{ℚ̄_ℓ,X} -`. -/
@[implicit_reducible]
noncomputable def derivedHom :
    (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClSheaf X ℓ)))ᵒᵖ ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (padicAlgClSheaf X ℓ)) ⥤
        DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (padicAlgClSheaf X ℓ)) :=
  MonoidalClosed.internalHom

@[inherit_doc derivedHom]
scoped notation "RHom(" X ")⟦ℚ̄_" ℓ "⟧" => derivedHom ℓ X

/-- The derived hom of module objects over `ℚ̄_ℓ,X` is right adjoint to the derived tensor
product, as an adjunction with a parameter: `- ⊗ᴸ_{ℚ̄_ℓ,X} - ⊣₂ RHom_{ℚ̄_ℓ,X}(-, -)`. -/
noncomputable def derivedTensorHomAdjunction₂ : -⊗ᴸ-(X)⟦ℚ̄_ℓ⟧ ⊣₂ RHom(X)⟦ℚ̄_ℓ⟧ :=
  MonoidalClosed.internalHomAdjunction₂

variable {X}

/-- For a fixed `K : D(Mod_{ℚ̄_ℓ,X})`, the derived tensor product `K ⊗ᴸ_{ℚ̄_ℓ,X} -` is left
adjoint to the derived hom `RHom_{ℚ̄_ℓ,X}(K, -)`. -/
noncomputable def derivedTensorHomAdjunction
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClSheaf X ℓ))) :
    (-⊗ᴸ-(X)⟦ℚ̄_ℓ⟧).obj K ⊣ (RHom(X)⟦ℚ̄_ℓ⟧).obj (op K) :=
  (derivedTensorHomAdjunction₂ ℓ X).adj K

/-- The derived hom `RHom_{ℚ̄_ℓ,X}(K, -)` is a right adjoint. -/
instance isRightAdjoint_derivedHom_obj
    (K : (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClSheaf X ℓ)))ᵒᵖ) :
    ((RHom(X)⟦ℚ̄_ℓ⟧).obj K).IsRightAdjoint :=
  (derivedTensorHomAdjunction ℓ K.unop).isRightAdjoint

end AlgebraicGeometry.ProEtale.PadicAlgClRing
