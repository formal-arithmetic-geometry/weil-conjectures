/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.Derived.Tensor

/-!

# The derived internal hom of module objects over `C(-, T)`

Let `T` be a commutative topological ring and `X` a scheme, so that the derived category
`D(Mod_{A_X(T)})` of module objects over the coefficient ring object `A_X(T) = C(-, T)` carries
the derived tensor product `- ⊗ᴸ_{A_X(T)} -` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.Derived.Tensor`. Under the
same hypotheses `D(Mod_{A_X(T)})` is monoidal closed
(`WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed`), and this file defines the
*derived hom* `RHom_{A_X(T)}(-, -)` of module objects to be the internal hom of that closed
structure, i.e. the right adjoint of the derived tensor product.

## Main definitions

- `AlgebraicGeometry.ProEtale.ContinuousMapRing.derivedHom` : the derived hom
  `RHom_{A_X(T)}(-, -) : D(Mod_{A_X(T)})ᵒᵖ ⥤ D(Mod_{A_X(T)}) ⥤ D(Mod_{A_X(T)})`, with scoped
  notation `RHom(X)⟦T⟧`.

## Main results

- `AlgebraicGeometry.ProEtale.ContinuousMapRing.derivedTensorHomAdjunction₂` : the adjunction
  with parameter `- ⊗ᴸ_{A_X(T)} - ⊣₂ RHom_{A_X(T)}(-, -)`.

- `AlgebraicGeometry.ProEtale.ContinuousMapRing.derivedTensorHomAdjunction` : its unary shadow,
  the adjunction `K ⊗ᴸ_{A_X(T)} - ⊣ RHom_{A_X(T)}(K, -)` for a fixed `K : D(Mod_{A_X(T)})`.

## Implementation notes

This is the module-object counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom`. The closedness of
`D(Mod_{A_X(T)})` is the sorried instance `DerivedCategory.monoidalClosed`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale.ContinuousMapRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] (X : Scheme.{u})

/-- The derived hom `RHom_{A_X(T)}(-, -) : D(Mod_{A_X(T)})ᵒᵖ ⥤ D(Mod_{A_X(T)}) ⥤ D(Mod_{A_X(T)})`
on the unbounded derived category of module objects over the coefficient ring object `A_X(T)`:
the internal hom of the monoidal closed structure on `D(Mod_{A_X(T)})`, i.e. the right adjoint
of the derived tensor product `- ⊗ᴸ_{A_X(T)} -`. -/
@[implicit_reducible]
noncomputable def derivedHom :
    (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (continuousMapRingObj T X)))ᵒᵖ ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (continuousMapRingObj T X)) ⥤
        DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (continuousMapRingObj T X)) :=
  MonoidalClosed.internalHom

@[inherit_doc derivedHom]
scoped notation "RHom(" X ")⟦" T "⟧" => derivedHom T X

/-- The derived hom of module objects over `A_X(T)` is right adjoint to the derived tensor
product, as an adjunction with a parameter: `- ⊗ᴸ_{A_X(T)} - ⊣₂ RHom_{A_X(T)}(-, -)`. -/
noncomputable def derivedTensorHomAdjunction₂ : -⊗ᴸ-(X)⟦T⟧ ⊣₂ RHom(X)⟦T⟧ :=
  MonoidalClosed.internalHomAdjunction₂

variable {X}

/-- For a fixed `K : D(Mod_{A_X(T)})`, the derived tensor product `K ⊗ᴸ_{A_X(T)} -` is left
adjoint to the derived hom `RHom_{A_X(T)}(K, -)`. -/
noncomputable def derivedTensorHomAdjunction
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (continuousMapRingObj T X))) :
    (-⊗ᴸ-(X)⟦T⟧).obj K ⊣ (RHom(X)⟦T⟧).obj (op K) :=
  (derivedTensorHomAdjunction₂ T X).adj K

/-- The derived hom `RHom_{A_X(T)}(K, -)` is a right adjoint. -/
instance isRightAdjoint_derivedHom_obj
    (K : (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (continuousMapRingObj T X)))ᵒᵖ) :
    ((RHom(X)⟦T⟧).obj K).IsRightAdjoint :=
  (derivedTensorHomAdjunction T K.unop).isRightAdjoint

end AlgebraicGeometry.ProEtale.ContinuousMapRing
