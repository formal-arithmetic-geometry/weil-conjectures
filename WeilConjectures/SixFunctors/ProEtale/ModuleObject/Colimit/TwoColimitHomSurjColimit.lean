/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendChangeTransfer
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClUnderived

/-!
# `Res_E(ℚ̄_ℓ,X ⊗_{F_X} Y)` as a filtered colimit of complexes

Let `ℓ` be a prime, `X` a scheme and `E, F ≤ G` finite subextensions of `ℚ̄_ℓ`. For a finite
subextension `k ⊇ E, F`, the adjoint transfers (`CategoryTheory.Adjunction.compIsoTransfer`) of
the transitivity isomorphisms of the extensions of scalars give `E_X`-linear maps
```
Res_{E→k}(k_X ⊗_{F_X} M) ⟶ Res_{E→k'}(k'_X ⊗_{F_X} M),   Res_{E→k}(k_X ⊗_{F_X} M) ⟶
Res_{E→Ω}(ℚ̄_ℓ,X ⊗_{F_X} M)
```
(`ProEtale.subfieldExtendScalarsTransfer`, `ProEtale.subfieldExtendScalarsTransferToPadicAlgCl`),
whose underlying maps are `x ⊗ m ↦ x ⊗ m` (`Mod.extendChangeHom`). For a complex `Y` of
`F_X`-modules, these form a diagram of complexes of `E_X`-modules over the finite
subextensions `k ⊇ G` (`ProEtale.subfieldExtendScalarsDiagram`) with a cocone of vertex
`Res_{E→Ω}(ℚ̄_ℓ,X ⊗_{F_X} Y)` (`ProEtale.subfieldExtendScalarsCocone`), which is a colimit cocone
(`ProEtale.isColimitSubfieldExtendScalarsCocone`): colimits of complexes are computed degreewise,
colimits of module objects on the underlying objects, and
`ℚ̄_ℓ,X ⊗_{F_X} M = colim_k k_X ⊗_{F_X} M` (`Mod.isColimitExtendScalarsColimitCocone`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod

variable {C : Type*} [Category C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R : C} [MonObj R] [IsCommMonObj R]

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

section Transfer

variable {E F k k' : FiniteIntermediateField ℓ}

end Transfer

section Diagram

variable {E F G : FiniteIntermediateField ℓ} (hE : E ≤ G) (hF : F ≤ G)
  (Y : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ℤ)

end Diagram

end AlgebraicGeometry.ProEtale
