/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Noetherian
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Dévissage of a constructible sheaf

A constructible sheaf `F` of `Λ`-modules on a Noetherian scheme `X` has a finite filtration
`0 = F₀ ⊆ F₁ ⊆ ⋯ ⊆ F_m = F` whose subquotients are extensions by zero of lisse sheaves along
locally closed immersions (`AlgebraicGeometry.Etale.exists_filtration_isFiniteLocallyConstant`,
blueprint `lem-fin-constructible-devissage`). A locally closed immersion is written as a closed
immersion `i : Y ⟶ W` into an open subscheme `W ⊆ X`, and the extension by zero along it is
`(W.ι)_! ∘ i_*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open AlgebraicGeometry.Etale

noncomputable section

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- Blueprint `lem-fin-constructible-devissage`: Dévissage of a constructible sheaf.

Let `X` be Noetherian (in the blueprint: of finite type over a field) and `F` a constructible
sheaf of `Λ`-modules on `X_ét`. There is a finite filtration by subsheaves
`0 = F₀ ⊆ F₁ ⊆ ⋯ ⊆ F_m = F` and, for each `1 ≤ r ≤ m`, a locally closed subscheme of `X`, given
as a closed immersion `i_r : Y_r ⟶ W_r` into an open `W_r ⊆ X`, with a finite locally constant
sheaf `L_r` on `Y_r`, such that `F_r / F_{r-1} ≅ (W_r ⟶ X)_! (i_r)_* L_r`. The filtration need
not split. -/
theorem Etale.exists_filtration_isFiniteLocallyConstant {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    ∃ (m : ℕ) (Fil : Fin (m + 1) → Subobject F), Monotone Fil ∧ IsZero (Subobject.underlying.obj (Fil 0)) ∧
      Fil (Fin.last m) = ⊤ ∧ ∀ (r : Fin m) (h : Fil r.castSucc ≤ Fil r.succ),
        ∃ (W : X.Opens) (Y : Scheme.{u}) (i : Y ⟶ W) (_ : IsClosedImmersion i)
          (L : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
          IsFiniteLocallyConstantSheaf L ∧
            Nonempty (cokernel (Subobject.ofLE _ _ h) ≅
              (W.ι)_!open[ModuleCat.{u + 1} Λ].obj ((i)_*[ModuleCat.{u + 1} Λ].obj L)) :=
  sorry

end AlgebraicGeometry

end
