/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.FiniteDerived
public import WeilConjectures.ConstructibleSheaf.Noetherian

/-!
# Constructibility of direct images along open immersions

Let `Λ` be a finite commutative ring, `X` a scheme of finite type over a field and
`j : U ⟶ X` an open immersion. For a constructible sheaf `F` of `Λ`-modules on `U_ét` the
direct image `j_* F` is constructible on `X_ét`
(`AlgebraicGeometry.Etale.isConstructibleSheaf_lowerStar_of_isOpenImmersion`, blueprint
`thm-fin-open-degree-zero`), and so is the boundary sheaf `i^* j_* F` on the closed complement
`i : Z ⟶ X` (`AlgebraicGeometry.Etale.isConstructibleSheaf_upperStar_lowerStar_of_isOpenImmersion`,
blueprint `lem-fin-boundary-sheaf`).
-/

@[expose] public section

universe u

open CategoryTheory Limits
open AlgebraicGeometry.Etale

noncomputable section

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- Blueprint `thm-fin-open-degree-zero`: Constructibility of the degree-zero open direct image.

Let `X` be of finite type over a field `k`, `j : U ⟶ X` an open immersion and `F` a
constructible sheaf of modules over a finite commutative ring `Λ` on `U_ét`. Then `j_* F` is
constructible on `X_ét`. -/
theorem isConstructibleSheaf_lowerStar_of_isOpenImmersion {k : Type u} [Field k]
    {U X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    IsConstructibleSheaf ((j)_*[ModuleCat.{u + 1} Λ].obj F) :=
  sorry

/-- Blueprint `lem-fin-boundary-sheaf`: Boundary sheaf of an open immersion.

Let `X` be of finite type over a field `k`, `j : U ⟶ X` an open immersion, `i : Z ⟶ X` a
closed immersion onto the closed complement of `U`, and `F` a constructible sheaf of
`Λ`-modules on `U_ét`. Then the boundary sheaf `i^* j_* F` is constructible on `Z_ét`. -/
theorem isConstructibleSheaf_upperStar_lowerStar_of_isOpenImmersion {k : Type u} [Field k]
    {U X Z : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (j : U ⟶ X) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
    (_hij : Set.range i.base = (Set.range j.base)ᶜ)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    IsConstructibleSheaf ((i)^*[ModuleCat.{u + 1} Λ].obj ((j)_*[ModuleCat.{u + 1} Λ].obj F)) :=
  have := isConstructibleSheaf_lowerStar_of_isOpenImmersion aX j F
  IsConstructibleSheaf.upperStar i _

end Etale

end AlgebraicGeometry

end
