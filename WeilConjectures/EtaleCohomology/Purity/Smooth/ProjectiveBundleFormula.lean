/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveFormulaLocalization

/-!
# The projective bundle formula

For the projective space `q : ℙⁿ_S = ℙ(Option n; S) ⟶ S` and the first Chern class `h` of a
hyperplane class, the map `(1, h, …, hⁿ) : ⊕ₐ Λ_S(-a)[-2a] ⟶ Rq_* Λ` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_projectiveFormulaMap`), and more generally for a projective bundle
(`AlgebraicGeometry.Etale.isIso_projectiveFormulaMap_of_projectiveBundle`). This is blueprint
`thm-pur-projective-bundle-formula`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open ProjectiveSpace

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ] (n : Type u)
  (S : Scheme.{u}) [HasInvertibleExponent Λ S]

variable {Λ n S}

variable [HasKummerClass.IsNormalized Λ] {k : Type u} [Field k] (aS : S ⟶ Spec (.of k))
  [IsSeparated aS] [LocallyOfFiniteType aS]

attribute [local instance] HasInvertibleExponent.opens

include aS in
/-- Blueprint `thm-pur-projective-bundle-formula`: Projective-bundle formula without purity

*The trivial bundle.* For the projective space `q : ℙⁿ_S = ℙ(Option n; S) ⟶ S`, `n` with `r`
elements, over a separated scheme of finite type over a field on which the exponent of `Λ` is
invertible, and `h = c₁(𝒪(1))` the first Chern class of a hyperplane class
(`AlgebraicGeometry.Etale.hyperplaneChernClass`),

`(1, h, …, hʳ) : ⊕_{a ≤ r} Λ_S(-a)[-2a] ⟶ Rq_* Λ_{ℙʳ_S}`

is an isomorphism. The blueprint states the formula for the projectivization `ℙ_B(F)` of any
vector bundle `F`; the projectivization of a vector bundle is not constructed in this repository,
and the formula for it follows from this case by restriction to trivialising opens.

By induction on `n` (`Fintype.induction_empty_option`) from `projectiveFormula_pempty`,
`projectiveFormula_of_equiv` and the localization step `projectiveFormula_option`
(in `WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveFormulaLocalization`). The
projectivization of a vector bundle, and more generally a projective bundle, is treated in
`WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveBundle`. -/
theorem isIso_projectiveFormulaMap [Fintype n]
    (γ : constantComplex Λ ℙ(Option n; S) ⟶ (R(hyperplane n S)_![ModuleCat.{u + 1} Λ]).obj
      ((R(hyperplane n S)^![ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ ℙ(Option n; S) ((1 : ℕ) : ℤ))⟦2 * ((1 : ℕ) : ℤ)⟧)))
    (hγ : IsHyperplaneClass Λ n S γ) :
    IsIso (projectiveFormulaMap (ℙ(Option n; S) ↘ S) (hyperplaneChernClass γ)
      (Fintype.card n)) := by
  have key : ∀ (n : Type u) [Fintype n], ProjectiveFormula Λ S n :=
    Fintype.induction_empty_option (P := fun n _ ↦ ProjectiveFormula Λ S n)
      (fun _ β _ e h ↦ letI := Fintype.ofEquiv β e.symm; projectiveFormula_of_equiv aS e h)
      projectiveFormula_pempty
      (fun _ _ h ↦ projectiveFormula_option aS h)
  exact key n γ hγ

end Etale

end AlgebraicGeometry
