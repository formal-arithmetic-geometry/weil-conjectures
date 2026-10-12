/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs
public import WeilConjectures.SixFunctors.ProEtale.Derived.Constructible

/-!
# The bounded constructible complete category `Dᵇc(T_proét, A)`

Let `R` be a commutative ring with an ideal `I` (an adic coefficient datum `(A, I)`, with
`P_n = A/Iⁿ`), and let `T` be a scheme. Following blueprint
`def-weil-pbc-bounded-constructible-complete`, an object `K` of `D(T_proét, R)` lies in
`Dᵇc(T_proét, A)` if

- `K` is derived `I`-complete (`DerivedCategory.derivedComplete`), i.e. `K ≅ R lim_n K_n`
  along the reduction maps to its reductions `K_n = K ⊗ᴸ R/Iⁿ`;
- the reduction tower `n ↦ K_n` (`DerivedCategory.derivedCompletionDiagram`) has étale origins
  and is uniformly bounded constructible: there are `a ≤ b` such that every `K_n` is
  `ν^* L_n` for a bounded constructible étale complex `L_n`, with cohomology in `[a, b]`
  (`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleIn`).

The étale origins of the levels are automatically compatible with the transition maps of the
tower: `D(ν^*)` is fully faithful on bounded below complexes
(`AlgebraicGeometry.ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map`), so the
transition maps `K_{n+1} ⟶ K_n` come from unique maps `L_{n+1} ⟶ L_n`.

## Implementation notes

The derived category `D(T_proét, A)` is modelled, following the project convention of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`, as the derived category of
sheaves of `R`-modules on the pro-étale site, and derived `I`-completeness is the homotopy-limit
condition of that file (Stacks, Tags 091N and 091Z) rather than the Koszul formulation of the
blueprint's intrinsic completion, to which it is equivalent (`prop-weil-pbc-koszul-reconstruction`,
recorded there as classical input). The levels `K_n` are sheaves of `R`-modules killed by `Iⁿ`,
and their bounded constructibility is that of `Dᵇc_proét(T, R)`.

The standing assumptions of the blueprint (`T` noetherian of finite dimension, the torsion
orders invertible on `T`) are not part of the definition.

-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R] (I : Ideal R)

/-- Derived `I`-complete objects of `D(J, R)` whose reductions `K ⊗ᴸ R/Iⁿ` satisfy a property
`P a b` for fixed `a, b` and all `n`: the shape of the bounded constructible complete category,
with `P a b` the bounded constructible objects with cohomology in `[a, b]`.

It is stated for a general site, as the definitions of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`, so that the derived monoidal
structure is only unfolded at a generic site (see the implementation notes there). -/
def completeWithUniformReductions
    (P : ℤ → ℤ → ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))) :
    ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  fun K ↦ derivedComplete J I K ∧
    ∃ a b : ℤ, ∀ n : ℕ, P a b ((derivedCompletionDiagram J I K).obj (Opposite.op n))

variable {J I}

lemma completeWithUniformReductions.derivedComplete
    {P : ℤ → ℤ → ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))}
    {K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (hK : completeWithUniformReductions J I P K) : derivedComplete J I K :=
  hK.1

lemma completeWithUniformReductions.exists_forall
    {P : ℤ → ℤ → ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))}
    {K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (hK : completeWithUniformReductions J I P K) :
    ∃ a b : ℤ, ∀ n : ℕ, P a b ((derivedCompletionDiagram J I K).obj (Opposite.op n)) :=
  hK.2

end DerivedCategory

namespace AlgebraicGeometry.ProEtale

variable {R : Type (u + 1)} [CommRing R] (I : Ideal R) (T : Scheme.{u})

/-- Blueprint `def-weil-pbc-bounded-constructible-complete`: Bounded constructible complete
category.

An object `K` of `D(T_proét, R)` is *bounded constructible complete* if it is derived
`I`-complete and its tower of reductions `K_n = K ⊗ᴸ R/Iⁿ` is uniformly bounded constructible of
étale origin: there are `a, b` such that each `K_n` lies in `D_c^[a, b]_proét(T, R)`, i.e. is
`ν^*` of a bounded constructible étale complex and has cohomology in `[a, b]`. -/
def DerivedCategory.boundedConstructibleComplete :
    ObjectProperty
      (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R))) :=
  _root_.DerivedCategory.completeWithUniformReductions (Scheme.ProEt.topology T) I
    (DerivedCategory.constructibleIn (ModuleCat.{u + 1} R) T)

/-- Blueprint `def-weil-pbc-bounded-constructible-complete`: the bounded constructible complete
category `Dᵇc(T_proét, A)`, the full subcategory of `D(T_proét, R)` of bounded constructible
complete objects (`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleComplete`). -/
def DerivedCategoryBoundedConstructibleComplete : Type _ :=
  (DerivedCategory.boundedConstructibleComplete I T).FullSubcategory

noncomputable instance : Category (DerivedCategoryBoundedConstructibleComplete I T) :=
  inferInstanceAs <| Category (DerivedCategory.boundedConstructibleComplete I T).FullSubcategory

/-- The inclusion of `Dᵇc(T_proét, A)` into `D(T_proét, R)`. -/
noncomputable def DerivedCategoryBoundedConstructibleComplete.ι :
    DerivedCategoryBoundedConstructibleComplete I T ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R)) :=
  (DerivedCategory.boundedConstructibleComplete I T).ι

end AlgebraicGeometry.ProEtale
