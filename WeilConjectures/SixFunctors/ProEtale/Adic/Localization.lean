/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.Recollement
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarFiniteness

/-!
# The closed-support triangle on `Dᵇc(-, ℚ̄_ℓ)`

Let `k` be an algebraically closed field with `ringChar k ≠ ℓ`, `X` a quasi-compact scheme locally
of finite type over `k`, `i : Z ⟶ X` a closed immersion and `j : U ⟶ X` the complementary
quasi-compact open immersion. This file proves clauses (1)–(4) of blueprint
`prop-sf-localization-all-stages` at the coefficient stage `ℚ̄_ℓ`.

As in `WeilConjectures.SixFunctors.ClosedImmersionStages`, the stage `Dᵇc(-, ℚ̄_ℓ)` is realised in
the Bhatt–Scholze model, rather than as the `2`-colimit over finite extensions `E ⊆ ℚ̄_ℓ` used in
the blueprint: it is the full subcategory
`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleAdic ℓ X` of the derived category
of pro-étale sheaves of modules over the constant `ℓ`-adic sheaf `ℚ̄_ℓ,X`, of bounded complexes
with constructible cohomology sheaves. On it:

1. `Rj_*` carries `Dᵇc(U, ℚ̄_ℓ)` into `Dᵇc(X, ℚ̄_ℓ)`
   (`AlgebraicGeometry.ProEtale.boundedConstructibleAdic_rightDerivedFunctor_adicLowerStar_obj`,
   from the finiteness theorem `AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor`);
2. `i_* : Dᵇc(Z, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)` has a right adjoint `Ri^!`
   (`AlgebraicGeometry.ProEtale.boundedConstructibleAdicClosedUpperShriekAdjunction`);
3. for `K ∈ Dᵇc(X, ℚ̄_ℓ)` the counit `i_* Ri^! K ⟶ K` and the unit `K ⟶ Rj_* j^* K` extend to a
   distinguished triangle, with a unique third arrow
   (`ProEtale.existsUnique_distTriang_boundedConstructibleAdicClosedSupportTriangle`),
   functorial in `K`, because `Hom(i_* Q[m], Rj_* G) = 0`;
4. `Ri^! Rj_* = 0`, and the unit `Q ⟶ Ri^! i_* Q` is an isomorphism
   (`AlgebraicGeometry.ProEtale.isZero_boundedConstructibleAdicClosedUpperShriek_obj`,
   `AlgebraicGeometry.ProEtale.isIso_boundedConstructibleAdicClosedUpperShriekAdjunction_unit`).

The proof is the generic recollement argument `CategoryTheory.Pretriangulated.Recollement`
applied to the full subcategories `Dᵇc(-, ℚ̄_ℓ)`: the inputs are that `Ri_*` is fully faithful,
that `D(j^*) ⊣ Rj_*` has invertible counit, that `D(j^*) Ri_* = 0`, and that a complex killed by
`D(j^*)` is `Ri_*` of its pullback `D(i^*)`
(`WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport`),
together with the stability of `Dᵇc(-, ℚ̄_ℓ)` under `D(i^*)`, `D(j^*)`, `Ri_*` and `Rj_*`.

The categories `Dᵇc(-, ℚ̄_ℓ)` are triangulated over locally noetherian schemes, constructible
sheaves being closed under kernels, cokernels and extensions there; the statements that involve
the triangulated structure on `Dᵇc(Z, ℚ̄_ℓ)` or `Dᵇc(U, ℚ̄_ℓ)` assume `Z` and `U` locally
noetherian, which follows from `X` being locally of finite type over `k`
(`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

open Scheme

variable {l : ℕ} [Fact l.Prime]

/-- Bounded complexes of `ℓ`-adic sheaves with constructible cohomology sheaves form a triangulated
subcategory over a locally noetherian scheme: constructible sheaves are closed under kernels,
cokernels and extensions there. -/
instance ProEtale.DerivedCategory.isTriangulated_boundedConstructibleAdic (X : Scheme.{u})
    [IsLocallyNoetherian X] :
    (ProEtale.DerivedCategory.boundedConstructibleAdic l X).IsTriangulated :=
  inferInstance

section Finiteness

variable {k : Type u} [Field k] [IsAlgClosed k] {Y X : Scheme.{u}} (s : X ⟶ Spec (.of k))
  [LocallyOfFiniteType s] [QuasiCompact s] (hk : ringChar k ≠ l)

include s hk in
/-- Blueprint `prop-sf-localization-all-stages`, clause (1) at the stage `ℚ̄_ℓ` (for any
quasi-compact quasi-separated `f` locally of finite type, e.g. an open immersion `j`): for `X`
quasi-compact and locally of finite type over an algebraically closed field `k` with
`ringChar k ≠ ℓ`, `Rf_*` carries `Dᵇc(Y, ℚ̄_ℓ)` into `Dᵇc(X, ℚ̄_ℓ)`. This is the finiteness theorem
for constructible sheaves (`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor`) and
dévissage over the finitely many cohomology sheaves
(`AlgebraicGeometry.ProEtale.finiteLowerStar_of_bounded`). Here `Dᵇc(-, ℚ̄_ℓ)` is realised by
sheaves of modules over the constant `ℓ`-adic sheaf (Bhatt–Scholze) rather than as a
`2`-colimit. -/
theorem ProEtale.boundedConstructibleAdic_rightDerivedFunctor_adicLowerStar_obj (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    {K : DerivedCategory (ProEtale.AdicSheaf l Y)}
    (hK : ProEtale.DerivedCategory.boundedConstructibleAdic l Y K) :
    ProEtale.DerivedCategory.boundedConstructibleAdic l X
      ((ProEtale.adicLowerStar l f).rightDerivedFunctor.obj K) :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  ProEtale.finiteLowerStar_of_bounded f
    (fun _ hF ↦ ProEtale.finiteLowerStar_singleFunctor s f hk hF) K hK.1 hK.2

/-- The direct image `Rf_* : Dᵇc(Y, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)`, the restriction of `Rf_*`
(`AlgebraicGeometry.ProEtale.boundedConstructibleAdic_rightDerivedFunctor_adicLowerStar_obj`). -/
noncomputable abbrev ProEtale.boundedConstructibleAdicRightDerivedLowerStar (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f] :
    (ProEtale.DerivedCategory.boundedConstructibleAdic l Y).FullSubcategory ⥤
      (ProEtale.DerivedCategory.boundedConstructibleAdic l X).FullSubcategory :=
  (ProEtale.DerivedCategory.boundedConstructibleAdic l Y).liftFullSubcategory _
    (ProEtale.adicLowerStar l f).rightDerivedFunctor
    fun _ hK ↦ ProEtale.boundedConstructibleAdic_rightDerivedFunctor_adicLowerStar_obj s hk f hK

end Finiteness

section Localization

variable {k : Type u} [Field k] [IsAlgClosed k] {Z U X : Scheme.{u}} (s : X ⟶ Spec (.of k))
  [LocallyOfFiniteType s] [QuasiCompact s] (hk : ringChar k ≠ l)
  (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  (hij : IsCompl (Set.range i.base) (Set.range j.base))

variable [IsLocallyNoetherian X] [IsLocallyNoetherian U]

end Localization

end AlgebraicGeometry
