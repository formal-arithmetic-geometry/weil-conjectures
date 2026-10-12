/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.Derived.HomComparison

/-!
# The derived comparison pullback is braided

Let `ν^* : Sh(X_ét, A) ⥤ Sh(X_proét, A)` be the comparison pullback. It is a braided monoidal
functor, being the strong monoidal left adjoint of the lax braided restriction `ν_*`, and so is
its total left derived functor `Lν^* : D(X_ét) ⥤ D(X_proét)` when `ν^*` preserves flat
sheaves. In particular `Lν^*` has a canonical comparison map `ν^* RHom(K, M) ⟶ RHom(ν^* K, ν^* M)`
(`CategoryTheory.Functor.LaxMonoidal.ihomComparison`), which is an isomorphism on constructible
complexes of finite Tor amplitude (blueprint `lem-weil-finite-duality-site-comparison`).

## Main definitions

- `AlgebraicGeometry.ProEtale.braided_comparisonUpperStar`: `ν^*` is braided.
- `AlgebraicGeometry.ProEtale.leftDerivedComparisonUpperStarBraided`: `Lν^*` is braided.

## Main statements

- `AlgebraicGeometry.ProEtale.isIso_leftDerivedComparisonUpperStarIhomComparison`
  (`lem-weil-finite-duality-site-comparison`): the canonical comparison
  `ν^* RHom(K, M) ⟶ RHom(ν^* K, ν^* M)` is an isomorphism for `K ∈ Dctf(X_ét, Λ)` and
  `M ∈ Dᵇc(X_ét, Λ)`.
-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

variable (X : Scheme.{u})

/-- The restriction `ν_*` from pro-étale to étale sheaves is lax braided, being the pushforward
along the continuous inclusion of sites. -/
noncomputable instance laxBraided_comparisonLowerStar : ν_*(X)[A].LaxBraided := by
  unfold comparisonLowerStar
  infer_instance

/-- The comparison pullback `ν^*` is braided: it is the strong monoidal left adjoint of the lax
braided restriction `ν_*`, for a monoidal adjunction. Its monoidal structure is
`AlgebraicGeometry.ProEtale.monoidal_comparisonUpperStar`. -/
noncomputable instance braided_comparisonUpperStar : ν^*(X)[A].Braided :=
  { monoidal_comparisonUpperStar A X with
    braided := (comparisonAdjunction A X).μ_comp_map_braiding }

variable [Abelian.HasFunctorialFlatResolution A] [(ν^*(X)[A]).PreservesFlat]

/-- The derived comparison pullback `Lν^* : D(X_ét) ⥤ D(X_proét)` is a braided monoidal functor
for the braidings `DerivedCategory.braidedCategory` of the derived tensor products
(`CategoryTheory.Functor.leftDerivedBraided`). Its comonoidal structure is the tensor comparison
`CategoryTheory.Functor.leftDerivedTensorComparison`. -/
@[instance_reducible]
noncomputable def leftDerivedComparisonUpperStarBraided :
    letI := DerivedCategory.braidedCategory (Sheaf X.smallEtaleTopology A)
    letI := DerivedCategory.braidedCategory (Sheaf (Scheme.ProEt.topology X) A)
    (ν^*(X)[A]).leftDerivedFunctor.Braided :=
  (ν^*(X)[A]).leftDerivedBraided

/-- The canonical comparison map `ν^* RHom(K, M) ⟶ RHom(ν^* K, ν^* M)` of the braided monoidal
functor `Lν^*` (`AlgebraicGeometry.ProEtale.leftDerivedComparisonUpperStarBraided`): the
adjoint of `ν^* RHom(K, M) ⊗ᴸ ν^* K ≅ ν^* (RHom(K, M) ⊗ᴸ K) ⟶ ν^* M`
(`CategoryTheory.Functor.LaxMonoidal.ihomComparison`). -/
noncomputable def leftDerivedComparisonUpperStarIhomComparison
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (ν^*(X)[A]).leftDerivedFunctor.obj ((ihom K).obj M) ⟶
      (ihom ((ν^*(X)[A]).leftDerivedFunctor.obj K)).obj ((ν^*(X)[A]).leftDerivedFunctor.obj M) :=
  letI := leftDerivedComparisonUpperStarBraided A X
  (Functor.LaxMonoidal.ihomComparison (ν^*(X)[A]).leftDerivedFunctor K).natTrans.app M

end General

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `lem-weil-finite-duality-site-comparison`: Finite-stage duality under the site
comparison, the canonical form of clause 1.

Let `X` be a separated scheme of finite type over an algebraic closure `k` of `𝔽_p`, let `Λ` be
a finite ring whose exponent is invertible on `X`, and let `ν : X_proét ⟶ X_ét` be the site
comparison. For `K ∈ Dctf(X_ét, Λ)` and `M ∈ Dᵇc(X_ét, Λ)`, the canonical comparison map
`ν^* RHom(K, M) ⟶ RHom(ν^* K, ν^* M)` of the braided monoidal functor `Lν^*`
(`AlgebraicGeometry.ProEtale.leftDerivedComparisonUpperStarBraided`), the adjoint of
`ν^* RHom(K, M) ⊗ᴸ ν^* K ≅ ν^* (RHom(K, M) ⊗ᴸ K) ⟶ ν^* M`, is an isomorphism. The
existence of such isomorphisms, together with the identification of the dualizing complexes,
is
`ProEtale.DerivedCategory.nonempty_iso_mapDerivedCategory_derivedHom_of_isSeparated`.
-/
theorem isIso_leftDerivedComparisonUpperStarIhomComparison {k : Type u} [Field k]
    {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) k] [IsAlgClosure (ZMod p) k]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
    [QuasiCompact aX] [HasInvertibleExponent Λ X]
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X M) :
    IsIso (leftDerivedComparisonUpperStarIhomComparison (ModuleCat.{u + 1} Λ) X K M) :=
  sorry

end AlgebraicGeometry.ProEtale
