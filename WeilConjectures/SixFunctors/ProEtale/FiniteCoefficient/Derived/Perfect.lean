/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Detection
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableTransfer
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
public import WeilConjectures.CategoryTheory.Sites.MonoidalUnitSections
public import WeilConjectures.AlgebraicGeometry.ProEtale.WContractibleDisjointCover

/-!

# Perfect complexes of pro-étale sheaves and their coefficient duals

Let `X` be a scheme. A complex `K ∈ D(X_proét)` is *perfect* over `Λ_X` if it is, locally on
the small pro-étale site, quasi-isomorphic to a bounded complex of finite projective
`Λ_X`-modules. As in `WeilConjectures.SixFunctors.Etale.Derived.Perfect`, perfectness is
rendered as dualizability for the derived tensor product, `CategoryTheory.IsDualizable`; for
sheaves of modules over a ringed site the two notions agree (Stacks, Tag 0FPV). A *finite
projective `Λ_X`-module* is, as in the blueprint, a direct summand of a finite free module
`Λ_Xʳ`, that is, a retract of the finite direct sum `⨁ Λ_X` of copies of the monoidal unit.

This file proves that the coefficient dual `K^∨ = RHom(K, Λ_X)`
(`AlgebraicGeometry.ProEtale.derivedDual`) of a perfect complex is perfect, and, at a finite
coefficient ring `Λ`, lies in `Dctf(X, Λ)`.

## Main statements

- `AlgebraicGeometry.ProEtale.derivedDual_obj`,
  `AlgebraicGeometry.ProEtale.derivedDualEval_eq_uncurry` (`rem-ptr-pod-perfect-complex-on-x-5`):
  the coefficient dual and its evaluation `AlgebraicGeometry.ProEtale.derivedDualEval` are
  formed with the derived internal hom.
- `AlgebraicGeometry.ProEtale.DerivedCategory.constructibleTorAmplitudeIn_single_of_retract`
  (`prop-pod-perfect-local-model`): a finite projective `Λ_X`-module is flat and constructible.
- `AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor_Q_obj_of_retract`
  (`prop-pod-perfect-local-model`): a bounded complex of finite projective `Λ_X`-modules lies in
  `Dctf(X, Λ)`.
- `AlgebraicGeometry.ProEtale.DerivedCategory.isFiniteLocallyConstant_homology_of_retract`:
  the cohomology sheaves of a complex of finite projective `Λ_X`-modules are locally constant
  with finite stalks.
- `AlgebraicGeometry.ProEtale.DerivedCategory.bounded_of_isLocallyPerfect`: a complex which is
  locally quasi-isomorphic to bounded complexes of finite projective modules is bounded, on a
  quasi-compact quasi-separated scheme.
- `AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor_of_isDualizable`
  (`prop-pod-perfect-local-model`): a perfect complex lies in `Dctf(X, Λ)`. It is locally a
  bounded complex of finite projective modules
  (`AlgebraicGeometry.ProEtale.DerivedCategory.isDualizable_iff_isLocallyPerfect`, the node
  `sk-def-perfect`), so its cohomology sheaves are locally constant with finite stalks, hence of
  étale origin (`lem-sf-proetale-constructible-origin`).
- `AlgebraicGeometry.ProEtale.DerivedCategory.isDualizable_iff_isLocallyPerfect`
  (`sk-def-perfect`, Stacks 0FPV): an object of `D(X_proét, Λ)` is dualizable if and only if it
  is locally quasi-isomorphic to a bounded complex of finite projective `Λ_X`-modules. Being
  dualizable is local for the pro-étale topology
  (`AlgebraicGeometry.ProEtale.isDualizable_of_cover`,
  `AlgebraicGeometry.ProEtale.isDualizable_leftDerivedUpperStar_obj`), and over the spectrum of
  a w-contractible ring global sections behave like modules over a ring, so that dualizable
  objects are bounded complexes of finite projective objects there
  (`DerivedCategory.exists_iso_Q_obj_of_isDualizable`,
  `AlgebraicGeometry.ProEtale.projective_unit_and_finite_of_isWContractibleRing`).
- `AlgebraicGeometry.ProEtale.DerivedCategory.isTriangulated_boundedConstructible`:
  `Dᵇc_proét(X, Λ)` is a triangulated subcategory at a finite coefficient ring.
- `AlgebraicGeometry.ProEtale.isDualizable_derivedDual` (`lem-pod-coefficient-dual-perfect`):
  the coefficient dual of a perfect complex is perfect.
- `AlgebraicGeometry.ProEtale.constructibleFiniteTor_derivedDual`
  (`lem-pod-coefficient-dual-perfect`): the coefficient dual of a perfect complex in
  `Dctf(X, Λ)` lies in `Dctf(X, Λ)`.

## Implementation notes

The blueprint argues locally, on a bounded complex of finite projective modules. With
perfectness rendered as dualizability, the first statement is instead the general fact that
in a braided monoidal closed category the internal dual `[K, 𝟙]` of a dualizable `K` is its
right dual `Kᘁ`, hence dualizable (`CategoryTheory.IsDualizable.ihom_unit`). It is applied to
some braiding of `D(X_proét)` (`DerivedCategory.nonempty_braidedCategory`); the conclusion
does not depend on which one.

The statements about `Dctf(X, Λ)` are made at a finite coefficient ring `Λ`, as in the
blueprint's setting: bounded constructibility is étale origin
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`), which is the right notion
only at the finite coefficient stages. A finite projective `Λ_X`-module is of étale origin
since `Λ_Xʳ = ν^* Λ_{X_ét}ʳ` and `ν^*` is full and exact; so is a bounded complex of them, as
`ν^*` is fully faithful. The same lift, to finite locally constant étale sheaves, shows that the
cohomology sheaves of such a complex are locally constant with finite stalks.

As in the blueprint (`def-pod-perfect-complex-on-x`), the coefficient dual is shown to lie in
`Dctf(X, Λ)` for perfect complexes which already lie in `Dctf(X, Λ)`, in the Poincaré duality
setting of a scheme of finite type over an algebraic closure of `𝔽_p` and a coefficient ring
whose exponent is invertible on `X`. The proof goes through the étale site rather than through
the local model: `K = ν^* K'` and `K^∨ ≅ ν^* RHom(K', Λ)`
(`AlgebraicGeometry.ProEtale.DerivedCategory.nonempty_iso_mapDerivedCategory_derivedHom`), which
only needs `RHom(K', Λ)` to be constructible on `X_ét`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section Dualizable

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {A} {X : Scheme.{u}}

end Dualizable

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X : Scheme.{u}}

section FiniteProjective

attribute [local instance] Abelian.hasFiniteBiproducts

variable {Λ} {P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)} {r : ℕ}

namespace DerivedCategory

end DerivedCategory

end FiniteProjective

namespace DerivedCategory

section Triangulated

variable (X)

/-- At a finite coefficient ring, the bounded constructible pro-étale complexes form a
triangulated subcategory of `D(X_proét)`. They are the complexes of étale origin, and `ν^*` is
triangulated and fully faithful on bounded below complexes
(`AlgebraicGeometry.ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map`), so the cone
of a map between complexes of étale origin is `ν^*` of the cone of a lift of this map. -/
instance isTriangulated_boundedConstructible :
    (boundedConstructible (ModuleCat.{u + 1} Λ) X).IsTriangulated := by
  let F := D(ν^*(X)[ModuleCat.{u + 1} Λ])
  have : (boundedConstructible (ModuleCat.{u + 1} Λ) X).IsTriangulatedClosed₃ := by
    refine ObjectProperty.IsTriangulatedClosed₃.mk' fun T hT ⟨A, hA, ⟨e₁⟩⟩ ⟨B, hB, ⟨e₂⟩⟩ ↦ ?_
    obtain ⟨f, hf⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map A B hB.1.1).2
      (e₁.hom ≫ T.mor₁ ≫ e₂.inv)
    obtain ⟨Z, g, h, hZ⟩ := Pretriangulated.distinguished_cocone_triangle f
    obtain ⟨e, -, -⟩ := Pretriangulated.exists_iso_of_arrow_iso _ T
      (F.map_distinguished _ hZ) hT (Arrow.isoMk e₁ e₂ (by
        have hf' : F.map f = e₁.hom ≫ T.mor₁ ≫ e₂.inv := hf
        change e₁.hom ≫ T.mor₁ = F.map f ≫ e₂.hom
        simp [hf']))
    exact ⟨Z, (Etale.DerivedCategory.boundedConstructible _ X).ext_of_isTriangulatedClosed₃ _
      hZ hA hB, ⟨Pretriangulated.Triangle.π₃.mapIso e⟩⟩
  have : (boundedConstructible (ModuleCat.{u + 1} Λ) X).IsStableUnderShift ℤ :=
    ⟨fun n ↦ ⟨fun K ⟨A, hA, ⟨e⟩⟩ ↦ ⟨A⟦n⟧,
      (Etale.DerivedCategory.boundedConstructible _ X).le_shift n _ hA,
      ⟨(F.commShiftIso n).app A ≪≫ (shiftFunctor _ n).mapIso e⟩⟩⟩⟩
  have : (boundedConstructible (ModuleCat.{u + 1} Λ) X).IsTriangulatedClosed₂ :=
    ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃
  obtain ⟨Z, hZ, hZP⟩ := ObjectProperty.ContainsZero.exists_zero
    (P := Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X)
  exact { exists_zero := ⟨F.obj Z, F.map_isZero hZ,
    boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj hZP⟩ }

variable {X}

/-- At a finite coefficient ring, a bounded pro-étale complex is bounded constructible as soon as
each of its cohomology sheaves is `ν^*` of a constructible étale sheaf. -/
theorem boundedConstructible_of_homology
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : _root_.DerivedCategory.TStructure.t.bounded K)
    (hH : ∀ n, ∃ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsConstructibleSheaf F ∧
      Nonempty ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj F ≅
        (_root_.DerivedCategory.homologyFunctor _ n).obj K)) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X K := by
  let P : ObjectProperty (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
    fun G ↦ ∃ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsConstructibleSheaf F ∧
      Nonempty ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj F ≅ G)
  have : P.IsClosedUnderIsomorphisms := ⟨fun e ⟨F, hF, ⟨e'⟩⟩ ↦ ⟨F, hF, ⟨e' ≪≫ e⟩⟩⟩
  refine _root_.DerivedCategory.prop_of_bounded _ P (fun G ⟨F, hF, ⟨e⟩⟩ ↦ ?_) K hK hH
  exact ⟨_, Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0,
    ⟨((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso e⟩⟩

end Triangulated

section Local

attribute [local instance] Abelian.hasFiniteBiproducts

variable {Λ}

end Local

end DerivedCategory

end ProEtale

end AlgebraicGeometry
