/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.ConstructibleSheaf.ExtensionByZero
public import WeilConjectures.ConstructibleSheaf.FiniteMorphism

/-!
# Derived finite direct images and constructibility

Let `Λ` be a finite commutative ring. The direct image along a finite morphism is exact
(`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isFinite`), so its higher direct
images vanish, and it preserves and reflects constructibility over Noetherian bases:

- `AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerStar_singleFunctor_of_isFinite`:
  `R^q f_* F = 0` for `q ≠ 0` and `f` finite.
- `AlgebraicGeometry.Etale.isConstructibleSheaf_lowerStar_of_isFinite` (blueprint
  `lem-fin-finite-morphism`): finite direct images of constructible sheaves over a base of finite
  type over a field.
- `AlgebraicGeometry.Etale.isConstructibleSheaf_lowerStar_of_isClosedImmersion` (blueprint
  `lem-fin-closed-immersion`): closed direct images of constructible sheaves.
- `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible_of_rightDerivedLowerStar`
  (blueprint `lem-fin-finite-reflects-derived`): `Rp_*` reflects membership in `D^b_c` for `p`
  finite between Noetherian schemes.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor
open AlgebraicGeometry.Etale

noncomputable section

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Blueprint `lem-fin-finite-morphism`, vanishing part: for a finite morphism `f : X ⟶ S` and a
sheaf `F` of `Λ`-modules on `X_ét`, the higher direct images `R^q f_* F` vanish for `q ≠ 0`,
the direct image `f_*` being exact. -/
theorem isZero_homology_rightDerivedLowerStar_singleFunctor_of_isFinite {X S : Scheme.{u}}
    (f : X ⟶ S) [IsFinite f] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (hq : q ≠ 0) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) :=
  sorry

variable [Finite Λ]

/-- Blueprint `lem-fin-finite-morphism`: Finite direct images of constructible sheaves.

Let `f : X ⟶ S` be finite with `S` of finite type over a field `k`, and let `F` be a
constructible sheaf of `Λ`-modules on `X_ét`. Then `f_* F` is constructible on `S_ét` and
`R^q f_* F = 0` for every `q > 0`. The case of a Noetherian base is
`AlgebraicGeometry.Scheme.IsConstructibleSheaf.lowerStar_of_isFinite`. -/
theorem isConstructibleSheaf_lowerStar_of_isFinite {k : Type u} [Field k] {X S : Scheme.{u}}
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS] (f : X ⟶ S) [IsFinite f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    IsConstructibleSheaf ((f)_*[ModuleCat.{u + 1} Λ].obj F) ∧
      ∀ q : ℤ, 0 < q → IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) :=
  sorry

/-- Blueprint `lem-fin-closed-immersion`: Closed immersions preserve constructibility.

Let `i : Z ⟶ X` be a closed immersion and `G` a constructible sheaf of `Λ`-modules on `Z_ét`.
Then `i_* G` is constructible on `X_ét` and `R^q i_* G = 0` for `q > 0`. The open complement of
`i` is assumed quasi-compact, which is automatic for `X` locally Noetherian (see
`WeilConjectures.ConstructibleSheaf.ExtensionByZero`). -/
theorem isConstructibleSheaf_lowerStar_of_isClosedImmersion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [QuasiCompact (openComplementOfIsClosedImmersion i).ι]
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf G] :
    IsConstructibleSheaf ((i)_*[ModuleCat.{u + 1} Λ].obj G) ∧
      ∀ q : ℤ, 0 < q → IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((R((i)_*[ModuleCat.{u + 1} Λ])).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) :=
  sorry

/-- Blueprint `lem-fin-finite-reflects-derived`: Finite direct image reflects bounded
constructibility.

Let `p : Z ⟶ S` be a finite morphism of Noetherian schemes. A complex `K` of étale sheaves of
`Λ`-modules on `Z` lies in `D^b_c(Z, Λ)` as soon as `Rp_* K` lies in `D^b_c(S, Λ)`. -/
theorem DerivedCategory.boundedConstructible_of_rightDerivedLowerStar {Z S : Scheme.{u}}
    [IsNoetherian Z] [IsNoetherian S] (p : Z ⟶ S) [IsFinite p]
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) S
      ((R((p)_*[ModuleCat.{u + 1} Λ])).obj K)) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z K :=
  sorry

end Etale

end AlgebraicGeometry

end
