/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ChowLemma.ProjectiveModification
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Modification
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Projective

/-!
# Constructibility of proper direct images

Let `k` be a field and `Λ` a finite ring killed by an integer invertible in `k`. For a proper
morphism `f : X ⟶ S` with `S` of finite type over `k`:

- `AlgebraicGeometry.Etale.hasConstructibleDirectImages_of_isProper`
  (`thm-fin-proper-constructibility-complete`): `𝒞(f)` holds. The proof is Noetherian induction
  on closed subsets of `X`, using a projective modification given by Chow's lemma
  (`AlgebraicGeometry.exists_projective_modification`), the projective case and the transfer
  along modifications `AlgebraicGeometry.Etale.HasConstructibleDirectImages.of_modification`.
- `AlgebraicGeometry.Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_of_isProper`
  (`thm-fin-proper-case`): moreover `Rᵠf_* F = 0` for `q > 2d` if the geometric fibres have
  dimension at most `d`.
- `AlgebraicGeometry.Etale.isIso_homology_derivedBaseChangeMapPlus_of_isProper`
  (`obl-fin-comparison`): the comparison with the cohomology of geometric fibres.
- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isProper`
  (`lem-fin-proper-bounded-constructible`): `Rf_*` preserves `D^b_c`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]

/-- Blueprint `thm-fin-proper-constructibility-complete`: Proper direct-image constructibility.

Let `Λ` be a finite ring killed by an integer invertible in the field `k`. Every proper morphism
`f : X ⟶ S` with `S` of finite type over `k` satisfies `𝒞(f)`: the higher direct images
`Rᵠf_* F` of constructible sheaves `F` of `Λ`-modules are constructible. -/
theorem hasConstructibleDirectImages_of_isProper {X S : Scheme.{u}} (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] (f : X ⟶ S) [IsProper f] :
    HasConstructibleDirectImages Λ f :=
  sorry

/-- Blueprint `thm-fin-proper-case`: The proper case: direct images of proper morphisms.

Let `f : X ⟶ S` be a proper morphism with `S` of finite type over `k`, all of whose geometric
fibres have dimension at most `d`, and let `F` be a constructible sheaf of `Λ`-modules on `X_ét`,
`Λ` a finite ring killed by an integer invertible in `k`. Then `Rᵠf_* F` is constructible on
`S_ét` for every `q`, and `Rᵠf_* F = 0` for `q > 2d`. -/
theorem isConstructibleSheaf_homology_rightDerivedLowerStar_of_isProper {X S : Scheme.{u}}
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS] (f : X ⟶ S) [IsProper f]
    (d : ℕ) (hd : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    (∀ q : ℤ, IsConstructibleSheaf ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F)))) ∧
    ∀ q : ℤ, (2 * d : ℤ) < q → IsZero ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F))) :=
  sorry

/-- Blueprint `obl-fin-comparison`: The comparison and finitude of proper direct images.

Let `f : X ⟶ S` be a proper morphism with `S` of finite type over `k`, whose geometric fibres
have dimension at most `d`, and let `F` be a constructible sheaf of `Λ`-modules on `X_ét`, for a
finite ring `Λ` killed by an integer invertible in `k`. Let `s : Spec Ω ⟶ S` be a geometric point
(`Ω` algebraically closed), with geometric fibre `X_s = X ×_S Spec Ω`, projections
`i_s : X_s ⟶ X` and `a_s : X_s ⟶ Spec Ω`. Then:

1. (the comparison) for every `q`, the base change map `s^*(Rᵠf_* F) ⟶ Hᵠ(X_s, F|_{X_s})`
   (the `q`-th homology of `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus` at `F`, the
   right-hand side being the sheaf `Rᵠa_{s*}(i_s^* F)` on `Spec Ω`) is an isomorphism, the
   fibre cohomology is finite, and it vanishes for `q > 2d`;
2. (the finitude) every `Rᵠf_* F` is constructible, and `Rᵠf_* F = 0` for `q > 2d`. -/
theorem isIso_homology_derivedBaseChangeMapPlus_of_isProper {X S : Scheme.{u}}
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS] (f : X ⟶ S) [IsProper f]
    (d : ℕ) (hd : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) (q : ℤ),
      IsIso ((Plus.homologyFunctor _ q).map ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ)
        (IsPullback.of_hasPullback f s).toCommSq).app ((Plus.singleFunctor _ 0).obj F))) ∧
      IsFiniteSheaf ((Plus.homologyFunctor _ q).obj
        ((pullback.snd f s)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
          (((pullback.fst f s)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj
            ((Plus.singleFunctor _ 0).obj F)))) ∧
      ((2 * d : ℤ) < q → IsZero ((Plus.homologyFunctor _ q).obj
        ((pullback.snd f s)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
          (((pullback.fst f s)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj
            ((Plus.singleFunctor _ 0).obj F)))))) ∧
    (∀ q : ℤ, IsConstructibleSheaf ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F)))) ∧
    ∀ q : ℤ, (2 * d : ℤ) < q → IsZero ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F))) :=
  sorry

/-- Blueprint `lem-fin-proper-bounded-constructible`: Bounded constructible complexes under a
proper direct image.

Let `b : Y ⟶ S` be proper with `S` of finite type over `k`, and let `Λ` be a finite ring killed
by an integer invertible in `k`. For `K ∈ D^b_c(Y, Λ)`, the derived direct image `Rb_* K` lies in
`D^b_c(S, Λ)`. -/
theorem boundedConstructible_rightDerivedLowerStar_of_isProper {Y S : Scheme.{u}}
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS] (b : Y ⟶ S) [IsProper b]
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K) :
    Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) S
      ((R((b)_*[ModuleCat.{u + 1} Λ])).obj K) :=
  sorry

end Etale

end AlgebraicGeometry
