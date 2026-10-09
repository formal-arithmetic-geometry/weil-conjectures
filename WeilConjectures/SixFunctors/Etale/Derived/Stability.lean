/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.KFlat

/-!

# Stability of the constructible finite-Tor categories under the six operations

Let `A` be a monoidal Grothendieck abelian coefficient category. This file states that the six
operations of `WeilConjectures.SixFunctors.Etale.Derived.*` preserve the small categories
`D_c^[a, b](X, A)` and `Dctf(X, A)` of
`WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude`, together with the explicit shifts the
blueprint records for the cohomological range and for the Tor amplitude, and it constructs the
restrictions of `Lf^*`, `Rf_*`, `Rf_!`, `Rf^!` and `𝔻_X` to `Dctf`.

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.leftDerivedUpperStar`,
  `…rightDerivedLowerStar`, `…rightDerivedLowerShriek`, `…rightDerivedUpperShriek`,
  `…verdierDual` (`sk-thm-sf-ctf-stability`): the descended functors between the small
  categories `Dctf`.

## Main statements

- `AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedLowerShriek`
  (`sk-lem-sf-open-ctf`).
- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar`,
  `AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar`
  (`sk-thm-sf-direct-image-tor-amplitude`).
- `AlgebraicGeometry.Etale.boundedConstructible_derivedHom`,
  `AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom`,
  `AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom_of_isDualizable` (`sk-thm-sf-hom-ctf`).
- `AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isOpenImmersion`,
  `…_of_isFinite_of_etale`, `…_of_isClosedImmersion`, `…_of_smoothOfRelativeDimension`,
  `AlgebraicGeometry.Etale.exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek`
  (`sk-prop-sf-rf-shriek-preservation`, clauses (i)–(iv)).
- `exists_constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_topologicalKrullDim_le`, in
  the namespace `AlgebraicGeometry.Etale` (`sk-prop-sf-rf-shriek-preservation`, clause (iv)
  with its constants).
- `AlgebraicGeometry.Etale.constructibleFiniteTor_leftDerivedUpperStar`,
  `AlgebraicGeometry.Etale.constructibleFiniteTor_tensor`,
  `AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerStar`,
  `AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerShriek`,
  `AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedUpperShriek`
  (`sk-thm-sf-ctf-stability`, clauses (i)–(v)).
- `AlgebraicGeometry.Etale.ctf_generated_by_rightDerivedLowerStar_rightDerivedLowerShriek`
  (`sk-lem-sf-ctf-generation`).
- `AlgebraicGeometry.Etale.torAmplitudeIn_singleFunctor_obj_of_flat`: a flat constructible
  sheaf in degree `0` has Tor amplitude in `[0, 0]`.

## Implementation notes

* Clause (vi) of `sk-thm-sf-ctf-stability` — that `𝔻_X` preserves `Dctf(X, A)` and is an
  anti-equivalence of it — is **not restated here**: it is
  `AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual` and
  `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual` of
  `WeilConjectures.SixFunctors.Etale.Derived.Dualizing`. Only the descended functor
  `DerivedCategoryFiniteTor.verdierDual` is built here, out of those.
* Clause (i) of `sk-thm-sf-ctf-stability` assumes that pullbacks preserve flat sheaves
  (`AlgebraicGeometry.Etale.UpperStarPreservesFlat A`, an instance for `A = ModuleCat Λ`, where
  flatness is checked on stalks). For a general coefficient category `A` this is not known, and
  it is the special case of the Tor amplitude statement for a flat sheaf in degree `0`. The
  proof represents a complex of Tor amplitude in `[a, b]` by a complex of flat sheaves in
  degrees `[a, b]` (`DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn`) and pulls it
  back termwise.
* Clause (vii) of `sk-thm-sf-ctf-stability` — compatibility of each of (i)–(vi) with finite
  reduction, with scalar extension and with the pro-étale realization — is **not stated**. It
  quantifies over the coefficient stages `A_{E,n} ⇝ 𝒪_E ⇝ E ⇝ ℚ̄_ℓ` and over the étale/pro-étale
  comparison `ν^*`, neither of which is available: the coefficient stages are modelled here by
  *choosing* a coefficient category `A := ModuleCat R`, so a statement relating two choices needs
  a change-of-coefficients functor that the library does not yet have.
* The internal-Hom half of clause (ii) of `sk-thm-sf-ctf-stability` is not restated: it *is*
  `torAmplitudeIn_derivedHom` below, with the same shifts.
* `sk-lem-sf-ctf-generation` is stated for `A = ModuleCat Λ` with `Λ` finite, because its proof
  uses flat constructible models (`hasTorAmplitudeIn_iff_exists_flatConstructibleModel`), which
  need finite stalks, and the `π₁(U)`-composition factors of the stalks; this is what the
  blueprint assumes. Flatness of the lisse generators is `ObjectProperty.flat`, as in
  `WeilConjectures.SixFunctors.Etale.Derived.Finiteness`. The blueprint restricts to varieties
  over a separably closed field; the statement here only asks `X` to be Noetherian, which is
  all the proof uses.
* "Thick subcategory" in `sk-lem-sf-ctf-generation` is spelled as an `ObjectProperty` that is
  `ObjectProperty.IsTriangulated`, `ObjectProperty.IsStableUnderRetracts` and
  `ObjectProperty.IsClosedUnderIsomorphisms`; generation is the statement that any such property
  containing the generators contains all of `Dctf(X, A)`. Mathlib has no `thickClosure`.
* The counterexample of `sk-thm-sf-hom-ctf` (the origin in `𝔸¹`, showing that the sharper
  interval fails without dualizability) is prose only and is not formalised.
* A dimension bound `dim X ≤ d` is `topologicalKrullDim X ≤ (d : WithBot ℕ∞)`. What Lean needs
  to form `Rf_!` and `Rf^!` is that `f` admits a compactification, `HasCompactification f`,
  taken as an
  explicit hypothesis throughout (it is *not* automatic for an open immersion, Nagata's theorem
  requiring a quasi-compact quasi-separated target). `HasCompactification f` already supplies
  `IsSeparated f` and `LocallyOfFiniteType f`, so "separated of finite type" is spelled as
  `[HasCompactification f] [QuasiCompact f]` where `Rf_!` or `Rf^!` occurs.
* The blueprint states this section for finite-type schemes over a separably closed field and
  for one of the coefficient stages; the amplitude bounds `2d` and `2d + 1` come from the
  vanishing of `R^p f_*` above twice the dimension, which uses those standing hypotheses. As
  everywhere in this folder the statements are made relatively, for an arbitrary base and an
  arbitrary coefficient category `A`, with the dimension bound carried explicitly; the absolute
  case is the base `Spec k`. The dimension bound alone does not give the vanishing above twice
  the dimension: that also needs the coefficients' characteristic to be invertible on the base
  and a base on which the cohomological-dimension bound holds (finite type over a separably
  closed field, or quasi-excellent Noetherian by Gabber). For `Λ = 𝔽_p` on `𝔸¹` over `𝔽̄_p`
  the Artin–Schreier cohomology makes `Ri^!Λ` at the origin non-constructible. There is not
  yet a way to say "the characteristic of `A` is invertible on `X`" for a general coefficient
  category `A`, so this hypothesis is missing from every statement here carrying a `2d` bound.
* Constructible sheaves have finitely generated stalks (`AlgebraicGeometry.Scheme.IsFiniteSheaf`).
  The statements about direct images, internal homs, exceptional inverse images and the Verdier
  dual hold for torsion coefficients only, and assume that finitely generated objects of `A` are
  finite (`CategoryTheory.ConcreteCategory.FiniteOfIsFinitelyGenerated`, which holds for
  `ModuleCat Λ` with `Λ` finite); the direct image statements, used at the integral stage on the
  torsion reductions, assume instead that `K` is killed by a nonzero integer and that `A` is
  noetherian (`CategoryTheory.ConcreteCategory.FinitelyGeneratedOfMono`). With coefficients `ℤ`,
  `H³(ℙ¹, ℤ) ≅ H²(ℙ¹, ℚ/ℤ)` contains `ℚ_ℓ/ℤ_ℓ`, so `Rf_*ℤ` is not constructible for
  `f : ℙ¹ ⟶ Spec k`. The `ℓ`-adic coefficient stages are reached through the pro-étale formalism
  instead.
* The clause (iv) statements of `sk-prop-sf-rf-shriek-preservation` and clause (v) of
  `sk-thm-sf-ctf-stability` assume `Y` Noetherian (`[IsNoetherian Y]`). Quasi-compactness of
  `Y` is needed for a uniform shift, since `f` must be covered by finitely many affine charts:
  for `f : ⊔ₙ 𝔸ⁿ_k ⟶ ⊔ₙ Spec k` the complex `Rf^!Λ` sits in degree `-2n` on the `n`-th
  component. Noetherianity gives `dim 𝔸ⁿ_V = dim V + n`, which fails for general rings.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

omit [HasSmallSiteSheafify A] in
/-- Membership in `D_c^[a, b]` with Tor amplitude in `[a, b]` is invariant under
isomorphism. -/
lemma constructibleTorAmplitudeIn_of_iso {X : Scheme.{u}} {a b : ℤ}
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (e : K ≅ K')
    (hK : constructibleTorAmplitudeIn A X a b K) : constructibleTorAmplitudeIn A X a b K' := by
  obtain ⟨⟨hbc, h₁, h₂⟩, hta⟩ := hK
  exact ⟨⟨(boundedConstructible A X).prop_of_iso e hbc,
    _root_.DerivedCategory.TStructure.t.isGE_of_iso e a,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e b⟩,
    (torAmplitudeIn A X a b).prop_of_iso e hta⟩


/-! ### The exceptional inverse image -/

/-- Blueprint `sk-prop-sf-rf-shriek-preservation`: Preservation for the exceptional inverse
image.

Clause (i), finite étale case: for a finite étale `f`, `Rf^!` preserves the constructible
interval and the Tor amplitude *unchanged*. -/
theorem constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isFinite_of_etale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [_root_.AlgebraicGeometry.Etale f]
    [HasCompactification f] [(R(f)_![A]).IsLeftAdjoint] (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hK : constructibleTorAmplitudeIn A Y a b K) :
    constructibleTorAmplitudeIn A X a b ((R(f)^![A]).obj K) :=
  sorry

/-! ### Stability of `Dctf` under the six operations -/

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor
subcategories.

Clause (i), constructibility: the pullback of a bounded constructible complex is bounded
constructible. -/
theorem boundedConstructible_leftDerivedUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hbc : boundedConstructible A Y K) :
    boundedConstructible A X ((L((f)^*[A])).obj K) :=
  (boundedConstructible A X).prop_of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory A f).app K).symm
    (hbc.mapDerivedCategory_upperStar f)

omit [HasSmallSiteSheafify A] in
/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor
subcategories.

Clause (i), amplitude: `Lf^*` preserves the Tor amplitude interval unchanged, the pullback of
a bounded flat model being a bounded flat model in the same degrees.

The pullback is assumed to preserve flat sheaves (`AlgebraicGeometry.Etale.UpperStarPreservesFlat`,
which holds for `A = ModuleCat Λ`). This is no restriction: the statement for `a = b = 0` and
`K` a flat sheaf in degree `0` says exactly that `f^*` of a flat sheaf is flat. -/
theorem torAmplitudeIn_leftDerivedUpperStar [UpperStarPreservesFlat A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hta : torAmplitudeIn A Y a b K) :
    torAmplitudeIn A X a b ((L((f)^*[A])).obj K) := by
  -- `K` is represented by a complex `P` of flat sheaves in degrees `[a, b]`, so `Lf^* K` is
  -- represented by the complex `f^* P` of flat sheaves in degrees `[a, b]`
  obtain ⟨P, _, _, hP, ⟨e⟩⟩ := _root_.DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn hta
  refine (torAmplitudeIn A X a b).prop_of_iso
    (((f)^*[A].mapDerivedCategoryFactors.app P).symm ≪≫
      (f)^*[A].mapDerivedCategory.mapIso e ≪≫
      ((leftDerivedUpperStarIsoMapDerivedCategory A f).app K).symm)
    (_root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat _ a b fun n ↦ ?_)
  exact Functor.PreservesFlat.flat_obj (F := (f)^*[A]) (hP n)

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor
subcategories.

Clause (i): `Lf^* : Dctf(Y, A) ⥤ Dctf(X, A)` is defined. -/
theorem constructibleFiniteTor_leftDerivedUpperStar [UpperStarPreservesFlat A] {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hK : constructibleFiniteTor A Y K) :
    constructibleFiniteTor A X ((L((f)^*[A])).obj K) := by
  obtain ⟨hbc, a, b, hta⟩ := hK
  exact ⟨boundedConstructible_leftDerivedUpperStar A f hbc,
    a, b, torAmplitudeIn_leftDerivedUpperStar A f a b hta⟩

omit [HasSmallSiteSheafify A] in
/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor
subcategories.

Clause (ii), amplitude: Tor amplitudes add under the derived tensor product,
`[a, b], [c, d] ↦ [a + c, b + d]`. -/
theorem torAmplitudeIn_tensor (X : Scheme.{u}) (a b c d : ℤ)
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hKt : torAmplitudeIn A X a b K) (hMt : torAmplitudeIn A X c d M) :
    torAmplitudeIn A X (a + c) (b + d) (((-⊗ᴸ-(X)[A]).obj K).obj M) :=
  _root_.DerivedCategory.torAmplitudeIn_tensor hKt hMt

omit [HasSmallSiteSheafify A] in
/-- The derived tensor product of a bounded complex with a complex of finite Tor amplitude is
bounded. -/
theorem bounded_derivedTensor_of_finiteTorAmplitude (X : Scheme.{u})
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : _root_.DerivedCategory.TStructure.t.bounded K) (hMt : finiteTorAmplitude A X M) :
    _root_.DerivedCategory.TStructure.t.bounded (((-⊗ᴸ-(X)[A]).obj K).obj M) := by
  obtain ⟨a, b, hab⟩ := (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded K).2 hK
  obtain ⟨c, d, hcd⟩ := hMt
  exact (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).1
    ⟨_, _, _root_.DerivedCategory.homologyConcentratedIn_tensor_of_torAmplitudeIn_right hab hcd⟩

/-- **Dévissage for the derived tensor product.** Suppose that constructible sheaves are closed
under kernels, cokernels and extensions, and that the homology sheaves of `F[0] ⊗ᴸ G[0]` are
constructible for constructible sheaves `F` and `G`. Then the derived tensor product of two
bounded complexes with constructible homology has constructible homology. -/
theorem constructibleHomology_derivedTensor [PreservesFiniteLimits (CategoryTheory.forget A)]
    {X : Scheme.{u}} [(Etale.constructibleSheaf A X).IsClosedUnderKernels]
    [(Etale.constructibleSheaf A X).IsClosedUnderCokernels]
    [(Etale.constructibleSheaf A X).IsClosedUnderExtensions]
    (hTor : ∀ F G : Sheaf X.smallEtaleTopology A, Etale.constructibleSheaf A X F →
      Etale.constructibleSheaf A X G → ∀ n : ℤ, Etale.constructibleSheaf A X
        ((_root_.DerivedCategory.homologyFunctor _ n).obj
          (((-⊗ᴸ-(X)[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G))))
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : boundedConstructible A X K) (hM : boundedConstructible A X M) :
    constructibleHomology A X (((-⊗ᴸ-(X)[A]).obj K).obj M) := by
  rw [constructibleHomology_eq]
  have : (_root_.DerivedCategory.homologyProperty (Etale.constructibleSheaf A X)).IsTriangulated :=
    inferInstance
  -- first for `K` a constructible sheaf in degree `0`
  have h₀ (F : Sheaf X.smallEtaleTopology A) (hF : Etale.constructibleSheaf A X F) :
      _root_.DerivedCategory.homologyProperty (Etale.constructibleSheaf A X)
        (((-⊗ᴸ-(X)[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).obj M) :=
    letI := _root_.DerivedCategory.commShiftTensorLeft
      (K := (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F)
    have : ((-⊗ᴸ-(X)[A]).obj ((_root_.DerivedCategory.singleFunctor
        (Sheaf X.smallEtaleTopology A) 0).obj F)).IsTriangulated :=
      _root_.DerivedCategory.isTriangulated_tensorLeft
        (K := (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F)
    _root_.DerivedCategory.prop_of_bounded
      ((_root_.DerivedCategory.homologyProperty (Etale.constructibleSheaf A X)).inverseImage
        ((-⊗ᴸ-(X)[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))
      (Etale.constructibleSheaf A X) (fun G hG n ↦ hTor F G hF hG n) M hM.1 hM.2
  let := _root_.DerivedCategory.commShiftTensorRight (K := M)
  have : ((-⊗ᴸ-(X)[A]).flip.obj M).IsTriangulated :=
    _root_.DerivedCategory.isTriangulated_tensorRight (K := M)
  exact _root_.DerivedCategory.prop_of_bounded
    ((_root_.DerivedCategory.homologyProperty (Etale.constructibleSheaf A X)).inverseImage
      ((-⊗ᴸ-(X)[A]).flip.obj M))
    (Etale.constructibleSheaf A X) h₀ K hK.1 hK.2

/-! ### The derived tensor product at a finite coefficient ring -/

section Tensor

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `lem-sf-tor-sheaf-constructible`: Tor sheaves of constructible sheaves.

For a finite ring `Λ` and constructible sheaves `F` and `G` of `Λ`-modules on `X_ét`, every
homology sheaf of `F ⊗ᴸ G` is constructible: on a common stratification both are locally
constant, and on a cover where both are constant `Hʳ(F ⊗ᴸ G)` is the constant sheaf
`Tor_{-r}(M, N)` of finite modules. -/
theorem isConstructibleSheaf_homology_tensor_singleFunctor {X : Scheme.{u}}
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] [IsConstructibleSheaf G] (r : ℤ) :
    IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ r).obj
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) :=
  sorry

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor
subcategories.

Clause (ii), constructibility: for a finite ring `Λ`, the derived tensor product of two
bounded constructible complexes, one of them of finite Tor amplitude, is bounded constructible.
Finite Tor amplitude of one factor is needed for boundedness: over `ℤ/ℓ²` on a point,
`ℤ/ℓ ⊗ᴸ ℤ/ℓ` has a nonzero `Tor_i` for every `i ≥ 0`. The coefficients cannot be an arbitrary
coefficient category: over `R = k[x, y₁, y₂, …]` on a point, `R/(x yᵢ)ᵢ ⊗ᴸ R/(x)` has the
non-finitely generated `Tor₁ = (yᵢ)ᵢ/(x yᵢ)ᵢ` in degree `-1`, although `R/(x)` has Tor
amplitude in `[-1, 0]`. -/
theorem boundedConstructible_tensor (X : Scheme.{u})
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M)
    (hMt : finiteTorAmplitude (ModuleCat.{u + 1} Λ) X M) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M) :=
  have : IsNoetherianRing Λ := inferInstance
  ⟨bounded_derivedTensor_of_finiteTorAmplitude _ X hK.1 hMt,
    constructibleHomology_derivedTensor _ (fun F G hF hG n ↦ by
      have := (Etale.constructibleSheaf_iff _ _ _).mp hF
      have := (Etale.constructibleSheaf_iff _ _ _).mp hG
      exact (Etale.constructibleSheaf_iff _ _ _).mpr
        (isConstructibleSheaf_homology_tensor_singleFunctor Λ F G n)) hK hM⟩

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor
subcategories.

Clause (ii): `- ⊗ᴸ - : Dctf(X, Λ) × Dctf(X, Λ) ⥤ Dctf(X, Λ)` is defined, for a finite ring
`Λ`. The internal-Hom half of the clause is `AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom`
below. -/
theorem constructibleFiniteTor_tensor (X : Scheme.{u})
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M) := by
  obtain ⟨hKbc, a, b, hKt⟩ := hK
  obtain ⟨hMbc, c, d, hMt⟩ := hM
  exact ⟨boundedConstructible_tensor Λ X hKbc hMbc ⟨c, d, hMt⟩,
    a + c, b + d, torAmplitudeIn_tensor _ X a b c d hKt hMt⟩

end Tensor

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor
subcategories.

Clause (iv): `Rf_! : Dctf(X, A) ⥤ Dctf(Y, A)` is defined for every separated finite-type `f`
admitting a compactification. One assembles the open-immersion case
(`AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedLowerShriek`) with the proper
case, where `Rf_! = Rf_*`, along a compactification of `f`. -/
theorem constructibleFiniteTor_rightDerivedLowerShriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    [ConcreteCategory.FiniteOfIsFinitelyGenerated A]
    [HasCompactification f] [QuasiCompact f]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : constructibleFiniteTor A X K) :
    constructibleFiniteTor A Y ((R(f)_![A]).obj K) :=
  sorry

/-! ### Open immersions -/

section OpenImmersion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {U Y : Scheme.{u}} (j : U ⟶ Y)
  [IsOpenImmersion j] [HasCompactification j] [QuasiCompact j]

/-- The derived lower shriek along a quasi-compact open immersion `j` is extension by zero,
`Rj_! ≅ D(j_!)`: it is computed by the compactification `U ⟶[j] Y ⟶[𝟙] Y`, and `Rj_!` does not
depend on the compactification (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`). -/
noncomputable def rightDerivedLowerShriekIsoOfIsOpenImmersion :
    R(j)_![ModuleCat.{u + 1} Λ] ≅ D((j)_!open[ModuleCat.{u + 1} Λ]) :=
  (rightDerivedLowerShriekIso Λ (Compactification.ofIsOpenImmersion j)).symm ≪≫
    Functor.isoWhiskerLeft D((j)_!open[ModuleCat.{u + 1} Λ])
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (𝟙 Y)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso (Etale.lowerStarId (ModuleCat.{u + 1} Λ) Y) ≪≫
        Functor.mapDerivedCategoryIdIso _) ≪≫
    Functor.rightUnitor _

/-- Blueprint `sk-lem-sf-open-ctf`: Extension by zero preserves the finite-Tor constructible
category.

For a quasi-compact open immersion `j : U ⟶ Y` admitting a compactification and a finite ring
`Λ`, extension by zero sends `Dctf(U, Λ)` into `Dctf(Y, Λ)` *without moving the interval*: if
`K` is bounded constructible with homology concentrated in `[a, b]` and Tor amplitude in
`[a, b]`, then so is `Rj_! K`. Indeed `Rj_! = j_!` is exact, the extension by zero of a
constructible sheaf is constructible, and `j_!K ⊗ᴸ F ≅ j_!(K ⊗ᴸ j^*F)` by the projection
formula. -/
theorem constructibleTorAmplitudeIn_rightDerivedLowerShriek (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) U a b K) :
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b
      ((R(j)_![ModuleCat.{u + 1} Λ]).obj K) := by
  obtain ⟨⟨hbc, hab⟩, hta⟩ := hK
  let F := (j)_!open[ModuleCat.{u + 1} Λ]
  refine constructibleTorAmplitudeIn_of_iso _
    ((rightDerivedLowerShriekIsoOfIsOpenImmersion Λ j).app K).symm ⟨⟨⟨?_, fun n ↦ ?_⟩,
      F.homologyConcentratedIn_mapDerivedCategory_obj hab⟩, fun G ↦ ?_⟩
  · exact F.bounded_mapDerivedCategory_obj hbc.1
  · have := hbc.2 n
    have : IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ n ⋙ F).obj K) :=
      IsConstructibleSheaf.openImmersionLowerShriek j j.closedComplement
        j.range_closedComplement ((_root_.DerivedCategory.homologyFunctor _ n).obj K)
    exact IsConstructibleSheaf.of_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K)
  · -- `j_!K ⊗ᴸ G ≅ j_!(K ⊗ᴸ j^*G)`
    have e := (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} Λ) j).app
      K).app ((_root_.DerivedCategory.singleFunctor _ 0).obj G)).symm ≪≫
      F.mapDerivedCategory.mapIso (((-⊗ᴸ-(U)[ModuleCat.{u + 1} Λ]).obj K).mapIso
        ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) j).app G))
    obtain ⟨h₁, h₂⟩ := F.homologyConcentratedIn_mapDerivedCategory_obj (hta ((j)^*[_].obj G))
    have : _root_.DerivedCategory.TStructure.t.IsGE (F.mapDerivedCategory.obj
        (((-⊗ᴸ-(U)[ModuleCat.{u + 1} Λ]).obj K).obj (((j)^*[ModuleCat.{u + 1} Λ] ⋙
          _root_.DerivedCategory.singleFunctor _ 0).obj G))) a := h₁
    have : _root_.DerivedCategory.TStructure.t.IsLE (F.mapDerivedCategory.obj
        (((-⊗ᴸ-(U)[ModuleCat.{u + 1} Λ]).obj K).obj (((j)^*[ModuleCat.{u + 1} Λ] ⋙
          _root_.DerivedCategory.singleFunctor _ 0).obj G))) b := h₂
    exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm a,
      _root_.DerivedCategory.TStructure.t.isLE_of_iso e.symm b⟩

/-- For a quasi-compact open immersion `j`, the exceptional inverse image is the restriction,
`Rj^! ≅ D(j^*)`: both are right adjoint to `Rj_! ≅ D(j_!)`. -/
noncomputable def rightDerivedUpperShriekIsoOfIsOpenImmersion :
    R(j)^![ModuleCat.{u + 1} Λ] ≅ D((j)^*[ModuleCat.{u + 1} Λ]) :=
  (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) j).rightAdjointUniq
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).ofNatIsoLeft
      (rightDerivedLowerShriekIsoOfIsOpenImmersion Λ j).symm)

/-- Blueprint `sk-prop-sf-rf-shriek-preservation`: Preservation for the exceptional inverse
image.

Clause (i), open-immersion case: for a quasi-compact open immersion `f` and a finite ring `Λ`,
`Rf^!` preserves the constructible interval and the Tor amplitude *unchanged*, the right adjoint
of `Rf_! ≅ f_!` being the exact functor `f^*`. -/
theorem constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isOpenImmersion (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K) :
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) U a b
      ((R(j)^![ModuleCat.{u + 1} Λ]).obj K) := by
  obtain ⟨⟨hbc, hab⟩, hta⟩ := hK
  refine constructibleTorAmplitudeIn_of_iso _
    ((rightDerivedUpperShriekIsoOfIsOpenImmersion Λ j).app K).symm ⟨⟨?_,
      ((j)^*[ModuleCat.{u + 1} Λ]).homologyConcentratedIn_mapDerivedCategory_obj hab⟩, ?_⟩
  · exact hbc.mapDerivedCategory_upperStar j
  · exact (torAmplitudeIn (ModuleCat.{u + 1} Λ) U a b).prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ j).app K)
      (torAmplitudeIn_leftDerivedUpperStar _ j a b hta)

end OpenImmersion

/-! ### The descended functors -/

section Functors

variable {X Y : Scheme.{u}}

/-- Blueprint `sk-thm-sf-ctf-stability`, clause (i): the restriction
`Lf^* : Dctf(Y, A) ⥤ Dctf(X, A)` of the derived pullback to the small categories. -/
noncomputable def DerivedCategoryFiniteTor.leftDerivedUpperStar [UpperStarPreservesFlat A]
    (f : X ⟶ Y) :
    DerivedCategoryFiniteTor A Y ⥤ DerivedCategoryFiniteTor A X :=
  ObjectProperty.lift _ (DerivedCategoryFiniteTor.ι A Y ⋙ L((f)^*[A]))
    fun K ↦ constructibleFiniteTor_leftDerivedUpperStar A f K.property

/-- Blueprint `sk-thm-sf-ctf-stability`, clause (iv): the restriction
`Rf_! : Dctf(X, A) ⥤ Dctf(Y, A)` of the compactly supported direct image to the small
categories. -/
noncomputable def DerivedCategoryFiniteTor.rightDerivedLowerShriek (f : X ⟶ Y)
    [ConcreteCategory.FiniteOfIsFinitelyGenerated A]
    [HasCompactification f] [QuasiCompact f] :
    DerivedCategoryFiniteTor A X ⥤ DerivedCategoryFiniteTor A Y :=
  ObjectProperty.lift _ (DerivedCategoryFiniteTor.ι A X ⋙ R(f)_![A])
    fun K ↦ constructibleFiniteTor_rightDerivedLowerShriek A f K.property

/-- Blueprint `sk-thm-sf-ctf-stability`, clause (vi): the restriction
`𝔻_X : Dctf(X, A)ᵒᵖ ⥤ Dctf(X, A)` of the Verdier dual to the small categories, given that `𝔻_X`
preserves `Dctf(X, A)`. For a finite `Λ` whose exponent is invertible on `k` and `X` separated of
finite type over `k`, this is `AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual`; that
the restriction is an anti-equivalence is
`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual`. -/
noncomputable def DerivedCategoryFiniteTor.verdierDual {S : Scheme.{u}} (a : X ⟶ S)
    [HasCompactification a] [(R(a)_![A]).IsLeftAdjoint]
    (h : ∀ ⦃K⦄, constructibleFiniteTor A X K →
      constructibleFiniteTor A X ((Etale.verdierDual A a).obj (op K))) :
    (DerivedCategoryFiniteTor A X)ᵒᵖ ⥤ DerivedCategoryFiniteTor A X :=
  ObjectProperty.lift _ ((DerivedCategoryFiniteTor.ι A X).op ⋙ Etale.verdierDual A a)
    fun K ↦ h K.unop.property

end Functors

/-! ### Torsion coefficients with invertible exponent

The statements of this section are the ones of `sk-thm-sf-direct-image-tor-amplitude`,
`sk-thm-sf-hom-ctf`, `sk-prop-sf-rf-shriek-preservation` (ii)–(iv) and
`sk-thm-sf-ctf-stability` (iii), (v), (vi) whose content is a bound on étale cohomological
dimension, a constructibility theorem for direct images or purity. They are made in the setting
of `sk-def-sf-setting`: the coefficients are a finite ring `Λ` whose exponent is invertible on
the schemes in sight, and the schemes are of finite type over a field `k`. Neither hypothesis
can be dropped: for `Λ = 𝔽_p` on `𝔸¹` over `𝔽̄_p`, `H¹(𝔸¹, 𝔽_p)` is infinite (Artin–Schreier),
so `Rf_*` of the constant sheaf along `𝔸¹ ⟶ Spec 𝔽̄_p` is not constructible; and over a
general Noetherian base étale cohomology need not vanish above twice the dimension. -/

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]

/-! #### Direct image -/

/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility.

Let `f : X ⟶ Y` be a morphism of finite-type `k`-schemes, and let `K` be a bounded constructible
complex on `X_ét` killed by an integer `N` invertible on `Y`. Then `Rf_* K` is bounded
constructible on `Y_ét`. The coefficients are noetherian: subobjects of finitely generated
objects of `A` are finitely generated (`CategoryTheory.ConcreteCategory.FinitelyGeneratedOfMono`,
which holds for `ModuleCat Λ` with `Λ` noetherian).

Each hypothesis is needed. Without torsion the statement fails, `H³(ℙ¹, ℤ)` containing
`ℚ_ℓ/ℤ_ℓ`; without the noetherian hypothesis it fails for a rank-one local system on `𝔾_m` with
stalk `𝔽_ℓ[x, y₁, y₂, …]/(xˡ, x yᵢ)` and monodromy `1 + x`, whose `H⁰` is the non-finitely
generated annihilator of `x`; and for `N = p` on `𝔸¹` over `𝔽̄_p`, `H¹(𝔸¹, 𝔽_p)` is infinite
(Artin–Schreier). -/
theorem boundedConstructible_rightDerivedLowerStar [ConcreteCategory.FinitelyGeneratedOfMono A]
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
    [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (N : ℕ) [NeZero N]
    (hN : N • 𝟙 K = 0) (hNY : IsUnit (N : Γ(Y, ⊤))) (hbc : boundedConstructible A X K) :
    boundedConstructible A Y ((R((f)_*[A])).obj K) :=
  sorry

/-- Blueprint `sk-thm-sf-direct-image-tor-amplitude`: Direct image with finite Tor amplitude.

Let `f : X ⟶ Y` be a separated morphism of finite-type `k`-schemes with `dim X ≤ d`, and let `K`
be a bounded constructible complex on `X_ét` of Tor amplitude in `[a, b]`, killed by an integer
`N` invertible on `Y`. Then `Rf_* K` has Tor amplitude in `[a, b + 2d]`. The shift `2d` is the
uniform vanishing of `Rᵖf_*` above twice the dimension of the source. The coefficients are as in
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar`. -/
theorem torAmplitudeIn_rightDerivedLowerStar [ConcreteCategory.FinitelyGeneratedOfMono A]
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
    [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [IsSeparated f] (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (N : ℕ) [NeZero N]
    (hN : N • 𝟙 K = 0) (hNY : IsUnit (N : Γ(Y, ⊤)))
    (hbc : boundedConstructible A X K) (hta : torAmplitudeIn A X a b K) :
    torAmplitudeIn A Y a (b + 2 * (d : ℤ)) ((R((f)_*[A])).obj K) :=
  sorry

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor
subcategories.

Clause (iii): `Rf_* : Dctf(X, Λ) ⥤ Dctf(Y, Λ)` is defined for every separated morphism of
finite-type `k`-schemes, for a finite `Λ` whose exponent is invertible on `Y`. It is
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar` together with
`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar`, a finite-type `k`-scheme being
finite dimensional. -/
theorem constructibleFiniteTor_rightDerivedLowerStar {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY]
    [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX) [IsSeparated f] [HasInvertibleExponent Λ Y]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  obtain ⟨hbc, a, b, hta⟩ := hK
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aX
  obtain ⟨N, hN0, hNΛ, hNY⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := Y)
  have : NeZero N := ⟨hN0.ne'⟩
  have hN := nsmul_id_eq_zero_of_natCast_eq_zero hNΛ K
  have : IsNoetherianRing Λ := inferInstance
  exact ⟨boundedConstructible_rightDerivedLowerStar _ aX aY f hf N hN hNY hbc, a, b + 2 * (d : ℤ),
    torAmplitudeIn_rightDerivedLowerStar _ aX aY f hf d hd a b N hN hNY hbc hta⟩

/-! #### Internal hom -/

section DerivedHom

variable {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [HasInvertibleExponent Λ X] (m : ℕ) (hm : topologicalKrullDim X ≤ (m : WithBot ℕ∞))
  (a b c d : ℤ)
  {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}

include aX in
/-- Blueprint `sk-thm-sf-hom-ctf`: Internal Hom with finite Tor amplitude.

For `X` of finite type over `k`, a finite `Λ` whose exponent is invertible on `X` and bounded
constructible `K` and `M` on `X_ét` of finite Tor amplitude, the internal hom `RHom(K, M)` is
bounded constructible. -/
theorem boundedConstructible_derivedHom
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K)
    (hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M)
    (hMt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M) :=
  sorry

include aX hm in
/-- Blueprint `sk-thm-sf-hom-ctf`: Internal Hom with finite Tor amplitude.

If `K` and `M` have Tor amplitude in `[a, b]` and `[c, d]` and `dim X ≤ m`, then `RHom(K, M)`
has Tor amplitude in `[c - b - 2m, d - a + 2m]`. The blueprint derives this from
`RHom(K, M) ≅ 𝔻_X (K ⊗ᴸ 𝔻_X M)`, the dualizing complex having cohomology in `[-2m, 0]`. -/
theorem torAmplitudeIn_derivedHom
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K)
    (hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M)
    (hMt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b - 2 * (m : ℤ)) (d - a + 2 * (m : ℤ))
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M) :=
  sorry

include aX in
/-- Blueprint `sk-thm-sf-hom-ctf`: Internal Hom with finite Tor amplitude.

If moreover `K` is dualizable, the sharper interval `[c - b, d - a]` holds, from the local
identification `RHom(K, M) ≅ K^∨ ⊗ᴸ M`. It genuinely fails in general: for the origin
`i : {0} ⟶ 𝔸¹` both `i_* Λ` and `Λ` have Tor amplitude `[0, 0]` while
`RHom(i_* Λ, Λ) = i_* Λ(-1)[-2]`. -/
theorem torAmplitudeIn_derivedHom_of_isDualizable
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) (hKd : IsDualizable K)
    (hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M)
    (hMt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b) (d - a)
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M) :=
  sorry

end DerivedHom

/-! #### The exceptional inverse image -/

/-- Blueprint `sk-prop-sf-rf-shriek-preservation`: Preservation for the exceptional inverse
image.

Clause (ii): for a closed immersion `i : Z ⟶ T` into a finite-type `k`-scheme of dimension
`≤ d`, and a finite `Λ` whose exponent is invertible on `T`, the exceptional inverse image widens
the upper end of the interval by `2d + 1`, that is, `D_c^[a, b] ↦ D_c^[a, b + 2d + 1]`. The bound
is in terms of the dimension of the target, and comes from the localization triangle for the
open complement, the vanishing of étale cohomology above twice the dimension giving the `2d`
and the triangle the extra `+1`. No bound in terms of the codimension alone holds: for
`Z = V(y) ⊂ T = Spec k[x, y]/(xy)`, `H²(Ri^!Λ)` is nonzero at the origin, coming from the
punctured `y`-axis, although `Z` has codimension `0`. For `Z` regular of pure codimension `c` in
a regular `T`, the sharp `Ri^!Λ_T ≅ Λ_Z(-c)[-2c]` is `sk-thm-regular`. -/
theorem constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion
    {Z T : Scheme.{u}} (aT : T ⟶ Spec (.of k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
    [HasInvertibleExponent Λ T] (i : Z ⟶ T) [IsClosedImmersion i] [HasCompactification i]
    (d : ℕ) (hd : topologicalKrullDim T ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) T a b K) :
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Z a (b + 2 * d + 1)
      ((R(i)^![ModuleCat.{u + 1} Λ]).obj K) :=
  sorry

/-- Blueprint `sk-prop-sf-rf-shriek-preservation`: Preservation for the exceptional inverse
image.

Clause (iii): for `f` smooth of pure relative dimension `d` and a finite `Λ` whose exponent is
invertible on `Y`, the exceptional inverse image shifts both intervals by `-2d`,
`D_c^[a, b] ↦ D_c^[a - 2d, b - 2d]`, by purity `Rf^! ≅ Lf^*(-)(d)[2d]`. -/
theorem constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_smoothOfRelativeDimension
    {X Y : Scheme.{u}} [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] (d : ℕ)
    [SmoothOfRelativeDimension d f] (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K) :
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * d) (b - 2 * d)
      ((R(f)^![ModuleCat.{u + 1} Λ]).obj K) :=
  sorry

/-- Blueprint `sk-prop-sf-rf-shriek-preservation`: Preservation for the exceptional inverse
image.

Clause (iv), with its constants: let `f : X ⟶ Y` be a separated finite-type morphism admitting
a compactification, with `Y` of finite type over `k`, and let `Λ` be finite with exponent
invertible on `Y`. There is a `D`, depending only on `f`, such that whenever `dim Y ≤ d`, `Rf^!`
sends `D_c^[a, b]` into `D_c^[a - 2D, b + 2d + 1]`. Here `D` is the maximal embedding dimension
of the affine charts `U ↪ 𝔸^{d_U}_V` of `f`.

The proof has three steps.
1. Localise: the amplitudes are Zariski-local on `X` and `Rj^! = j^*` for an open immersion
   `j`, so it suffices to treat finitely many affine charts `U ↪ 𝔸^{n}_V ⟶ V` with `n ≤ D`;
   finitely many suffice because `Y` is quasi-compact.
2. Compose: the smooth clause (iii) for `𝔸^n_V ⟶ V` sends `[a, b]` to `[a - 2n, b - 2n]`, and
   the closed-immersion clause (ii) into `𝔸^n_V` then sends it to
   `[a - 2n, b - 2n + 2(d + n) + 1]`.
3. Count dimensions: `dim 𝔸^n_V = dim V + n ≤ d + n`, so the upper end is `b + 2d + 1`. -/
theorem exists_constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_topologicalKrullDim_le
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] :
    ∃ D : ℕ, ∀ (d : ℕ), topologicalKrullDim Y ≤ (d : WithBot ℕ∞) →
      ∀ (a b : ℤ) (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
          constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * D) (b + 2 * d + 1)
            ((R(f)^![ModuleCat.{u + 1} Λ]).obj K) :=
  sorry

/-- Blueprint `sk-prop-sf-rf-shriek-preservation`: Preservation for the exceptional inverse
image.

Clause (iv), dimension-free form with the shift forgotten: every separated finite-type `f`
admitting a compactification, over a finite-type `k`-scheme `Y`, preserves the constructible
intervals up to a single shift `c`, depending only on `f`, widening every interval `[a, b]` to
`[a - c, b + c]`. Since `Y` is finite dimensional, say `dim Y ≤ d`, this is the preceding
theorem with `c = 2D + 2d + 1`. -/
theorem exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] :
    ∃ c : ℤ, ∀ (a b : ℤ)
      (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
        constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - c) (b + c)
          ((R(f)^![ModuleCat.{u + 1} Λ]).obj K) := by
  obtain ⟨D, hD⟩ :=
    exists_constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_topologicalKrullDim_le Λ aY f
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aY
  refine ⟨2 * D + 2 * d + 1, fun a b K hK ↦ ?_⟩
  obtain ⟨⟨hbc, hconc⟩, hta⟩ := hD d hd a b K hK
  exact ⟨⟨hbc, hconc.mono (by omega) (by omega)⟩, hta.mono (by omega) (by omega)⟩

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor
subcategories.

Clause (v): `Rf^! : Dctf(Y, Λ) ⥤ Dctf(X, Λ)` is defined for every separated finite-type `f`
admitting a compactification, over a finite-type `k`-scheme `Y`, for a finite `Λ` whose exponent
is invertible on `Y`. This is
`AlgebraicGeometry.Etale.exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek`
with the shift forgotten. -/
theorem constructibleFiniteTor_rightDerivedUpperShriek {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X ((R(f)^![ModuleCat.{u + 1} Λ]).obj K) := by
  obtain ⟨c, hc⟩ := exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek Λ aY f
  obtain ⟨a, b, hab⟩ :=
    (exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor K).2 hK
  exact (exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor _).1
    ⟨a - c, b + c, hc a b K hab⟩

/-- The dualizing complex `ω_Y = Ra_Y^! Λ_S` lies in `Dctf(Y, Λ)` when the unit `Λ_S` does,
for `S` of finite type over a field `k` and a finite `Λ` whose exponent is invertible on `S`, by
the stability of `Dctf` under `Ra_Y^!`. In the blueprint's setting (`S` the spectrum of a
field) the unit is in `Dctf`. -/
theorem constructibleFiniteTor_dualizingComplex {Y S : Scheme.{u}} (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [HasInvertibleExponent Λ S] (aY : Y ⟶ S)
    [HasCompactification aY] [QuasiCompact aY]
    (hΛ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) S (𝟙_ _)) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y (dualizingComplex _ aY) :=
  constructibleFiniteTor_rightDerivedUpperShriek Λ aS aY hΛ

/-! #### The descended functors -/

section Functors

variable {X Y : Scheme.{u}}

/-- Blueprint `sk-thm-sf-ctf-stability`, clause (iii): the restriction
`Rf_* : Dctf(X, Λ) ⥤ Dctf(Y, Λ)` of the derived direct image to the small categories, for a
separated morphism of finite-type `k`-schemes and a finite `Λ` whose exponent is invertible on
`Y`. -/
noncomputable def DerivedCategoryFiniteTor.rightDerivedLowerStar (aX : X ⟶ Spec (.of k))
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY]
    [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX) [IsSeparated f]
    [HasInvertibleExponent Λ Y] :
    DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X ⥤
      DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y :=
  ObjectProperty.lift _
    (DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) X ⋙ R((f)_*[ModuleCat.{u + 1} Λ]))
    fun K ↦ constructibleFiniteTor_rightDerivedLowerStar Λ aX aY f hf K.property

/-- Blueprint `sk-thm-sf-ctf-stability`, clause (v): the restriction
`Rf^! : Dctf(Y, Λ) ⥤ Dctf(X, Λ)` of the exceptional inverse image to the small categories, for
a separated finite-type `f` over a finite-type `k`-scheme `Y` and a finite `Λ` whose exponent
is invertible on `Y`. -/
noncomputable def DerivedCategoryFiniteTor.rightDerivedUpperShriek (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [HasInvertibleExponent Λ Y] (f : X ⟶ Y)
    [HasCompactification f] [QuasiCompact f] :
    DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y ⥤
      DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X :=
  ObjectProperty.lift _
    (DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) Y ⋙ R(f)^![ModuleCat.{u + 1} Λ])
    fun K ↦ constructibleFiniteTor_rightDerivedUpperShriek Λ aY f K.property

end Functors

end Torsion

/-! ### Tor amplitude of a flat sheaf -/

section FlatSheaf

variable (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}

/-- Tor amplitude in the sense of `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`,
tested on one homology sheaf at a time, is Tor amplitude in the sense of
`AlgebraicGeometry.Etale.DerivedCategory.torAmplitudeIn`, tested through the canonical
t-structure. -/
lemma torAmplitudeIn_of_hasTorAmplitudeIn {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h : DerivedCategory.hasTorAmplitudeIn Λ X a b K) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K := fun F ↦ by
  rw [_root_.DerivedCategory.homologyConcentratedIn_iff]
  exact ⟨(_root_.DerivedCategory.isGE_iff _ a).2 fun q hq ↦ h F q (.inl hq),
    (_root_.DerivedCategory.isLE_iff _ b).2 fun q hq ↦ h F q (.inr hq)⟩

/-- A flat constructible sheaf placed in degree `0` has Tor amplitude in `[0, 0]`: the single
complex is its own bounded flat model
(`AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatModel`). -/
theorem torAmplitudeIn_singleFunctor_obj_of_flat
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    (hF : ObjectProperty.flat F) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X 0 0
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F) := by
  refine torAmplitudeIn_of_hasTorAmplitudeIn Λ ((hasTorAmplitudeIn_iff_exists_flatModel Λ 0 0
    le_rfl _ (DerivedCategory.boundedConstructible_singleFunctor_obj F 0)).2
    ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F, ⟨fun q hq ↦ ?_, fun q ↦ ?_⟩,
      ⟨(_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app F⟩⟩)
  · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  · by_cases hq : q = 0
    · subst hq
      exact ObjectProperty.prop_of_iso _ (HomologicalComplex.singleObjXSelf _ 0 F).symm hF
    · exact ObjectProperty.flat_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)

end FlatSheaf

/-! ### Generation of `Dctf` -/

/-- Blueprint `sk-lem-sf-ctf-generation`: Finite/open generation of `Dctf`.

Let `X` be a Noetherian scheme and `Λ` a finite ring. Then `Dctf(X, Λ)` is generated as a
thick subcategory by the objects `Rg_* Rj_! L`, where `U` is a stratum of a stratification of
`X`, `j : U ⟶ Ū` is the open immersion of `U` into its closure, `g : Ū ⟶ X` is the closed
immersion of that closure, and `L` is a lisse (finite locally constant) flat sheaf of
`Λ`-modules on `U`. Note the order: lower-star outside lower-shriek.

"Thick subcategory generated by" is unwound here: any property `P` of objects of `D(X_ét, Λ)`
that is triangulated, stable under retracts and closed under isomorphisms, and that holds for
all the generators above, holds for every object of `Dctf(X, Λ)`.

The lisse coefficients cannot be replaced by constant ones `Λ_U`: for `X = 𝔾_m`, `p ≠ 2` and
`Λ = 𝔽₃`, the complexes whose generic-stalk cohomology has only trivial `π₁`-composition factors
form a thick subcategory containing every `Rg_* Rj_! Λ_U` but not the order-`2` Kummer sheaf.

The proof resolves `K` by a bounded complex of flat constructible sheaves
(`AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatConstructibleModel`), reduces to one
flat constructible sheaf `F` by the stupid-truncation triangles, and then uses the open–closed
sequence `0 ⟶ j_!(F|_U) ⟶ F ⟶ i_* i^* F ⟶ 0` for a dense open `U` on which `F` is lisse,
together with Noetherian induction on the closed subsets of `X`. -/
theorem ctf_generated_by_rightDerivedLowerStar_rightDerivedLowerShriek (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] (X : Scheme.{u}) [IsNoetherian X]
    (P : ObjectProperty
      (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    [P.IsTriangulated] [P.IsStableUnderRetracts] [P.IsClosedUnderIsomorphisms]
    (hP : ∀ (str : Scheme.Stratification X) (i : Fin str.n) (Ubar : Scheme.{u})
      (j : str.domain i ⟶ Ubar) [IsOpenImmersion j] [HasCompactification j]
      (g : Ubar ⟶ X) [IsClosedImmersion g], Set.range (j ≫ g) = str.stratum i →
      Set.range g = _root_.closure (str.stratum i) →
      ∀ (L : Sheaf (str.domain i).smallEtaleTopology (ModuleCat.{u + 1} Λ))
        [IsFiniteLocallyConstantSheaf L], ObjectProperty.flat L →
        P ((R((g)_*[ModuleCat.{u + 1} Λ])).obj ((R(j)_![ModuleCat.{u + 1} Λ]).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L))))
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    P K :=
  sorry

end Etale

end AlgebraicGeometry
