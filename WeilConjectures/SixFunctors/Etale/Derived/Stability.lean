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
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

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

/-! ### Extension by zero -/

/-- Blueprint `sk-lem-sf-open-ctf`: Extension by zero preserves the finite-Tor constructible
category.

For an open immersion `j : U ⟶ Y` admitting a compactification, extension by zero sends
`Dctf(U, A)` into `Dctf(Y, A)` *without moving the interval*: if `K` is bounded constructible
with homology concentrated in `[a, b]` and Tor amplitude in `[a, b]`, then so is `Rj_! K`. -/
theorem constructibleTorAmplitudeIn_rightDerivedLowerShriek {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] [HasCompactification j] (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf U.smallEtaleTopology A)}
    (hK : constructibleTorAmplitudeIn A U a b K) :
    constructibleTorAmplitudeIn A Y a b ((R(j)_![A]).obj K) :=
  sorry

/-! ### Direct image -/

/-- Blueprint `sk-thm-sf-direct-image-tor-amplitude`: Direct image with finite Tor amplitude.

Let `f : X ⟶ Y` be separated of finite type with `dim X ≤ d`, and let `K` be a bounded
constructible complex on `X_ét` of Tor amplitude in `[a, b]`. Then `Rf_* K` is bounded
constructible on `Y_ét`. -/
theorem boundedConstructible_rightDerivedLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hbc : boundedConstructible A X K) (hta : torAmplitudeIn A X a b K) :
    boundedConstructible A Y ((R((f)_*[A])).obj K) :=
  sorry

/-- Blueprint `sk-thm-sf-direct-image-tor-amplitude`: Direct image with finite Tor amplitude.

In the situation of `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar`, the
direct image has Tor amplitude in `[a, b + 2d]`. The shift `2d` is the uniform vanishing of
`Rᵖf_*` above twice the dimension of the source. -/
theorem torAmplitudeIn_rightDerivedLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hbc : boundedConstructible A X K) (hta : torAmplitudeIn A X a b K) :
    torAmplitudeIn A Y a (b + 2 * (d : ℤ)) ((R((f)_*[A])).obj K) :=
  sorry

/-! ### Internal hom -/

section DerivedHom

variable (X : Scheme.{u}) (m : ℕ) (hm : topologicalKrullDim X ≤ (m : WithBot ℕ∞)) (a b c d : ℤ)
  {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}

/-- Blueprint `sk-thm-sf-hom-ctf`: Internal Hom with finite Tor amplitude.

For bounded constructible `K` and `M` on `X_ét`, the internal hom `RHom(K, M)` is bounded
constructible. -/
theorem boundedConstructible_derivedHom (hK : boundedConstructible A X K)
    (hKt : torAmplitudeIn A X a b K) (hM : boundedConstructible A X M)
    (hMt : torAmplitudeIn A X c d M) :
    boundedConstructible A X (((RHom(X)[A]).obj (op K)).obj M) :=
  sorry

/-- Blueprint `sk-thm-sf-hom-ctf`: Internal Hom with finite Tor amplitude.

If `K` and `M` have Tor amplitude in `[a, b]` and `[c, d]` and `dim X ≤ m`, then `RHom(K, M)`
has Tor amplitude in `[c - b - 2m, d - a + 2m]`. The blueprint derives this from
`RHom(K, M) ≅ 𝔻_X (K ⊗ᴸ 𝔻_X M)`, the dualizing complex having cohomology in `[-2m, 0]`. -/
theorem torAmplitudeIn_derivedHom (hK : boundedConstructible A X K)
    (hKt : torAmplitudeIn A X a b K) (hM : boundedConstructible A X M)
    (hMt : torAmplitudeIn A X c d M) :
    torAmplitudeIn A X (c - b - 2 * (m : ℤ)) (d - a + 2 * (m : ℤ))
      (((RHom(X)[A]).obj (op K)).obj M) :=
  sorry

/-- Blueprint `sk-thm-sf-hom-ctf`: Internal Hom with finite Tor amplitude.

If moreover `K` is dualizable, the sharper interval `[c - b, d - a]` holds, from the local
identification `RHom(K, M) ≅ K^∨ ⊗ᴸ M`. It genuinely fails in general: for the origin
`i : {0} ⟶ 𝔸¹` both `i_* A` and `A` have Tor amplitude `[0, 0]` while
`RHom(i_* A, A) = i_* A(-1)[-2]`. -/
theorem torAmplitudeIn_derivedHom_of_isDualizable (hK : boundedConstructible A X K)
    (hKt : torAmplitudeIn A X a b K) (hKd : IsDualizable K)
    (hM : boundedConstructible A X M) (hMt : torAmplitudeIn A X c d M) :
    torAmplitudeIn A X (c - b) (d - a) (((RHom(X)[A]).obj (op K)).obj M) :=
  sorry

end DerivedHom

/-! ### The exceptional inverse image -/

/-- Blueprint `sk-prop-sf-rf-shriek-preservation`: Preservation for the exceptional inverse
image.

Clause (i), open-immersion case: for an open immersion `f`, `Rf^!` preserves the constructible
interval and the Tor amplitude *unchanged*, the ambient right adjoint being the exact functor
`Lf^*`. -/
theorem constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] [HasCompactification f] (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hK : constructibleTorAmplitudeIn A Y a b K) :
    constructibleTorAmplitudeIn A X a b ((R(f)^![A]).obj K) :=
  sorry

/-- Blueprint `sk-prop-sf-rf-shriek-preservation`: Preservation for the exceptional inverse
image.

Clause (i), finite étale case: for a finite étale `f`, `Rf^!` preserves the constructible
interval and the Tor amplitude *unchanged*. -/
theorem constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isFinite_of_etale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [_root_.AlgebraicGeometry.Etale f]
    [HasCompactification f] (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hK : constructibleTorAmplitudeIn A Y a b K) :
    constructibleTorAmplitudeIn A X a b ((R(f)^![A]).obj K) :=
  sorry

/-- Blueprint `sk-prop-sf-rf-shriek-preservation`: Preservation for the exceptional inverse
image.

Clause (ii): for a closed immersion `i : Z ⟶ T` into a target of dimension `≤ d`, the
exceptional inverse image widens the upper end of the interval by `2d + 1`, that is,
`D_c^[a, b] ↦ D_c^[a, b + 2d + 1]`. The bound is in terms of the dimension of the target, and
comes from the localization triangle for the open complement, the vanishing of étale cohomology
above twice the dimension giving the `2d` and the triangle the extra `+1`. No bound in terms of
the codimension alone holds: for `Z = V(y) ⊂ T = Spec k[x, y]/(xy)`, `H²(Ri^!Λ)` is nonzero at
the origin, coming from the punctured `y`-axis, although `Z` has codimension `0`. For `Z`
regular of pure codimension `c` in a regular `T`, the sharp `Ri^!Λ_T ≅ Λ_Z(-c)[-2c]` is
`sk-thm-regular`. -/
theorem constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] [HasCompactification i] (d : ℕ)
    (hd : topologicalKrullDim T ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)}
    (hK : constructibleTorAmplitudeIn A T a b K) :
    constructibleTorAmplitudeIn A Z a (b + 2 * d + 1) ((R(i)^![A]).obj K) :=
  sorry

/-- Blueprint `sk-prop-sf-rf-shriek-preservation`: Preservation for the exceptional inverse
image.

Clause (iii): for `f` smooth of pure relative dimension `d`, the exceptional inverse image
shifts both intervals by `-2d`, `D_c^[a, b] ↦ D_c^[a - 2d, b - 2d]`, by purity
`Rf^! ≅ Lf^*(-)(d)[2d]`. -/
theorem constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_smoothOfRelativeDimension
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (d : ℕ)
    [SmoothOfRelativeDimension d f] (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hK : constructibleTorAmplitudeIn A Y a b K) :
    constructibleTorAmplitudeIn A X (a - 2 * d) (b - 2 * d) ((R(f)^![A]).obj K) :=
  sorry

/-- Blueprint `sk-prop-sf-rf-shriek-preservation`: Preservation for the exceptional inverse
image.

Clause (iv), with its constants: let `f : X ⟶ Y` be separated of finite type, admitting a
compactification, with `Y` Noetherian. There is a `D`, depending only on `f`, such that whenever
`dim Y ≤ d`, `Rf^!` sends `D_c^[a, b]` into `D_c^[a - 2D, b + 2d + 1]`. Here `D` is the maximal
embedding dimension of the affine charts `U ↪ 𝔸^{d_U}_V` of `f`.

The proof has three steps.
1. Localise: the amplitudes are Zariski-local on `X` and `Rj^! = j^*` for an open immersion
   `j`, so it suffices to treat finitely many affine charts `U ↪ 𝔸^{n}_V ⟶ V` with `n ≤ D`;
   finitely many suffice because `Y` is quasi-compact.
2. Compose: the smooth clause (iii) for `𝔸^n_V ⟶ V` sends `[a, b]` to `[a - 2n, b - 2n]`, and
   the closed-immersion clause (ii) into `𝔸^n_V` then sends it to
   `[a - 2n, b - 2n + 2(d + n) + 1]`.
3. Count dimensions: `dim 𝔸^n_V = dim V + n ≤ d + n`, using that `V` is Noetherian, so the upper
   end is `b + 2d + 1`. -/
theorem exists_constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_topologicalKrullDim_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsNoetherian Y] :
    ∃ D : ℕ, ∀ (d : ℕ), topologicalKrullDim Y ≤ (d : WithBot ℕ∞) →
      ∀ (a b : ℤ) (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)),
        constructibleTorAmplitudeIn A Y a b K →
          constructibleTorAmplitudeIn A X (a - 2 * D) (b + 2 * d + 1) ((R(f)^![A]).obj K) :=
  sorry

/-- Blueprint `sk-prop-sf-rf-shriek-preservation`: Preservation for the exceptional inverse
image.

Clause (iv), dimension-free form with the shift forgotten: every separated finite-type `f`
admitting a compactification, over a Noetherian `Y`, preserves the constructible intervals up
to a single shift `c`, depending only on `f`, widening every interval `[a, b]` to
`[a - c, b + c]`. When `dim Y ≤ d` this follows from the preceding theorem, with
`c = max(2D, 2d + 1)`. Under the blueprint's standing hypothesis (finite type over a
field) `dim Y` is always finite, but this repository cannot yet prove that, so no dimension
hypothesis is imposed here: clause (v) of `sk-thm-sf-ctf-stability`
(`AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedUpperShriek`) is proved from it. -/
-- TODO: once finite-type schemes over a field are known to be finite-dimensional, state this
-- under that hypothesis and prove it from the constant-bearing form above.
theorem exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsNoetherian Y] :
    ∃ c : ℤ, ∀ (a b : ℤ) (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)),
      constructibleTorAmplitudeIn A Y a b K →
        constructibleTorAmplitudeIn A X (a - c) (b + c) ((R(f)^![A]).obj K) :=
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
  sorry

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor
subcategories.

Clause (i), amplitude: `Lf^*` preserves the Tor amplitude interval unchanged, the pullback of
a bounded flat model being a bounded flat model in the same degrees. -/
theorem torAmplitudeIn_leftDerivedUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hta : torAmplitudeIn A Y a b K) :
    torAmplitudeIn A X a b ((L((f)^*[A])).obj K) :=
  sorry

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor
subcategories.

Clause (i): `Lf^* : Dctf(Y, A) ⥤ Dctf(X, A)` is defined. -/
theorem constructibleFiniteTor_leftDerivedUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hK : constructibleFiniteTor A Y K) :
    constructibleFiniteTor A X ((L((f)^*[A])).obj K) := by
  obtain ⟨hbc, a, b, hta⟩ := hK
  exact ⟨boundedConstructible_leftDerivedUpperStar A f hbc,
    a, b, torAmplitudeIn_leftDerivedUpperStar A f a b hta⟩

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor
subcategories.

Clause (ii), constructibility: the derived tensor product of two bounded constructible
complexes, one of them of finite Tor amplitude, is bounded constructible. Finite Tor amplitude
of one factor is needed for boundedness: over `ℤ/ℓ²` on a point, `ℤ/ℓ ⊗ᴸ ℤ/ℓ` has a nonzero
`Tor_i` for every `i ≥ 0`. -/
theorem boundedConstructible_tensor (X : Scheme.{u})
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : boundedConstructible A X K) (hM : boundedConstructible A X M)
    (hMt : finiteTorAmplitude A X M) :
    boundedConstructible A X (((-⊗ᴸ-(X)[A]).obj K).obj M) :=
  sorry

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor
subcategories.

Clause (ii), amplitude: Tor amplitudes add under the derived tensor product,
`[a, b], [c, d] ↦ [a + c, b + d]`. -/
theorem torAmplitudeIn_tensor (X : Scheme.{u}) (a b c d : ℤ)
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hKt : torAmplitudeIn A X a b K) (hMt : torAmplitudeIn A X c d M) :
    torAmplitudeIn A X (a + c) (b + d) (((-⊗ᴸ-(X)[A]).obj K).obj M) :=
  sorry

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor
subcategories.

Clause (ii): `- ⊗ᴸ - : Dctf(X, A) × Dctf(X, A) ⥤ Dctf(X, A)` is defined. The internal-Hom
half of the clause is `AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom` above. -/
theorem constructibleFiniteTor_tensor (X : Scheme.{u})
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : constructibleFiniteTor A X K) (hM : constructibleFiniteTor A X M) :
    constructibleFiniteTor A X (((-⊗ᴸ-(X)[A]).obj K).obj M) := by
  obtain ⟨hKbc, a, b, hKt⟩ := hK
  obtain ⟨hMbc, c, d, hMt⟩ := hM
  exact ⟨boundedConstructible_tensor A X hKbc hMbc ⟨c, d, hMt⟩,
    a + c, b + d, torAmplitudeIn_tensor A X a b c d hKt hMt⟩

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor
subcategories.

Clause (iii): `Rf_* : Dctf(X, A) ⥤ Dctf(Y, A)` is defined for every separated finite-type `f`.
This is `AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar` with the dimension bound
forgotten; the missing input that would turn it into a proof is that a finite-type scheme has
finite topological Krull dimension, which this repository does not yet have. -/
theorem constructibleFiniteTor_rightDerivedLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : constructibleFiniteTor A X K) :
    constructibleFiniteTor A Y ((R((f)_*[A])).obj K) :=
  sorry

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor
subcategories.

Clause (iv): `Rf_! : Dctf(X, A) ⥤ Dctf(Y, A)` is defined for every separated finite-type `f`
admitting a compactification. One assembles the open-immersion case
(`AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedLowerShriek`) with the proper
case, where `Rf_! = Rf_*`, along a compactification of `f`. -/
theorem constructibleFiniteTor_rightDerivedLowerShriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [QuasiCompact f]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : constructibleFiniteTor A X K) :
    constructibleFiniteTor A Y ((R(f)_![A]).obj K) :=
  sorry

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor
subcategories.

Clause (v): `Rf^! : Dctf(Y, A) ⥤ Dctf(X, A)` is defined for every separated finite-type `f`
admitting a compactification, over a Noetherian `Y`. This is
`AlgebraicGeometry.Etale.exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek`
with the shift forgotten. -/
theorem constructibleFiniteTor_rightDerivedUpperShriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [QuasiCompact f] [IsNoetherian Y]
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hK : constructibleFiniteTor A Y K) :
    constructibleFiniteTor A X ((R(f)^![A]).obj K) := by
  obtain ⟨c, hc⟩ := exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek A f
  obtain ⟨a, b, hab⟩ :=
    (exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor K).2 hK
  exact (exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor _).1
    ⟨a - c, b + c, hc a b K hab⟩

/-! ### The descended functors -/

section Functors

variable {X Y : Scheme.{u}}

/-- Blueprint `sk-thm-sf-ctf-stability`, clause (i): the restriction
`Lf^* : Dctf(Y, A) ⥤ Dctf(X, A)` of the derived pullback to the small categories. -/
noncomputable def DerivedCategoryFiniteTor.leftDerivedUpperStar (f : X ⟶ Y) :
    DerivedCategoryFiniteTor A Y ⥤ DerivedCategoryFiniteTor A X :=
  ObjectProperty.lift _ (DerivedCategoryFiniteTor.ι A Y ⋙ L((f)^*[A]))
    fun K ↦ constructibleFiniteTor_leftDerivedUpperStar A f K.property

/-- Blueprint `sk-thm-sf-ctf-stability`, clause (iii): the restriction
`Rf_* : Dctf(X, A) ⥤ Dctf(Y, A)` of the derived direct image to the small categories. -/
noncomputable def DerivedCategoryFiniteTor.rightDerivedLowerStar (f : X ⟶ Y) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    DerivedCategoryFiniteTor A X ⥤ DerivedCategoryFiniteTor A Y :=
  ObjectProperty.lift _ (DerivedCategoryFiniteTor.ι A X ⋙ R((f)_*[A]))
    fun K ↦ constructibleFiniteTor_rightDerivedLowerStar A f K.property

/-- Blueprint `sk-thm-sf-ctf-stability`, clause (iv): the restriction
`Rf_! : Dctf(X, A) ⥤ Dctf(Y, A)` of the compactly supported direct image to the small
categories. -/
noncomputable def DerivedCategoryFiniteTor.rightDerivedLowerShriek (f : X ⟶ Y)
    [HasCompactification f] [QuasiCompact f] :
    DerivedCategoryFiniteTor A X ⥤ DerivedCategoryFiniteTor A Y :=
  ObjectProperty.lift _ (DerivedCategoryFiniteTor.ι A X ⋙ R(f)_![A])
    fun K ↦ constructibleFiniteTor_rightDerivedLowerShriek A f K.property

/-- Blueprint `sk-thm-sf-ctf-stability`, clause (v): the restriction
`Rf^! : Dctf(Y, A) ⥤ Dctf(X, A)` of the exceptional inverse image to the small categories. -/
noncomputable def DerivedCategoryFiniteTor.rightDerivedUpperShriek (f : X ⟶ Y)
    [HasCompactification f] [QuasiCompact f] [IsNoetherian Y] :
    DerivedCategoryFiniteTor A Y ⥤ DerivedCategoryFiniteTor A X :=
  ObjectProperty.lift _ (DerivedCategoryFiniteTor.ι A Y ⋙ R(f)^![A])
    fun K ↦ constructibleFiniteTor_rightDerivedUpperShriek A f K.property

/-- Blueprint `sk-thm-sf-ctf-stability`, clause (vi): the restriction
`𝔻_X : Dctf(X, A)ᵒᵖ ⥤ Dctf(X, A)` of the Verdier dual to the small categories. That it is an
anti-equivalence is `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual`. -/
noncomputable def DerivedCategoryFiniteTor.verdierDual {S : Scheme.{u}} (a : X ⟶ S)
    [HasCompactification a] :
    (DerivedCategoryFiniteTor A X)ᵒᵖ ⥤ DerivedCategoryFiniteTor A X :=
  ObjectProperty.lift _ ((DerivedCategoryFiniteTor.ι A X).op ⋙ Etale.verdierDual A a)
    fun K ↦ constructibleFiniteTor_verdierDual A a K.unop.property

end Functors

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
