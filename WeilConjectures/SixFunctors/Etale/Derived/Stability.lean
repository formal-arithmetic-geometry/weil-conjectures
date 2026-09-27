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
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!

# Stability of the constructible finite-Tor categories under the six operations

Let `A` be a monoidal Grothendieck abelian coefficient category. This file states that the six
operations of `WeilConjectures.SixFunctors.Etale.Derived.*` preserve the small categories
`D_c^[a, b](X, A)` and `Dctf(X, A)` of
`WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude`, together with the explicit shifts the
blueprint records for the cohomological range and for the Tor amplitude.

Following the convention of this branch, membership of `Dctf(X, A)` is spelled out on an object
`K` of `D(X_ét)` as the conjunction
`Etale.DerivedCategory.boundedConstructible A X K ∧ Etale.DerivedCategory.finiteTorAmplitude A X K`
rather than by quantifying over the full subcategory, and an interval is recorded by the pair of
properties `Etale.DerivedCategory.homologyConcentratedIn` and
`Etale.DerivedCategory.torAmplitudeIn`.

A dimension bound `dim X ≤ d` is `topologicalKrullDim X ≤ (d : WithBot ℕ∞)`; the ambient datum a
morphism must carry for `Rf_!` and `Rf^!` to exist is `HasCompactification f`, taken as an
explicit hypothesis throughout (it is *not* automatic for an open immersion, Nagata's theorem
requiring a quasi-compact quasi-separated target).

## Main statements

- `AlgebraicGeometry.Etale.lowerShriek_preserves_constructible_torAmplitudeIn`
  (`sk-lem-sf-open-ctf`).
- `AlgebraicGeometry.Etale.rightDerivedLowerStar_torAmplitudeIn`
  (`sk-thm-sf-direct-image-tor-amplitude`).
- `AlgebraicGeometry.Etale.derivedHom_torAmplitudeIn` (`sk-thm-sf-hom-ctf`).
- `AlgebraicGeometry.Etale.upperShriek_preserves_of_isOpenImmersion_or_finiteEtale`,
  `AlgebraicGeometry.Etale.upperShriek_preserves_of_isClosedImmersion`,
  `AlgebraicGeometry.Etale.upperShriek_preserves_of_smoothOfRelativeDimension`,
  `AlgebraicGeometry.Etale.exists_shift_upperShriek_preserves`
  (`sk-prop-sf-rf-shriek-preservation`, clauses (i)–(iv)).
- `AlgebraicGeometry.Etale.ctfStability_leftDerivedUpperStar`,
  `AlgebraicGeometry.Etale.ctfStability_tensor`,
  `AlgebraicGeometry.Etale.ctfStability_rightDerivedLowerStar`,
  `AlgebraicGeometry.Etale.ctfStability_rightDerivedLowerShriek`,
  `AlgebraicGeometry.Etale.ctfStability_rightDerivedUpperShriek`,
  `AlgebraicGeometry.Etale.ctfStability_verdierDual`
  (`sk-thm-sf-ctf-stability`, clauses (i)–(vi)).
- `AlgebraicGeometry.Etale.ctf_generated_by_lowerShriek_lowerStar_unit`
  (`sk-lem-sf-ctf-generation`).

## Implementation notes

* Clause (vii) of `sk-thm-sf-ctf-stability` — compatibility of each of (i)–(vi) with finite
  reduction, with scalar extension and with the pro-étale realization — is **not stated**. It
  quantifies over the coefficient stages `A_{E,n} ⇝ 𝒪_E ⇝ E ⇝ ℚ̄_ℓ` and over the étale/pro-étale
  comparison `ν^*`, neither of which is available: the coefficient stages are modelled here by
  *choosing* a coefficient category `A := ModuleCat R`, so a statement relating two choices needs
  a change-of-coefficients functor that the library does not yet have.
* The internal-Hom half of clause (ii) of `sk-thm-sf-ctf-stability` is not restated: it *is*
  `derivedHom_torAmplitudeIn` below, with the same shifts `[c - b - 2m, d - a + 2m]` and
  `[c - b, d - a]`. Only the tensor half is given its own `ctfStability_*` declaration.
* "Thick subcategory" in `sk-lem-sf-ctf-generation` is spelled as an `ObjectProperty` that is
  `ObjectProperty.IsTriangulated`, `ObjectProperty.IsStableUnderRetracts` and
  `ObjectProperty.IsClosedUnderIsomorphisms`; generation is the statement that any such property
  containing the generators contains all of `Dctf(X, A)`. Mathlib has no `thickClosure`.
* The counterexample of `sk-thm-sf-hom-ctf` (the origin in `𝔸¹`, showing that the sharper
  interval fails without site-perfectness) is prose only and is not formalised.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite Functor

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

For an open immersion `j : U ⟶ Y` carrying the ambient datum, extension by zero sends
`Dctf(U, A)` into `Dctf(Y, A)` *without moving either interval*: if `K` is bounded constructible
with homology concentrated in `[a, b]` and Tor amplitude in `[a, b]`, then so is `Rj_! K`. The
reason is that `j_!` is exact, so `Hʳ(j_! K) = j_! Hʳ(K)`, that a finite stratification of `U`
together with the closed complement `Y \ U` stratifies `Y`, and that the amplitude of `Rj_! K` is
tested by restricting an arbitrary sheaf on `Y` back to `U`. -/
theorem lowerShriek_preserves_constructible_torAmplitudeIn {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] [HasCompactification j] (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf U.smallEtaleTopology A)}
    (hbc : boundedConstructible A U K) (hhc : homologyConcentratedIn A U a b K)
    (hta : torAmplitudeIn A U a b K) :
    boundedConstructible A Y ((R(j)_![A]).obj K) ∧
      homologyConcentratedIn A Y a b ((R(j)_![A]).obj K) ∧
      torAmplitudeIn A Y a b ((R(j)_![A]).obj K) :=
  sorry

/-! ### Direct image -/

/-- Blueprint `sk-thm-sf-direct-image-tor-amplitude`: Direct image with finite Tor amplitude.

Let `f : X ⟶ Y` be separated of finite type with `dim X ≤ d`, and let `K` be a bounded
constructible complex on `X_ét` of finite Tor amplitude in `[a, b]`. Then `Rf_* K` is bounded
constructible on `Y_ét` with finite Tor amplitude in `[a, b + 2d]`. The shift `2d` is the uniform
vanishing of `Rᵖf_*` above twice the dimension of the source, applied to the `E₂`-page
`Rᵖf_* Hᑫ(K ⊗ᴸ κ)` of the truncation spectral sequence for the residue field `κ`; the residue
test then converts that concentration back into a bound on the Tor amplitude of `Rf_* K`. -/
theorem rightDerivedLowerStar_torAmplitudeIn {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hbc : boundedConstructible A X K) (hta : torAmplitudeIn A X a b K) :
    boundedConstructible A Y ((R((f)_*[A])).obj K) ∧
      torAmplitudeIn A Y a (b + 2 * (d : ℤ)) ((R((f)_*[A])).obj K) :=
  sorry

/-! ### Internal hom -/

/-- Blueprint `sk-thm-sf-hom-ctf`: Internal Hom with finite Tor amplitude.

Let `K` and `M` be bounded constructible complexes on `X_ét` of finite Tor amplitude in `[a, b]`
and in `[c, d]` respectively, and suppose `dim X ≤ m`. Then `RHom(K, M)` is bounded constructible
of Tor amplitude in `[c - b - 2m, d - a + 2m]`, and if `K` is site-perfect the sharper interval
`[c - b, d - a]` holds.

The general interval comes from writing `RHom(K, M) ≅ 𝔻_X (K ⊗ᴸ 𝔻_X M)` and using that the
Verdier dual moves Tor amplitude `[c, d]` to `[-d - 2m, -c]`, the dualizing complex having
cohomology in `[-2m, 0]`; the sharper one from the local identification
`RHom(K, M) ≅ K^∨ ⊗ᴸ M` available when `K` is dualizable. The sharper interval genuinely fails
in general: for the origin `i : {0} ⟶ 𝔸¹` both `i_* A` and `A` have Tor amplitude `[0, 0]` while
`RHom(i_* A, A) = i_* A(-1)[-2]`. -/
theorem derivedHom_torAmplitudeIn (X : Scheme.{u}) (m : ℕ)
    (hm : topologicalKrullDim X ≤ (m : WithBot ℕ∞)) (a b c d : ℤ)
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : boundedConstructible A X K) (hKt : torAmplitudeIn A X a b K)
    (hM : boundedConstructible A X M) (hMt : torAmplitudeIn A X c d M) :
    boundedConstructible A X (((RHom(X)[A]).obj (op K)).obj M) ∧
      torAmplitudeIn A X (c - b - 2 * (m : ℤ)) (d - a + 2 * (m : ℤ))
        (((RHom(X)[A]).obj (op K)).obj M) ∧
      (sitePerfect A X K →
        torAmplitudeIn A X (c - b) (d - a) (((RHom(X)[A]).obj (op K)).obj M)) :=
  sorry

/-! ### The exceptional inverse image -/

/-- Blueprint `sk-prop-sf-rf-shriek-preservation`: Preservation for the exceptional inverse image.

Clause (i): for `f` an open immersion or finite étale, `Rf^!` preserves the constructible
interval and the Tor amplitude *unchanged*. For such an `f` the ambient right adjoint is the
exact functor `Lf^*`; pulling back a finite constructible stratification gives one again and
`Hᑫ(Lf^* K) ≅ f^* Hᑫ(K)`, while inverse image preserves flatness, so a bounded flat model in
degrees `[a, b]` pulls back to one. -/
theorem upperShriek_preserves_of_isOpenImmersion_or_finiteEtale {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f]
    (hf : IsOpenImmersion f ∨ (IsFinite f ∧ _root_.AlgebraicGeometry.Etale f)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hbc : boundedConstructible A Y K) (hhc : homologyConcentratedIn A Y a b K)
    (hta : torAmplitudeIn A Y a b K) :
    boundedConstructible A X ((R(f)^![A]).obj K) ∧
      homologyConcentratedIn A X a b ((R(f)^![A]).obj K) ∧
      torAmplitudeIn A X a b ((R(f)^![A]).obj K) :=
  sorry

/-- Blueprint `sk-prop-sf-rf-shriek-preservation`: Preservation for the exceptional inverse image.

Clause (ii): for a closed immersion `i : Z ⟶ T` into a target of dimension `≤ d`, the exceptional
inverse image shifts the constructible interval by `2d + 1`, `D_c^[a, b] ↦ D_c^[a, b + 2d + 1]`
(that is, by `2·codim + 1` in the pure case), and shifts the Tor amplitude the same way.

The bound comes from the localization triangle for the open complement `j : T \ Z ⟶ T`: the
strict-henselization stalk formula and the vanishing of étale cohomology above twice the
dimension give `Rᑫj_* M = 0` for `q > 2d` and every module sheaf `M`, which bounds `Ri^!` in
terms of `Rj_*` with the extra `+1` coming from the triangle. -/
theorem upperShriek_preserves_of_isClosedImmersion {Z T : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i] [HasCompactification i] (d : ℕ)
    (hd : topologicalKrullDim T ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)}
    (hbc : boundedConstructible A T K) (hhc : homologyConcentratedIn A T a b K)
    (hta : torAmplitudeIn A T a b K) :
    boundedConstructible A Z ((R(i)^![A]).obj K) ∧
      homologyConcentratedIn A Z a (b + 2 * (d : ℤ) + 1) ((R(i)^![A]).obj K) ∧
      torAmplitudeIn A Z a (b + 2 * (d : ℤ) + 1) ((R(i)^![A]).obj K) :=
  sorry

/-- Blueprint `sk-prop-sf-rf-shriek-preservation`: Preservation for the exceptional inverse image.

Clause (iii): for `f` smooth of pure relative dimension `d`, the exceptional inverse image shifts
both intervals by `-2d`, `D_c^[a, b] ↦ D_c^[a - 2d, b - 2d]`. Indeed purity identifies `Rf^!`
with `Lf^*(-)(d)[2d]`: the exact functor `Lf^*` preserves bounded constructibility, the Tate
twist does not move degrees, and the shift `[2d]` accounts for the whole displacement, on the Tor
amplitude as well after testing against the residue field. -/
theorem upperShriek_preserves_of_smoothOfRelativeDimension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (d : ℕ) [SmoothOfRelativeDimension d f] (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hbc : boundedConstructible A Y K) (hhc : homologyConcentratedIn A Y a b K)
    (hta : torAmplitudeIn A Y a b K) :
    boundedConstructible A X ((R(f)^![A]).obj K) ∧
      homologyConcentratedIn A X (a - 2 * (d : ℤ)) (b - 2 * (d : ℤ)) ((R(f)^![A]).obj K) ∧
      torAmplitudeIn A X (a - 2 * (d : ℤ)) (b - 2 * (d : ℤ)) ((R(f)^![A]).obj K) :=
  sorry

/-- Blueprint `sk-prop-sf-rf-shriek-preservation`: Preservation for the exceptional inverse image.

Clause (iv): *every* separated finite-type `f` carrying the ambient datum preserves the
constructible intervals up to some shift. The blueprint's "with the shift computed from the
affine charts" is rendered here as a single integer `c`, depending only on `f`, widening every
interval `[a, b]` to `[a - c, b + c]`; a chart-by-chart factorisation of `f` as a closed immersion
followed by a smooth projection composes clauses (ii) and (iii), and `c` is the sum of the two
shifts, maximised over a finite set of charts. In particular `Rf^!` preserves `Dctf`. -/
theorem exists_shift_upperShriek_preserves {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] [HasCompactification f] :
    ∃ c : ℤ, ∀ (a b : ℤ) (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)),
      boundedConstructible A Y K → homologyConcentratedIn A Y a b K →
        torAmplitudeIn A Y a b K →
        boundedConstructible A X ((R(f)^![A]).obj K) ∧
          homologyConcentratedIn A X (a - c) (b + c) ((R(f)^![A]).obj K) ∧
          torAmplitudeIn A X (a - c) (b + c) ((R(f)^![A]).obj K) :=
  sorry

/-! ### Stability of `Dctf` under the six operations -/

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor subcategories.

Clause (i): `Lf^* : Dctf(Y, A) ⥤ Dctf(X, A)` is defined, and it preserves the Tor amplitude
interval unchanged. The pullback of a bounded flat model is a bounded flat model in the same
degrees, and pullback preserves bounded constructibility. -/
theorem ctfStability_leftDerivedUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hbc : boundedConstructible A Y K) (hta : torAmplitudeIn A Y a b K) :
    boundedConstructible A X ((L((f)^*[A])).obj K) ∧
      torAmplitudeIn A X a b ((L((f)^*[A])).obj K) :=
  sorry

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor subcategories.

Clause (ii), tensor half: `- ⊗ᴸ - : Dctf(X, A) × Dctf(X, A) ⥤ Dctf(X, A)` is defined, with Tor
amplitudes adding, `[a, b], [c, d] ↦ [a + c, b + d]`. The internal-Hom half of clause (ii) is
`AlgebraicGeometry.Etale.derivedHom_torAmplitudeIn` above, with the shifts
`[c - b - 2m, d - a + 2m]` for `dim X ≤ m` and `[c - b, d - a]` when the first argument is
site-perfect. -/
theorem ctfStability_tensor (X : Scheme.{u}) (a b c d : ℤ)
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : boundedConstructible A X K) (hKt : torAmplitudeIn A X a b K)
    (hM : boundedConstructible A X M) (hMt : torAmplitudeIn A X c d M) :
    boundedConstructible A X (((-⊗ᴸ-(X)[A]).obj K).obj M) ∧
      torAmplitudeIn A X (a + c) (b + d) (((-⊗ᴸ-(X)[A]).obj K).obj M) :=
  sorry

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor subcategories.

Clause (iii): `Rf_* : Dctf(X, A) ⥤ Dctf(Y, A)` is defined for every separated finite-type `f`.
This is `AlgebraicGeometry.Etale.rightDerivedLowerStar_torAmplitudeIn` with the dimension bound
forgotten: some finite interval always exists, since a finite-type scheme has finite dimension. -/
theorem ctfStability_rightDerivedLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : boundedConstructible A X K ∧ finiteTorAmplitude A X K) :
    boundedConstructible A Y ((R((f)_*[A])).obj K) ∧
      finiteTorAmplitude A Y ((R((f)_*[A])).obj K) :=
  sorry

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor subcategories.

Clause (iv): `Rf_! : Dctf(X, A) ⥤ Dctf(Y, A)` is defined for every separated finite-type `f`
carrying the ambient datum. One assembles the open-immersion case
(`AlgebraicGeometry.Etale.lowerShriek_preserves_constructible_torAmplitudeIn`) with the proper
case, where `Rf_! = Rf_*`, along a compactification of `f`. -/
theorem ctfStability_rightDerivedLowerShriek {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] [HasCompactification f]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : boundedConstructible A X K ∧ finiteTorAmplitude A X K) :
    boundedConstructible A Y ((R(f)_![A]).obj K) ∧
      finiteTorAmplitude A Y ((R(f)_![A]).obj K) :=
  sorry

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor subcategories.

Clause (v): `Rf^! : Dctf(Y, A) ⥤ Dctf(X, A)` is defined for every `f` carrying the ambient datum.
This is `AlgebraicGeometry.Etale.exists_shift_upperShriek_preserves` with the shift forgotten. -/
theorem ctfStability_rightDerivedUpperShriek {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] [HasCompactification f]
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hK : boundedConstructible A Y K ∧ finiteTorAmplitude A Y K) :
    boundedConstructible A X ((R(f)^![A]).obj K) ∧
      finiteTorAmplitude A X ((R(f)^![A]).obj K) :=
  sorry

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor subcategories.

Clause (vi): the Verdier dual `𝔻_X = RHom(-, ω_X)` is defined on `Dctf(X, A)` and is a
contravariant anti-equivalence of it, `𝔻_X 𝔻_X ≅ id`. It is `RHom(-, ω_X)` for the dualizing
complex `ω_X = Rp^! Λ_S` of the structure morphism `p`, which lies in `Dctf(X, A)` by clause (v),
so clause (ii) applies; biduality is `sk-prop-sf-biduality-general`. -/
theorem ctfStability_verdierDual {X S : Scheme.{u}} (p : X ⟶ S) [HasCompactification p]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : boundedConstructible A X K ∧ finiteTorAmplitude A X K) :
    (boundedConstructible A X ((verdierDual A p).obj (op K)) ∧
        finiteTorAmplitude A X ((verdierDual A p).obj (op K))) ∧
      Nonempty (K ≅ (verdierDual A p).obj (op ((verdierDual A p).obj (op K)))) :=
  sorry

/-! ### Generation of `Dctf` -/

/-- Blueprint `sk-lem-sf-ctf-generation`: Finite/open generation of `Dctf`.

On a separated finite-type scheme `X`, the category `Dctf(X, A)` is generated as a thick
subcategory by the objects `Rg_* j_! Λ_U`, where `U` is an open stratum of a stratification of
`X`, `j : U ⟶ Ū` is the open immersion of `U` into its closure and `g : Ū ⟶ X` is the finite map
of that closure to `X`.

"Thick subcategory generated by" is unwound here: any property `P` of objects of `D(X_ét)` that
is triangulated, stable under retracts and closed under isomorphisms, and that holds for all the
generators above, holds for every object of `Dctf(X, A)`. The proof reduces by truncation
triangles to a single constructible sheaf, then by the open–closed triangle and induction on the
number of strata to `g_* j_! L` with `L` lisse, and finally expresses each composition factor of
`L` as a direct summand of some `Rg_* j_! Λ_U`. -/
theorem ctf_generated_by_lowerShriek_lowerStar_unit (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X]
    (P : ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)))
    [P.IsTriangulated] [P.IsStableUnderRetracts] [P.IsClosedUnderIsomorphisms]
    (hP : ∀ (S : Scheme.Stratification X) (i : Fin S.n) (Ubar : Scheme.{u})
      (j : S.domain i ⟶ Ubar) (_ : IsOpenImmersion j) (_ : HasCompactification j)
      (g : Ubar ⟶ X) (_ : IsFinite g), Set.range (j ≫ g) = S.stratum i →
      Set.range g = _root_.closure (S.stratum i) →
      P ((R((g)_*[A])).obj ((R(j)_![A]).obj (𝟙_ _))))
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hK : boundedConstructible A X K ∧ finiteTorAmplitude A X K) :
    P K :=
  sorry

end Etale

end AlgebraicGeometry
