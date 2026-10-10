/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.NumberTheory.Padics.Complex
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.Presentation
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Supports
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# Finiteness, perfectness, flat models and Künneth

The four finiteness inputs the purity chapter takes from the six-functor formalism:

* `Rf_*` and `Rf_!` preserve bounded constructibility, with a cohomological-dimension bound
  in terms of the fibre dimension (`sk-prop-sf-finiteness`);
* compactly supported cohomology is a perfect complex of `Λ`-modules
  (`sk-prop-sf-trace-perfectness`);
* finite Tor amplitude in `[a, b]` is the same as admitting a bounded flat model concentrated
  in `[a, b]` (`sk-lem-sf-flat-model`);
* the Künneth formula and the projection formula in ordinary étale cohomology
  (`sk-prop-sf-kunneth-ordinary`).

Throughout, `Λ` is a finite coefficient ring whose exponent is invertible on the schemes in
question (`AlgebraicGeometry.HasInvertibleExponent`) and the schemes are of finite type over a
field: without the invertibility the Artin–Schreier sequence already defeats constructibility
of `R¹f_*` in characteristic `p`.

## Implementation notes

`sk-prop-sf-trace-perfectness` concludes that `RΓ_c(X, K)` is *perfect*: bounded, with finite
cohomology modules, and of finite Tor amplitude. The three are stated separately below, finite
Tor amplitude in the sense of `DerivedCategory.finiteTorAmplitude` for `D(ModuleCat Λ)`; they
are assembled into perfectness in `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect`.
The geometric-stalk half of the same subsection is omitted.

## Main statements

- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent`
- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek` and
  `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek_padicAlgCl`
- `AlgebraicGeometry.Etale.isZero_compactlySupportedCohomology_of_lt`
- `AlgebraicGeometry.Etale.finite_compactlySupportedCohomology`
- `AlgebraicGeometry.Etale.finiteTorAmplitude_compactlySupportedGlobalSections`
- `AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatModel`
- `AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatConstructibleModel`
- `AlgebraicGeometry.Etale.nonempty_iso_kunneth`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}

section Finiteness

variable [Finite Λ] {k : Type u} [Field k]

/-- Blueprint `sbc-thm-finiteness-finite-type`: Finiteness of higher direct images of
finite-type morphisms (the ordinary direct image of a sheaf)

Let `f : X ⟶ Y` be a morphism of finite-type schemes over a field `k`, and let `F` be a
constructible sheaf of `Λ`-modules on `X_ét`, for a finite ring `Λ` whose exponent is invertible
in `k`. Then `Rf_* F` is bounded constructible. -/
theorem boundedConstructible_rightDerivedLowerStar_singleFunctor_obj
    [HasInvertibleExponent Λ (Spec (.of k))] (f : X ⟶ Y) (aX : X ⟶ Spec (.of k))
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY]
    [QuasiCompact aY] (hf : f ≫ aY = aX) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) :=
  sorry

/-- Blueprint `sbc-thm-finiteness-finite-type`: Finiteness of higher direct images of
finite-type morphisms (the compactly supported direct image of a sheaf)

Let `f : X ⟶ Y` be a separated finite-type morphism, admitting a compactification, of
finite-type schemes over a field `k`, and let `F` be a constructible sheaf of `Λ`-modules on
`X_ét`, for a finite ring `Λ` whose exponent is invertible in `k`. Then `Rf_! F` is bounded
constructible. -/
theorem boundedConstructible_rightDerivedLowerShriek_singleFunctor_obj
    [HasInvertibleExponent Λ (Spec (.of k))] (f : X ⟶ Y) [HasCompactification f]
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (hf : f ≫ aY = aX)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) :=
  sorry

/-- **Dévissage for bounded constructible complexes.** A triangulated functor
`Φ : D(X_ét, Λ) ⥤ D(Y_ét, Λ)` carries `D^b_c(X, Λ)` into `D^b_c(Y, Λ)` as soon as it carries
every constructible sheaf, placed in degree `0`, into `D^b_c(Y, Λ)`. -/
lemma boundedConstructible_obj_of_singleFunctor
    (Φ : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [Φ.CommShift ℤ] [Φ.IsTriangulated]
    (hΦ : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F],
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
        (Φ.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y (Φ.obj K) :=
  _root_.DerivedCategory.prop_of_bounded
    ((DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y).inverseImage Φ)
    (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X) (fun F hF ↦ by
      have : IsConstructibleSheaf F := hF
      exact hΦ F) K hK.1 hK.2

/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility

**Finiteness of direct images.** Let `Λ` be a finite ring whose exponent is invertible on `X`
and let `f : X ⟶ Y` be a quasi-compact morphism of finite-type `k`-schemes. Then `Rf_*`
carries `D^b_c(X, Λ)` into `D^b_c(Y, Λ)`; separatedness of `f` is not needed.

The underlying numerical input is that the torsion cohomological dimension of a finite-type
`k`-scheme of dimension `d` over a field of torsion cohomological dimension at most `c` is
bounded by `2d + c`; in particular it is `0` for the spectrum of a separably closed field.

The schemes have to be quasi-compact: for `Y` an infinite disjoint union of copies of `Spec k`
and `X` the disjoint union of the projective spaces `ℙⁿ_k`, one over each copy, the direct image
of the constant sheaf has nonzero cohomology sheaves in all even degrees.

The proof reduces to a single constructible sheaf by dévissage
(`AlgebraicGeometry.Etale.boundedConstructible_obj_of_singleFunctor`), where it is
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_singleFunctor_obj`. -/
theorem boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent (f : X ⟶ Y)
    [QuasiCompact f] [HasInvertibleExponent Λ X] (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [LocallyOfFiniteType aY] [QuasiCompact aY] (hf : f ≫ aY = aX)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  by_cases hX : IsEmpty X
  · exact (DerivedCategory.boundedConstructible _ Y).prop_of_isZero
      (Functor.map_isZero _ (isZero_derivedCategory_of_isEmpty (ModuleCat.{u + 1} Λ) X K))
  have : Nonempty X := not_isEmpty_iff.1 hX
  have := HasInvertibleExponent.of_hom_of_nonempty (Λ := Λ) aX
  have : QuasiCompact aX := hf ▸ inferInstance
  exact boundedConstructible_obj_of_singleFunctor Λ _ (fun F _ ↦
    boundedConstructible_rightDerivedLowerStar_singleFunctor_obj Λ f aX aY hf F) K hK

omit [Finite Λ] [CommRing Λ] in
/-- The source of a morphism admitting a compactification, to a quasi-compact scheme locally of
finite type over a field, is a noetherian space: it is open in the compactification, which is
of finite type over the field. -/
lemma noetherianSpace_of_hasCompactification (f : X ⟶ Y) [HasCompactification f]
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :
    TopologicalSpace.NoetherianSpace X := by
  let c := HasCompactification.compactification f
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian (c.g ≫ aY)
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace (c.g ≫ aY)
  have : IsNoetherian c.Z := ⟨⟩
  exact c.i.isOpenEmbedding.isInducing.noetherianSpace

/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility

**Finiteness of compactly supported direct images.** For `f : X ⟶ Y` separated of finite type
between finite-type `k`-schemes, `Rf_!` carries `D^b_c(X, Λ)` into `D^b_c(Y, Λ)`.

The base `Y` has to be quasi-compact, for the reason explained at
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent`
(there the morphism is proper, so that `Rf_! = Rf_*`). -/
theorem boundedConstructible_rightDerivedLowerShriek (f : X ⟶ Y) [HasCompactification f]
    [HasInvertibleExponent Λ X] (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [LocallyOfFiniteType aY] [QuasiCompact aY] (hf : f ≫ aY = aX)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) := by
  by_cases hX : IsEmpty X
  · exact (DerivedCategory.boundedConstructible _ Y).prop_of_isZero
      (Functor.map_isZero _ (isZero_derivedCategory_of_isEmpty (ModuleCat.{u + 1} Λ) X K))
  have : Nonempty X := not_isEmpty_iff.1 hX
  have := HasInvertibleExponent.of_hom_of_nonempty (Λ := Λ) aX
  have := noetherianSpace_of_hasCompactification f aY
  have : QuasiCompact aX := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  exact boundedConstructible_obj_of_singleFunctor Λ _ (fun F _ ↦
    boundedConstructible_rightDerivedLowerShriek_singleFunctor_obj Λ f aX aY hf F) K hK

/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility

**Finiteness of compactly supported direct images with `ℚ̄_ℓ`-coefficients.** For a prime `ℓ`
invertible in `k` and `f : X ⟶ Y` separated of finite type between finite-type `k`-schemes,
`Rf_!` carries `D^b_c(X, ℚ̄_ℓ)` into `D^b_c(Y, ℚ̄_ℓ)`.

The blueprint deduces this from the finite-coefficient case
`boundedConstructible_rightDerivedLowerShriek` by passing to the limit over the `ℤ/ℓⁿ` and
inverting `ℓ`; that passage is not formalised. -/
theorem boundedConstructible_rightDerivedLowerShriek_padicAlgCl (l : ℕ) [Fact l.Prime]
    (hl : ringChar k ≠ l) (f : X ⟶ Y) [HasCompactification f] (aX : X ⟶ Spec (.of k))
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [LocallyOfFiniteType aY]
    [QuasiCompact aY] (hf : f ≫ aY = aX)
    (K : _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l)))))
    (hK : DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l))) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l))) Y
      ((R(f)_![ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l))]).obj K) :=
  sorry

/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility

**The fibre-dimension bound.** If `e` bounds the dimensions of the *geometric* fibres of a
separated finite-type `f : X ⟶ Y`, then `R^q f_! K = 0` for `q > 2e` and every bounded
constructible `K` concentrated in degrees `≤ 0`; for a sheaf `𝓕` placed in degree `0` this is
the blueprint's `R^q f_! 𝓕 = 0`. Some bound on the degrees of `K` is needed: for `f = 𝟙` the
complex `K = Λ[-1]` has `H^1(Rf_! K) = Λ`. -/
theorem isZero_homology_rightDerivedLowerShriek (f : X ⟶ Y) [HasCompactification f]
    [HasInvertibleExponent Λ X] (e : ℕ)
    (he : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (Limits.pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hK₀ : _root_.DerivedCategory.TStructure.t.IsLE K 0) (q : ℤ) (hq : (2 * e : ℤ) < q) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)) :=
  sorry

end Finiteness

section Perfectness

variable [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX] [HasCompactification aX]
  [HasInvertibleExponent Λ X]

omit [IsSeparated aX] in
/-- Blueprint `sk-prop-sf-trace-perfectness`: Perfectness of compact cohomology and of
geometric stalks

**Boundedness of compactly supported cohomology.** Let `Λ` be a finite coefficient ring, `k`
separably closed, `X` separated of finite type over `k` with structure morphism `a_X`, and
`K ∈ D^b_{ctf}(X, Λ)`. Then `RΓ_c(X, K) = Ra_{X!} K` vanishes in all but finitely many
degrees. Separable closedness of the base is essential: over `Spec ℚ` already
`H¹_c(Spec ℚ, ℤ/n) = Hom(G_ℚ, ℤ/n)` is infinite. -/
theorem isZero_compactlySupportedCohomology_of_lt
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((H_c(aX)[ModuleCat.{u + 1} Λ](q)).obj K) := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, -⟩ := boundedConstructible_rightDerivedLowerShriek Λ aX aX (𝟙 _)
    (Category.comp_id aX) K hK.1
  refine ⟨a, b, fun q hq ↦ IsZero.of_iso ((Sheaf.Γ _ _).map_isZero ?_)
    ((homologyRightDerivedGlobalSectionsIsoOfIsSepClosed q).app _)⟩
  rcases hq with hq | hq
  · exact (_root_.DerivedCategory.isGE_iff _ a).1 ha q hq
  · exact (_root_.DerivedCategory.isLE_iff _ b).1 hb q hq

omit [IsSeparated aX] in
/-- Blueprint `sk-prop-sf-trace-perfectness`: Perfectness of compact cohomology and of
geometric stalks

**Finiteness of compactly supported cohomology.** In the situation of
`AlgebraicGeometry.Etale.isZero_compactlySupportedCohomology_of_lt`, every compactly supported
cohomology module `H^q_c(X, K)` is a finite `Λ`-module. Together with boundedness and finite
Tor amplitude these are exactly perfectness over the Artinian local ring `A_{E,n}`. -/
theorem finite_compactlySupportedCohomology
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) (q : ℤ) :
    Module.Finite Λ ((H_c(aX)[ModuleCat.{u + 1} Λ](q)).obj K) := by
  let L := (_root_.DerivedCategory.homologyFunctor _ q).obj ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K)
  have : IsConstructibleSheaf L := (boundedConstructible_rightDerivedLowerShriek Λ aX aX (𝟙 _)
    (Category.comp_id aX) K hK.1).2 q
  have := finite_Γ_of_isConstructibleSheaf L
  have : Module.Finite Λ ((_root_.DerivedCategory.homologyFunctor _ q ⋙
      Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K)) := this
  exact Module.Finite.equiv ((homologyRightDerivedGlobalSectionsIsoOfIsSepClosed q).app
    ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K)).symm.toLinearEquiv

/-- Blueprint `sk-prop-sf-trace-perfectness`: Perfectness of compact cohomology and of
geometric stalks

**Finite Tor amplitude of compactly supported cohomology.** In the situation of
`AlgebraicGeometry.Etale.isZero_compactlySupportedCohomology_of_lt`, the complex of
`Λ`-modules `RΓ_c(X, K)` has finite Tor amplitude: by the projection formula
`RΓ_c(X, K) ⊗ᴸ M ≅ RΓ_c(X, K ⊗ᴸ M_X)` for a `Λ`-module `M`, and the cohomological amplitude of
`Ra_{X!}` on complexes of Tor amplitude in a fixed interval. -/
theorem finiteTorAmplitude_compactlySupportedGlobalSections
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    _root_.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} Λ)
      ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K) :=
  sorry

end Perfectness

/-- A complex `P` of sheaves of `Λ`-modules on `X_ét` is a *bounded flat complex in degrees
`[a, b]`* if every `P^q` is flat and `P^q = 0` for `q ∉ [a, b]`. -/
def IsBoundedFlatComplex (a b : ℤ)
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) : Prop :=
  (∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) ∧ ∀ q : ℤ, ObjectProperty.flat (P.X q)

variable {Λ} in
/-- Tor amplitude tested on one homology sheaf at a time
(`AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`) is Tor amplitude tested through
the canonical t-structure (`AlgebraicGeometry.Etale.DerivedCategory.torAmplitudeIn`). -/
lemma DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} :
    DerivedCategory.hasTorAmplitudeIn Λ X a b K ↔
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K := by
  refine ⟨fun h F ↦ ?_, fun h F q hq ↦ ?_⟩
  · rw [_root_.DerivedCategory.homologyConcentratedIn_iff]
    exact ⟨(_root_.DerivedCategory.isGE_iff _ a).2 fun q hq ↦ h F q (.inl hq),
      (_root_.DerivedCategory.isLE_iff _ b).2 fun q hq ↦ h F q (.inr hq)⟩
  · obtain ⟨h₁, h₂⟩ := h F
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff _ a).1 h₁ q hq
    · exact (_root_.DerivedCategory.isLE_iff _ b).1 h₂ q hq

variable {Λ} in
/-- A bounded flat complex in degrees `[a, b]` is a complex of flat sheaves strictly
concentrated in degrees `[a, b]`. -/
lemma isBoundedFlatComplex_iff {a b : ℤ}
    {P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ} :
    IsBoundedFlatComplex Λ a b P ↔
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧ ∀ q : ℤ, ObjectProperty.flat (P.X q) := by
  rw [CochainComplex.isStrictlyGE_iff, CochainComplex.isStrictlyLE_iff]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ⟨fun q hq ↦ h₁ q (.inl hq), fun q hq ↦ h₁ q (.inr hq), h₂⟩,
    fun ⟨h₁, h₂, h₃⟩ ↦ ⟨fun q hq ↦ ?_, h₃⟩⟩
  rcases hq with hq | hq
  · exact h₁ q hq
  · exact h₂ q hq

/-- Blueprint `sk-lem-sf-flat-model`: Bounded flat model of finite Tor amplitude

**Finite Tor amplitude means a bounded flat model.** For `K ∈ D^b_c(X, Λ)` and integers
`a ≤ b` the following are equivalent: `K` has Tor amplitude in `[a, b]`; and `K` is isomorphic
to a bounded flat complex `P` in degrees `[a, b]`.

One direction is that a bounded-above complex of flat sheaves is K-flat; the other truncates a
bounded-above free resolution and checks that the truncation is flat by the Tor criterion. -/
theorem hasTorAmplitudeIn_iff_exists_flatModel (a b : ℤ) (_hab : a ≤ b)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.hasTorAmplitudeIn Λ X a b K ↔
      ∃ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ,
        IsBoundedFlatComplex Λ a b P ∧ Nonempty (K ≅ (_root_.DerivedCategory.Q).obj P) := by
  rw [DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn]
  refine (_root_.DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat a b K).trans
    ⟨fun ⟨P, h₁, h₂, h₃, ⟨e⟩⟩ ↦ ⟨P, isBoundedFlatComplex_iff.2 ⟨h₁, h₂, h₃⟩, ⟨e.symm⟩⟩,
    fun ⟨P, hP, ⟨e⟩⟩ ↦ ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := isBoundedFlatComplex_iff.1 hP
  exact ⟨P, h₁, h₂, h₃, ⟨e.symm⟩⟩

/-- Blueprint `sk-lem-sf-flat-model`: Bounded flat model of finite Tor amplitude

**Constructible variant.** Let `X` be Noetherian and `Λ` finite. For `K ∈ D^b_c(X, Λ)` and
integers `a ≤ b`, `K` has Tor amplitude in `[a, b]` if and only if it is isomorphic to a bounded
flat complex `P` in degrees `[a, b]` whose terms are *constructible*. In particular every object
of `Dctf(X, Λ)` has such a model.

The bounded-above resolution of `hasTorAmplitudeIn_iff_exists_flatModel` is built with terms
finite sums of sheaves `j_{V!} Λ_V`, by `Scheme.exists_epi_sigma_lowerShriek_constantSheaf`
applied to the constructible cohomology sheaves of `K` and to the constructible kernels and
cokernels that arise (`Scheme.IsConstructibleSheaf.kernel`,
`Scheme.IsConstructibleSheaf.cokernel`); its truncation in degree `a` is then a cokernel of a
map of constructible sheaves, hence flat and constructible. The converse is the corresponding
direction of `hasTorAmplitudeIn_iff_exists_flatModel`. The statement is made for a finite ring
`Λ`, as in the blueprint. -/
theorem hasTorAmplitudeIn_iff_exists_flatConstructibleModel [Finite Λ] [IsNoetherian X]
    (a b : ℤ) (hab : a ≤ b)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.hasTorAmplitudeIn Λ X a b K ↔
      ∃ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ,
        IsBoundedFlatComplex Λ a b P ∧ (∀ q : ℤ, IsConstructibleSheaf (P.X q)) ∧
        Nonempty (K ≅ (_root_.DerivedCategory.Q).obj P) :=
  sorry

section Kunneth

variable [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [LocallyOfFiniteType aY]
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

/-- Blueprint `sk-prop-sf-kunneth-ordinary`: Künneth and the projection formula in ordinary
étale cohomology

**Künneth.** Let `k` be separably closed, let the exponent of `Λ` be invertible on `X` and `Y`
and let `X`, `Y` be finite-type `k`-schemes. For the cartesian square

```
  W --p₂--> Y
  |         |
  p₁        a_Y
  |         |
  v         v
  X --a_X-> Spec k
```

exhibiting `W = X ×_k Y`, the exterior-product map

`RΓ(X, E) ⊗^L RΓ(Y, K) ≅ RΓ(X ×_k Y, Lp₁^* E ⊗^L Lp₂^* K)`

is an isomorphism for all `E ∈ D(X_ét, Λ)` and `K ∈ D(Y_ét, Λ)` — unbounded, and with no
properness hypothesis. Without the cartesian hypothesis the statement is false: for `W = ∅`
and `X = Y = Spec k` the right-hand side is `0` and the left-hand side is `Λ`. -/
theorem nonempty_iso_kunneth {W : Scheme.{u}} (p₁ : W ⟶ X) (p₂ : W ⟶ Y)
    (sq : IsPullback p₁ p₂ aX aY)
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj E ⊗
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj K ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) W).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) W).obj
            ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj E)).obj
          ((L((p₂)^*[ModuleCat.{u + 1} Λ])).obj K))) :=
  sorry

omit [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y] in
/-- Blueprint `sk-prop-sf-kunneth-ordinary`: Künneth and the projection formula in ordinary
étale cohomology

**The projection formula for a proper morphism.** For `f : X ⟶ Y` proper between finite-type
`k`-schemes and all `E ∈ D(X_ét, Λ)`, `L ∈ D(Y_ét, Λ)`,

`Rf_* E ⊗^L L ≅ Rf_*(E ⊗^L Lf^* L)`.

It is the projection formula for `Rf_!` at finite coefficients
(`AlgebraicGeometry.Etale.hasProjectionFormula_of_finite`), transported along `Rf_! ≅ Rf_*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`). -/
theorem nonempty_iso_derivedTensor_rightDerivedLowerStar_of_isProper (f : X ⟶ Y) [IsProper f]
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj
          ((R((f)_*[ModuleCat.{u + 1} Λ])).obj E)).obj L ≅
      (R((f)_*[ModuleCat.{u + 1} Λ])).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj E).obj
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj L))) := by
  obtain ⟨e⟩ := nonempty_iso_derivedTensor_obj_rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f E
    (hasProjectionFormula_of_finite Λ f E)
  let φ := rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f
  exact ⟨((derivedTensor (ModuleCat.{u + 1} Λ) Y).mapIso (φ.app E).symm).app L ≪≫ e.app L ≪≫
    φ.app _⟩

end Kunneth

end Etale

end AlgebraicGeometry
