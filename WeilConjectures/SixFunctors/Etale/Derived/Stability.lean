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
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Compactification.Affine
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Devissage
public import WeilConjectures.SixFunctors.OpenClosed.Derived
public import WeilConjectures.SixFunctors.Etale.Derived.Supports
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
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

* The statements about the derived tensor product's constructibility and about open immersions
  are made for a finite coefficient ring `Λ`. For an arbitrary coefficient category the tensor
  statement is false (over `R = k[x, y₁, y₂, …]` on a point, `R/(x yᵢ)ᵢ ⊗ᴸ R/(x)` has the
  non-finitely generated `Tor₁ = (yᵢ)ᵢ/(x yᵢ)ᵢ`), and `Rj_!` is computed through an arbitrary
  compactification of `j`, which agrees with extension by zero only when `Rj_!` is known to be
  independent of the compactification
  (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`, proved for a finite ring and a
  quasi-compact `j`).
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

omit [HasSmallSiteSheafify A] in
/-- If `K` is dualizable of Tor amplitude in `[a, b]` and `M` has Tor amplitude in `[c, d]`,
then `RHom(K, M) ≅ K^∨ ⊗ᴸ M` has Tor amplitude in `[c - b, d - a]`, the dual `K^∨` having Tor
amplitude in `[-b, -a]`
(`DerivedCategory.torAmplitudeIn_of_exactPairing`). -/
theorem torAmplitudeIn_derivedHom_of_isDualizable_aux {X : Scheme.{u}} {a b c d : ℤ}
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hKt : torAmplitudeIn A X a b K) (hKd : IsDualizable K) (hMt : torAmplitudeIn A X c d M) :
    torAmplitudeIn A X (c - b) (d - a) (((RHom(X)[A]).obj (op K)).obj M) := by
  -- `RHom(K, M) ≅ K^∨ ⊗ᴸ M`, and the dual `K^∨` has Tor amplitude in `[-b, -a]`
  obtain ⟨_⟩ := hKd
  obtain ⟨_⟩ := nonempty_exactPairing_swap K Kᘁ
  obtain ⟨e⟩ := nonempty_iso_coefficientDual_tensor (isDualizable_of_hasRightDual K) M
  have hd := _root_.DerivedCategory.torAmplitudeIn_of_exactPairing (L := Kᘁ) hKt
  have h := _root_.DerivedCategory.torAmplitudeIn_tensor hd hMt
  refine (torAmplitudeIn A X _ _).prop_of_iso
    (whiskerRightIso (coefficientDualIsoOfExactPairing Kᘁ K).symm M ≪≫ e) ?_
  rw [show c - b = -b + c by omega, show d - a = -a + d by omega]
  exact h

/-! ### Internal hom: reductions -/

section DerivedHomReductions

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]

omit [HasSmallSiteSheafify A] in
/-- **Restriction to an open commutes with the internal hom**, `j^* RHom(K, N) ≅
RHom(j^* K, j^* N)`: the two sides are right adjoint to `G ↦ K ⊗ᴸ j_! G` and to
`G ↦ j_!(j^* K ⊗ᴸ G)`, which agree by the projection formula for `j_!` (and the symmetry of the
derived tensor product). -/
theorem nonempty_iso_mapDerivedCategory_upperStar_derivedHom {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [Etale.UpperStarPreservesFlat A]
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    (K N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    Nonempty (D((j)^*[A]).obj ((RHom(X)[A].obj (op K)).obj N) ≅
      (RHom(U)[A].obj (op (D((j)^*[A]).obj K))).obj (D((j)^*[A]).obj N)) := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory (Sheaf X.smallEtaleTopology A)
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory (Sheaf U.smallEtaleTopology A)
  let adj₁ := (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).comp
    (derivedTensorHomAdjunction A K)
  let adj₂ := (derivedTensorHomAdjunction A (D((j)^*[A]).obj K)).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction A j)
  let e : D((j)_!open[A]) ⋙ (-⊗ᴸ-(X)[A]).obj K ≅
      (-⊗ᴸ-(U)[A]).obj (D((j)^*[A]).obj K) ⋙ D((j)_!open[A]) :=
    Functor.isoWhiskerLeft _ (BraidedCategory.tensorLeftIsoTensorRight K) ≪≫
      (((flipFunctor _ _ _).mapIso
        (derivedOpenImmersionLowerShriekProjectionIso (FC := FC) A j)).app K).symm ≪≫
      Functor.isoWhiskerRight ((curriedTensor _).flip.mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory A j).app K) ≪≫
          (BraidedCategory.tensorLeftIsoTensorRight _).symm) D((j)_!open[A])
  exact ⟨((adj₁.ofNatIsoLeft e).rightAdjointUniq adj₂).app N⟩

end DerivedHomReductions

omit [HasSmallSiteSheafify A] in
/-- If `M` is reflexive for the Verdier dual, `RHom(K, M) ≅ 𝔻(𝔻M ⊗ᴸ K)`: currying
`RHom(𝔻M ⊗ᴸ K, ω) ≅ RHom(K, RHom(𝔻M, ω))`. -/
theorem nonempty_iso_derivedHom_verdierDual {X S : Scheme.{u}} (a : X ⟶ S)
    [HasCompactification a] [(R(a)_![A]).IsLeftAdjoint]
    (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (e : M ≅ (verdierDual A a).obj (op ((verdierDual A a).obj (op M)))) :
    Nonempty ((RHom(X)[A].obj (op K)).obj M ≅
      (verdierDual A a).obj (op ((verdierDual A a).obj (op M) ⊗ K))) := by
  let N := (verdierDual A a).obj (op M)
  exact ⟨(RHom(X)[A].obj (op K)).mapIso e ≪≫
    ((((derivedTensorHomAdjunction A (N ⊗ K)).ofNatIsoLeft (tensorLeftTensor N K)).rightAdjointUniq
      ((derivedTensorHomAdjunction A K).comp (derivedTensorHomAdjunction A N))).app
        (dualizingComplex A a)).symm⟩


omit [HasSmallSiteSheafify A] in
/-- If the Verdier dual relative to `a` preserves `Dctf(X, A)` and is reflexive on it, and the
derived tensor product preserves `Dctf(X, A)`, so does the internal hom. -/
theorem constructibleFiniteTor_derivedHom_of_verdierDual {X S : Scheme.{u}} (a : X ⟶ S)
    [HasCompactification a] [(R(a)_![A]).IsLeftAdjoint]
    (hD : ∀ {N}, constructibleFiniteTor A X N →
      constructibleFiniteTor A X ((verdierDual A a).obj (op N)))
    (hbid : ∀ {N}, constructibleFiniteTor A X N →
      Nonempty (N ≅ (verdierDual A a).obj (op ((verdierDual A a).obj (op N)))))
    (htens : ∀ {K M}, constructibleFiniteTor A X K → constructibleFiniteTor A X M →
      constructibleFiniteTor A X (((-⊗ᴸ-(X)[A]).obj K).obj M))
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : constructibleFiniteTor A X K) (hM : constructibleFiniteTor A X M) :
    constructibleFiniteTor A X ((RHom(X)[A].obj (op K)).obj M) := by
  obtain ⟨e⟩ := hbid hM
  obtain ⟨e'⟩ := nonempty_iso_derivedHom_verdierDual A a K M e
  obtain ⟨hbc, c, d, hcd⟩ := hD (htens (hD hM) hK)
  exact ⟨(boundedConstructible A X).prop_of_iso e'.symm hbc, c, d,
    (torAmplitudeIn A X c d).prop_of_iso e'.symm hcd⟩

/-- The reduction of the finite étale case of `sk-prop-sf-rf-shriek-preservation`: if the direct
image along a proper `f` is *left* adjoint to the pullback, then `Rf^! ≅ D(f^*)`, so `Rf^!`
preserves the constructible interval and the Tor amplitude unchanged. For a finite étale `f`
the adjunction `f_* ⊣ f^*` holds because `f_*` agrees with the étale extension by zero, but this
is not available for a general coefficient category `A`. -/
theorem constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_adjunction
    [UpperStarPreservesFlat A] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    [HasCompactification f] [(R(f)_![A]).IsLeftAdjoint] (adj : (f)_*[A] ⊣ (f)^*[A]) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hK : constructibleTorAmplitudeIn A Y a b K) :
    constructibleTorAmplitudeIn A X a b ((R(f)^![A]).obj K) := by
  have := adj.leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (f)_*[A] :=
    PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _
  -- `Rf_! ≅ Rf_* ≅ D(f_*)`, whose right adjoint is `D(f^*)`
  let e : R(f)_![A] ≅ (f)_*[A].mapDerivedCategory :=
    rightDerivedLowerShriekIsoRightDerivedLowerStar A f ≪≫
      (f)_*[A].rightDerivedFunctorIsoMapDerivedCategory
  let e' : R(f)^![A] ≅ (f)^*[A].mapDerivedCategory :=
    (rightDerivedUpperShriekAdjunction A f).rightAdjointUniq
      (adj.mapDerivedCategoryAdjunction.ofNatIsoLeft e.symm)
  obtain ⟨⟨hbc, hab⟩, hta⟩ := hK
  refine constructibleTorAmplitudeIn_of_iso _ (e'.app K).symm ⟨⟨?_,
    ((f)^*[A]).homologyConcentratedIn_mapDerivedCategory_obj hab⟩, ?_⟩
  · exact hbc.mapDerivedCategory_upperStar f
  · exact (torAmplitudeIn A X a b).prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ f).app K)
      (torAmplitudeIn_leftDerivedUpperStar _ f a b hta)

/-! ### Closed immersions: reduction to the open complement -/

section ClosedImmersion

open Pretriangulated

variable {FC : A → A → Type (u + 1)} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [PreservesFiniteLimits (CategoryTheory.forget A)]

/-- For a closed immersion `i`, restricting an extension by zero recovers the complement:
`D(i^*) (Ri_! Q) ≅ Q`, since `Ri_! = Ri_* = D(i_*)` and `i^* i_* ≅ 𝟭`. -/
noncomputable def mapDerivedCategoryUpperStarRightDerivedLowerShriekIso {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] [HasCompactification i]
    [Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    [T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)] :
    R(i)_![A] ⋙ D((i)^*[A]) ≅ 𝟭 _ :=
  Functor.isoWhiskerRight (rightDerivedLowerShriekIsoRightDerivedLowerStar A i ≪≫
    Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory (FC := FC) A i) _ ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (asIso (Etale.upperStarLowerStarAdjunction A i).counit) ≪≫
    Functor.mapDerivedCategoryIdIso _

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A] in
/-- Concentration in `[a, b]` is invariant under isomorphism. -/
lemma homologyConcentratedIn_of_iso {X : Scheme.{u}} {a b : ℤ}
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (e : K ≅ K')
    (h : _root_.DerivedCategory.homologyConcentratedIn a b K) :
    _root_.DerivedCategory.homologyConcentratedIn a b K' := by
  obtain ⟨h₁, h₂⟩ := h
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso e a,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e b⟩

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A] in
/-- In a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]` with `X₂` concentrated in `[a, b]` and
`X₃` in `[a, e]`, `b ≤ e`, the first term is concentrated in `[a, e + 1]`. -/
lemma homologyConcentratedIn_obj₁ {X : Scheme.{u}}
    (T : Triangle (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)))
    (hT : T ∈ distTriang _) {a b e : ℤ} (hbe : b ≤ e)
    (h₂ : _root_.DerivedCategory.homologyConcentratedIn a b T.obj₂)
    (h₃ : _root_.DerivedCategory.homologyConcentratedIn a e T.obj₃) :
    _root_.DerivedCategory.homologyConcentratedIn a (e + 1) T.obj₁ := by
  have hT' := inv_rot_of_distTriang T hT
  obtain ⟨g₂, l₂⟩ := h₂
  obtain ⟨g₃, l₃⟩ := h₃
  have : _root_.DerivedCategory.TStructure.t.IsGE T.invRotate.obj₁ (a + 1) :=
    _root_.DerivedCategory.TStructure.t.isGE_shift T.obj₃ a (-1) (a + 1)
  have : _root_.DerivedCategory.TStructure.t.IsLE T.invRotate.obj₁ (e + 1) :=
    _root_.DerivedCategory.TStructure.t.isLE_shift T.obj₃ e (-1) (e + 1)
  have : _root_.DerivedCategory.TStructure.t.IsLE T.invRotate.obj₃ b := l₂
  have : _root_.DerivedCategory.TStructure.t.IsGE T.invRotate.obj₃ a := g₂
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE₂ _ hT' a
      (_root_.DerivedCategory.TStructure.t.isGE_of_ge _ a (a + 1)) ‹_›,
    _root_.DerivedCategory.TStructure.t.isLE₂ _ hT' (e + 1) ‹_›
      (_root_.DerivedCategory.TStructure.t.isLE_of_le _ b (e + 1))⟩

/-- **The exceptional inverse image along a closed immersion, from the open complement.**
Let `i : Z ⟶ T` be a closed immersion with open complement `j`. If `K` lies in `D_c^[a, b]` with
Tor amplitude in `[a, b]`, and `Rj_* j^* K` in `D_c^[a, e]` with Tor amplitude in `[a, e]`,
`b ≤ e`, then `Ri^! K` lies in `D_c^[a, e + 1]` with Tor amplitude in `[a, e + 1]`: the
localization triangle `Ri_! Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶` bounds `Ri_! Ri^! K`, and for the Tor
amplitude the projection formula identifies `Ri_!(Ri^! K ⊗ᴸ G)` with `Ri_! Ri^! K ⊗ᴸ i_* G`. -/
theorem constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion_of_lowerStar
    [UpperStarPreservesFlat A] {Z T U : Scheme.{u}}
    [(Etale.constructibleSheaf A T).IsClosedUnderKernels]
    [(Etale.constructibleSheaf A T).IsClosedUnderCokernels]
    [(Etale.constructibleSheaf A T).IsClosedUnderExtensions]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    (i : Z ⟶ T) [IsClosedImmersion i] [HasCompactification i] [(R(i)_![A]).IsLeftAdjoint]
    (j : U ⟶ T) [IsOpenImmersion j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {a b e : ℤ} (hbe : b ≤ e) {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)}
    (hK : constructibleTorAmplitudeIn A T a b K)
    (hM : constructibleTorAmplitudeIn A T a e ((R((j)_*[A])).obj ((L((j)^*[A])).obj K)))
    (hPF : ∀ L, HasProjectionFormula A i ((R(i)^![A]).obj K) L) :
    constructibleTorAmplitudeIn A Z a (e + 1) ((R(i)^![A]).obj K) := by
  obtain ⟨⟨hKbc, hKc⟩, hKt⟩ := hK
  obtain ⟨⟨hMbc, hMc⟩, hMt⟩ := hM
  have hT := supportedLocalizationTriangle_mem_distTriang A i j hij K
  set N := (R(i)_![A]).obj ((R(i)^![A]).obj K)
  -- `N` is bounded constructible
  have hNbc : boundedConstructible A T N :=
    (boundedConstructible A T).ext_of_isTriangulatedClosed₂ _ (inv_rot_of_distTriang _ hT)
      ((boundedConstructible A T).le_shift (-1) _ hMbc) hKbc
  -- `N` lies in `[a, e + 1]` with Tor amplitude in `[a, e + 1]`
  have hNc := homologyConcentratedIn_obj₁ A _ hT hbe hKc hMc
  have hNt : torAmplitudeIn A T a (e + 1) N := fun F ↦ by
    let G := (-⊗ᴸ-(T)[A]).flip.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)
    let := _root_.DerivedCategory.commShiftTensorRight
      (K := (_root_.DerivedCategory.singleFunctor (Sheaf T.smallEtaleTopology A) 0).obj F)
    have : G.IsTriangulated := _root_.DerivedCategory.isTriangulated_tensorRight
      (K := (_root_.DerivedCategory.singleFunctor (Sheaf T.smallEtaleTopology A) 0).obj F)
    exact homologyConcentratedIn_obj₁ A _ (G.map_distinguished _ hT) hbe (hKt F) (hMt F)
  -- `Ri^! K ≅ i^* N`
  let ε := mapDerivedCategoryUpperStarRightDerivedLowerShriekIso (FC := FC) A i
  refine ⟨⟨(boundedConstructible A Z).prop_of_iso (ε.app _)
      (hNbc.mapDerivedCategory_upperStar i),
    homologyConcentratedIn_of_iso A (ε.app _)
      (((i)^*[A]).homologyConcentratedIn_mapDerivedCategory_obj hNc)⟩, fun G ↦ ?_⟩
  -- `i_! (Ri^! K ⊗ᴸ G) ≅ N ⊗ᴸ i_* G` by the projection formula
  have : IsIso (((projectionMap A i).app ((R(i)^![A]).obj K)).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj ((i)_*[A].obj G))) :=
    hPF ((_root_.DerivedCategory.singleFunctor _ 0).obj ((i)_*[A].obj G))
  let e₁ : (L((i)^*[A])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj ((i)_*[A].obj G)) ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj G :=
    (singleFunctorCompLeftDerivedUpperStarIso A i).app _ ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso
        ((asIso (Etale.upperStarLowerStarAdjunction A i).counit).app G)
  let e₂ : (R(i)_![A]).obj (((-⊗ᴸ-(Z)[A]).obj ((R(i)^![A]).obj K)).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) ≅
        ((-⊗ᴸ-(T)[A]).obj N).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((i)_*[A].obj G)) :=
    (R(i)_![A]).mapIso (((-⊗ᴸ-(Z)[A]).obj _).mapIso e₁.symm) ≪≫
      (asIso (((projectionMap A i).app ((R(i)^![A]).obj K)).app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj ((i)_*[A].obj G)))).symm
  exact homologyConcentratedIn_of_iso A ((ε.app _).symm ≪≫ (D((i)^*[A])).mapIso e₂).symm
    (((i)^*[A]).homologyConcentratedIn_mapDerivedCategory_obj (hNt _))

end ClosedImmersion

/-! ### Gluing over a finite open cover -/

section Gluing

open ZeroObject

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A] in
/-- A homology sheaf vanishes if it vanishes after restriction to the members of an open
cover. -/
lemma isZero_homology_of_openCover {X : Scheme.{u}}
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i)
    (R : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) (q : ℤ)
    (h : ∀ i, IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      (D(((U i).ι)^*[A]).obj R))) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj R) := by
  have := Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective A
    (ι := ULift.{u} (Fin n)) (fun i ↦ (U i.down).ι)
    (fun x ↦ by obtain ⟨i, hi⟩ := hU x; exact ⟨⟨i⟩, ⟨x, hi⟩, rfl⟩)
    (0 : (_root_.DerivedCategory.homologyFunctor _ q).obj R ⟶ 0) (fun i ↦
      isIso_of_source_target_iso_zero _ ((h i.down).of_iso
        ((((U i.down).ι)^*[A].mapDerivedCategoryHomologyFunctorIso q).app R)).isoZero
        (Functor.map_isZero _ (isZero_zero _)).isoZero)
  exact (isZero_zero _).of_iso
    (asIso (0 : (_root_.DerivedCategory.homologyFunctor _ q).obj R ⟶ 0))

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A] in
/-- Concentration in `[a, b]` is local for an open cover. -/
lemma homologyConcentratedIn_of_openCover {X : Scheme.{u}}
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i)
    (R : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) {a b : ℤ}
    (h : ∀ i, _root_.DerivedCategory.homologyConcentratedIn a b (D(((U i).ι)^*[A]).obj R)) :
    _root_.DerivedCategory.homologyConcentratedIn a b R :=
  ⟨(_root_.DerivedCategory.isGE_iff R a).2 fun q hq ↦ isZero_homology_of_openCover A U hU R q
      fun i ↦ (_root_.DerivedCategory.isGE_iff _ a).1 (h i).1 q hq,
    (_root_.DerivedCategory.isLE_iff R b).2 fun q hq ↦ isZero_homology_of_openCover A U hU R q
      fun i ↦ (_root_.DerivedCategory.isLE_iff _ b).1 (h i).2 q hq⟩

omit [HasSmallSiteSheafify A] in
/-- Tor amplitude in `[a, b]` is local for an open cover. -/
lemma torAmplitudeIn_of_openCover [UpperStarPreservesFlat A] {X : Scheme.{u}}
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i)
    (R : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) {a b : ℤ}
    (h : ∀ i, torAmplitudeIn A (U i) a b (D(((U i).ι)^*[A]).obj R)) :
    torAmplitudeIn A X a b R := fun G ↦ by
  refine homologyConcentratedIn_of_openCover A U hU _ fun i ↦ ?_
  let j := (U i).ι
  let e : D((j)^*[A]).obj (R ⊗ (_root_.DerivedCategory.singleFunctor _ 0).obj G) ≅
      D((j)^*[A]).obj R ⊗ (_root_.DerivedCategory.singleFunctor _ 0).obj ((j)^*[A].obj G) :=
    ((leftDerivedUpperStarIsoMapDerivedCategory A j).app _).symm ≪≫
      leftDerivedUpperStarTensorIso A j _ _ ≪≫
      tensorIso ((leftDerivedUpperStarIsoMapDerivedCategory A j).app R)
        ((singleFunctorCompLeftDerivedUpperStarIso A j).app G)
  obtain ⟨h₁, h₂⟩ := h i ((j)^*[A].obj G)
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm a,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e.symm b⟩

end Gluing

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

omit [Finite Λ] in
/-- Constructibility of a sheaf of modules is local for a finite open cover of a scheme whose
underlying space is noetherian. -/
theorem _root_.AlgebraicGeometry.Scheme.isConstructibleSheaf_of_openCover :
    ∀ (n : ℕ) {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (U : Fin n → X.Opens) (_ : ∀ x, ∃ i, x ∈ U i)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
    (∀ i, IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U i).ι).obj F)) →
      IsConstructibleSheaf F := by
  intro n
  induction n with
  | zero =>
    intro X _ U hU F _
    have : IsEmpty X := ⟨fun x ↦ by obtain ⟨i, -⟩ := hU x; exact i.elim0⟩
    exact IsConstructibleSheaf.of_isZero (Etale.isZero_sheaf_of_isEmpty _)
  | succ n ih =>
    intro X _ U hU F h
    have : TopologicalSpace.NoetherianSpace (U 0) :=
      (U 0).ι.isOpenEmbedding.isInducing.noetherianSpace
    have : QuasiCompact (U 0).ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
    rw [Scheme.isConstructibleSheaf_iff_upperStar (U 0).ι (U 0).closedComplement (by simp)]
    refine ⟨h 0, ?_⟩
    let i := (U 0).closedComplement
    have : TopologicalSpace.NoetherianSpace _ := i.isClosedEmbedding.isInducing.noetherianSpace
    refine ih (fun k ↦ i ⁻¹ᵁ U k.succ) (fun z ↦ ?_) _ (fun k ↦ ?_)
    · have hz : i.base z ∉ U 0 := by
        have : i.base z ∈ Set.range i.base := ⟨z, rfl⟩
        rwa [(U 0).range_closedComplement] at this
      obtain ⟨k, hk⟩ := hU (i.base z)
      obtain ⟨k, rfl⟩ := Fin.eq_zero_or_eq_succ k |>.resolve_left (by rintro rfl; exact hz hk)
      exact ⟨k, hk⟩
    · have := h k.succ
      have : IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U k.succ).ι ⋙
          Etale.upperStar (ModuleCat.{u + 1} Λ) (i ∣_ U k.succ)).obj F) :=
        IsConstructibleSheaf.upperStar (i ∣_ U k.succ)
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U k.succ).ι).obj F)
      exact IsConstructibleSheaf.of_iso
        (((Etale.upperStarComp _ (i ∣_ U k.succ) (U k.succ).ι).app F).symm ≪≫
          eqToIso (by rw [morphismRestrict_ι]) ≪≫
          (Etale.upperStarComp _ (i ⁻¹ᵁ U k.succ).ι i).app F)

open ZeroObject in
omit [Finite Λ] in
/-- A bounded complex whose restrictions to the members of a finite open cover of a noetherian
space are bounded constructible is bounded constructible. -/
theorem boundedConstructible_of_openCover {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i)
    (R : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : ∀ i, boundedConstructible (ModuleCat.{u + 1} Λ) (U i)
      (D(((U i).ι)^*[ModuleCat.{u + 1} Λ]).obj R)) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X R := by
  -- homology commutes with the restrictions
  have e (i : Fin n) (q : ℤ) :=
    ((((U i).ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso q).app R
  refine ⟨?_, fun q ↦ ?_⟩
  · choose c d hcd using fun i ↦
      (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).2 (h i).1
    -- a zero sheaf is detected on the cover
    have hz (q : ℤ) (hq : ∀ i, IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (D(((U i).ι)^*[ModuleCat.{u + 1} Λ]).obj R))) :
        IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj R) := by
      have := Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
        (ι := ULift.{u} (Fin n)) (fun i ↦ (U i.down).ι)
        (fun x ↦ by obtain ⟨i, hi⟩ := hU x; exact ⟨⟨i⟩, ⟨x, hi⟩, rfl⟩)
        (0 : (_root_.DerivedCategory.homologyFunctor _ q).obj R ⟶ 0) (fun i ↦
          isIso_of_source_target_iso_zero _ ((hq i.down).of_iso (e i.down q)).isoZero
            (Functor.map_isZero _ (isZero_zero _)).isoZero)
      exact (isZero_zero _).of_iso
        (asIso (0 : (_root_.DerivedCategory.homologyFunctor _ q).obj R ⟶ 0))
    refine (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded R).1
      ⟨-∑ i, |c i|, ∑ i, |d i|, ?_, ?_⟩
    · refine (_root_.DerivedCategory.isGE_iff R _).2 fun q hq ↦ hz q fun i ↦
        (_root_.DerivedCategory.isGE_iff _ (c i)).1 (hcd i).1 q ?_
      have := Finset.single_le_sum (f := fun i ↦ |c i|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_univ i)
      have := neg_abs_le (c i)
      omega
    · refine (_root_.DerivedCategory.isLE_iff R _).2 fun q hq ↦ hz q fun i ↦
        (_root_.DerivedCategory.isLE_iff _ (d i)).1 (hcd i).2 q ?_
      have := Finset.single_le_sum (f := fun i ↦ |d i|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_univ i)
      have := le_abs_self (d i)
      omega
  · refine Scheme.isConstructibleSheaf_of_openCover Λ n U hU _ fun i ↦ ?_
    have : IsConstructibleSheaf ((D(((U i).ι)^*[ModuleCat.{u + 1} Λ]) ⋙
        _root_.DerivedCategory.homologyFunctor _ q).obj R) := (h i).2 q
    exact IsConstructibleSheaf.of_iso (e i q).symm


omit [Finite Λ] in
/-- A complex of finite Tor amplitude with bounded constructible homology restricts to one along
a pullback. -/
lemma constructibleFiniteTor_mapDerivedCategory_upperStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hN : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y N) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (D((f)^*[ModuleCat.{u + 1} Λ]).obj N) := by
  obtain ⟨hbc, c, d, hcd⟩ := hN
  exact ⟨hbc.mapDerivedCategory_upperStar f, c, d,
    (torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d).prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ f).app N)
      (torAmplitudeIn_leftDerivedUpperStar _ f c d hcd)⟩

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
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian aX }
  by_cases hX : IsEmpty X
  · exact boundedConstructible_of_openCover Λ (n := 0) Fin.elim0
      (fun x ↦ (hX.false x).elim) _ (fun i ↦ i.elim0)
  rw [not_isEmpty_iff] at hX
  have := HasInvertibleExponent.of_hom_of_nonempty (Λ := Λ) aX
  -- a finite cover by affine opens
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun V : X.affineOpens ↦ (V : Set X))
    (fun V ↦ V.1.isOpen) (fun x _ ↦ by
      obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hxV⟩)
  let U : Fin t.card → X.Opens := fun i ↦ (t.equivFin.symm i).1.1
  refine boundedConstructible_of_openCover Λ U (fun x ↦ ?_) _ (fun i ↦ ?_)
  · obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨t.equivFin ⟨V, hV⟩, by simpa [U] using hx⟩
  have : IsAffine (U i) := (t.equivFin.symm i).1.2
  let aU := (U i).ι ≫ aX
  obtain ⟨e⟩ := nonempty_iso_mapDerivedCategory_upperStar_derivedHom _ (U i).ι K M
  exact (boundedConstructible _ _).prop_of_iso e.symm
    (constructibleFiniteTor_derivedHom_of_verdierDual _ aU
      (constructibleFiniteTor_verdierDual Λ aU) (nonempty_iso_verdierDual_verdierDual Λ aU)
      (constructibleFiniteTor_tensor Λ _)
      (constructibleFiniteTor_mapDerivedCategory_upperStar Λ _ ⟨hK, a, b, hKt⟩)
      (constructibleFiniteTor_mapDerivedCategory_upperStar Λ _ ⟨hM, c, d, hMt⟩)).1

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

-- `aX` and the coefficient hypotheses are part of the blueprint setting, unused by the proof
set_option linter.unusedSectionVars false in
include aX in
/-- Blueprint `sk-thm-sf-hom-ctf`: Internal Hom with finite Tor amplitude.

If moreover `K` is dualizable, the sharper interval `[c - b, d - a]` holds, from the local
identification `RHom(K, M) ≅ K^∨ ⊗ᴸ M`. It genuinely fails in general: for the origin
`i : {0} ⟶ 𝔸¹` both `i_* Λ` and `Λ` have Tor amplitude `[0, 0]` while
`RHom(i_* Λ, Λ) = i_* Λ(-1)[-2]`. -/
theorem torAmplitudeIn_derivedHom_of_isDualizable
    (_hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) (hKd : IsDualizable K)
    (_hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M)
    (hMt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b) (d - a)
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M) :=
  torAmplitudeIn_derivedHom_of_isDualizable_aux _ hKt hKd hMt

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
      ((R(i)^![ModuleCat.{u + 1} Λ]).obj K) := by
  have : IsNoetherianRing Λ := inferInstance
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace aT
  have : IsNoetherian T := { __ := LocallyOfFiniteType.isLocallyNoetherian aT }
  let V := openComplementOfIsClosedImmersion i
  have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact V.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hij : Set.range i.base = (Set.range V.ι.base)ᶜ := by
    simp [V, openComplementOfIsClosedImmersion]
  obtain ⟨⟨hbc, hc⟩, ht⟩ := hK
  -- the restriction of `K` to the open complement
  have hbc' := boundedConstructible_leftDerivedUpperStar _ V.ι hbc
  have ht' := torAmplitudeIn_leftDerivedUpperStar _ V.ι a b ht
  obtain ⟨N, hN0, hNΛ, hNT⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := T)
  have : NeZero N := ⟨hN0.ne'⟩
  have hN := nsmul_id_eq_zero_of_natCast_eq_zero hNΛ ((L((V.ι)^*[ModuleCat.{u + 1} Λ])).obj K)
  have hdV : topologicalKrullDim V ≤ (d : WithBot ℕ∞) :=
    (V.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans hd
  have hMt := torAmplitudeIn_rightDerivedLowerStar _ (V.ι ≫ aT) aT V.ι rfl d hdV a b N hN hNT
    hbc' ht'
  have hM : constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) T a (b + 2 * d)
      ((R((V.ι)_*[ModuleCat.{u + 1} Λ])).obj ((L((V.ι)^*[ModuleCat.{u + 1} Λ])).obj K)) :=
    ⟨⟨boundedConstructible_rightDerivedLowerStar _ (V.ι ≫ aT) aT V.ι rfl N hN hNT hbc',
      _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hMt⟩, hMt⟩
  have := constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion_of_lowerStar
    (ModuleCat.{u + 1} Λ) i V.ι hij (by omega : b ≤ b + 2 * d) ⟨⟨hbc, hc⟩, ht⟩ hM
    (fun L ↦ hasProjectionFormula_of_finite Λ i _ L)
  rwa [show b + 2 * (d : ℤ) + 1 = b + 2 * d + 1 by ring] at this

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

omit [Finite Λ] in
/-- Membership in `D_c^[a, b]` with Tor amplitude in `[a, b]` is local for a finite open cover
of a scheme with noetherian underlying space. -/
theorem constructibleTorAmplitudeIn_of_openCover {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i)
    (R : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) {a b : ℤ}
    (h : ∀ i, constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) (U i)
      a b (D(((U i).ι)^*[ModuleCat.{u + 1} Λ]).obj R)) :
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X a b R :=
  ⟨⟨boundedConstructible_of_openCover Λ U hU R fun i ↦ (h i).1.1,
    homologyConcentratedIn_of_openCover _ U hU R fun i ↦ (h i).1.2⟩,
    torAmplitudeIn_of_openCover _ U hU R fun i ↦ (h i).2⟩


/-- The chart step of clause (iv): for an immersion `c : U ⟶ 𝔸ⁿ_V` over an affine open
`v : V ⟶ Y`, `R(c ≫ π ≫ v)^!` sends `D_c^[a, b]` to `D_c^[a - 2n, b + 2d + 1]` when
`dim Y ≤ d`. -/
theorem constructibleTorAmplitudeIn_rightDerivedUpperShriek_chart {U V Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (v : V ⟶ Y) [IsOpenImmersion v] [IsAffine V] {n : ℕ}
    (c : U ⟶ 𝔸(ULift.{u} (Fin n); V)) [IsImmersion c] [IsAffine U]
    [HasCompactification (c ≫ 𝔸(ULift.{u} (Fin n); V) ↘ V ≫ v)]
    (d : ℕ) (hd : topologicalKrullDim Y ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K) :
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) U (a - 2 * n) (b + 2 * d + 1)
      ((R(c ≫ 𝔸(ULift.{u} (Fin n); V) ↘ V ≫ v)^![ModuleCat.{u + 1} Λ]).obj K) := by
  have : IsNoetherianRing Λ := inferInstance
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  let π := 𝔸(ULift.{u} (Fin n); V) ↘ V
  let W := c.coborderRange
  let ι := c.liftCoborder
  have : TopologicalSpace.NoetherianSpace V := v.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact v := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  have : IsNoetherian V := {}
  have : IsNoetherianRing Γ(V, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top V⟩
  have : IsLocallyNoetherian 𝔸(ULift.{u} (Fin n); V) := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsNoetherian 𝔸(ULift.{u} (Fin n); V) := {}
  have : TopologicalSpace.NoetherianSpace W := W.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact W.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : HasCompactification v := (Compactification.ofIsOpenImmersion v).hasCompactification
  have : HasCompactification W.ι := (Compactification.ofIsOpenImmersion W.ι).hasCompactification
  have : HasCompactification ι := (Compactification.ofIsProper ι).hasCompactification
  have : HasInvertibleExponent Λ V := HasInvertibleExponent.of_hom v
  have : HasInvertibleExponent Λ W := HasInvertibleExponent.of_hom (W.ι ≫ π ≫ v)
  have : SmoothOfRelativeDimension n π := by
    simpa using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin n)) V
  have hdW : topologicalKrullDim W ≤ ((d + n : ℕ) : WithBot ℕ∞) := by
    refine (W.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans ?_
    rw [topologicalKrullDim_affineSpace_of_isAffine]
    have hV := (v.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans hd
    simp only [Nat.card_eq_fintype_card, Fintype.card_ulift, Fintype.card_fin, Nat.cast_add]
    exact add_le_add hV le_rfl
  have h₁ := constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isOpenImmersion Λ v a b hK
  have h₂ := constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_smoothOfRelativeDimension Λ π
    n a b h₁
  have h₃ := constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isOpenImmersion Λ W.ι _ _ h₂
  have h₄ := constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion Λ
    (W.ι ≫ π ≫ v ≫ aY) ι (d + n) hdW _ _ h₃
  have hc : c ≫ π ≫ v = ι ≫ W.ι ≫ π ≫ v := by
    rw [← Category.assoc ι, c.liftCoborder_ι]
  have heq : ∀ {g₁ g₂ : U ⟶ Y} [HasCompactification g₁] [HasCompactification g₂], g₁ = g₂ →
      Nonempty (R(g₁)^![ModuleCat.{u + 1} Λ] ≅ R(g₂)^![ModuleCat.{u + 1} Λ]) := by
    intro g₁ g₂ _ _ h
    subst h
    exact ⟨Iso.refl _⟩
  obtain ⟨e₀⟩ := heq hc
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ ι (W.ι ≫ π ≫ v)
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ W.ι (π ≫ v)
  obtain ⟨e₃⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ π v
  refine constructibleTorAmplitudeIn_of_iso _ ((e₀ ≪≫ e₁ ≪≫ Functor.isoWhiskerRight e₂ _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight e₃ _) _).app K).symm ?_
  have hb : b - 2 * (n : ℤ) + 2 * ((d + n : ℕ) : ℤ) + 1 = b + 2 * d + 1 := by push_cast; ring
  rw [hb] at h₄
  exact h₄

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
            ((R(f)^![ModuleCat.{u + 1} Λ]).obj K) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := {}
  -- affine charts `U ⊆ f⁻¹ V`
  have hchart (x : X) : ∃ (U : X.affineOpens) (V : Y.affineOpens),
      x ∈ (U : X.Opens) ∧ (U : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens) := by
    obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
      (show f.base x ∈ (⊤ : Y.Opens) from trivial)
    obtain ⟨U, hU, hxU, hUV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
      (show x ∈ f ⁻¹ᵁ V from hxV)
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hxU, hUV⟩
  choose U V hxU hUV using hchart
  -- immersions of the charts into affine spaces over the `V`
  have hemb (x : X) : ∃ (n : ℕ) (c : ((U x : X.Opens) : Scheme.{u}) ⟶
      𝔸(ULift.{u} (Fin n); (V x : Y.Opens))), IsImmersion c ∧
      c ≫ 𝔸(ULift.{u} (Fin n); (V x : Y.Opens)) ↘ _ ≫ (V x : Y.Opens).ι =
        (U x : X.Opens).ι ≫ f := by
    have hr : Set.range ((U x : X.Opens).ι ≫ f).base ⊆ Set.range (V x : Y.Opens).ι.base := by
      rintro - ⟨y, rfl⟩
      simpa using hUV x y.2
    let g := IsOpenImmersion.lift (V x : Y.Opens).ι ((U x : X.Opens).ι ≫ f) hr
    have hg : g ≫ (V x : Y.Opens).ι = (U x : X.Opens).ι ≫ f := IsOpenImmersion.lift_fac _ _ _
    have : LocallyOfFiniteType (g ≫ (V x : Y.Opens).ι) := by rw [hg]; infer_instance
    have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (V x : Y.Opens).ι
    have : IsAffine ((U x : X.Opens) : Scheme.{u}) := (U x).2
    obtain ⟨n, c, hc, himm⟩ := exists_immersion_affineSpace_of_quasiAffine g
    exact ⟨n, c, himm, by rw [← Category.assoc, hc, hg]⟩
  choose n c hc hcf using hemb
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ ((U x : X.Opens) : Set X))
    (fun x ↦ (U x : X.Opens).isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxU x⟩)
  refine ⟨t.sup n, fun d hd a b K hK ↦ ?_⟩
  let Uc : Fin t.card → X.Opens := fun i ↦ (U (t.equivFin.symm i)).1
  refine constructibleTorAmplitudeIn_of_openCover Λ Uc (fun x ↦ ?_) _ fun i ↦ ?_
  · obtain ⟨y, hy, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨t.equivFin ⟨y, hy⟩, by simpa [Uc] using hx⟩
  set x := (t.equivFin.symm i).1
  have hxt : x ∈ t := (t.equivFin.symm i).2
  have : IsAffine ((U x : X.Opens) : Scheme.{u}) := (U x).2
  have : IsAffine ((V x : Y.Opens) : Scheme.{u}) := (V x).2
  have := hc x
  have : TopologicalSpace.NoetherianSpace (U x : X.Opens) :=
    (U x : X.Opens).ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact (U x : X.Opens).ι :=
    ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : HasCompactification (U x : X.Opens).ι :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  have hK' := constructibleTorAmplitudeIn_rightDerivedUpperShriek_chart Λ aY (V x : Y.Opens).ι
    (c x) d hd a b hK
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ (U x : X.Opens).ι f
  have heq : ∀ {g₁ g₂ : ((U x : X.Opens) : Scheme.{u}) ⟶ Y} [HasCompactification g₁]
      [HasCompactification g₂], g₁ = g₂ →
      Nonempty (R(g₁)^![ModuleCat.{u + 1} Λ] ≅ R(g₂)^![ModuleCat.{u + 1} Λ]) := by
    intro g₁ g₂ _ _ h
    subst h
    exact ⟨Iso.refl _⟩
  obtain ⟨e₂⟩ := heq (hcf x)
  have hmono := hK'
  refine constructibleTorAmplitudeIn_of_iso _ (((rightDerivedUpperShriekIsoOfIsOpenImmersion Λ
    (U x : X.Opens).ι).app _).symm ≪≫ (e₁.app K).symm ≪≫ (e₂.app K).symm).symm ?_
  obtain ⟨⟨hbc, hc₁, hc₂⟩, hta⟩ := hK'
  have hn : n x ≤ t.sup n := Finset.le_sup hxt
  exact ⟨⟨hbc, _root_.DerivedCategory.TStructure.t.isGE_of_ge _ _ (a - 2 * n x) (by omega),
    hc₂⟩, hta.mono (by omega) le_rfl⟩

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

section Generation

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The derived direct image along an identity is the identity. -/
noncomputable def rightDerivedLowerStarIdIso (Y : Scheme.{u}) :
    R((𝟙 Y)_*[ModuleCat.{u + 1} Λ]) ≅ 𝟭 _ :=
  (Etale.lowerStar (ModuleCat.{u + 1} Λ) (𝟙 Y)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryNatIso (Etale.lowerStarId (ModuleCat.{u + 1} Λ) Y) ≪≫
    Functor.mapDerivedCategoryIdIso _

omit [Finite Λ] in
variable {Λ} in
/-- Tor amplitude through the canonical t-structure gives Tor amplitude tested on one homology
sheaf at a time. -/
lemma hasTorAmplitudeIn_of_torAmplitudeIn {X : Scheme.{u}} {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    DerivedCategory.hasTorAmplitudeIn Λ X a b K := fun F q hq ↦ by
  obtain ⟨h₁, h₂⟩ := h F
  rcases hq with hq | hq
  · exact (_root_.DerivedCategory.isGE_iff _ a).1 h₁ q hq
  · exact (_root_.DerivedCategory.isLE_iff _ b).1 h₂ q hq

/-- The dévissage step of `sk-lem-sf-ctf-generation`: a thick subcategory containing the
generators `Rg_* Rj_! L` contains `Rι_* F` for every flat constructible sheaf `F` on a closed
subscheme `ι : Z ⟶ X`. By Noetherian induction on the support `T = ι(Z)`: `F` is lisse on a dense
open `V ⊆ Z`, and the open–closed triangle `j_! j^* F ⟶ F ⟶ i_* i^* F` for `V` and its closed
complement exhibits `Rι_* F` as an extension of a generator and of the direct image of the flat
constructible sheaf `i^* F` from a closed subscheme with smaller support. -/
theorem prop_rightDerivedLowerStar_of_flat (X : Scheme.{u}) [IsNoetherian X]
    (P : ObjectProperty
      (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hP : ∀ (str : Scheme.Stratification X) (i : Fin str.n) (Ubar : Scheme.{u})
      (j : str.domain i ⟶ Ubar) [IsOpenImmersion j] [HasCompactification j]
      (g : Ubar ⟶ X) [IsClosedImmersion g], Set.range (j ≫ g) = str.stratum i →
      Set.range g = _root_.closure (str.stratum i) →
      ∀ (L : Sheaf (str.domain i).smallEtaleTopology (ModuleCat.{u + 1} Λ))
        [IsFiniteLocallyConstantSheaf L], ObjectProperty.flat L →
        P ((R((g)_*[ModuleCat.{u + 1} Λ])).obj ((R(j)_![ModuleCat.{u + 1} Λ]).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L)))) :
    ∀ (T : TopologicalSpace.Closeds X) {Z : Scheme.{u}} (ι : Z ⟶ X) [IsClosedImmersion ι],
      Set.range ι.base = T → ∀ (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        [IsConstructibleSheaf F], ObjectProperty.flat F →
        P ((R((ι)_*[ModuleCat.{u + 1} Λ])).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
  intro T
  induction T using WellFoundedLT.induction with
  | ind T ih =>
  intro Z ι _ hT F _ hF
  by_cases hZ : IsEmpty Z
  · exact P.prop_of_isZero (Functor.map_isZero _ (isZero_derivedCategory_of_isEmpty _ Z _))
  rw [not_isEmpty_iff] at hZ
  obtain ⟨V, hVd, hV⟩ := IsConstructibleSheaf.exists_dense_open F
  have : TopologicalSpace.NoetherianSpace Z := ι.isClosedEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact V.ι := ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : HasCompactification V.ι := (Compactification.ofIsOpenImmersion V.ι).hasCompactification
  obtain ⟨w, hw⟩ := exists_distTriang_openClosed (ModuleCat.{u + 1} Λ) V.ι V.closedComplement
    (by simp) ((_root_.DerivedCategory.singleFunctor _ 0).obj F)
  refine P.ext_of_isTriangulatedClosed₂ _ ((R((ι)_*[ModuleCat.{u + 1} Λ])).map_distinguished _ hw)
    ?_ ?_
  · -- the open part is a generator
    let str := Scheme.Stratification.ofClosedImmersionOpens ι V
    have := hP str (show Fin str.n from (1 : Fin 3)) Z
      (V.ι : str.domain (show Fin str.n from (1 : Fin 3)) ⟶ Z) ι (by simp [str,
      Scheme.Stratification.ofClosedImmersionOpens, Set.range_comp]) (by
        change Set.range ι.base = closure (ι.base '' V)
        rw [ι.isClosedEmbedding.closure_image_eq, hVd.closure_eq, Set.image_univ])
      ((V.ι)^*[_].obj F) (Functor.PreservesFlat.flat_obj (F := (V.ι)^*[_]) hF)
    exact P.prop_of_iso ((R((ι)_*[ModuleCat.{u + 1} Λ])).mapIso
      ((rightDerivedLowerShriekIsoOfIsOpenImmersion Λ V.ι).app _ ≪≫
        D((V.ι)_!open[ModuleCat.{u + 1} Λ]).mapIso
          ((((V.ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app F).symm)) this
  · -- the closed part is handled by induction
    have hlt : (⟨Set.range (V.closedComplement ≫ ι).base,
        (V.closedComplement ≫ ι).isClosedEmbedding.isClosed_range⟩ :
          TopologicalSpace.Closeds X) < T := by
      rw [← SetLike.coe_ssubset_coe, TopologicalSpace.Closeds.coe_mk, ← hT, Scheme.Hom.comp_base,
        TopCat.coe_comp, Set.range_comp]
      refine (Set.image_subset_range _ _).ssubset_of_ne fun h ↦ ?_
      obtain ⟨z, hz⟩ := hVd.nonempty
      obtain ⟨y, hy, hyz⟩ : ι.base z ∈ ι.base '' Set.range V.closedComplement.base :=
        h ▸ ⟨z, rfl⟩
      rw [ι.isClosedEmbedding.injective hyz, V.range_closedComplement] at hy
      exact hy hz
    have : IsConstructibleSheaf ((V.closedComplement)^*[ModuleCat.{u + 1} Λ].obj F) :=
      IsConstructibleSheaf.upperStar _ _
    exact P.prop_of_iso (((rightDerivedLowerStarComp _ V.closedComplement ι).app _).symm ≪≫
      (R((ι)_*[ModuleCat.{u + 1} Λ])).mapIso
        ((R((V.closedComplement)_*[ModuleCat.{u + 1} Λ])).mapIso
        ((((V.closedComplement)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app
          F).symm))
      (ih _ hlt (V.closedComplement ≫ ι) rfl _
        (Functor.PreservesFlat.flat_obj (F := (V.closedComplement)^*[_]) hF))

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
  by
  obtain ⟨a, b, ⟨⟨hbc, hab⟩, hta⟩⟩ :=
    (exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor K).2 hK
  by_cases hab' : a ≤ b
  swap
  · have : K.IsGE a := hab.1
    have : K.IsLE b := hab.2
    exact P.prop_of_isZero (_root_.DerivedCategory.TStructure.t.isZero K b a (by omega))
  -- a bounded model by flat constructible sheaves, reduced to its terms by dévissage
  obtain ⟨Pc, ⟨hPz, hPflat⟩, hPc, ⟨e⟩⟩ := (hasTorAmplitudeIn_iff_exists_flatConstructibleModel
    Λ a b hab' K hbc).1 (hasTorAmplitudeIn_of_torAmplitudeIn hta)
  have : Pc.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi ↦ hPz i (.inl hi)
  have : Pc.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi ↦ hPz i (.inr hi)
  have hS := HomotopyCategory.mem_subcategory_of_strictly_bounded
    (P.inverseImage _root_.DerivedCategory.Qh) Pc a b (fun n _ _ ↦ ?_)
  · exact P.prop_of_iso e.symm (P.prop_of_iso
      ((_root_.DerivedCategory.quotientCompQhIso _).app Pc) hS)
  have := hPc n
  exact P.prop_of_iso ((rightDerivedLowerStarIdIso Λ X).app _)
    (prop_rightDerivedLowerStar_of_flat Λ X P hP ⊤ (𝟙 X) (by simp) (Pc.X n) (hPflat n))

end Generation

end Etale

end AlgebraicGeometry
