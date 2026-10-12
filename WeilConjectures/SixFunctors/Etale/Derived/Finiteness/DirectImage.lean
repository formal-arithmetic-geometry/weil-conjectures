/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.NumberTheory.Padics.Complex
public import WeilConjectures.AlgebraicGeometry.BaseChangeDimension
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.ConstructibleSheaf.Presentation
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.Supports
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Finiteness of direct images

`Rf_*` and `Rf_!` preserve bounded constructibility, with a cohomological-dimension bound in
terms of the fibre dimension (`sk-prop-sf-finiteness`). Here `Λ` is a finite coefficient ring
whose exponent is invertible on the schemes in question
(`AlgebraicGeometry.HasInvertibleExponent`) and the schemes are of finite type over a field:
without the invertibility the Artin–Schreier sequence already defeats constructibility of
`R¹f_*` in characteristic `p`.

The proofs follow the blueprint: the finiteness of `Rf_*` is the theorem
`thm-dg-finite-type-constructibility`, that of `Rf_! = Rg_* ∘ j_!` follows from it for the
proper `g` of a compactification together with the constructibility of extensions by zero, and
the vanishing of `Rᵠf_!` above twice the fibre dimension is read off the sheaf case
`sbc-thm-finiteness-finite-type` by a dévissage along the truncation triangles. The theorems
`thm-dg-finite-type-constructibility`, `sbc-thm-finiteness-finite-type` (vanishing clause) and
`cor-fin-deligne-open-finite-coefficients` are nodes of the blueprint subsection `sk-prop-sf-cbc`
and are stated here with `sorry`; they are proved there.

## Main statements

- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent`
- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek` and
  `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek_padicAlgCl`
- `AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerShriek`
- `thm-fin-open-immersion`, both in the namespace `AlgebraicGeometry.Etale`:
  `boundedConstructible_rightDerivedLowerStar_singleFunctor_of_isOpenImmersion` and
  `isZero_upperStar_homology_rightDerivedLowerStar_singleFunctor`
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

/-! ### Inputs from the blueprint subsection `sk-prop-sf-cbc` -/

/-- Blueprint `cor-fin-deligne-open-finite-coefficients`: Open direct images with arbitrary
finite allowable coefficients.

Let `Λ` be a finite ring annihilated by an integer invertible in the field `k`, and let
`j : X ⟶ Y` be an open immersion of finite-type `k`-schemes (`X` is of finite type over `k` as
soon as `Y` is, `Y` being noetherian). Then `Rj_*` carries `D^b_c(X, Λ)` into `D^b_c(Y, Λ)`.

This is a node of the blueprint subsection `sk-prop-sf-cbc`, where it is proved by Deligne's
generic constructibility for an open immersion and a dévissage from `𝔽_ℓ` to `Λ`. -/
theorem boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion
    [HasInvertibleExponent Λ (Spec (.of k))] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] (j : X ⟶ Y) [IsOpenImmersion j]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj K) :=
  sorry

/-- Blueprint `thm-dg-finite-type-constructibility`: Bounded constructibility of every
finite-type direct image.

Let `f : X ⟶ Y` be a morphism between finite-type schemes over a field `k`, and let `Λ` be a
finite ring annihilated by an integer invertible in `k`. Then `Rf_*` carries `D^b_c(X, Λ)` into
`D^b_c(Y, Λ)`. The morphism `f` need not be separated.

This is a node of the blueprint subsection `sk-prop-sf-cbc`, where it is proved by a finite Čech
resolution reducing it to an open immersion followed by a projective morphism. -/
theorem boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType
    [HasInvertibleExponent Λ (Spec (.of k))] (f : X ⟶ Y) (aX : X ⟶ Spec (.of k))
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY]
    [QuasiCompact aY] (hf : f ≫ aY = aX)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) :=
  sorry

/-- Blueprint `sbc-thm-finiteness-finite-type`: Finiteness of higher direct images of
finite-type morphisms, the vanishing clause.

Let `f : X ⟶ Y` be a separated finite-type morphism (here: one admitting a compactification)
between finite-type schemes over a field `k`, let `Λ` be a finite ring whose exponent is
invertible on `Y` and let `𝓕` be a sheaf of `Λ`-modules on `X_ét`. If the geometric fibres of
`f` have dimension at most `e`, then `Rᵠf_! 𝓕 = 0` for `q > 2e`. Constructibility of `𝓕` is
not needed: the bound only uses the dimensions of the original fibres (blueprint
`lem-dg-compact-support-amplitude`).

This is a node of the blueprint subsection `sk-prop-sf-cbc`, where it is proved. Its other
clauses, the bounded constructibility of `Rf_* 𝓕` and of `Rf_! 𝓕`, are the sheaf cases of
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType` and
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek`. -/
theorem isZero_homology_rightDerivedLowerShriek_singleFunctor
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f]
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (hf : f ≫ aY = aX) (e : ℕ)
    (he : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (Limits.pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (hq : (2 * e : ℤ) < q) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) :=
  sorry

/-! ### Auxiliary lemmas -/

omit [Finite Λ] in
/-- A zero object of the derived category of étale sheaves is bounded constructible. -/
lemma boundedConstructible_of_isZero
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsZero K) : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K := by
  have h (i : ℤ) := (_root_.DerivedCategory.homologyFunctor _ i).map_isZero hK
  exact ⟨⟨⟨0, (_root_.DerivedCategory.isGE_iff K 0).2 fun i _ ↦ h i⟩,
    ⟨0, (_root_.DerivedCategory.isLE_iff K 0).2 fun i _ ↦ h i⟩⟩,
    fun n ↦ IsConstructibleSheaf.of_isZero (h n)⟩

omit [Finite Λ] in
/-- Extension by zero along a quasi-compact open immersion `j` preserves bounded
constructibility: `j_!` is exact, and the extension by zero of a constructible sheaf is
constructible. -/
lemma boundedConstructible_mapDerivedCategory_openImmersionLowerShriek (j : X ⟶ Y)
    [IsOpenImmersion j] [QuasiCompact j]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      (D((j)_!open[ModuleCat.{u + 1} Λ]).obj K) := by
  let F := (j)_!open[ModuleCat.{u + 1} Λ]
  refine ⟨F.bounded_mapDerivedCategory_obj hK.1, fun n ↦ ?_⟩
  have := hK.2 n
  have : IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ n ⋙ F).obj K) :=
    IsConstructibleSheaf.openImmersionLowerShriek j j.closedComplement
      j.range_closedComplement ((_root_.DerivedCategory.homologyFunctor _ n).obj K)
  exact IsConstructibleSheaf.of_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K)

omit [Finite Λ] in
open _root_.DerivedCategory in
/-- **Dévissage for the amplitude of `Rf_!`.** If `Rf_!` sends every constructible sheaf in
degree `0` into degrees `≤ e`, then it sends a bounded complex with constructible homology
concentrated in `[a, a + m - 1]` into degrees `≤ a + m - 1 + e`: by induction on `m`, along the
truncation triangle `τ_{< b} K ⟶ K ⟶ τ_{≥ b} K ⟶` with `b = a + m - 1`, whose third term is
`Hᵇ K` placed in degree `b`. -/
lemma isLE_rightDerivedLowerShriek_obj (f : X ⟶ Y) [HasCompactification f] (e : ℤ)
    (h : ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsConstructibleSheaf F →
      _root_.DerivedCategory.TStructure.t.IsLE
        ((R(f)_![ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) e)
    (m : ℕ) :
    ∀ (a : ℤ) (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      K.IsGE a → K.IsLE (a + m - 1) →
      (∀ q, IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) →
      _root_.DerivedCategory.TStructure.t.IsLE ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)
        (a + m - 1 + e) := by
  induction m with
  | zero =>
    intro a K _ _ _
    have : K.IsLE (a - 1) := by simpa using ‹K.IsLE (a + ↑(0 : ℕ) - 1)›
    have hK := (R(f)_![ModuleCat.{u + 1} Λ]).map_isZero (TStructure.t.isZero K (a - 1) a (by lia))
    exact (isLE_iff _ _).2 fun i _ ↦ (homologyFunctor _ i).map_isZero hK
  | succ m ih =>
    intro a K _ _ hK
    set b : ℤ := a + m
    let T := (TStructure.t.triangleLTGE b).obj K
    have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished b K
    -- the third term is `Hᵇ K` placed in degree `b`
    have : T.obj₃.IsLE b := by
      have : K.IsLE b := TStructure.t.isLE_of_le K (a + ↑(m + 1) - 1) _ (by lia)
      exact inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE b).obj K) b)
    have : T.obj₃.IsGE b := inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncGE b).obj K) b)
    obtain ⟨G, ⟨eG⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE T.obj₃ b
    have := isIso_homologyMap_mor₂ _ hT b (b + 1) rfl (isZero_of_isLE _ (b - 1) _ (by lia))
      (isZero_of_isLE _ (b - 1) _ (by lia))
    have hG : IsConstructibleSheaf G := by
      have : IsConstructibleSheaf ((homologyFunctor _ b).obj T.obj₂) := hK b
      exact IsConstructibleSheaf.of_iso (asIso ((homologyFunctor _ b).map T.mor₂) ≪≫
        (homologyFunctor _ b).mapIso eG ≪≫ (singleFunctorCompHomologyFunctorIso _ b).app G)
    have h₃ : TStructure.t.IsLE ((R(f)_![ModuleCat.{u + 1} Λ]).obj T.obj₃) (b + e) := by
      have := h G hG
      have : TStructure.t.IsLE ((R(f)_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ (-b)).obj
          (((singleFunctors _).functor 0).obj G)) (b + e) :=
        TStructure.t.isLE_shift _ e (-b) (b + e) (by lia)
      exact TStructure.t.isLE_of_iso ((R(f)_![ModuleCat.{u + 1} Λ]).mapIso
        (eG ≪≫ (((singleFunctors _).shiftIso (-b) b 0 (by lia)).app G).symm) ≪≫
          ((R(f)_![ModuleCat.{u + 1} Λ]).commShiftIso (-b)).app _).symm _
    -- the first term is handled by induction
    have h₁ : TStructure.t.IsLE ((R(f)_![ModuleCat.{u + 1} Λ]).obj T.obj₁) (b + e) := by
      have := ih a T.obj₁
        (inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj K) a))
        (TStructure.t.isLE_truncLT_obj _ _ _ (by lia)) fun q ↦ ?_
      · exact TStructure.t.isLE_of_le _ (a + m - 1 + e) _ (by lia)
      · by_cases hq : q < b
        · have : IsIso ((homologyFunctor _ q).map T.mor₁) :=
            isIso_homologyMap_mor₁ _ hT (q - 1) q (by lia)
              (isZero_of_isGE _ b _ (by lia)) (isZero_of_isGE _ b _ (by lia))
          have : IsConstructibleSheaf ((homologyFunctor _ q).obj T.obj₂) := hK q
          exact IsConstructibleSheaf.of_iso (asIso ((homologyFunctor _ q).map T.mor₁)).symm
        · have : T.obj₁.IsLE (b - 1) := TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
          exact IsConstructibleSheaf.of_isZero (isZero_of_isLE _ (b - 1) _ (by lia))
    have : TStructure.t.IsLE ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) (b + e) :=
      TStructure.t.isLE₂ _ ((R(f)_![ModuleCat.{u + 1} Λ]).map_distinguished _ hT) (b + e) h₁ h₃
    exact TStructure.t.isLE_of_le _ (b + e) _ (by lia)

omit [Finite Λ] in
/-- For an open immersion `j`, restricting `Rj_* K` back along `j` gives `K` again: compute
`Rj_*` on a K-injective complex `I` representing `K`, and use that the counit
`j^* j_* ⟶ 𝟭` is an isomorphism, `j_*` being fully faithful. -/
noncomputable def mapDerivedCategoryUpperStarRightDerivedLowerStarIso (j : X ⟶ Y)
    [IsOpenImmersion j]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D((j)^*[ModuleCat.{u + 1} Λ]).obj ((R((j)_*[ModuleCat.{u + 1} Λ])).obj K) ≅ K :=
  have h := _root_.DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  let I := h.choose
  have : I.IsKInjective := h.choose_spec.1
  let e : K ≅ _root_.DerivedCategory.Q.obj I := h.choose_spec.2.some
  D((j)^*[ModuleCat.{u + 1} Λ]).mapIso
      ((R((j)_*[ModuleCat.{u + 1} Λ])).mapIso e ≪≫
        ((j)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorObjQIso I) ≪≫
    ((j)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryFactors.app _ ≪≫
    _root_.DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
      (asIso (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit) _).app I ≪≫
        (Functor.mapHomologicalComplexIdIso _ _).app I) ≪≫ e.symm

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

open ZeroObject in
omit [Finite Λ] in
/-- An étale sheaf of `Λ`-modules on `Y` whose pullback to every geometric point of `Y` vanishes
is zero, the geometric points forming a conservative family. -/
lemma isZero_of_forall_isZero_upperStar (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      IsZero ((Etale.upperStar (ModuleCat.{u + 1} Λ) s).obj G)) : IsZero G := by
  have : IsIso (0 : G ⟶ 0) := Scheme.isIso_of_isIso_sheafFiber_map _ fun y ↦ by
    have : LocallySmall.{u + 1} Y.Etale := locallySmall_max.{u + 1, u}
    have : LocallySmall.{u + 1} (Spec (.of (AlgebraicClosure (Y.residueField y)))).Etale :=
      locallySmall_max.{u + 1, u}
    have : ((Y.uliftPointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} Λ)).IsLeftAdjoint :=
      inferInstance
    have : (((pointSmallEtale (𝟙 (Spec (.of (AlgebraicClosure (Y.residueField y)))))).ulift.{u + 1}
      ).sheafFiber (A := ModuleCat.{u + 1} Λ)).IsLeftAdjoint := inferInstance
    have e := (Etale.upperStarCompUliftSheafFiberIso (ModuleCat.{u + 1} Λ) (Y.algClosurePoint y)
      (𝟙 _)).app G
    rw [Category.id_comp] at e
    have hz : IsZero ((Y.uliftPointSmallEtale y).sheafFiber.obj G) := by
      refine IsZero.of_iso ?_ e.symm
      exact (((pointSmallEtale (𝟙 _)).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map_isZero (h _ _)
    exact isIso_of_source_target_iso_zero _ hz.isoZero
      (((Y.uliftPointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} Λ)).map_isZero
        (isZero_zero _)).isoZero
  exact IsZero.of_iso (isZero_zero _) (asIso (0 : G ⟶ 0))

/-! ### Open immersions -/

/-- Blueprint `thm-fin-open-immersion`: Open-immersion direct images (constructibility).

Let `j : X ⟶ Y` be an open immersion of finite-type schemes over a field `k`, and let `𝓕` be a
constructible sheaf of `Λ`-modules on `X_ét`, for a finite `Λ` annihilated by an integer
invertible in `k`. Then every higher direct image `Rᵠj_* 𝓕` is constructible, and they vanish
for all sufficiently large `q`: `Rj_* 𝓕` is bounded constructible. This is
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion`
(`cor-fin-deligne-open-finite-coefficients`) applied to `𝓕` in degree `0`. The vanishing of the
restrictions of the `Rᵠj_* 𝓕` to `X` for `q > 0` is
`AlgebraicGeometry.Etale.isZero_upperStar_homology_rightDerivedLowerStar_singleFunctor`. -/
theorem boundedConstructible_rightDerivedLowerStar_singleFunctor_of_isOpenImmersion
    [HasInvertibleExponent Λ (Spec (.of k))] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] (j : X ⟶ Y) [IsOpenImmersion j]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) :=
  boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion Λ aY j _
    (DerivedCategory.boundedConstructible_singleFunctor_obj F 0)

omit [Finite Λ] in
/-- Blueprint `thm-fin-open-immersion`: Open-immersion direct images (support).

For an open immersion `j : X ⟶ Y` and a sheaf `𝓕` of `Λ`-modules on `X_ét`, the restriction of
`Rᵠj_* 𝓕` to `X` vanishes for `q ≠ 0`: restriction is exact, so it commutes with the homology
sheaves, and `j^* Rj_* 𝓕 ≅ 𝓕` (`j^* j_* I ≅ I` for an injective resolution `I` of `𝓕`). The
constructibility part of the blueprint statement is
`boundedConstructible_rightDerivedLowerStar_singleFunctor_of_isOpenImmersion`.
-/
theorem isZero_upperStar_homology_rightDerivedLowerStar_singleFunctor (j : X ⟶ Y)
    [IsOpenImmersion j] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (hq : q ≠ 0) :
    IsZero ((j)^*[ModuleCat.{u + 1} Λ].obj ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) := by
  let e := mapDerivedCategoryUpperStarRightDerivedLowerStarIso Λ j
    ((_root_.DerivedCategory.singleFunctor _ 0).obj F)
  refine IsZero.of_iso ?_ ((((j)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso
    q).app _ ≪≫ (_root_.DerivedCategory.homologyFunctor _ q).mapIso e)
  obtain hq | hq := hq.lt_or_gt
  · exact _root_.DerivedCategory.isZero_of_isGE _ 0 q hq
  · exact _root_.DerivedCategory.isZero_of_isLE _ 0 q hq

/-! ### Finiteness of `Rf_*` and `Rf_!` -/

/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility

**Finiteness of direct images.** Let `Λ` be a finite ring whose exponent is invertible on `X`
and let `f : X ⟶ Y` be a quasi-compact morphism between `k`-schemes locally of finite type, with
`Y` quasi-compact. Then `Rf_*` carries `D^b_c(X, Λ)` into `D^b_c(Y, Λ)`; separatedness of `f` is
not needed. This is
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType`
(`thm-dg-finite-type-constructibility`): `X` is quasi-compact since `f` and `Y` are, and the
exponent of `Λ` is invertible in `k` as soon as `X` is nonempty.

Some finiteness hypothesis on `Y` is needed: for `f : ⊔ₙ ℙⁿ_k ⟶ ⊔ₙ Spec k`, which is proper,
`Rf_* Λ` has `H²ⁿ ≠ 0` on the `n`-th point, so it is not bounded.

The cohomological-dimension bound of the blueprint statement is
`AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_add_lt` (`thm-sc-finite-type-torsion-cd`),
and its special case for the spectrum of a separably closed field is
`AlgebraicGeometry.Scheme.subsingleton_H_of_isSepClosed` (`lem-kun-cd-sep-closed-point`). -/
theorem boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent (f : X ⟶ Y)
    [QuasiCompact f] [HasInvertibleExponent Λ X] (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [LocallyOfFiniteType aY] [QuasiCompact aY] (hf : f ≫ aY = aX)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  cases isEmpty_or_nonempty X with
  | inl hX =>
    exact boundedConstructible_of_isZero Λ
      ((R((f)_*[ModuleCat.{u + 1} Λ])).map_isZero (isZero_derivedCategory_of_isEmpty _ X K))
  | inr hX =>
    have := HasInvertibleExponent.of_hom_of_nonempty (Λ := Λ) aX
    have : QuasiCompact aX := hf ▸ inferInstance
    exact boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType Λ f aX aY hf K hK

/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility

**Finiteness of compactly supported direct images.** For `f : X ⟶ Y` admitting a
compactification, between `k`-schemes locally of finite type with `Y` quasi-compact, `Rf_!`
carries `D^b_c(X, Λ)` into `D^b_c(Y, Λ)`. For the chosen compactification `X ⟶[j] Z ⟶[g] Y`,
`Rf_! = Rg_* ∘ j_!`: extension by zero preserves constructibility, and `Rg_*` preserves bounded
constructibility by
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent`.

As for `Rf_*`, some finiteness hypothesis on `Y` is needed. -/
theorem boundedConstructible_rightDerivedLowerShriek (f : X ⟶ Y) [HasCompactification f]
    [HasInvertibleExponent Λ X] (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [LocallyOfFiniteType aY] [QuasiCompact aY] (hf : f ≫ aY = aX)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) := by
  subst hf
  cases isEmpty_or_nonempty X with
  | inl hX =>
    exact boundedConstructible_of_isZero Λ
      ((R(f)_![ModuleCat.{u + 1} Λ]).map_isZero (isZero_derivedCategory_of_isEmpty _ X K))
  | inr hX =>
    have := HasInvertibleExponent.of_hom_of_nonempty (Λ := Λ) (f ≫ aY)
    let c := HasCompactification.compactification f
    have : HasInvertibleExponent Λ c.Z := HasInvertibleExponent.of_hom (c.g ≫ aY)
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
    have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
    have : IsNoetherian c.Z := { __ := LocallyOfFiniteType.isLocallyNoetherian (c.g ≫ aY) }
    have : TopologicalSpace.NoetherianSpace X := c.i.isOpenEmbedding.isInducing.noetherianSpace
    exact boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent Λ c.g (c.g ≫ aY) aY
      rfl _ (boundedConstructible_mapDerivedCategory_openImmersionLowerShriek Λ c.i hK)

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
    (hf : f ≫ aY = aX)
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
complex `K = Λ[-1]` has `H^1(Rf_! K) = Λ`.

The proof checks the vanishing at the geometric points `s : Spec Ω ⟶ Y`: by compactly
supported base change the pullback of `Rf_! K` to `s` is `Rf'_!` of the pullback of `K` to the
geometric fibre `f' : X ×_Y Spec Ω ⟶ Spec Ω`, and there the bound is
`AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerShriek_singleFunctor` together
with the dévissage `DerivedCategory.isLE_obj_of_isLE`. Constructibility of `K` is not used. -/
theorem isZero_homology_rightDerivedLowerShriek (f : X ⟶ Y) [HasCompactification f]
    [HasInvertibleExponent Λ X] (e : ℕ)
    (he : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (Limits.pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hK₀ : _root_.DerivedCategory.TStructure.t.IsLE K 0) (q : ℤ) (hq : (2 * e : ℤ) < q) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)) := by
  refine isZero_of_forall_isZero_upperStar Λ _ fun Ω _ _ s ↦ ?_
  let f' := pullback.snd f s
  let g' := pullback.fst f s
  have sq : IsPullback g' f' f s := IsPullback.of_hasPullback f s
  have := noetherianSpace_of_hasCompactification f' (𝟙 (Spec (.of Ω)))
  have : QuasiCompact f' := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  let K' := ((Etale.upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategory).obj K
  have eK : (Etale.upperStar (ModuleCat.{u + 1} Λ) s).obj
      ((_root_.DerivedCategory.homologyFunctor _ q).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)) ≅
      (_root_.DerivedCategory.homologyFunctor _ q).obj ((R(f')_![ModuleCat.{u + 1} Λ]).obj K') :=
    (Functor.mapDerivedCategoryHomologyFunctorIso (Etale.upperStar (ModuleCat.{u + 1} Λ) s) q).app
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) ≪≫
      (_root_.DerivedCategory.homologyFunctor _ q).mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory _ s).symm.app _ ≪≫
          asIso ((rightDerivedLowerShriekBaseChangeMap Λ sq).app K) ≪≫
          (R(f')_![ModuleCat.{u + 1} Λ]).mapIso
            ((leftDerivedUpperStarIsoMapDerivedCategory _ g').app K))
  refine IsZero.of_iso ?_ eK
  by_cases hX : IsEmpty (Limits.pullback f s : Scheme.{u})
  · exact Functor.map_isZero _ (Functor.map_isZero _
      (isZero_derivedCategory_of_isEmpty (ModuleCat.{u + 1} Λ) _ K'))
  have : Nonempty (Limits.pullback f s : Scheme.{u}) := not_isEmpty_iff.1 hX
  have := HasInvertibleExponent.of_hom (Λ := Λ) g'
  have := HasInvertibleExponent.of_hom_of_nonempty (Λ := Λ) f'
  have hK' : _root_.DerivedCategory.TStructure.t.bounded K' :=
    Functor.bounded_mapDerivedCategory_obj _ hK.1
  have : K'.IsLE 0 := Functor.isLE_mapDerivedCategory_obj _ K 0
  have hΦ : ∀ F : Sheaf (Limits.pullback f s).smallEtaleTopology (ModuleCat.{u + 1} Λ),
      ((R(f')_![ModuleCat.{u + 1} Λ]).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).IsLE (2 * e) := fun F ↦ by
    rw [_root_.DerivedCategory.isLE_iff]
    refine fun i hi ↦ isZero_homology_rightDerivedLowerShriek_singleFunctor Λ f' f' (𝟙 _)
      (Category.comp_id _) e (fun Ω' _ _ t ↦ ?_) F i (by lia)
    rw [IsHomeomorph.topologicalKrullDim_eq _
      (pullbackLeftPullbackSndIso f s t).hom.homeomorph.isHomeomorph]
    exact he Ω' (t ≫ s)
  have := _root_.DerivedCategory.isLE_obj_of_isLE (R(f')_![ModuleCat.{u + 1} Λ]) (2 * e) hΦ
    K' hK' 0
  exact (_root_.DerivedCategory.isLE_iff _ _).1 this q (by lia)

end Finiteness

end Etale

end AlgebraicGeometry
