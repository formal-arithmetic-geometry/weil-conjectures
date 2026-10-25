/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.PowIntersection
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.NumberTheory.Padics.IntegersToAlgCl
public import WeilConjectures.SixFunctors.Etale.Derived.RationalStage
public import WeilConjectures.TraceFormula.CurveLocal.FrobeniusModel
public import WeilConjectures.TraceFormula.CurveLocal.RestrictionZero
public import WeilConjectures.TraceFormula.CurveSupportedPairing
public import WeilConjectures.TraceFormula.PointFiberFunctor

/-!

# From finite coefficients to `ℚ̄_ℓ`: the supported restriction is zero for Frobenius

Blueprint `sk-lem-tf-curve-restriction-zero` is proved on the classical étale models with finite
`ℓ`-primary coefficients
(`AlgebraicGeometry.Etale.CurveLocalModel.sectionsWithSupportRestriction_eq_zero`,
packaged for all models and coefficient rings as
`AlgebraicGeometry.Etale.CurveLocalModel.restrictionZero`). Its last step, as in the blueprint
proof ("the comparison theorems transport this identity back to the proétale formulation"),
transports this vanishing to the `ℚ̄_ℓ`-coefficient pro-étale supported restriction `ρ_P` of
`Correspondence.FixedLocus.supportedRestriction`
(`Correspondence.upperStar_map_supportedRestriction_frobeniusGraph_eq_zero_of_restrictionZero`).
This is the passage `ℚ̄_ℓ = colim_E E`, `E = 𝒪_E[1/ℓ]`, `𝒪_E = lim_n 𝒪_E / ℓ^n`:

* `K` descends to a finite subextension `E` and has an integral model `K₀` over `𝒪_E`
  (`ProEtale.exists_padicAlgCl_iso_integralModel`, blueprints `sk-thm-sfb-qlbar-two-colimit` and
  `sk-lem-tf-rational-model`, the latter proved in `WeilConjectures.TraceFormula.RationalModel`);
* the comparison theorems of the six-functor formalism identify the stalk of `ρ_P` at the fixed
  point with `ℚ̄_ℓ ⊗ᴸ_{𝒪_E} f₀` for a morphism `f₀` of perfect `𝒪_E`-complexes whose reductions
  modulo `ℓ^n` are the classical supported restrictions `ρ_{a,b}` on the strictly local model at
  the fixed point (`AlgebraicGeometry.Etale.CurveLocalModel.ofModelFrobenius`) with finite
  coefficients (`Correspondence.HasIntegralReductionModel`). This identification is stated as a
  compatibility required from the six-functor formalism
  (`Correspondence.exists_integralModel_reduction_supportedRestriction`);
* the reductions vanish by the classical computation, so `f₀` is divisible by every `ℓ^n`, hence
  zero by the Krull intersection theorem, and so is the stalk of `ρ_P`, the fibre functor of the
  point being faithful (`Correspondence.eq_zero_of_hasIntegralReductionModel`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.Etale.CurveLocalModel

variable (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ)

/-- **The supported restriction is zero for Frobenius, for all models and coefficient rings**
(blueprint `sk-lem-tf-curve-restriction-zero`): for every strictly local model of a smooth curve
over `k`, every finite commutative `ℓ`-primary ring `Λ`, all `L, K ∈ D^b_{ctf}(X, Λ)` with
`K_ȳ = 0` and `P = (L ⊠ K)|_T`, the supported restriction `ρ_{a,b}` is zero. -/
def RestrictionZero : Prop :=
  ∀ (M : CurveLocalModel k) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ],
    (∃ n : ℕ, (ℓ : Λ) ^ n = 0) →
    ∀ (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      DerivedCategory.boundedConstructibleFiniteTor Λ M.X L →
      DerivedCategory.boundedConstructibleFiniteTor Λ M.X K →
      IsZero ((L((M.y)^*[ModuleCat.{u + 1} Λ])).obj K) →
      ∀ (P : DerivedCategory.Plus (Sheaf M.T.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        (P.obj ≅ (L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
          (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)) →
        sectionsWithSupportRestriction (ModuleCat.{u + 1} Λ) M.b M.a M.yB
          M.openComplement_yB_le P = 0

variable {k ℓ}

/-- `RestrictionZero` holds for every prime `ℓ` invertible in `k` (blueprint
`sk-lem-tf-curve-restriction-zero`). -/
theorem restrictionZero [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) : RestrictionZero k ℓ :=
  fun M _ _ _ hΛ L K hL hK hKy P eP ↦
    M.sectionsWithSupportRestriction_eq_zero ℓ hℓ hΛ L K hL hK hKy P eP


variable (ℓ) in
/-- **Classical coefficient data on a strictly local model**: a finite `ℓ`-primary coefficient
ring `Λ`, complexes `L, K ∈ D^b_{ctf}(X, Λ)` with `K_ȳ = 0`, and a model `P` of `(L ⊠ K)|_T` on
the strict localization, as in `RestrictionZero`. -/
structure CoefficientDatum (M : CurveLocalModel k) where
  /-- The coefficient ring. -/
  Λ : Type (u + 1)
  [commRing : CommRing Λ]
  [finite : Finite Λ]
  isNilpotent_natCast : ∃ n : ℕ, (ℓ : Λ) ^ n = 0
  /-- The first factor. -/
  L : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  /-- The second factor, with vanishing stalk at `y`. -/
  K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  boundedConstructibleFiniteTor_L : DerivedCategory.boundedConstructibleFiniteTor Λ M.X L
  boundedConstructibleFiniteTor_K : DerivedCategory.boundedConstructibleFiniteTor Λ M.X K
  isZero_upperStar_y : IsZero ((L((M.y)^*[ModuleCat.{u + 1} Λ])).obj K)
  /-- A model of `(L ⊠ K)|_T`. -/
  P : DerivedCategory.Plus (Sheaf M.T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  /-- The identification `P ≅ (L ⊠ K)|_T`. -/
  iso : P.obj ≅ (L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
    (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)

attribute [instance] CoefficientDatum.commRing CoefficientDatum.finite

namespace CoefficientDatum

variable {M : CurveLocalModel k} (D : M.CoefficientDatum ℓ)

/-- The sections with support `RΓ_a(T, P)` on the graph. -/
noncomputable abbrev source : DerivedCategory (ModuleCat.{u + 1} D.Λ) :=
  ((sectionsWithSupportTriangle (ModuleCat.{u + 1} D.Λ) M.a).obj D.P).obj₁

/-- The local cohomology `RΓ_y(B, b^* P)` on the diagonal. -/
noncomputable abbrev target : DerivedCategory (ModuleCat.{u + 1} D.Λ) :=
  ((sectionsWithSupportTriangle (ModuleCat.{u + 1} D.Λ) M.yB).obj
    ((Functor.mapDerivedCategoryPlus (M.b)^*[ModuleCat.{u + 1} D.Λ]).obj D.P)).obj₁

/-- The classical supported restriction `ρ_{a,b} : RΓ_a(T, P) ⟶ RΓ_y(B, b^* P)` of the datum. -/
noncomputable abbrev supportedRestriction : D.source ⟶ D.target :=
  sectionsWithSupportRestriction (ModuleCat.{u + 1} D.Λ) M.b M.a M.yB M.openComplement_yB_le D.P

/-- The classical supported restriction of a coefficient datum vanishes when `RestrictionZero`
holds. -/
lemma supportedRestriction_eq_zero (h : RestrictionZero k ℓ) : D.supportedRestriction = 0 :=
  h M D.Λ D.isNilpotent_natCast D.L D.K D.boundedConstructibleFiniteTor_L
    D.boundedConstructibleFiniteTor_K D.isZero_upperStar_y D.P D.iso

end CoefficientDatum

end AlgebraicGeometry.Etale.CurveLocalModel

namespace CategoryTheory

/-- In an `R`-linear category, composing with `(ℓ : ℤ)^n • 𝟙` is the multiplication by the image
`(ℓ : R)^n`. -/
lemma Linear.comp_zsmul_natCast_pow_id {R : Type*} [CommRing R] {C : Type*} [Category* C]
    [Preadditive C] [Linear R C] {X Y : C} (g : X ⟶ Y) (ℓ n : ℕ) :
    g ≫ (((ℓ : ℤ) ^ n) • 𝟙 Y) = ((ℓ : R) ^ n) • g := by
  rw [Preadditive.comp_zsmul, Category.comp_id, ← Int.cast_smul_eq_zsmul R]
  push_cast
  rfl

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

/-- A prime `ℓ` different from the characteristic of `k` is invertible in `k`. -/
lemma natCast_ne_zero_of_ringChar_ne : (ℓ : k) ≠ 0 := by
  intro h
  have h₁ := (ringChar.spec k ℓ).1 h
  have hp : (ringChar k).Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  exact (Fact.out : ringChar k ≠ ℓ) ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 h₁)

namespace Correspondence

open PadicAlgCl

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀} {Φ : X ⟶ X}

/-- The fixed point `x = ι(z)` of `Φ_m` underlying a point `z` of the fixed locus of the graph
correspondence `(𝟙, Φ_m)`. -/
lemma comp_ι_comp_frobeniusIterate {m : ℕ}
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (z : RationalPoint F.F) :
    (z ≫ F.ι) ≫ frobeniusIterate Φ m = z ≫ F.ι := by
  rw [Category.assoc]
  exact (congrArg (z ≫ ·) F.w).symm.trans (congrArg (z ≫ ·) (Category.comp_id F.ι))

/-- The classical strictly local model (`AlgebraicGeometry.Etale.CurveLocalModel.ofModelFrobenius`)
at the fixed point `x = ι(z)` of `Φ_m` underlying a point `z` of the fixed locus of `(𝟙, Φ_m)`. -/
noncomputable abbrev frobeniusLocalModel [IsAlgClosed k] [SmoothOfRelativeDimension 1 X.hom]
    (hΦ : IsModelFrobenius Φ f₀ p) {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (z : RationalPoint F.F) :
    Etale.CurveLocalModel k :=
  Etale.CurveLocalModel.ofModelFrobenius hΦ hm (z ≫ F.ι) (comp_ι_comp_frobeniusIterate v F z)

variable (ℓ) in
/-- A morphism `ρ` of the point category `Dᵇc(s)⟦ℚ̄_ℓ⟧` *has an integral model reducing to
classical supported restrictions on the strictly local model `M`* if there is a morphism
`f₀ : A₀ ⟶ B₀` of perfect `𝒪_E`-complexes with `Fib_s(ρ) ≅ ℚ̄_ℓ ⊗ᴸ f₀` (as arrows) such that for
every `n` there are classical coefficient data on `M` (with coefficients `Λ`, a ring under
`𝒪_E`) for which `f₀` followed by the reduction `B₀ ⟶ B₀ / ℓ^n` (part of a distinguished triangle
on the multiplication by `ℓ^n`) is the reduction `A₀ ⟶ RΓ_a(T, P)` followed by the classical
supported restriction `ρ_{a,b}`, read in `D(𝒪_E)`. -/
def HasIntegralReductionModel [IsAlgClosed k] (M : Etale.CurveLocalModel k)
    (E : FiniteIntermediateField ℓ) {A B : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (ρ : A ⟶ B) : Prop :=
  ∃ (A₀ B₀ : DerivedCategory (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers ℓ E.1))))
    (f₀ : A₀ ⟶ B₀),
    A₀.IsPerfect ∧ B₀.IsPerfect ∧
    Nonempty (Arrow.mk ((pointFiberFunctor ℓ k).map ρ) ≅
      Arrow.mk ((ModuleCat.derivedExtendScalars (PadicAlgCl.integersToULift.{u} ℓ E.1)
        (PadicAlgCl.flat_integersToULift ℓ E.1)).map f₀)) ∧
    ∀ n : ℕ, ∃ (D : M.CoefficientDatum ℓ)
      (φ : Shrink.{u + 1} (PadicAlgCl.integers ℓ E.1) →+* D.Λ)
      (πA : A₀ ⟶ (ModuleCat.restrictScalars φ).mapDerivedCategory.obj D.source)
      (πB : B₀ ⟶ (ModuleCat.restrictScalars φ).mapDerivedCategory.obj D.target)
      (δ : (ModuleCat.restrictScalars φ).mapDerivedCategory.obj D.target ⟶ B₀⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk (((ℓ : ℤ) ^ n) • 𝟙 B₀) πB δ ∈ distTriang _ ∧
      πA ≫ (ModuleCat.restrictScalars φ).mapDerivedCategory.map D.supportedRestriction =
        f₀ ≫ πB

/-- **Integral vanishing criterion**: if `RestrictionZero` holds, a morphism of the point category
with an integral model reducing to classical supported restrictions vanishes. The reductions of
the integral model `f₀` modulo every `ℓ^n` vanish, so `f₀` is divisible by every `ℓ^n`, hence
zero by the Krull intersection theorem (`DerivedCategory.IsPerfect.eq_zero_of_forall_eq_pow_smul`);
the fibre functor of the point is faithful. -/
lemma eq_zero_of_hasIntegralReductionModel [IsAlgClosed k] {M : Etale.CurveLocalModel k}
    {E : FiniteIntermediateField ℓ} {A B : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {ρ : A ⟶ B} (H : HasIntegralReductionModel ℓ M E ρ)
    (hRZ : Etale.CurveLocalModel.RestrictionZero k ℓ) : ρ = 0 := by
  obtain ⟨A₀, B₀, f₀, hA, hB, ⟨eArr⟩, hred⟩ := H
  have hf₀ : f₀ = 0 := by
    refine DerivedCategory.IsPerfect.eq_zero_of_forall_eq_pow_smul hA hB
      (PadicAlgCl.natCast_mem_maximalIdeal_shrink ℓ E.1) fun n ↦ ?_
    have hn := hred n
    obtain ⟨D, hn⟩ := hn
    obtain ⟨φ, hn⟩ := hn
    obtain ⟨πA, πB, δ, hn⟩ := hn
    obtain ⟨hT, hcomm⟩ := hn
    have h0 := D.supportedRestriction_eq_zero hRZ
    simp only [h0, Functor.map_zero, Limits.comp_zero] at hcomm
    have hex := Pretriangulated.Triangle.coyoneda_exact₂ _ hT f₀ hcomm.symm
    refine ⟨hex.choose, hex.choose_spec.trans ?_⟩
    exact Linear.comp_zsmul_natCast_pow_id hex.choose ℓ n
  have : (pointFiberFunctor ℓ k).Additive := by unfold pointFiberFunctor; infer_instance
  have : (pointFiberFunctor ℓ k).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  apply (bijective_pointFiberFunctor_map ℓ k _ _).1
  have hw := eArr.hom.w
  simp only [Arrow.mk_hom, hf₀, Functor.map_zero, Limits.comp_zero] at hw
  simp only [Functor.map_zero]
  have hr : eArr.hom.right ≫ eArr.inv.right = 𝟙 _ := by
    rw [← Arrow.comp_right, Iso.hom_inv_id, Arrow.id_right]
  calc (pointFiberFunctor ℓ k).map ρ
      = ((pointFiberFunctor ℓ k).map ρ ≫ eArr.hom.right) ≫ eArr.inv.right := by
        rw [Category.assoc, hr]; exact (Category.comp_id _).symm
    _ = 0 := by rw [← hw, Limits.zero_comp]

/-- Compatibility required from the comparison theorems of the six-functor formalism
(`sk-thm-sf-package`: for finite coefficients the six operations, supports and strict
localizations may be read on the small étale site; `sk-prop-scalar-six`: the coefficient changes
`𝒪_E ⟶ ℚ̄_ℓ` and `𝒪_E ⟶ 𝒪_E / ℓ^n` commute with the six operations, their units, counits and
exchange maps; `sk-prop-sf-comparison`: comparison with the étale site) and from the description
of the supported restriction on the strict localization (blueprint
`det-tf-supported-restriction`) (to be proved there): **the stalk of the supported restriction
has an integral model whose reductions are the classical supported restrictions**.

In the situation of
`upperStar_map_supportedRestriction_frobeniusGraph_eq_zero_of_restrictionZero`, let `K₀` be a
bounded constructible `𝒪_E`-complex with `ℚ̄_ℓ ⊗ᴸ K₀ ≅ K`. Then there is a morphism
`f₀ : A₀ ⟶ B₀` of perfect `𝒪_E`-complexes (the integral stalk at `z` of `ρ_{P₀}`,
`P₀ = K₀ ⊠ D_X K₀`, read on the geometric point) such that

* `ℚ̄_ℓ ⊗ᴸ f₀` is the stalk at `z` of `ρ_P`, read through the fibre functor `Fib_s` of the point;
* for every `n`, with finite coefficients `Λ = 𝒪_E / ℓ^n`, `B₀ / ℓ^n` (the cone of `ℓ^n` on `B₀`)
  is the target of the classical supported restriction `ρ_{a,b}` on the strictly local model at
  `x = ι(z)` (`AlgebraicGeometry.Etale.CurveLocalModel.ofModelFrobenius`) for the reductions
  `L = (D_X K₀)/ℓ^n` and `K' = K₀'/ℓ^n` of the two factors (in the transposed order of the
  model, `K₀'` an integral model of `K` with `(K₀')_x = 0`), and `f₀` followed by the reduction
  `B₀ ⟶ B₀ / ℓ^n` is the reduction `A₀ ⟶ A₀ / ℓ^n` followed by `ρ_{a,b}`, all read in `D(𝒪_E)`. -/
theorem exists_integralModel_reduction_supportedRestriction
    [IsAlgClosed k] [SmoothOfRelativeDimension 1 X.hom] [LocallyOfFiniteType f₀]
    (hΦ : IsModelFrobenius Φ f₀ p) {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (z : RationalPoint F.F)
    (hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (z ≫ F.ι)).obj K))
    (E : FiniteIntermediateField ℓ)
    (K₀ : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
    (e : (constructibleToPadicAlgCl X.left ℓ E).obj
      ((boundedConstructibleExtendScalars X.left ℓ E).obj K₀) ≅ K) :
    HasIntegralReductionModel ℓ (frobeniusLocalModel hΦ hm v F z) E
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).map
        (F.supportedRestriction (externalProduct ℓ K (verdierDual ℓ (toPoint X) K)))) :=
  sorry

/-- **Transport of the vanishing of the supported restriction from finite coefficients to an
integral model**: in the situation of
`upperStar_map_supportedRestriction_frobeniusGraph_eq_zero_of_restrictionZero`, suppose that
`K ≅ ℚ̄_ℓ ⊗ᴸ_{𝒪_E} K₀` for a finite subextension `E` and a bounded constructible `𝒪_E`-complex
`K₀`. If the supported restriction on the classical strictly local models vanishes for all finite
`ℓ`-primary coefficient rings (`AlgebraicGeometry.Etale.CurveLocalModel.RestrictionZero`), then
the stalk at `z` of the supported restriction `ρ_P`, `P = K ⊠ D_X K`, vanishes.

The stalk of `ρ_P` is `ℚ̄_ℓ ⊗ᴸ f₀` for a morphism `f₀` of perfect `𝒪_E`-complexes whose reductions
modulo `ℓ^n` are classical supported restrictions
(`exists_integralModel_reduction_supportedRestriction`). These vanish, so `f₀` is divisible by
every `ℓ^n`, hence zero by the Krull intersection theorem
(`DerivedCategory.IsPerfect.eq_zero_of_forall_eq_pow_smul`); the fibre functor of the point is
faithful. -/
theorem upperStar_map_supportedRestriction_frobeniusGraph_eq_zero_of_integralModel
    [IsAlgClosed k] [SmoothOfRelativeDimension 1 X.hom] [LocallyOfFiniteType f₀]
    (hΦ : IsModelFrobenius Φ f₀ p) {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (z : RationalPoint F.F)
    (hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (z ≫ F.ι)).obj K))
    (E : FiniteIntermediateField ℓ)
    (K₀ : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
    (e : (constructibleToPadicAlgCl X.left ℓ E).obj
      ((boundedConstructibleExtendScalars X.left ℓ E).obj K₀) ≅ K)
    (hRZ : Etale.CurveLocalModel.RestrictionZero k ℓ) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).map
      (F.supportedRestriction (externalProduct ℓ K (verdierDual ℓ (toPoint X) K))) = 0 :=
  eq_zero_of_hasIntegralReductionModel
    (exists_integralModel_reduction_supportedRestriction hΦ hm v F z hK E K₀ e) hRZ


/-- **Transport of the vanishing of the supported restriction from finite coefficients to
`ℚ̄_ℓ`** (blueprints `sk-lem-tf-curve-restriction-zero`, last step, and
`sk-lem-tf-rational-model`). If the supported restriction on the classical strictly local models
vanishes for all finite `ℓ`-primary coefficient rings
(`AlgebraicGeometry.Etale.CurveLocalModel.RestrictionZero`), then, for `X` smooth of relative
dimension one over the algebraically closed field `k` with the model Frobenius `Φ` of a model over
a finite field, `m ≥ 1`, `v : LΦ_m^* K ⟶ K`, and a point `z` of the fixed locus of `(𝟙, Φ_m)`
whose image `x` in `X` has `K_x = 0`, the stalk at `z` of the `ℚ̄_ℓ`-coefficient supported
restriction `ρ_P`, `P = K ⊠ D_X K`, vanishes.

This is the passage `ℚ̄_ℓ = colim_E E`, `E = 𝒪_E[1/ℓ]`, `𝒪_E = lim_n 𝒪_E / π_E^n`: `K` descends
to a finite subextension `E` and has an integral model `K₀` over `𝒪_E`
(`ProEtale.exists_padicAlgCl_iso_integralModel`, blueprints `sk-thm-sfb-qlbar-two-colimit` and
`sk-lem-tf-rational-model`), and the comparison theorems transport the vanishing from the
reductions of `K₀` (`upperStar_map_supportedRestriction_frobeniusGraph_eq_zero_of_integralModel`).
-/
theorem upperStar_map_supportedRestriction_frobeniusGraph_eq_zero_of_restrictionZero
    [IsAlgClosed k] [SmoothOfRelativeDimension 1 X.hom] [LocallyOfFiniteType f₀]
    (hΦ : IsModelFrobenius Φ f₀ p) {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (z : RationalPoint F.F)
    (hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (z ≫ F.ι)).obj K))
    (h : Etale.CurveLocalModel.RestrictionZero k ℓ) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).map
      (F.supportedRestriction (externalProduct ℓ K (verdierDual ℓ (toPoint X) K))) = 0 := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  have hK₀ := ProEtale.exists_padicAlgCl_iso_integralModel X.left ℓ K
  exact upperStar_map_supportedRestriction_frobeniusGraph_eq_zero_of_integralModel hΦ hm v F z hK
    hK₀.choose hK₀.choose_spec.choose hK₀.choose_spec.choose_spec.some h

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
