/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Rational

/-!
# Coherence of rational and `ℚ̄_ℓ` purity

The `E`- and `ℚ̄_ℓ`-purity isomorphisms are transported from the integral stage along exact
functors: the rationalization `- ⊗ᴸ_{𝒪_E} E`, the scalar extensions `- ⊗_E E'` along finite
extensions `E ⊆ E'` and the functors `D(-, E) ⥤ D(-, ℚ̄_ℓ)` into the colimit. This file records
the formal properties of these transports used by the blueprint.

## Main statements

- `AlgebraicGeometry.Etale.map_hom_comp_eq_of_retract`: purity isomorphisms natural in the
  object preserve idempotent summands.
- `AlgebraicGeometry.Etale.map_map_hom_comp_eq`: the transports along coefficient extensions are
  transitive.
- `AlgebraicGeometry.Etale.isIso_map_fromIntegral_realization`: the `ℚ̄_ℓ`-stage purity
  isomorphism.
- `AlgebraicGeometry.Etale.map_smoothPurityTrace_eq_comp`: the rational transport of the smooth
  trace.
- `AlgebraicGeometry.Etale.dualizingComplex_purity_all_stages`: the dualizing complexes.

## Implementation notes

The scalar extensions between the categories `D_comp(-, E)` for different `E`, and the
`ℚ̄_ℓ`-category itself (the `2`-colimit over the finite extensions `E/ℚ_ℓ`), are not constructed
in the repository, nor is the compactly supported direct image on `D_comp(-, E)`. They are
therefore arguments of the statements, and the statements are the compatibilities that their
construction is used for.
-/

@[expose] public section

universe w u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

section Formal

variable {C D : Type*} [Category C] [Category D]

/-- Blueprint `prop-pur-rational-purity-transitivity-summands`: Transitivity and summand
preservation of rational purity

**Summands.** A purity isomorphism `Γ : F ≅ G` natural in the object (blueprint
`prop-pur-smooth-purity-naturality-cover`) preserves idempotent summands: if `K` is a retract of
`L` through `i : K ⟶ L`, `r : L ⟶ K` with `i ≫ r = 𝟙`, then `Γ_K` is the summand
`F(K) ⟶ F(L) ⟶ G(L) ⟶ G(K)` of `Γ_L`. -/
theorem map_hom_comp_eq_of_retract {F G : C ⥤ D} (Γ : F ≅ G) {K L : C} (i : K ⟶ L)
    (r : L ⟶ K) (h : i ≫ r = 𝟙 K) :
    F.map i ≫ Γ.hom.app L ≫ G.map r = Γ.hom.app K := by
  rw [Γ.hom.naturality_assoc, ← G.map_comp, h, G.map_id, Category.comp_id]

variable {D' D'' : Type*} [Category D'] [Category D'']

/-- Blueprint `prop-pur-rational-purity-transitivity-summands`: Transitivity and summand
preservation of rational purity

**Transitivity.** Let `Φ : D ⥤ D'` and `Φ' : D' ⥤ D''` be extensions of the coefficient field
(`E ⊆ E' ⊆ E''`), and let the purity isomorphisms `γ`, `γ'`, `γ''` at the three stages be
compatible with `Φ` and `Φ'` through the identifications `a, b` of their sources and targets.
Then `γ` is compatible with the composite extension `Φ ⋙ Φ'`, through the composite
identifications: transport along `E ⊆ E''` is transport along `E ⊆ E'` followed by transport
along `E' ⊆ E''`. -/
theorem map_map_hom_comp_eq (Φ : D ⥤ D') (Φ' : D' ⥤ D'') {S T : D} {S' T' : D'} {S'' T'' : D''}
    (γ : S ≅ T) (γ' : S' ≅ T') (γ'' : S'' ≅ T'') (a₁ : Φ.obj S ≅ S') (b₁ : Φ.obj T ≅ T')
    (a₂ : Φ'.obj S' ≅ S'') (b₂ : Φ'.obj T' ≅ T'')
    (h₁ : Φ.map γ.hom ≫ b₁.hom = a₁.hom ≫ γ'.hom)
    (h₂ : Φ'.map γ'.hom ≫ b₂.hom = a₂.hom ≫ γ''.hom) :
    (Φ ⋙ Φ').map γ.hom ≫ Φ'.map b₁.hom ≫ b₂.hom =
      (Φ'.map a₁.hom ≫ a₂.hom) ≫ γ''.hom := by
  rw [Functor.comp_map, ← Φ'.map_comp_assoc, h₁, Φ'.map_comp_assoc, h₂, Category.assoc]

end Formal

section Rational

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Small.{u + 1} E] {X : Scheme.{u}}

/-- Blueprint `thm-pur-rational-and-qbar-purity`: Rational and `ℚ̄_ℓ` purity

**The `ℚ̄_ℓ`-stage.** A `ℚ̄_ℓ`-object is represented by an `E`-object for a finite `E/ℚ_ℓ`, through
the functor `ι_E : D_comp(X, E) ⥤ D(X, ℚ̄_ℓ)` into the colimit; the `ℚ̄_ℓ`-purity isomorphism is
the transport of the `E`-purity isomorphism along `ι_E`. For a morphism `e` of `D_comp(X, 𝒪_E)`
between lattices which is an isomorphism (the adic purity isomorphism of
`AlgebraicGeometry.Etale.exists_iso_realization_twistShiftPullbackLevel`), its image in the
`ℚ̄_ℓ`-stage is an isomorphism; that it does not depend on `E` is
`AlgebraicGeometry.Etale.map_map_hom_comp_eq`. -/
theorem isIso_map_fromIntegral_realization {Q : Type*} [Category Q]
    (ι : DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E ⥤ Q)
    {S T : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E} (e : S ⟶ T)
    [IsIso e] :
    IsIso (ι.map ((DerivedCategoryDerivedCompleteRational.fromIntegral
      X.smallEtaleTopology l E).map e)) :=
  inferInstance

variable {Y : Scheme.{u}}

/-- Blueprint `prop-pur-rational-purity-trace-coherence`: Trace and coherence compatibilities of
rational purity

The `E`-stage operations are the transports of the integral ones along the exact functor
`ρ = - ⊗ᴸ_{𝒪_E} E` (`DerivedCategoryDerivedCompleteRational.fromIntegral`): `Rf_!^E ∘ ρ ≅ ρ ∘ Rf_!`
(`hF`) and the counit of `Rf_!^E ⊣ Rf^{!,E}` is the image of the integral counit (`hε`). Then the
`E`-smooth trace, `Rf_!^E(γ_E)` followed by the counit, is the transport of the integral smooth
trace `Tr = Rf_!(γ) ≫ ε`: rational purity commutes with the smooth trace. The coherence squares
are transported in the same way, `ρ` being a functor. -/
theorem map_smoothPurityTrace_eq_comp
    {FX : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E}
    {FXE : DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteRational Y.smallEtaleTopology l E}
    (hF : DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E ⋙ FXE ≅
      FX ⋙ DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l E)
    {S T : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E}
    {K : DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E}
    (γ : S ≅ T) (ε : FX.obj T ⟶ K)
    (εE : FXE.obj ((DerivedCategoryDerivedCompleteRational.fromIntegral
      X.smallEtaleTopology l E).obj T) ⟶
      (DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l E).obj K)
    (hε : εE = hF.hom.app T ≫
      (DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l E).map ε) :
    FXE.map ((DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E).map
        γ.hom) ≫ εE =
      hF.hom.app S ≫
        (DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l E).map
          (FX.map γ.hom ≫ ε) := by
  have h := hF.hom.naturality γ.hom
  simp only [Functor.comp_obj, Functor.comp_map] at h
  rw [hε, reassoc_of% h, Functor.map_comp]

variable [∀ n : ℕ, Finite (Shrink.{u + 1} (PadicAlgCl.integers l E) ⧸
    PadicAlgCl.maximalIdealShrink l E ^ (n + 1))]
  [∀ n : ℕ, HasTateTwist (Shrink.{u + 1} (PadicAlgCl.integers l E) ⧸
    PadicAlgCl.maximalIdealShrink l E ^ (n + 1))]

/-- Blueprint `cor-pur-adic-and-rational-smooth-dualizing-complexes`: Adic and rational smooth
dualizing complexes

Let `a : X ⟶ Spec k` be smooth separated, locally of finite type, of pure dimension `d`, and
`Λ = (Λ_n)_n` a normalized system on `Spec k` (the coefficient system `𝒪_E ⧸ 𝔪ⁿ⁺¹`). Then
* at every finite level `n`, the counit `Ra_! ω_X ⟶ Λ_n` is the smooth trace
  `RΓ_c(X, Λ_n(d)[2d]) ⟶ Λ_n` read through a purity identification `ω_X ≅ Λ_{n,X}(d)[2d]`
  (`AlgebraicGeometry.Etale.exists_counit_eq_smoothPurityTrace`), which the transports below carry
  to the adic and rational stages;
* the dualizing complex `ω_{X,𝒪_E} = Ra^! Λ` and `Λ_X(d)[2d]`, the realizations of the systems
  `S`, `T` with levels `La^* Λ_n(d)[2d]` and `Ra^! Λ_n`, are derived complete and identified by
  an isomorphism reducing to the finite-level purity isomorphisms, and its image in
  `D_comp(X, E)` is an isomorphism
  (`AlgebraicGeometry.Etale.exists_iso_fromIntegral_realization_twistShiftPullbackLevel` at
  `f = a`). -/
theorem dualizingComplex_purity_all_stages {k : Type u} [Field k]
    [∀ n : ℕ, HasTateTwist.IsNormalized (Shrink.{u + 1} (PadicAlgCl.integers l E) ⧸
      PadicAlgCl.maximalIdealShrink l E ^ (n + 1))]
    {d : ℕ} (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a]
    [SmoothOfRelativeDimension d a] [HasCompactification a]
    [∀ n : ℕ, HasInvertibleExponent (Shrink.{u + 1} (PadicAlgCl.integers l E) ⧸
      PadicAlgCl.maximalIdealShrink l E ^ (n + 1)) X]
    (K : NormalizedTower (PadicAlgCl.maximalIdealShrink l E) (Spec (.of k)))
    (S T : NormalizedTower (PadicAlgCl.maximalIdealShrink l E) X)
    (eS : ∀ n : ℕ, S.obj n ≅ twistShiftPullbackLevel d a K n)
    (eT : ∀ n : ℕ, T.obj n ≅ upperShriekLevel a K n)
    (γ : ∀ n : ℕ, twistShiftPullbackLevel d a K n ≅ upperShriekLevel a K n)
    (hγ : ∀ n : ℕ, S.map n ≫ (derivedRestrictScalars (quotientPowSuccFactor _ n) X).map
        (eS n ≪≫ γ n ≪≫ (eT n).symm).hom =
      (eS (n + 1) ≪≫ γ (n + 1) ≪≫ (eT (n + 1)).symm).hom ≫ T.map n)
    {cS : Cone S.restrict} (hcS : Pretriangulated.IsHomotopyLimit cS)
    {cT : Cone T.restrict} (hcT : Pretriangulated.IsHomotopyLimit cT) :
    (∀ n : ℕ, ∃ γn : (twistShift _ X d).obj ((L((a)^*[ModuleCat.{u + 1}
          (Shrink.{u + 1} (PadicAlgCl.integers l E) ⧸
            PadicAlgCl.maximalIdealShrink l E ^ (n + 1))])).obj (constantComplex _ _)) ≅
        (R(a)^![ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E) ⧸
          PadicAlgCl.maximalIdealShrink l E ^ (n + 1))]).obj (constantComplex _ _),
      (rightDerivedUpperShriekAdjunction _ a).counit.app (constantComplex _ _) =
        (R(a)_![_]).map γn.inv ≫ smoothPurityTrace _ d a γn) ∧
    ∃ (hS : DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E cS.pt)
      (hT : DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E cT.pt)
      (e : cS.pt ≅ cT.pt),
      (∀ n : ℕ, e.hom ≫ cT.π.app (Opposite.op n) =
        cS.π.app (Opposite.op n) ≫
          (derivedRestrictScalars (Ideal.Quotient.mk (PadicAlgCl.maximalIdealShrink l E ^ (n + 1)))
            X).map (eS n ≪≫ γ n ≪≫ (eT n).symm).hom) ∧
      IsIso ((DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E).map
        (X := ⟨cS.pt, hS⟩) (Y := ⟨cT.pt, hT⟩) (ObjectProperty.homMk e.hom)) :=
  ⟨fun _ ↦ exists_counit_eq_smoothPurityTrace _ a,
    exists_iso_fromIntegral_realization_twistShiftPullbackLevel l E d a K S T eS eT γ hγ hcS hcT⟩

/-- Blueprint `sk-thm-purity-transport`: Smooth purity over `𝒪_E`, `E` and `ℚ̄_ℓ`

Let `f : X ⟶ Y` be smooth separated of relative dimension `d`, `K = (K_n)_n` a normalized
system over `𝒪_E` on `Y`, and let the finite-coefficient purity isomorphisms `γ_{f,K_n}` be
compatible with the finite reductions (`thm-pur-finite-reduction-of-purity`,
`AlgebraicGeometry.Etale.map_smoothPurityIso_hom_comp`). Then the purity map extends to the three
remaining stages:
* over `𝒪_E`, `Lf^* K(d)[2d] ≅ Rf^! K` between the (derived complete) realizations, with
  reduction `γ_{f,K_n}` at every level;
* over `E`, its image in `D_comp(X, E)` is an isomorphism;
* over `ℚ̄_ℓ`, its image under the functor `ι : D_comp(X, E) ⥤ D(X, ℚ̄_ℓ)` into the colimit is an
  isomorphism.
The compatibilities with composition, base change, finite reduction and scalar extension and
the counit normalization are `AlgebraicGeometry.Etale.smoothPurityTrace_comp`,
`AlgebraicGeometry.Etale.smoothPurityTrace_baseChange`,
`AlgebraicGeometry.Etale.map_smoothPurityTrace`,
`AlgebraicGeometry.Etale.map_map_hom_comp_eq` and
`AlgebraicGeometry.Etale.dualizingComplex_purity_all_stages`. -/
theorem exists_iso_smoothPurity_transport (d : ℤ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (K : NormalizedTower (PadicAlgCl.maximalIdealShrink l E) Y)
    (S T : NormalizedTower (PadicAlgCl.maximalIdealShrink l E) X)
    (eS : ∀ n : ℕ, S.obj n ≅ twistShiftPullbackLevel d f K n)
    (eT : ∀ n : ℕ, T.obj n ≅ upperShriekLevel f K n)
    (γ : ∀ n : ℕ, twistShiftPullbackLevel d f K n ≅ upperShriekLevel f K n)
    (hγ : ∀ n : ℕ, S.map n ≫ (derivedRestrictScalars (quotientPowSuccFactor _ n) X).map
        (eS n ≪≫ γ n ≪≫ (eT n).symm).hom =
      (eS (n + 1) ≪≫ γ (n + 1) ≪≫ (eT (n + 1)).symm).hom ≫ T.map n)
    {cS : Cone S.restrict} (hcS : Pretriangulated.IsHomotopyLimit cS)
    {cT : Cone T.restrict} (hcT : Pretriangulated.IsHomotopyLimit cT) {Q : Type*} [Category Q]
    (ι : DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E ⥤ Q) :
    ∃ (hS : DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E cS.pt)
      (hT : DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E cT.pt)
      (e : cS.pt ≅ cT.pt),
      (∀ n : ℕ, e.hom ≫ cT.π.app (Opposite.op n) =
        cS.π.app (Opposite.op n) ≫
          (derivedRestrictScalars (Ideal.Quotient.mk (PadicAlgCl.maximalIdealShrink l E ^ (n + 1)))
            X).map (eS n ≪≫ γ n ≪≫ (eT n).symm).hom) ∧
      IsIso ((DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E).map
        (X := ⟨cS.pt, hS⟩) (Y := ⟨cT.pt, hT⟩) (ObjectProperty.homMk e.hom)) ∧
      IsIso (ι.map ((DerivedCategoryDerivedCompleteRational.fromIntegral
        X.smallEtaleTopology l E).map
        (X := ⟨cS.pt, hS⟩) (Y := ⟨cT.pt, hT⟩) (ObjectProperty.homMk e.hom))) := by
  obtain ⟨hS, hT, e, he, hE⟩ :=
    exists_iso_fromIntegral_realization_twistShiftPullbackLevel l E d f K S T eS eT γ hγ hcS hcT
  exact ⟨hS, hT, e, he, hE, inferInstance⟩

end Rational

end Etale

end AlgebraicGeometry
