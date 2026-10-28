/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.FieldStagePointers
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Uniformizer
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible

/-!
# The uniform `Ext` bound for constructible `𝒪_E`-sheaves

Blueprint `sk-lem-int-ext` (2). Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of
integers `𝒪_E`, uniformizer `ϖ` and residue field `𝔽_E`, and let `X` be a separated scheme of finite
type over a field `k` of characteristic prime to `ℓ` with `cd_ℓ(k) < ∞`. For every constructible
`𝒪_{E,X}`-module `M` there is `d` with `Ext^q(M, B) = 0` for `q > d` and every constructible `B`
(`ProEtale.hasUniformConstructibleExtBound_padicIntegersRingObj_of_hasFiniteCohomologicalDimension`).

The proof avoids derived limits:

* *Torsion targets.* By the triangle `B --ϖ--> B ⟶ B ⊗ᴸ 𝔽_E ⟶`
  (`ProEtale.exists_distinguished_regularEndCenter_derivedExtendScalars`) and the adjunction
  between derived extension and restriction of scalars along `𝒪_E ⟶ 𝔽_E`,
  `Ext^q_{𝒪_E}(M, B ⊗ᴸ 𝔽_E) = Ext^q_{𝔽_E}(M ⊗ᴸ 𝔽_E, B ⊗ᴸ 𝔽_E)`. The source is a constructible
  complex of `𝔽_E`-sheaves and the target has constructible cohomology sheaves (of étale origin) in
  degrees `[-1, 0]`, so these groups vanish for `q` large, uniformly in `B`
  (`ProEtale.DerivedCategory.exists_forall_eq_zero_of_constructibleFiniteTor`, which uses
  `cd_ℓ(k) < ∞`).
* *Inverting `ϖ`.* Hence, for `q` large, multiplication by `ϖ` is bijective on
  `V = Hom(M, B[q])`.
* *Completeness.* On the countable power of `B`, `(xₙ) ↦ (xₙ - ϖ x_{n+1})` is an isomorphism
  (`ProEtale.isIso_sub_powShift_padicIntegersCenter_of_isConstructible`); applying `Hom(M, -[q])`,
  which commutes with products, `(xₙ) ↦ (xₙ - ϖ x_{n+1})` is injective on `V^ℕ`. For `v ∈ V` the
  sequence `xₙ = ϖ^{-n} v` lies in its kernel, so `v = 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory

/-- **Completeness kills `e`-divisible morphisms**: if `1 - powShift e` is invertible on the
countable power `∏ₙ A` and postcomposition with `e : A ⟶ A` is bijective on `M ⟶ A`, then every
morphism `M ⟶ A` vanishes. For `v : M ⟶ A`, the morphisms `xₙ = e^{-n} v` assemble into a
morphism `M ⟶ ∏ₙ A` killed by `1 - powShift e`. -/
lemma Limits.eq_zero_of_isIso_sub_powShift_of_bijective {C : Type*} [Category* C]
    [Preadditive C] {M A : C} [HasProduct fun _ : ℕ ↦ A] (e : A ⟶ A)
    [IsIso (𝟙 _ - powShift e)] (he : Function.Bijective fun f : M ⟶ A ↦ f ≫ e) (f : M ⟶ A) :
    f = 0 := by
  let x (n : ℕ) : M ⟶ A := (Equiv.ofBijective _ he).symm^[n] f
  have hx (n : ℕ) : x (n + 1) ≫ e = x n := by
    simp only [x, Function.iterate_succ_apply']
    exact (Equiv.ofBijective _ he).apply_symm_apply _
  have h : Pi.lift x = 0 := by
    rw [← cancel_mono (𝟙 _ - powShift e), zero_comp]
    refine Pi.hom_ext _ _ fun n ↦ ?_
    simp [hx]
  have h₀ := Pi.lift_π x 0
  rw [h, zero_comp] at h₀
  exact h₀.symm

section Triangulated

open Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

/-- In a distinguished triangle `T`, postcomposition with `T.mor₁` is bijective on morphisms out
of an object `M` without nonzero morphisms to `T.obj₃` and to `T.obj₃⟦-1⟧`. -/
lemma Pretriangulated.Triangle.bijective_comp_mor₁ {T : Triangle C} (hT : T ∈ distTriang C) {M : C}
    (h₃ : ∀ g : M ⟶ T.obj₃, g = 0) (h₃' : ∀ g : M ⟶ T.obj₃⟦(-1 : ℤ)⟧, g = 0) :
    Function.Bijective fun f : M ⟶ T.obj₁ ↦ f ≫ T.mor₁ := by
  refine ⟨fun f₁ f₂ hf ↦ ?_, fun g ↦ ?_⟩
  · rw [← sub_eq_zero]
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hT) (f₁ - f₂)
      (by simpa [sub_eq_zero] using hf)
    rw [hg, h₃' g, zero_comp]
  · obtain ⟨f, hf⟩ := Triangle.coyoneda_exact₂ _ hT g (h₃ _)
    exact ⟨f, hf.symm⟩

end Triangulated

/-- A morphism `X ⟶ Y⟦-n⟧` vanishes if all morphisms `X⟦n⟧ ⟶ Y` do. -/
lemma eq_zero_of_forall_shift_eq_zero {C : Type*} [Category* C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] {X Y : C} {n : ℤ} (h : ∀ g : X⟦n⟧ ⟶ Y, g = 0)
    (g : X ⟶ Y⟦-n⟧) : g = 0 := by
  refine (shiftFunctor C n).map_injective ?_
  rw [Functor.map_zero,
    ← cancel_mono ((shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)).hom.app Y), zero_comp]
  exact h _

/-- A morphism `X⟦n⟧ ⟶ Y` vanishes if all morphisms `X ⟶ Y⟦-n⟧` do. -/
lemma eq_zero_of_forall_eq_zero_shift {C : Type*} [Category* C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] {X Y : C} {n : ℤ} (h : ∀ g : X ⟶ Y⟦-n⟧, g = 0)
    (g : X⟦n⟧ ⟶ Y) : g = 0 := by
  refine (shiftFunctor C (-n)).map_injective ?_
  rw [Functor.map_zero,
    ← cancel_epi ((shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).inv.app X), comp_zero]
  exact h _

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

section Reduction

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}

/-- The derived extension of scalars along `𝒪_{E,X} ⟶ 𝔽_{E,X}` preserves complexes concentrated
in degrees `≤ n`: by the reduction triangle `K --ϖ--> K ⟶ K ⊗ᴸ 𝔽_E ⟶ K[1]`, the restriction of
scalars of `K ⊗ᴸ 𝔽_E` is an extension of `K[1]` by `K`, and restriction of scalars is faithful
and exact. -/
lemma isLE_leftDerivedFunctor_extendScalars_residueField
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (n : ℤ) [K.IsLE n] :
    ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K).IsLE n := by
  obtain ⟨ϖ, hϖ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E.1
  rw [Ideal.submodule_span_eq] at hϖ
  obtain ⟨g, h, hT⟩ := Mod.exists_distinguished_regularEndCenter_derivedExtendScalars
    (padicIntegersRegularEnd_hom_comp_residueField X ℓ E ϖ
      (hϖ ▸ Ideal.mem_span_singleton_self ϖ)) (shortExact_padicIntegersRegularEnd X ℓ E ϖ hϖ) K
  have : DerivedCategory.TStructure.t.IsLE (K⟦(1 : ℤ)⟧) n :=
    have := DerivedCategory.TStructure.t.isLE_shift K n 1 (n - 1) (add_sub_cancel 1 n)
    DerivedCategory.TStructure.t.isLE_of_le _ (n - 1) n (sub_le_self n zero_le_one)
  have h₂ := DerivedCategory.TStructure.t.isLE₂ _ (rot_of_distTriang _ hT) n
    (inferInstanceAs (DerivedCategory.TStructure.t.IsLE K n)) this
  exact (DerivedCategory.isLE_iff _ n).2 fun i hi ↦
    (Mod.comap (padicIntegersToResidueField X ℓ E)
      ).isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      ((DerivedCategory.isLE_iff _ n).1 h₂ i hi)

/-- The first derived reduction preserves complexes concentrated in degrees `≤ n`. -/
lemma isLE_derivedReduction_obj
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (n : ℤ) [K.IsLE n] :
    ((derivedReduction X ℓ E).obj K).IsLE n :=
  have := isLE_leftDerivedFunctor_extendScalars_residueField K n
  (residueFieldModuleSheaf X ℓ E).isLE_mapDerivedCategory_obj _ n

variable (X ℓ E) in
/-- The residue field `𝔽_E`, lifted to the universe `u + 1`, is a field. -/
@[implicit_reducible]
noncomputable def ResidueFieldCoeff.field : Field (ResidueFieldCoeff.{u} ℓ E) :=
  inferInstanceAs (Field (ULift.{u + 1} (integersResidueField ℓ E.1)))

/-- On a noetherian scheme, the first derived reduction of a bounded constructible
`𝒪_E`-complex is bounded constructible (of étale origin) of finite Tor amplitude, the
coefficients `𝔽_E` being a field. -/
lemma constructibleFiniteTor_derivedReduction_obj [IsNoetherian X]
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) X
      ((derivedReduction X ℓ E).obj K) := by
  let := ResidueFieldCoeff.field ℓ E
  have : Finite (ResidueFieldCoeff.{u} ℓ E) :=
    inferInstanceAs (Finite (ULift.{u + 1} (integersResidueField ℓ E.1)))
  obtain ⟨K', hK', ⟨e⟩⟩ := boundedConstructible_derivedReduction_obj X ℓ E K hK
  exact (DerivedCategory.constructibleFiniteTor _ X).prop_of_iso e
    (DerivedCategory.constructibleFiniteTor_mapDerivedCategory _ ⟨hK',
      Etale.DerivedCategory.finiteTorAmplitude_of_boundedConstructible_of_field _ X hK'⟩)

end Reduction

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) {k : Type u} [Field k]
  [Fact (ringChar k ≠ ℓ)]

/-- If `ℓ ≠ char k`, the exponent `ℓ` of the residue field `𝔽_E` is invertible on every
`k`-scheme. -/
lemma hasInvertibleExponent_residueFieldCoeff {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) :
    HasInvertibleExponent (ResidueFieldCoeff.{u} ℓ E) X := by
  have hℓ : (ℓ : k) ≠ 0 := fun h ↦
    ((Fact.out : ℓ.Prime).eq_one_or_self_of_dvd _ ((ringChar.spec k ℓ).1 h)).elim
      CharP.ringChar_ne_one (Fact.out : ringChar k ≠ ℓ)
  have : HasInvertibleExponent (ResidueFieldCoeff.{u} ℓ E) (Spec (.of k)) :=
    ⟨ℓ, (Fact.out : ℓ.Prime).pos, natCast_eq_zero_residueFieldCoeff ℓ E,
      by simpa using (Ne.isUnit hℓ).map (Scheme.ΓSpecIso (.of k)).inv.hom⟩
  exact .of_hom aX

/-- **Torsion targets**: for a separated finite-type scheme `X` over a field `k` with
`ℓ ≠ char k` and `cd_ℓ(k) < ∞`, and a bounded constructible `𝒪_E`-complex `P`, there is `d` with
`Hom(P, (K ⊗ᴸ 𝔽_E)[q]) = 0` for `q ≥ d` and every bounded constructible `K` concentrated in
degrees `≤ 0`, where `K ⊗ᴸ 𝔽_E` is regarded as an `𝒪_E`-complex. By adjunction these are the
morphisms `P ⊗ᴸ 𝔽_E ⟶ (K ⊗ᴸ 𝔽_E)[q]` of complexes of `𝔽_E`-sheaves, which vanish for `q` large
uniformly in `K` (`ProEtale.DerivedCategory.exists_forall_eq_zero_of_constructibleFiniteTor`). -/
theorem exists_forall_eq_zero_shift_comap_derivedExtendScalars_residueField {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [QuasiSeparated aX]
    [IsNoetherian X]
    (hk : Etale.HasFiniteCohomologicalDimension (ResidueFieldCoeff.{u} ℓ E) (Spec (.of k)))
    (P : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (hP : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) P) :
    ∃ d : ℤ, ∀ K, boundedConstructible
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) K → K.IsLE 0 →
      ∀ q ≥ d, ∀ f : P ⟶ ((Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory.obj
        ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K))⟦q⟧,
        f = 0 := by
  have : Finite (ResidueFieldCoeff.{u} ℓ E) :=
    inferInstanceAs (Finite (ULift.{u + 1} (integersResidueField ℓ E.1)))
  have := hasInvertibleExponent_residueFieldCoeff ℓ E aX
  have hC := constructibleFiniteTor_derivedReduction_obj P hP
  sorry
  obtain ⟨N, hN⟩ := DerivedCategory.exists_forall_eq_zero_of_constructibleFiniteTor hk aX hC
  refine ⟨-N, fun K hK hK₀ q hq f ↦ ?_⟩
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction (padicIntegersToResidueField X ℓ E)
  let F := (residueFieldModuleSheaf X ℓ E).mapDerivedCategory
  sorry

/-- Blueprint `sk-lem-int-ext` (2): for a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a separated
finite-type `k`-scheme `X`, with `ℓ ≠ char k` and `cd_ℓ(k) < ∞`, every constructible
`𝒪_{E,X}`-module `M` admits `d` with `Ext^q(M, B) = 0` for `q > d` and all constructible `B`. -/
theorem hasUniformConstructibleExtBound_padicIntegersRingObj_of_hasFiniteCohomologicalDimension
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aX]
    (hk : Etale.HasFiniteCohomologicalDimension (ResidueFieldCoeff.{u} ℓ E) (Spec (.of k))) :
    HasUniformConstructibleExtBound
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) X) :=
  sorry

end AlgebraicGeometry.ProEtale
