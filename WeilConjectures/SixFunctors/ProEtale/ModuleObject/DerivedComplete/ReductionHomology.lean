/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Uniformizer
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComapQuotient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ProjectiveTensorUnitCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ConstructibleReading
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-!
# The action of a uniformizer on the cohomology sheaves of an `𝒪_E`-complex

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, uniformizer `ϖ` and
residue field `𝔽_E`, and let `K` be a complex of `𝒪_{E,X}`-module objects on `X_proét`. The
reduction triangle `K --ϖ--> K ⟶ K₁ ⟶ K[1]`, where `K₁ = 𝔽_{E,X} ⊗ᴸ K` is regarded as a complex of
`𝒪_{E,X}`-modules, gives exact sequences
`0 ⟶ coker (ϖ on Hᵠ K) ⟶ Hᵠ K₁ ⟶ ker (ϖ on Hᵠ⁺¹ K) ⟶ 0`. This file records the consequences of
these sequences used in the integral criterion for bounded constructibility.

## Main results

* `ProEtale.nonempty_cokernel_padicIntegersCenter_homology_iso`: if `Hᵠ⁺¹ K = 0`, the cokernel of
  `ϖ` on `Hᵠ K` is `Hᵠ K₁`.
* `ProEtale.exists_epi_kernel_padicIntegersCenter_homology`: the kernel of `ϖ` on `Hᵠ K` is a
  quotient of `Hᵠ⁻¹ K₁`.
* `ProEtale.epi_padicIntegersCenter_homology_of_lt` and its variants: if `K₁` has cohomology in
  degrees `[a, b]`, then `ϖ` is surjective on `Hᵠ K` for `q ∉ [a, b]` and injective on `Hᵠ K`
  for `q ∉ [a + 1, b + 1]`.
* `ProEtale.boundedConstructible_comap_padicIntegersToResidueField`: restriction of scalars along
  `𝒪_{E,X} ⟶ 𝔽_{E,X}` preserves bounded constructible complexes; in particular `K₁` is bounded
  constructible as an `𝒪_{E,X}`-complex as soon as `𝔽_{E,X} ⊗ᴸ K` is. This uses that restriction
  of scalars along `𝒪_{E,X} ⟶ 𝔽_{E,X}` preserves constructibility
  (`ProEtale.isConstructibleModuleObject_comap_padicIntegersToResidueField`), since over a
  member of a pro-étale cover where the unit is projective, finitely presented `𝔽_E`-modules are
  finitely presented `𝒪_E`-modules (`CategoryTheory.Mod.IsFinitelyPresented.comap_of_regularEnd`).
* `ProEtale.boundedConstructible_comap_derivedExtendScalars_of_derivedReduction`: if the first
  derived reduction of `K` lies in the étale-origin `Dᵇc(X, 𝔽_E)`, then `K₁` is a bounded
  constructible complex of `𝒪_{E,X}`-modules.

Note that the cohomology sheaves `Hᵠ K` themselves need not be constructible, nor the cokernel
and kernel of `ϖ` on them: subobjects of constructible sheaves on `X_proét` need not be
constructible.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

/-! ### The homology sequence of a reduction triangle -/

namespace CategoryTheory.CatCenter

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] (z : CatCenter C)
  {K K₁ : DerivedCategory C} {g : K ⟶ K₁} {h : K₁ ⟶ K⟦(1 : ℤ)⟧}

omit [HasDerivedCategory C] in
/-- A central element `z` acts on the homology of a homological complex `K` through the degreewise
action `z.mapHomologicalComplex`, as `z` itself. -/
private lemma homologyMap_app {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex C c)
    (i : ι) :
    HomologicalComplex.homologyMap ((z.mapHomologicalComplex c).app K) i =
      z.app (K.homology i) := by
  have hc : HomologicalComplex.cyclesMap ((z.mapHomologicalComplex c).app K) i =
      z.app (K.cycles i) := by
    rw [← cancel_mono (K.iCycles i), HomologicalComplex.cyclesMap_i,
      mapHomologicalComplex_app_f, z.naturality]
  rw [← cancel_epi (K.homologyπ i), HomologicalComplex.homologyπ_naturality, hc, z.naturality]

/-- The central element of `D(C)` induced by `z` acts on the cohomology objects as `z`. -/
private lemma homologyFunctor_map_app (n : ℤ) (K : DerivedCategory C) :
    (DerivedCategory.homologyFunctor C n).map (z.derivedCategory.app K) =
      z.app ((DerivedCategory.homologyFunctor C n).obj K) := by
  refine map_app_of_iso _ _ _ (DerivedCategory.Q.objObjPreimageIso K) ?_
  rw [derivedCategory_app_Q_obj, ← cancel_mono
    ((DerivedCategory.homologyFunctorFactors C n).hom.app (DerivedCategory.Q.objPreimage K)),
    DerivedCategory.homologyFunctorFactors_hom_naturality, homologyMap_app]
  exact z.naturality _

/-- In a distinguished triangle `K --z--> K --g--> K₁ ⟶ K[1]` whose first map is a central
element, the sequence `Hᵠ K --z--> Hᵠ K --g--> Hᵠ K₁` is exact. -/
lemma exact_app_homologyFunctor_map
    (hT : Triangle.mk (z.derivedCategory.app K) g h ∈ distTriang _) (q : ℤ) :
    (ShortComplex.mk (z.app ((DerivedCategory.homologyFunctor C q).obj K))
      ((DerivedCategory.homologyFunctor C q).map g) (by
        have hw : z.derivedCategory.app K ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ hT
        rw [← homologyFunctor_map_app, ← Functor.map_comp, hw, Functor.map_zero])).Exact := by
  refine ShortComplex.exact_of_iso ?_ (DerivedCategory.HomologySequence.exact₂ _ hT q)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa using (homologyFunctor_map_app z q K).symm) (by simp)

/-- In a distinguished triangle `K --z--> K --g--> K₁ ⟶ K[1]` whose first map is a central
element, the sequence `Hᵠ⁰ K₁ --δ--> Hᵠ¹ K --z--> Hᵠ¹ K` is exact, where `q₀ + 1 = q₁`. -/
lemma exact_δ_app_homologyFunctor
    (hT : Triangle.mk (z.derivedCategory.app K) g h ∈ distTriang _) (q₀ q₁ : ℤ)
    (hq : q₀ + 1 = q₁) :
    (ShortComplex.mk (DerivedCategory.HomologySequence.δ
        (Triangle.mk (z.derivedCategory.app K) g h) q₀ q₁ hq)
      (z.app ((DerivedCategory.homologyFunctor C q₁).obj K)) (by
        rw [← homologyFunctor_map_app]
        exact DerivedCategory.HomologySequence.δ_comp _ hT q₀ q₁ hq)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (DerivedCategory.HomologySequence.exact₁ _ hT q₀ q₁ hq)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simpa using (homologyFunctor_map_app z q₁ K).symm)

/-- If `Hᵠ K₁ = 0`, the central element `z` acts surjectively on `Hᵠ K`. -/
lemma epi_app_homologyFunctor_obj_of_isZero
    (hT : Triangle.mk (z.derivedCategory.app K) g h ∈ distTriang _) (q : ℤ)
    (hq : IsZero ((DerivedCategory.homologyFunctor C q).obj K₁)) :
    Epi (z.app ((DerivedCategory.homologyFunctor C q).obj K)) :=
  (exact_app_homologyFunctor_map z hT q).epi_f (hq.eq_of_tgt _ _)

/-- The kernel of the action of `z` on `Hᵠ¹ K` is a quotient of `Hᵠ⁰ K₁`, where `q₀ + 1 = q₁`. -/
lemma exists_epi_kernel_app_homologyFunctor_obj
    (hT : Triangle.mk (z.derivedCategory.app K) g h ∈ distTriang _) (q₀ q₁ : ℤ)
    (hq : q₀ + 1 = q₁) :
    ∃ f : (DerivedCategory.homologyFunctor C q₀).obj K₁ ⟶
      kernel (z.app ((DerivedCategory.homologyFunctor C q₁).obj K)), Epi f :=
  ⟨_, (exact_δ_app_homologyFunctor z hT q₀ q₁ hq).epi_kernelLift⟩

/-- If `Hᵠ¹ K = 0`, the cokernel of the action of `z` on `Hᵠ⁰ K` is `Hᵠ⁰ K₁`, where
`q₀ + 1 = q₁`. -/
lemma nonempty_cokernel_app_homologyFunctor_obj_iso
    (hT : Triangle.mk (z.derivedCategory.app K) g h ∈ distTriang _) (q₀ q₁ : ℤ)
    (hq : q₀ + 1 = q₁) (h₁ : IsZero ((DerivedCategory.homologyFunctor C q₁).obj K)) :
    Nonempty (cokernel (z.app ((DerivedCategory.homologyFunctor C q₀).obj K)) ≅
      (DerivedCategory.homologyFunctor C q₀).obj K₁) := by
  have : Epi ((DerivedCategory.homologyFunctor C q₀).map g) :=
    (DerivedCategory.HomologySequence.exact₃ _ hT q₀ q₁ hq).epi_f (h₁.eq_of_tgt _ _)
  exact ⟨(colimit.isColimit _).coconePointUniqueUpToIso
    (exact_app_homologyFunctor_map z hT q₀).gIsCokernel⟩

end CategoryTheory.CatCenter

/-! ### Restriction of scalars along a quotient by a regular element -/

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] {φ : R ⟶ S} [IsMonHom φ]
  {r : 𝟙_ (Mod C R) ⟶ 𝟙_ (Mod C R)}

/-- If `0 ⟶ R --r--> R --φ--> S ⟶ 0` is short exact, the reduction `Rʲ ⟶ Sʲ` is an epimorphism
and every map out of `Rʲ` killing `r` factors through it: `Sʲ = Rʲ ⧸ r`. -/
lemma finiteFreeReduction_cokernel_of_regularEnd (w : r.hom ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact) (j : ℕ) :
    Epi (finiteFreeReduction φ j) ∧
      regularEndSMul r (finiteFree R j) ≫ finiteFreeReduction φ j = 0 ∧
      ∀ {W : Mod C R} (h : finiteFree R j ⟶ W), regularEndSMul r (finiteFree R j) ≫ h = 0 →
        ∃ h' : (comap φ).obj (finiteFree S j) ⟶ W, finiteFreeReduction φ j ≫ h' = h := by
  obtain ⟨hex, _⟩ := exact_regularEndSMul_extendUnit w hφ (finiteFree R j)
  refine ⟨epi_comp _ _, ?_, fun h hh ↦ ?_⟩
  · rw [finiteFreeReduction, ← Category.assoc, regularEndSMul_comp_extendUnit w,
      Limits.zero_comp]
  · let hc := hex.gIsCokernel
    refine ⟨(comap φ).map (finiteFreeIsoMap (extendScalars φ)
      (extendScalarsObjRegularIso φ) j).inv ≫ hc.desc (CokernelCofork.ofπ h hh), ?_⟩
    rw [finiteFreeReduction, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact hc.fac (CokernelCofork.ofπ h hh) WalkingParallelPair.one

/-- **Restriction of scalars along a quotient by a regular endomorphism preserves finite
presentation.** If the unit of `C` is projective and `0 ⟶ R --r--> R --φ--> S ⟶ 0` is short
exact, the restriction of scalars of a finitely presented `S`-module `N = coker (f : Sᵐ ⟶ Sⁿ)`
is the cokernel of `(g, r) : R^{m + n} ⟶ Rⁿ`, where `g : Rᵐ ⟶ Rⁿ` lifts `f`. -/
theorem IsFinitelyPresented.comap_of_regularEnd [Projective (𝟙_ C)] (w : r.hom ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact) {N : Mod C S}
    (h : IsFinitelyPresented S N) : IsFinitelyPresented R ((Mod.comap φ).obj N) := by
  obtain ⟨n, m, f, ⟨e⟩⟩ := h
  have : Projective (regular R) := projective_regular
  have : Projective (finiteFree R m) := projective_biproduct _
  obtain ⟨hm, -, -⟩ := finiteFreeReduction_cokernel_of_regularEnd w hφ m
  obtain ⟨hn, wn, hfn⟩ := finiteFreeReduction_cokernel_of_regularEnd w hφ n
  obtain ⟨g, hg⟩ := Projective.factors (finiteFreeReduction φ m ≫ (Mod.comap φ).map f)
    (finiteFreeReduction φ n)
  let G : finiteFree R (m + n) ⟶ finiteFree R n := biproduct.desc
    (Fin.addCases (motive := fun _ ↦ regular R ⟶ finiteFree R n)
      (fun i ↦ biproduct.ι (fun _ : Fin m ↦ regular R) i ≫ g)
      (fun i ↦ biproduct.ι (fun _ : Fin n ↦ regular R) i ≫
        regularEndSMul r (finiteFree R n)))
  have hG {W : Mod C R} (h : finiteFree R n ⟶ W) :
      G ≫ h = 0 ↔ g ≫ h = 0 ∧ regularEndSMul r (finiteFree R n) ≫ h = 0 := by
    constructor
    · intro hh
      refine ⟨biproduct.hom_ext' _ _ fun i ↦ ?_, biproduct.hom_ext' _ _ fun i ↦ ?_⟩
      · have := biproduct.ι _ (Fin.castAdd n i) ≫= hh
        simpa [G] using this
      · have := biproduct.ι _ (Fin.natAdd m i) ≫= hh
        simpa [G] using this
    · rintro ⟨h₁, h₂⟩
      refine biproduct.hom_ext' _ _ fun i ↦ ?_
      refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i
      · simp [G, h₁]
      · simp [G, h₂]
  have hc := isColimitOfHasCokernelOfPreservesColimit (Mod.comap φ) f
  have : Epi ((Mod.comap φ).map (cokernel.π f)) := Functor.map_epi _ _
  refine ⟨n, m + n, G, ⟨(Mod.comap φ).mapIso e ≪≫ IsColimit.coconePointUniqueUpToIso
    (isColimitCokernelCoforkOfLift (finiteFreeReduction φ m) (regularEndSMul r (finiteFree R n))
      (finiteFreeReduction φ n) hfn ((Mod.comap φ).map f) ((Mod.comap φ).map (cokernel.π f))
      (fun h hh ↦ ⟨hc.desc (CokernelCofork.ofπ h hh),
        hc.fac (CokernelCofork.ofπ h hh) WalkingParallelPair.one⟩)
      (by rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]) wn g hg G hG)
    (colimit.isColimit _)⟩⟩

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}

/-! ### Restriction of scalars along `𝒪_{E,X} ⟶ 𝔽_{E,X}` preserves constructibility -/

/-- Restriction of scalars along `𝒪_{E,X} ⟶ 𝔽_{E,X}` preserves pro-étale locally finitely
presented module objects: refine the cover by spectra of w-contractible rings, over which the
unit is projective, so that finitely presented `𝔽_E`-modules are finitely presented
`𝒪_E`-modules, `𝔽_E` being the quotient of `𝒪_E` by a uniformizer. -/
lemma isLocallyFinitelyPresented_comap_padicIntegersToResidueField {X : Scheme.{u}}
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (residueFieldRingObj X ℓ E)}
    (hN : IsLocallyFinitelyPresented (residueFieldRingObj X ℓ E) N) :
    IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)
      ((Mod.comap (padicIntegersToResidueField X ℓ E)).obj N) := by
  obtain ⟨ϖ, hϖ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E.1
  rw [Ideal.submodule_span_eq] at hϖ
  obtain ⟨𝒰, h𝒰⟩ := hN
  choose 𝒱 h𝒱 using fun i ↦ exists_cover_projective_tensorUnit (𝒰.X i)
  refine ⟨𝒰.bind 𝒱, fun i ↦ ?_⟩
  have := h𝒱 i.1 i.2
  refine (isFinitelyPresented_mapMod_iff _ ((𝒱 i.1).f i.2 ≫ 𝒰.f i.1) _).2 ?_
  have h₁ := IsFinitelyPresented.upperStar _ ((𝒱 i.1).f i.2)
    ((isFinitelyPresented_mapMod_iff _ _ _).1 (h𝒰 i.1))
  have h₂ := h₁.of_iso ((CondensedRing.upperStarComp _ ((𝒱 i.1).f i.2) (𝒰.f i.1)).app N).symm
  have h₃ := Mod.IsFinitelyPresented.comap_of_regularEnd _
    (shortExact_padicIntegersRegularEnd ((𝒱 i.1).X i.2) ℓ E ϖ hϖ) h₂
  exact h₃.of_iso ((comapUpperStarIso (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
    ((𝒱 i.1).f i.2 ≫ 𝒰.f i.1)).app N)

/-- **Restriction of scalars along `𝒪_{E,X} ⟶ 𝔽_{E,X}` preserves constructible module
objects**: it commutes with the pullbacks to the strata of a stratification. -/
lemma isConstructibleModuleObject_comap_padicIntegersToResidueField {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (residueFieldRingObj X ℓ E)}
    (hM : IsConstructibleModuleObject (residueFieldRingObj X ℓ E) M) :
    IsConstructibleModuleObject (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)
      ((Mod.comap (padicIntegersToResidueField X ℓ E)).obj M) := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ (isLocallyFinitelyPresented_mapMod_iff _ _ _).2 ?_⟩
  exact IsLocallyFinitelyPresented.of_iso
    ((comapUpperStarIso (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
      (S.immersion a)).app M)
    (isLocallyFinitelyPresented_comap_padicIntegersToResidueField
      ((isLocallyFinitelyPresented_mapMod_iff _ _ _).1 (hS a)))

/-! ### Bounded constructibility of the reduction -/

/-- **Restriction of scalars along `𝒪_{E,X} ⟶ 𝔽_{E,X}` preserves bounded constructible
complexes**: it is exact, hence preserves boundedness and commutes with the cohomology sheaves,
and it preserves constructible module objects. In particular, if `𝔽_{E,X} ⊗ᴸ K` is bounded
constructible, so is `K₁`, the same complex regarded as a complex of `𝒪_{E,X}`-modules. -/
theorem boundedConstructible_comap_padicIntegersToResidueField {X : Scheme.{u}}
    {L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (residueFieldRingObj X ℓ E))}
    (hL : boundedConstructible (residueFieldRingObj X ℓ E) L) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)
      ((Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory.obj L) := by
  exact ⟨Functor.bounded_mapDerivedCategory_obj _ hL.1, fun i ↦
    IsConstructibleModuleObject.of_iso
      (((Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategoryHomologyFunctorIso
        i).app _)
      (isConstructibleModuleObject_comap_padicIntegersToResidueField (hL.2 i))⟩

/-- If the first derived reduction of `K` lies in the étale-origin `Dᵇc(X, 𝔽_E)`, then the derived
extension of scalars `𝔽_{E,X} ⊗ᴸ K` is a bounded constructible complex of `𝔽_{E,X}`-modules: it
is the condensed reading of a bounded constructible étale complex
(`ProEtale.CondensedRing.boundedConstructible_inverse_obj_of_etale`). -/
theorem boundedConstructible_derivedExtendScalars_of_derivedReduction {X : Scheme.{u}}
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (h₁ : ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) X ((derivedReduction X ℓ E).obj K)) :
    boundedConstructible (residueFieldRingObj X ℓ E)
      ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K) := by
  obtain ⟨K', hK', ⟨e⟩⟩ := (DerivedCategory.boundedConstructible_iff _ _ _).1 h₁
  have := Functor.additive_of_iso
    (residueFieldModuleSheafIsoOfSection X ℓ E (residueFieldSectionFac X ℓ E))
  refine (boundedConstructible _).prop_of_iso ?_
    (CondensedRing.boundedConstructible_inverse_obj_of_etale (integersResidueField ℓ E) hK')
  exact (finiteCoefficientDerivedEquivalence X _).inverse.mapIso (e ≪≫
      (Functor.mapDerivedCategoryNatIso
        (residueFieldModuleSheafIsoOfSection X ℓ E (residueFieldSectionFac X ℓ E))).app _) ≪≫
    ((finiteCoefficientDerivedEquivalence X _).unitIso.app _).symm

/-- **The reduction `K₁` of `K` is bounded constructible**: if the first derived reduction of `K`
lies in the étale-origin `Dᵇc(X, 𝔽_E)`, then `K₁ = 𝔽_{E,X} ⊗ᴸ K`, regarded as a complex of
`𝒪_{E,X}`-modules, is bounded constructible: its cohomology sheaves are constructible
`𝒪_{E,X}`-modules, vanishing outside a bounded range of degrees. -/
theorem boundedConstructible_comap_derivedExtendScalars_of_derivedReduction {X : Scheme.{u}}
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (h₁ : ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) X ((derivedReduction X ℓ E).obj K)) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)
      ((Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory.obj
        ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K)) :=
  boundedConstructible_comap_padicIntegersToResidueField
    (boundedConstructible_derivedExtendScalars_of_derivedReduction K h₁)

/-! ### The action of `ϖ` on the cohomology sheaves -/

variable {X : Scheme.{u}} {ϖ : PadicAlgCl.integers ℓ E.1}

/-- The reduction triangle `K --ϖ--> K ⟶ K₁ ⟶ K[1]`, with `K₁ = 𝔽_{E,X} ⊗ᴸ K` regarded as a
complex of `𝒪_{E,X}`-modules. -/
lemma exists_distinguished_derivedUniformizer
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) = Ideal.span {ϖ})
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) :
    ∃ (g : K ⟶ (Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory.obj
        ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K))
      (h : (Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory.obj
        ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K) ⟶
        K⟦(1 : ℤ)⟧),
      Triangle.mk ((padicIntegersCenter X ℓ E ϖ).derivedCategory.app K) g h ∈ distTriang _ :=
  Mod.exists_distinguished_regularEndCenter_derivedExtendScalars _
    (shortExact_padicIntegersRegularEnd X ℓ E ϖ hϖ) K

/-- If `Hᵠ¹ K = 0`, the cokernel of `ϖ` on `Hᵠ⁰ K` is `Hᵠ⁰ K₁` as an `𝒪_{E,X}`-module, where
`q₀ + 1 = q₁` and `K₁ = 𝔽_{E,X} ⊗ᴸ K`. -/
theorem nonempty_cokernel_padicIntegersCenter_homology_iso
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) = Ideal.span {ϖ})
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (q₀ q₁ : ℤ)
    (hq : q₀ + 1 = q₁) (h₁ : IsZero ((DerivedCategory.homologyFunctor _ q₁).obj K)) :
    Nonempty (cokernel ((padicIntegersCenter X ℓ E ϖ).app
        ((DerivedCategory.homologyFunctor _ q₀).obj K)) ≅
      (DerivedCategory.homologyFunctor _ q₀).obj
        ((Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory.obj
          ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K))) :=
  have hT := (exists_distinguished_derivedUniformizer hϖ K).choose_spec.choose_spec
  CatCenter.nonempty_cokernel_app_homologyFunctor_obj_iso _ hT q₀ q₁ hq h₁

/-- The kernel of `ϖ` on `Hᵠ¹ K` is a quotient of `Hᵠ⁰ K₁`, where `q₀ + 1 = q₁` and
`K₁ = 𝔽_{E,X} ⊗ᴸ K`. -/
theorem exists_epi_kernel_padicIntegersCenter_homology
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) = Ideal.span {ϖ})
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (q₀ q₁ : ℤ)
    (hq : q₀ + 1 = q₁) :
    ∃ f : (DerivedCategory.homologyFunctor _ q₀).obj
        ((Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory.obj
          ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K)) ⟶
      kernel ((padicIntegersCenter X ℓ E ϖ).app ((DerivedCategory.homologyFunctor _ q₁).obj K)),
      Epi f :=
  have hT := (exists_distinguished_derivedUniformizer hϖ K).choose_spec.choose_spec
  CatCenter.exists_epi_kernel_app_homologyFunctor_obj _ hT q₀ q₁ hq

/-- If `Hᵠ K₁ = 0`, then `ϖ` acts surjectively on `Hᵠ K`, where `K₁ = 𝔽_{E,X} ⊗ᴸ K`. -/
theorem epi_padicIntegersCenter_homology_of_isZero
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) = Ideal.span {ϖ})
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (q : ℤ)
    (hq : IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory.obj
        ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K)))) :
    Epi ((padicIntegersCenter X ℓ E ϖ).app ((DerivedCategory.homologyFunctor _ q).obj K)) :=
  have hT := (exists_distinguished_derivedUniformizer hϖ K).choose_spec.choose_spec
  CatCenter.epi_app_homologyFunctor_obj_of_isZero _ hT q hq

end AlgebraicGeometry.ProEtale
