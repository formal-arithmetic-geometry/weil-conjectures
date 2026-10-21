/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q129, A5
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleNoetherianEtaleModules
public import Sheaf.AlgebraicGeometry.AffineLocallyConstructibleProEtaleModules
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.Paper.ProEtaleConstantModulePullbackComposition
import Sheaf.AlgebraicGeometry.ProEtaleFinitelyPresentedLocalModelsSerre
import Sheaf.AlgebraicGeometry.ProEtaleFinitelyPresentedLocalModelsPullback
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.ConstructibleSheaf.OpenClosed

/-!
# Constructible sheaves over discrete Noetherian rings form weak Serre subcategories

Source: Stacks Project, Tag 03RZ (3), etale-cohomology.tex, lemma-constructible-abelian;
Tag 09B5, proetale.tex, lemma-constructible-serre
(blueprint: lem-sfb-discrete-noetherian-constructible-serre).

## Main statements

- `etale_discreteNoetherian_constructible_serre`: the etale closure clauses.
- `proEtale_discreteNoetherian_constructible_serre`: the pro-etale closure clauses.

The two statements spell out zero, kernel, cokernel and extension closure in the ambient
categories of modules over the constant ring sheaves. No finite-ring or invertibility
hypothesis occurs. The etale predicate uses finite generation of constant module values;
over a Noetherian ring this is equivalent to the finite-presentation convention of the node.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry

namespace Scheme

open Opposite

-- Cache sheafification on the concrete sites before elaborating the local models.
-- This avoids reconstructing the same large instance terms at every constant sheaf.
private instance etaleModuleWeakSheafify (Y : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :
    HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R) := inferInstance

private instance etaleModuleOverWeakSheafify (Y : Scheme.{u}) (R : Type (u + 1))
    [CommRing R] (U : Y.Etale) :
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} R) := inferInstance

private instance etaleRingWeakSheafify (Y : Scheme.{u}) :
    HasWeakSheafify Y.smallEtaleTopology RingCat.{u + 1} := inferInstance

private instance etaleModuleLocallyBijective (Y : Scheme.{u}) (R : Type (u + 1))
    [CommRing R] : Y.smallEtaleTopology.WEqualsLocallyBijective (ModuleCat.{u + 1} R) :=
  inferInstance

private noncomputable instance etaleModuleAbelian (Y : Scheme.{u}) (R : Type (u + 1))
    [CommRing R] : Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  inferInstance

private instance : JointlySurjective etalePrecoverage.{u} :=
  inferInstanceAs (JointlySurjective (precoverage @Etale))

private def etaleFiniteModels {Y : Scheme.{u}} {R : Type (u + 1)} [CommRing R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) : Prop :=
  ∃ V : Cover.{u} etalePrecoverage Y, ∀ b : V.I₀,
    ∃ M : ModuleCat.{u + 1} R, Module.Finite R M ∧
      Nonempty (F.over (V.etalePrecoverageToEtale b) ≅
        (constantSheaf (Y.smallEtaleTopology.over (V.etalePrecoverageToEtale b))
          (ModuleCat.{u + 1} R)).obj M)

private noncomputable def finiteModelPullbackIso
    {Y : Scheme.{u}} {R : Type (u + 1)} [CommRing R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (U : Y.Etale) (M : ModuleCat.{u + 1} R)
    (e : F.over U ≅
      (constantSheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)).obj M) :
    (Etale.upperStar (ModuleCat.{u + 1} R) U.hom).obj F ≅
      (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M :=
  (overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} R) U F).symm ≪≫
    (Etale.overSheafEquiv U (ModuleCat.{u + 1} R)).functor.mapIso e ≪≫
    ((Etale.overEquiv U).constantSheafSheafCongrIso
      (Y.smallEtaleTopology.over U) U.left.smallEtaleTopology
      (ModuleCat.{u + 1} R) CategoryTheory.Over.mkIdTerminal).app M

private noncomputable def finiteModelStalkIso
    {Y : Scheme.{u}} {R : Type (u + 1)} [CommRing R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (U : Y.Etale) (M : ModuleCat.{u + 1} R)
    (e : F.over U ≅
      (constantSheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)).obj M)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U.left) :
    ((pointSmallEtale (s ≫ U.hom)).sheafFiber
      (A := ModuleCat.{u + 1} R)).obj F ≅ M := by
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  exact ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) U.hom s).app F).symm ≪≫
    (pointSmallEtale s).sheafFiber.mapIso (finiteModelPullbackIso F U M e) ≪≫
    (pointSmallEtale s).sheafFiberConstantSheafIso M

private theorem etaleFiniteModels_iff
    {Y : Scheme.{u}} {R : Type (u + 1)} [CommRing R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    etaleFiniteModels F ↔ IsFiniteLocallyConstantSheaf F := by
  classical
  constructor
  · rintro ⟨V, hV⟩
    refine { toIsLocallyConstantSheaf := ⟨⟨⟨V, fun b ↦ ?_⟩⟩⟩
             toIsFiniteSheaf := ⟨fun Ω _ _ s ↦ ?_⟩ }
    · obtain ⟨M, _, ⟨e⟩⟩ := hV b
      exact Sheaf.isConstant_of_iso _ e
    · obtain ⟨b, x, hx⟩ := V.exists_eq (s default)
      have : Etale (V.f b) := V.map_prop b
      obtain ⟨t, ht, _⟩ := exists_fac_of_etale_of_isSepClosed (V.f b) s x hx
      obtain ⟨M, hM, ⟨e⟩⟩ := hV b
      have hgen := (ModuleCat.isFinitelyGenerated_iff M).mpr hM
      have he := finiteModelStalkIso F (V.etalePrecoverageToEtale b) M e t
      change ((pointSmallEtale (t ≫ V.f b)).sheafFiber
        (A := ModuleCat.{u + 1} R)).obj F ≅ M at he
      rw [ht] at he
      exact hgen.of_iso he.symm
  · intro hF
    have := hF
    obtain ⟨d⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
    let V := d.cover.nonemptyMembers
    refine ⟨V, fun b ↦ ?_⟩
    have := d.isConstant b.1
    obtain ⟨M, ⟨e⟩⟩ :=
      (F.over (d.cover.etalePrecoverageToEtale b.1)).mem_essImage_of_isConstant
    let U := V.etalePrecoverageToEtale b
    have : Nonempty U.left := b.2
    let x : U.left := Classical.arbitrary _
    let Ω := SeparableClosure (U.left.residueField x)
    let t : Spec (.of Ω) ⟶ U.left := (SpecToEquivOfField Ω _).symm
      ⟨x, CommRingCat.ofHom (algebraMap (U.left.residueField x) Ω)⟩
    have hgen := (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
      (F := F) Ω (t ≫ U.hom)).of_iso (finiteModelStalkIso F U M e.symm t)
    exact ⟨M, (ModuleCat.isFinitelyGenerated_iff M).mp hgen, ⟨e.symm⟩⟩

private theorem etaleAffine_iff {X : Scheme.{u}} {R : Type (u + 1)}
    [CommRing R] [IsNoetherianRing R]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    IsAffineLocallyConstructibleEtaleModuleSheaf F ↔
      ∀ U : X.Opens, IsAffineOpen U →
        ∃ S : Stratification U.toScheme, ∀ a : Fin S.n,
          IsFiniteLocallyConstantSheaf
            ((Etale.upperStar (ModuleCat.{u + 1} R) (S.immersion a ≫ U.ι)).obj F) := by
  constructor
  · intro h U hU
    obtain ⟨S, _, hS⟩ := h U hU
    exact ⟨S, fun a ↦ (etaleFiniteModels_iff _).mp (hS a)⟩
  · intro h U hU
    obtain ⟨S, hS⟩ := h U hU
    exact ⟨S, S.isConstructible_stratum,
      fun a ↦ (etaleFiniteModels_iff _).mpr (hS a)⟩

/-- Lift a finite presentation through an extension and make the finitely many relations
constant after a covering refinement. The relation module is finitely generated by
Noetherianity. Source: Stacks Project, Modules on Sites, Tag 093U (3). -/
private lemma noetherian_exists_isConstant_over_of_shortExact
    {Y : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]
    {S : ShortComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    {M N : ModuleCat.{u + 1} Λ} [Module.Finite Λ N]
    (e₁ : (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M ≅ S.X₁)
    (e₃ : (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N ≅ S.X₃)
    (T : Y.Etale) :
    ∃ R ∈ Y.smallEtaleTopology T, ∀ ⦃V : Y.Etale⦄ (g : V ⟶ T), R g →
      (⊥ : Sieve V) ∉ Y.smallEtaleTopology V →
        (S.X₂.over V).IsConstant (Y.smallEtaleTopology.over V) := by
  classical
  obtain ⟨b, p, hp⟩ := Module.Finite.exists_fin' Λ N
  let J := Y.smallEtaleTopology
  let A := ModuleCat.{u + 1} Λ
  let x (i : Fin b) : S.X₃.obj.obj (op T) := e₃.hom.hom.app (op T)
    ((toSheafify J ((Functor.const _).obj N)).app (op T) (p (Pi.single i 1)))
  have : Sheaf.IsLocallySurjective S.g :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := S.g)).2 hS.epi_g
  have hR₁ : (⨅ i, Presheaf.imageSieve S.g.hom (x i)) ∈ J T :=
    J.iInf_mem _ fun i ↦ Presheaf.imageSieve_mem J S.g.hom (x i)
  -- sections of the short exact sequence
  have hsec (U : Y.Etale) :
      (S.map (sheafToPresheaf J A ⋙ (CategoryTheory.evaluation Y.Etaleᵒᵖ A).obj (op U))).Exact :=
    hS.exact.map_of_mono_of_preservesKernel _ hS.mono_f inferInstance
  have hinj (U : Y.Etale) : Function.Injective (S.f.hom.app (op U)) :=
    have := hS.mono_f
    have : Mono S.f.hom := inferInstance
    (ModuleCat.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 this (op U))
  -- naturality of the constant sections
  have hconst {Q : ModuleCat.{u + 1} Λ} {U U' : Y.Etale} (f : U' ⟶ U) (q : Q) :
      (sheafify J ((Functor.const _).obj Q)).map f.op
        ((toSheafify J ((Functor.const _).obj Q)).app (op U) q) =
      (toSheafify J ((Functor.const _).obj Q)).app (op U') q := by
    have := (toSheafify J ((Functor.const Y.Etaleᵒᵖ).obj Q)).naturality f.op
    exact (ConcreteCategory.congr_hom this q).symm
  have step : ∀ ⦃U : Y.Etale⦄ (g : U ⟶ T), (⨅ i, Presheaf.imageSieve S.g.hom (x i)) g →
      ∃ R₂ ∈ J U, ∀ ⦃V : Y.Etale⦄ (f : V ⟶ U), R₂ f → (⊥ : Sieve V) ∉ J V →
        (S.X₂.over V).IsConstant (J.over V) := by
    intro U g hg
    have hy (i : Fin b) := ((iInf_le _ i : (⨅ i, Presheaf.imageSieve S.g.hom (x i)) ≤ _) _ hg)
    choose y hy using hy
    have nat {F G : Y.Etaleᵒᵖ ⥤ A} (η : F ⟶ G) {U₁ U₂ : Y.Etale} (f : U₂ ⟶ U₁)
        (a : ToType (F.obj (op U₁))) :
        η.app (op U₂) (F.map f.op a) = G.map f.op (η.app (op U₁) a) :=
      ConcreteCategory.congr_hom (η.naturality f.op) a
    have hyU (i : Fin b) : S.g.hom.app (op U) (y i) = e₃.hom.hom.app (op U)
        ((toSheafify J ((Functor.const _).obj N)).app (op U) (p (Pi.single i 1))) := by
      rw [hy i]
      exact (nat e₃.hom.hom g _).symm.trans (congrArg (e₃.hom.hom.app (op U)) (hconst g _))
    have hsum (k : LinearMap.ker p) :
        ∑ i, (k : Fin b → Λ) i • (Pi.single i 1 : Fin b → Λ) = k := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    have hw (k : LinearMap.ker p) : ∃ w : ToType (S.X₁.obj.obj (op U)),
        S.f.hom.app (op U) w = ∑ i, (k : Fin b → Λ) i • y i := by
      refine (ShortComplex.moduleCat_exact_iff _).1 (hsec U) _ ?_
      change S.g.hom.app (op U) (∑ i, (k : Fin b → Λ) i • y i) = 0
      let L : (Fin b → Λ) →ₗ[Λ] ToType (S.X₃.obj.obj (op U)) := (e₃.hom.hom.app (op U)).hom ∘ₗ
        ((toSheafify J ((Functor.const _).obj N)).app (op U)).hom ∘ₗ p
      have hL (v : Fin b → Λ) : e₃.hom.hom.app (op U)
          ((toSheafify J ((Functor.const _).obj N)).app (op U) (p v)) = L v := rfl
      calc S.g.hom.app (op U) (∑ i, (k : Fin b → Λ) i • y i)
          = ∑ i, (k : Fin b → Λ) i • L (Pi.single i 1) := by
            simp only [map_sum, map_smul]
            exact Finset.sum_congr rfl fun i _ ↦ congrArg ((k : Fin b → Λ) i • ·) (hyU i)
        _ = L (∑ i, (k : Fin b → Λ) i • Pi.single i 1) := by simp only [map_sum, map_smul]
        _ = 0 := by
            rw [hsum]
            change e₃.hom.hom.app (op U) ((toSheafify J ((Functor.const _).obj N)).app (op U)
              (p k)) = 0
            rw [LinearMap.mem_ker.1 k.2, map_zero]
            exact map_zero (e₃.hom.hom.app (op U)).hom
    choose w hw using hw
    obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := Λ) (M := LinearMap.ker p)
    obtain ⟨R₂, hR₂, hm⟩ := J.exists_mem_forall_exists_toSheafify_const_app_eq M
      (fun k : (t : Set (LinearMap.ker p)) ↦ e₁.inv.hom.app (op U) (w k.1))
    refine ⟨R₂, hR₂, fun V f hf hV ↦ ?_⟩
    choose m hm using hm f hf
    let y' (i : Fin b) : ToType (S.X₂.obj.obj (op V)) := S.X₂.obj.map f.op (y i)
    have hy' (i : Fin b) : S.g.hom.app (op V) (y' i) = e₃.hom.hom.app (op V)
        ((toSheafify J ((Functor.const _).obj N)).app (op V) (p (Pi.single i 1))) := by
      change S.g.hom.app (op V) (S.X₂.obj.map f.op (y i)) = _
      rw [nat S.g.hom f, hyU]
      exact (nat e₃.hom.hom f _).symm.trans (congrArg (e₃.hom.hom.app (op V)) (hconst f _))
    let θ : M →ₗ[Λ] ToType (S.X₂.obj.obj (op V)) := (S.f.hom.app (op V)).hom ∘ₗ
      (e₁.hom.hom.app (op V)).hom ∘ₗ ((toSheafify J ((Functor.const _).obj M)).app (op V)).hom
    have hθ : Function.Injective θ := by
      have he : Function.Injective (e₁.hom.hom.app (op V)) :=
        ((sheafToPresheaf J A ⋙ (CategoryTheory.evaluation Y.Etaleᵒᵖ A).obj (op V)).mapIso
          e₁).toLinearEquiv.injective
      exact (hinj V).comp (he.comp (J.toSheafify_const_app_injective M hV))
    have hinv (a : ToType (S.X₁.obj.obj (op U))) :
        e₁.hom.hom.app (op U) (e₁.inv.hom.app (op U) a) = a :=
      ((sheafToPresheaf J A ⋙ (CategoryTheory.evaluation Y.Etaleᵒᵖ A).obj (op U)).mapIso
          e₁).toLinearEquiv.apply_symm_apply a
    have key₀ (k : (t : Set (LinearMap.ker p))) :
        θ (m k) = ∑ i, (k.1 : Fin b → Λ) i • y' i := by
      calc θ (m k) = S.f.hom.app (op V) (S.X₁.obj.map f.op (w k.1)) := by
              exact congrArg (S.f.hom.app (op V)) ((congrArg (e₁.hom.hom.app (op V)) (hm k)).trans
                ((nat e₁.hom.hom f _).trans (congrArg _ (hinv _))))
        _ = ∑ i, (k : Fin b → Λ) i • y' i := by
              rw [nat S.f.hom f, hw k.1, map_sum]
              simp only [map_smul, y']
    let L : LinearMap.ker p →ₗ[Λ] ToType (S.X₂.obj.obj (op V)) :=
      (Fintype.linearCombination Λ y') ∘ₗ (LinearMap.ker p).subtype
    have hle : LinearMap.range L ≤ LinearMap.range θ := by
      rw [LinearMap.range_eq_map, ← ht, Submodule.map_span]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, hk, rfl⟩
      exact ⟨m ⟨k, hk⟩, key₀ ⟨k, hk⟩⟩
    let e := LinearEquiv.ofInjective θ hθ
    let α : LinearMap.ker p →ₗ[Λ] M :=
      e.symm.toLinearMap ∘ₗ L.codRestrict _ fun k ↦ hle (LinearMap.mem_range_self L k)
    have key (k : LinearMap.ker p) : θ (α k) = ∑ i, (k : Fin b → Λ) i • y' i := by
      exact congrArg Subtype.val
        (e.apply_symm_apply ⟨L k, hle (LinearMap.mem_range_self L k)⟩)
    exact isConstant_over_of_shortExact_of_lift hS e₁ e₃ p hp V y' hy' α key
  choose R₂ hR₂ hP using step
  exact ⟨Sieve.bind _ R₂, J.bind_covering hR₁ hR₂, by
    rintro V _ ⟨U, f, g, hg, hf, rfl⟩ hV
    exact hP g hg f hf hV⟩

/-- Noetherian coefficients suffice for extension closure: trivialize the outer terms,
lift the finite presentation locally, and use exactness on stalks for finite generation.
Source: Stacks Project, Modules on Sites, Tag 093U (3). -/
private theorem noetherian_flc_of_shortExact
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₂ where
  toIsLocallyConstantSheaf := by
    obtain ⟨𝒰₀, h𝒰₀⟩ := IsLocallyConstantSheaf.exists_cover₂ S.X₁ S.X₃
    let 𝒰 := 𝒰₀.nonemptyMembers
    have key : ∀ i : 𝒰.I₀, ∃ 𝒱 : Cover.{u} etalePrecoverage (𝒰.X i), ∀ j,
        (S.X₂.over (Etale.mk (𝒱.f j ≫ 𝒰.f i))).IsConstant
          (X.smallEtaleTopology.over (Etale.mk (𝒱.f j ≫ 𝒰.f i))) := by
      intro i
      set Y := 𝒰.X i
      set g := 𝒰.f i
      have hF : ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj S.X₁).IsConstant
          Y.smallEtaleTopology := (h𝒰₀ i.1).1
      have hG : ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj S.X₃).IsConstant
          Y.smallEtaleTopology := (h𝒰₀ i.1).2
      obtain ⟨M, ⟨eM⟩⟩ :=
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj S.X₁).mem_essImage_of_isConstant
      obtain ⟨N, ⟨eN⟩⟩ :=
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj S.X₃).mem_essImage_of_isConstant
      have hfin : IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
          (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N) :=
        have := IsFiniteSheaf.upperStar (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
          (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) g S.X₃
        IsFiniteSheaf.of_iso (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
          (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) eN.symm
      have : Module.Finite Λ N := moduleFinite_of_isFiniteSheaf_constantSheaf (Y := Y) N
      obtain ⟨R, hR, hP⟩ := noetherian_exists_isConstant_over_of_shortExact
        (hS.map_of_exact (Etale.upperStar (ModuleCat.{u + 1} Λ) g)) eM eN (Etale.mk (𝟙 Y))
      refine ⟨Cover.ofSieve R hR, fun y ↦ ?_⟩
      set V := Cover.ofSieveObj R hR y
      set a := Cover.ofSieveHom R hR y
      have := Cover.nonempty_ofSieveObj R hR y
      have hk : ((Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj S.X₂)).IsConstant
            V.left.smallEtaleTopology := by
        have := hP a (Cover.ofSieveHom_mem R hR y) (bot_not_mem_smallEtaleTopology V)
        rwa [isConstant_over_iff_upperStar] at this
      rw [isConstant_over_iff_upperStar]
      change ((Etale.upperStar (ModuleCat.{u + 1} Λ) (a.left ≫ g)).obj S.X₂).IsConstant
        V.left.smallEtaleTopology
      refine Sheaf.isConstant_congr _ (?_ : (Etale.upperStar _ V.hom).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj S.X₂) ≅ _)
      exact eqToIso (congrArg (fun m ↦ (Etale.upperStar (ModuleCat.{u + 1} Λ) m).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj S.X₂))
          (Cover.ofSieveHom_left R hR y).symm) ≪≫
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) a.left g).app S.X₂).symm
    choose 𝒱 h𝒱 using key
    exact ⟨⟨⟨𝒰.bind 𝒱, fun ⟨i, j⟩ ↦ h𝒱 i j⟩⟩⟩
  toIsFiniteSheaf := ⟨fun Ω _ _ s ↦ by
    have hs := hS.map_of_exact ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ))
    have : Module.Finite Λ (S.map (pointSmallEtale s).sheafFiber).X₁ :=
      (ModuleCat.isFinitelyGenerated_iff _).1
        (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
          (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
          (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F := S.X₁) Ω s)
    have : Module.Finite Λ (S.map (pointSmallEtale s).sheafFiber).X₃ :=
      (ModuleCat.isFinitelyGenerated_iff _).1
        (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
          (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
          (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F := S.X₃) Ω s)
    exact (ModuleCat.isFinitelyGenerated_iff _).2
      (Module.Finite.of_exact
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hs.exact)
        hs.moduleCat_surjective_g)⟩

private theorem flc_pullback_comp {X Y Z : Scheme.{u}} {R : Type (u + 1)} [CommRing R]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R))
    (h : IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} R) g).obj F)) :
    IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} R) (f ≫ g)).obj F) := by
  let := h
  let : IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} R) f).obj
        ((Etale.upperStar (ModuleCat.{u + 1} R) g).obj F)) :=
    IsFiniteLocallyConstantSheaf.upperStar f _
  let e : (Etale.upperStar (ModuleCat.{u + 1} R) f).obj
      ((Etale.upperStar (ModuleCat.{u + 1} R) g).obj F) ≅
      (Etale.upperStar (ModuleCat.{u + 1} R) (f ≫ g)).obj F :=
    ((Etale.upperStarComp (ModuleCat.{u + 1} R) f g).app F).symm
  exact IsFiniteLocallyConstantSheaf.of_iso e

private theorem common_etale_strata {X : Scheme.{u}} {R : Type (u + 1)}
    [CommRing R] [IsNoetherianRing R]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (hF : IsAffineLocallyConstructibleEtaleModuleSheaf F)
    (hG : IsAffineLocallyConstructibleEtaleModuleSheaf G)
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ S : Stratification U.toScheme, ∀ a : Fin S.n,
      IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} R) (S.immersion a ≫ U.ι)).obj F) ∧
      IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} R) (S.immersion a ≫ U.ι)).obj G) := by
  obtain ⟨S, hS⟩ := (etaleAffine_iff F).mp hF U hU
  obtain ⟨T, hT⟩ := (etaleAffine_iff G).mp hG U hU
  refine ⟨S.inter T, fun a ↦ ?_⟩
  let i := (finProdFinEquiv.symm a).1
  let j := (finProdFinEquiv.symm a).2
  constructor
  · change IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} R)
        ((pullback.fst (S.immersion i) (T.immersion j) ≫ S.immersion i) ≫ U.ι)).obj F)
    rw [Category.assoc]
    exact flc_pullback_comp _ _ F (hS i)
  · change IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} R)
        ((pullback.fst (S.immersion i) (T.immersion j) ≫ S.immersion i) ≫ U.ι)).obj G)
    rw [pullback.condition, Category.assoc]
    exact flc_pullback_comp _ _ G (hT j)

private theorem etaleAffine_of_iso {X : Scheme.{u}} {R : Type (u + 1)}
    [CommRing R] [IsNoetherianRing R]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)} (e : F ≅ G)
    (hF : IsAffineLocallyConstructibleEtaleModuleSheaf F) :
    IsAffineLocallyConstructibleEtaleModuleSheaf G := by
  apply (etaleAffine_iff G).mpr
  intro U hU
  obtain ⟨S, hS⟩ := (etaleAffine_iff F).mp hF U hU
  refine ⟨S, fun a ↦ ?_⟩
  have := hS a
  exact IsFiniteLocallyConstantSheaf.of_iso
    ((Etale.upperStar (ModuleCat.{u + 1} R) (S.immersion a ≫ U.ι)).mapIso e)

private theorem etaleAffine_of_isZero {X : Scheme.{u}} {R : Type (u + 1)}
    [CommRing R] [IsNoetherianRing R]
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)} (hF : IsZero F) :
    IsAffineLocallyConstructibleEtaleModuleSheaf F := by
  apply (etaleAffine_iff F).mpr
  intro U _
  refine ⟨Stratification.trivial U.toScheme, fun a ↦ ?_⟩
  exact IsFiniteLocallyConstantSheaf.of_isZero
    ((Etale.upperStar (ModuleCat.{u + 1} R) (_ ≫ U.ι)).map_isZero hF)

private theorem etaleAffine_kernel_cokernel {X : Scheme.{u}} {R : Type (u + 1)}
    [CommRing R] [IsNoetherianRing R]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)} (f : F ⟶ G)
    (hF : IsAffineLocallyConstructibleEtaleModuleSheaf F)
    (hG : IsAffineLocallyConstructibleEtaleModuleSheaf G) :
    IsAffineLocallyConstructibleEtaleModuleSheaf (kernel f) ∧
      IsAffineLocallyConstructibleEtaleModuleSheaf (cokernel f) := by
  constructor
  all_goals
    apply (etaleAffine_iff _).mpr
    intro U hU
    obtain ⟨S, hS⟩ := common_etale_strata hF hG U hU
    refine ⟨S, fun a ↦ ?_⟩
    have := (hS a).1
    have := (hS a).2
    let L := Etale.upperStar (ModuleCat.{u + 1} R) (S.immersion a ≫ U.ι)
    first
    | have := IsFiniteLocallyConstantSheaf.kernel (L.map f)
      exact IsFiniteLocallyConstantSheaf.of_iso (PreservesKernel.iso L f).symm
    | have := IsFiniteLocallyConstantSheaf.cokernel (L.map f)
      exact IsFiniteLocallyConstantSheaf.of_iso (PreservesCokernel.iso L f).symm

private theorem etaleAffine_extension {X : Scheme.{u}} {R : Type (u + 1)}
    [CommRing R] [IsNoetherianRing R]
    (S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (hS : S.ShortExact)
    (h₁ : IsAffineLocallyConstructibleEtaleModuleSheaf S.X₁)
    (h₃ : IsAffineLocallyConstructibleEtaleModuleSheaf S.X₃) :
    IsAffineLocallyConstructibleEtaleModuleSheaf S.X₂ := by
  apply (etaleAffine_iff _).mpr
  intro U hU
  obtain ⟨T, hT⟩ := common_etale_strata h₁ h₃ U hU
  refine ⟨T, fun a ↦ ?_⟩
  let L := Etale.upperStar (ModuleCat.{u + 1} R) (T.immersion a ≫ U.ι)
  have : IsFiniteLocallyConstantSheaf (S.map L).X₁ := (hT a).1
  have : IsFiniteLocallyConstantSheaf (S.map L).X₃ := (hT a).2
  exact noetherian_flc_of_shortExact (hS.map_of_exact L)


private abbrev proFiniteModels {X : Scheme.{u}} (R : Type u) [CommRing R]
    (F : proEtaleRingModules X (proEtaleConstantRing X R)) : Prop :=
  IsFinitelyPresentedLocallyConstantProEtaleModule F

private theorem proFiniteModels_of_isZero {X : Scheme.{u}} {R : Type u} [CommRing R]
    {F : proEtaleRingModules X (proEtaleConstantRing X R)} (hF : IsZero F) :
    proFiniteModels R F := by
  exact IsFinitelyPresentedLocallyConstantProEtaleModule_of_isZero hF

private theorem proFiniteModels_of_iso {X : Scheme.{u}} {R : Type u} [CommRing R]
    {F G : proEtaleRingModules X (proEtaleConstantRing X R)} (e : F ≅ G)
    (hF : proFiniteModels R F) : proFiniteModels R G := by
  exact IsFinitelyPresentedLocallyConstantProEtaleModule_of_iso e hF

private theorem proFiniteModels_pullback_comp {X Y Z : Scheme.{u}} {R : Type u}
    [CommRing R] [IsNoetherianRing R] (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : proEtaleRingModules Z (proEtaleConstantRing Z R))
    (h : proFiniteModels R (proEtaleConstantModulePullback g R F)) :
    proFiniteModels R (proEtaleConstantModulePullback (f ≫ g) R F) := by
  obtain ⟨e⟩ := proEtaleConstantModulePullback_comp g f R
  exact proFiniteModels_of_iso (e.app F).symm
    (proEtale_fp_localModels_pullback f R _ h)

private theorem common_pro_strata {X : Scheme.{u}} {R : Type u}
    [CommRing R] [IsNoetherianRing R]
    {F G : proEtaleRingModules X (proEtaleConstantRing X R)}
    (hF : IsAffineLocallyConstructibleProEtaleModuleSheaf X R F)
    (hG : IsAffineLocallyConstructibleProEtaleModuleSheaf X R G)
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ S : Stratification U.toScheme, ∀ a : Fin S.n,
      proFiniteModels R (proEtaleConstantModulePullback (S.immersion a ≫ U.ι) R F) ∧
      proFiniteModels R (proEtaleConstantModulePullback (S.immersion a ≫ U.ι) R G) := by
  obtain ⟨S, _, hS⟩ := hF U hU
  obtain ⟨T, _, hT⟩ := hG U hU
  refine ⟨S.inter T, fun a ↦ ?_⟩
  let i := (finProdFinEquiv.symm a).1
  let j := (finProdFinEquiv.symm a).2
  constructor
  · change proFiniteModels R
      (proEtaleConstantModulePullback
        ((pullback.fst (S.immersion i) (T.immersion j) ≫ S.immersion i) ≫ U.ι) R F)
    rw [Category.assoc]
    exact proFiniteModels_pullback_comp _ _ F (hS i)
  · change proFiniteModels R
      (proEtaleConstantModulePullback
        ((pullback.fst (S.immersion i) (T.immersion j) ≫ S.immersion i) ≫ U.ι) R G)
    rw [pullback.condition, Category.assoc]
    exact proFiniteModels_pullback_comp _ _ G (hT j)

private theorem proAffine_kernel_cokernel {X : Scheme.{u}} {R : Type u}
    [CommRing R] [IsNoetherianRing R]
    {F G : proEtaleRingModules X (proEtaleConstantRing X R)} (f : F ⟶ G)
    (hF : IsAffineLocallyConstructibleProEtaleModuleSheaf X R F)
    (hG : IsAffineLocallyConstructibleProEtaleModuleSheaf X R G) :
    IsAffineLocallyConstructibleProEtaleModuleSheaf X R (kernel f) ∧
      IsAffineLocallyConstructibleProEtaleModuleSheaf X R (cokernel f) := by
  constructor
  all_goals
    intro U hU
    obtain ⟨S, hS⟩ := common_pro_strata hF hG U hU
    refine ⟨S, S.isConstructible_stratum, fun a ↦ ?_⟩
    let L := proEtaleConstantModulePullbackFunctor (S.immersion a ≫ U.ι) R
    obtain ⟨hK, hC⟩ := (proEtale_fp_localModels_serre (S.domain a) R).1
      _ _ (L.map f) (hS a).1 (hS a).2
    first
    | exact proFiniteModels_of_iso (PreservesKernel.iso L f).symm hK
    | exact proFiniteModels_of_iso (PreservesCokernel.iso L f).symm hC

private theorem proAffine_extension {X : Scheme.{u}} {R : Type u}
    [CommRing R] [IsNoetherianRing R]
    (S : ShortComplex (proEtaleRingModules X (proEtaleConstantRing X R)))
    (hS : S.ShortExact)
    (h₁ : IsAffineLocallyConstructibleProEtaleModuleSheaf X R S.X₁)
    (h₃ : IsAffineLocallyConstructibleProEtaleModuleSheaf X R S.X₃) :
    IsAffineLocallyConstructibleProEtaleModuleSheaf X R S.X₂ := by
  intro U hU
  obtain ⟨T, hT⟩ := common_pro_strata h₁ h₃ U hU
  refine ⟨T, T.isConstructible_stratum, fun a ↦ ?_⟩
  let L := proEtaleConstantModulePullbackFunctor (T.immersion a ≫ U.ι) R
  exact (proEtale_fp_localModels_serre (T.domain a) R).2
    (S.map L) (hS.map_of_exact L) (hT a).1 (hT a).2

/-- Global constructible fixed-scalar module sheaves over a Noetherian ring are
closed under extensions, without a finite-underlying-ring assumption.
Source: Stacks Project, Modules on Sites, Tag 093U (3)
(blueprint: lem-sfb-discrete-noetherian-constructible-serre).
Proof: take the fibre-product common refinement of the two finite stratifications.
Exact immersion pullback gives extensions of finite locally constant sheaves on each
stratum. The finite-presentation lifting argument noetherian_flc_of_shortExact above
makes the middle sheaf locally constant, and stalkwise exactness makes its values
finitely generated. The common refinement witnesses global constructibility. -/
theorem IsConstructibleSheaf.of_shortExact_of_isNoetherianRing
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₂ := by
  obtain ⟨T₁, hT₁⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := S.X₁)
  obtain ⟨T₃, hT₃⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := S.X₃)
  refine ⟨T₁.inter T₃, fun k ↦ ?_⟩
  have h₁ := (T₁.inter_refines_left T₃).isFiniteLocallyConstantSheaf_upperStar S.X₁ hT₁ k
  have h₃ := (T₁.inter_refines_right T₃).isFiniteLocallyConstantSheaf_upperStar S.X₃ hT₃ k
  let F := Etale.upperStar (ModuleCat.{u + 1} Λ) ((T₁.inter T₃).immersion k)
  have : PreservesFiniteLimits F := inferInstance
  have : PreservesFiniteColimits F := inferInstance
  have hS' : (S.map F).ShortExact := hS.map_of_exact F
  have : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (S.map F).X₁ := h₁
  have : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (S.map F).X₃ := h₃
  exact noetherian_flc_of_shortExact hS'

end Scheme

/-- Constructible etale module sheaves contain zero and are closed under kernels, cokernels
and extensions. Source: Stacks Project, Tag 03RZ (3)
(blueprint: lem-sfb-discrete-noetherian-constructible-serre).

Proof plan (the same six steps apply on either small site):
1. Finite presentation implies finite generation. Conversely, over the Noetherian ring,
`Module.finitePresentation_of_finite` gives finite presentation of each finite module.
2. The geometric inverse image preserves colimits and finite limits. A constant set sheaf
is a coproduct of terminal sheaves, so inverse image preserves constant sheaves naturally
in their values; applying this to the ring and module operations preserves constants as
ring and module sheaves, with no finiteness condition on their underlying sets.
3. The induced action agrees with module inverse image: both constant coefficient maps
are adjoint to the constant-section map. Abelian inverse image is exact, and module
kernels and cokernels have the corresponding underlying abelian kernels and cokernels.
Thus restriction to any stratum preserves kernels, cokernels and short exact sequences.
4. On every affine open, intersect the two finite stratifications by fibre products.
Pull back and refine the trivializing covers; localization exchange and inverse-image
composition identify the restrictions with the same constant modules on the common strata.
5. On each common stratum apply Tag 093U (3), the recorded locally constant finite-type
weak-Serre theorem, to the restricted map or exact sequence. Convert its finite-type
values back to finitely presented values by step 1. The common partition is a witness.
6. The zero module is finitely presented; on every affine open the identity stratum
trivializes the zero sheaf. The empty open also admits the empty partition.

The DAG inputs for these steps are:
- step 1: `def-sc-finitely-presented-module` and
  `lem-sc-noetherian-finite-module-finite-presentation`;
- step 2: `lem-weil-pbc-etale-inverse-image-algebraic-structures`,
  `def-weil-proetale-inverse-image`, `lem-weil-pbc-left-exact-site-inverse-image-tensor`,
  and `def-weil-pbc-constant-sheaf`;
- step 3: `lem-weil-pbc-site-pullback-abelian-exact` and
  `def-weil-sheaf-of-modules-category`;
- step 4: `lem-weil-pbc-constructible-stratification-intersection`,
  `lem-weil-pbc-site-morphism-composition`, `lem-weil-pbc-etale-covering-base-change`,
  and `lem-weil-pbc-localize-ringed-site-morphism`;
- step 5: `lem-weil-pbc-locally-constant-derived-serre`, the Noetherian finite-presentation
  lemma of step 1, `def-weil-pbc-proetale-site`, and `def-weil-pbc-etale-site`;
- step 6: the constant zero module and the identity stratum. -/
theorem etale_discreteNoetherian_constructible_serre
    (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] [IsNoetherianRing R] :
    Etale.constructibleNoetherianModules X R (0 : ringedSiteModules.{u + 1}
      ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of R))) ∧
    (∀ (F G : ringedSiteModules.{u + 1}
        ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of R)))
        (f : F ⟶ G),
      Etale.constructibleNoetherianModules X R F →
        Etale.constructibleNoetherianModules X R G →
          Etale.constructibleNoetherianModules X R (kernel f) ∧
          Etale.constructibleNoetherianModules X R (cokernel f)) ∧
    (∀ S : ShortComplex (ringedSiteModules.{u + 1}
        ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of R))),
      S.ShortExact → Etale.constructibleNoetherianModules X R S.X₁ →
        Etale.constructibleNoetherianModules X R S.X₃ →
          Etale.constructibleNoetherianModules X R S.X₂) := by
  let E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ≌
      ringedSiteModules.{u + 1}
        ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of R)) :=
    CategoryTheory.Equivalence.mk (Scheme.etaleConstantModuleFunctor X R)
      (Scheme.etaleConstantModuleRestrictionFunctor X R)
      (Scheme.etaleConstantModuleUnitIso X R) (Scheme.etaleConstantModuleCounitIso X R)
  let Q := Scheme.etaleConstantModuleRestrictionFunctor X R
  have : Q.IsEquivalence := E.isEquivalence_inverse
  refine ⟨Scheme.etaleAffine_of_isZero (Q.map_isZero (isZero_zero _)), ?_, ?_⟩
  · intro F G f hF hG
    obtain ⟨hK, hC⟩ := Scheme.etaleAffine_kernel_cokernel (Q.map f) hF hG
    exact ⟨Scheme.etaleAffine_of_iso (PreservesKernel.iso Q f).symm hK,
      Scheme.etaleAffine_of_iso (PreservesCokernel.iso Q f).symm hC⟩
  · intro S hS h₁ h₃
    exact Scheme.etaleAffine_extension (S.map Q) (hS.map_of_exact Q) h₁ h₃

/-- Constructible pro-etale module sheaves contain zero and are closed under kernels,
cokernels and extensions. Source: Stacks Project, Tag 09B5, with the direct common-partition
proof of Tags 03RZ (3) and 093U (3)
(blueprint: lem-sfb-discrete-noetherian-constructible-serre).

Proof plan:
1. Finite presentation implies finite generation, and Noetherianity gives the converse.
2. The covering-preserving base-change functor defines a geometric inverse image. It
preserves finite limits and colimits, hence constant sheaves as coproducts of terminals,
naturally in their values and therefore compatibly with ring and module operations.
3. The canonical coefficient structure map is this constant-ring identification: both
maps are adjoint to the constant-section family. Thus the tensor-defined module pullback
is the induced module inverse image. Abelian inverse image is exact; underlying abelian
kernels and cokernels compute those of module sheaves, so all stratum restrictions are exact.
4. For every affine open take the fibre-product common refinement of the two finite
constructible locally closed partitions. Pull back the two trivializing covers, using
cover preservation. Localization exchange identifies the pulled-back constant local
models on the localized sites, and inverse-image composition identifies restrictions.
5. Apply the arbitrary-site weak-Serre theorem, Tag 093U (3), on each common stratum.
Take small skeletons in the module universe; no points or finite underlying coefficient
sets are needed. Step 1 makes the resulting constant module values finitely presented.
6. The identity stratum and the constant zero module prove zero constructible on each
affine open; the empty partition is also allowed on the empty open. The preceding steps
prove the displayed kernel, cokernel and extension clauses affine-locally.

The DAG inputs for these steps are:
- step 1: `def-sc-finitely-presented-module` and
  `lem-sc-noetherian-finite-module-finite-presentation`;
- step 2: `lem-weil-pbc-etale-inverse-image-algebraic-structures`,
  `def-weil-proetale-inverse-image`, `lem-weil-pbc-left-exact-site-inverse-image-tensor`,
  and `def-weil-pbc-constant-sheaf`;
- step 3: `lem-weil-pbc-site-pullback-abelian-exact` and
  `def-weil-sheaf-of-modules-category`;
- step 4: `lem-weil-pbc-constructible-stratification-intersection`,
  `lem-weil-pbc-site-morphism-composition`, `lem-weil-pbc-etale-covering-base-change`,
  and `lem-weil-pbc-localize-ringed-site-morphism`;
- step 5: `lem-weil-pbc-locally-constant-derived-serre`, the Noetherian finite-presentation
  lemma of step 1, `def-weil-pbc-proetale-site`, and `def-weil-pbc-etale-site`;
- step 6: the constant zero module and the identity stratum. -/
theorem proEtale_discreteNoetherian_constructible_serre
    (X : Scheme.{u}) (R : Type u) [CommRing R] [IsNoetherianRing R] :
    Scheme.IsAffineLocallyConstructibleProEtaleModuleSheaf X R
      (0 : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X R)) ∧
    (∀ (F G : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X R))
        (f : F ⟶ G),
      Scheme.IsAffineLocallyConstructibleProEtaleModuleSheaf X R F →
        Scheme.IsAffineLocallyConstructibleProEtaleModuleSheaf X R G →
          Scheme.IsAffineLocallyConstructibleProEtaleModuleSheaf X R (kernel f) ∧
          Scheme.IsAffineLocallyConstructibleProEtaleModuleSheaf X R (cokernel f)) ∧
    (∀ S : ShortComplex (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X R)),
      S.ShortExact → Scheme.IsAffineLocallyConstructibleProEtaleModuleSheaf X R S.X₁ →
        Scheme.IsAffineLocallyConstructibleProEtaleModuleSheaf X R S.X₃ →
          Scheme.IsAffineLocallyConstructibleProEtaleModuleSheaf X R S.X₂) := by
  refine ⟨?_, ?_, fun S hS h₁ h₃ ↦ Scheme.proAffine_extension S hS h₁ h₃⟩
  · intro U _
    refine ⟨Scheme.Stratification.trivial U.toScheme, fun a ↦
      (Scheme.Stratification.trivial U.toScheme).isConstructible_stratum a, fun a ↦ ?_⟩
    exact Scheme.proFiniteModels_of_isZero
      ((Scheme.proEtaleConstantModulePullbackFunctor (_ ≫ U.ι) R).map_isZero
        (isZero_zero _))
  · intro F G f hF hG
    exact Scheme.proAffine_kernel_cokernel f hF hG

end AlgebraicGeometry
