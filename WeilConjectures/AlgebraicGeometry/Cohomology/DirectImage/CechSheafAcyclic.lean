/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechSheaf
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp

/-!
# The sheafified Čech complex computes the higher direct images

Let `f : X ⟶ T` be separated and `V : ι → X.Opens` a finite cover of `X` such that every finite
intersection `V_y = V (y 0) ⊓ ⋯ ⊓ V (y k)` is affine over `T`. For a quasi-coherent `𝒪_X`-module
`ℱ`, the terms `⨁_y j_* (ℱ|_{V_y})` of the sheafified Čech complex `𝒞(V, ℱ)` are `f_*`-acyclic,
so `R^q f_* ℱ ≅ H^q(f_* 𝒞(V, ℱ))`
(`AlgebraicGeometry.Scheme.Modules.higherDirectImageIsoCechSheaf`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y T : Scheme.{u}}

/-- Restriction along an open immersion preserves monomorphisms. -/
instance (j : Y ⟶ X) [IsOpenImmersion j] : (restrictFunctor j).PreservesMonomorphisms :=
  ⟨fun φ _ ↦ mono_of_injective_app _ fun W ↦ injective_app_of_mono' (j ''ᵁ W) φ⟩

/-- The pushforward along an open immersion preserves injective objects. -/
instance injective_pushforward_obj (j : Y ⟶ X) [IsOpenImmersion j] (I : Y.Modules) [Injective I] :
    Injective ((pushforward j).obj I) :=
  Injective.injective_of_adjoint (restrictAdjunction j) I

instance (f : X ⟶ T) : PreservesFiniteLimits (pushforward f) :=
  have := (pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits.{0, 0}
  inferInstance

/-- **Pushing forward along an affine open immersion.** Let `j : Y ⟶ X` be an affine open
immersion and `G` a quasi-coherent `𝒪_Y`-module. Then `j_*` sends an injective resolution of `G`
to an injective resolution of `j_* G`, since `R^q j_* G = 0` for `q > 0`. -/
noncomputable def injectiveResolutionPushforward (j : Y ⟶ X) [IsOpenImmersion j] [IsAffineHom j]
    [HasInjectiveResolutions Y.Modules] (G : Y.Modules)
    [SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) G] (I : InjectiveResolution G) :
    InjectiveResolution ((pushforward j).obj G) where
  cocomplex := ((pushforward j).mapHomologicalComplex _).obj I.cocomplex
  injective n := injective_pushforward_obj j (I.cocomplex.X n)
  ι := (pushforward j).mapResolution I.ι
  quasiIso := ⟨fun n ↦ by
    cases n with
    | zero =>
      rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
      · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
          ⟨I.exact₀.map_of_mono_of_preservesKernel (pushforward j) inferInstance inferInstance,
            inferInstanceAs (Mono ((pushforward j).map (I.ι.f 0)))⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp [Functor.mapResolution]) (by simp)
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _),
        HomologicalComplex.exactAt_iff_isZero_homology]
      exact (isZero_higherDirectImage_of_isAffineHom j G (Nat.succ_pos n)).of_iso
        (I.isoRightDerivedObj (pushforward j) (n + 1)).symm⟩

/-- **Acyclicity of `j_* G`.** Let `j : Y ⟶ X` be an affine open immersion with `j ≫ f` affine,
and `G` a quasi-coherent `𝒪_Y`-module. Then `j_* G` is `f_*`-acyclic: an injective resolution `I`
of `G` gives the injective resolution `j_* I` of `j_* G`, and
`R^q f_* (j_* G) = H^q(f_* j_* I) = R^q (j ≫ f)_* G = 0` for `q > 0`. -/
theorem rightAcyclic_pushforward_obj (j : Y ⟶ X) (f : X ⟶ T) [IsOpenImmersion j] [IsAffineHom j]
    [IsAffineHom (j ≫ f)] [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Y.Modules]
    (G : Y.Modules) [SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) G] :
    (pushforward f).rightAcyclic ((pushforward j).obj G) := by
  intro q
  let I := injectiveResolution G
  let J := injectiveResolutionPushforward j G I
  refine (isZero_higherDirectImage_of_isAffineHom (j ≫ f) G (Nat.succ_pos q)).of_iso ?_
  refine J.isoRightDerivedObj (pushforward f) (q + 1) ≪≫
    (HomologicalComplex.homologyFunctor _ _ (q + 1)).mapIso ?_ ≪≫
    (I.isoRightDerivedObj (pushforward (j ≫ f)) (q + 1)).symm
  exact (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).symm.app _ ≪≫
    (NatIso.mapHomologicalComplex (pushforwardComp j f) _).app I.cocomplex

lemma rightAcyclic_biproduct {C D : Type*} [Category* C] [Category* D] [Abelian C]
    [HasInjectiveResolutions C] [Abelian D] (F : C ⥤ D) [F.Additive] {J : Type*} [Finite J]
    (g : J → C) (hg : ∀ j, F.rightAcyclic (g j)) : F.rightAcyclic (⨁ g) := by
  intro q
  refine IsZero.of_iso ?_ ((F.rightDerived (q + 1)).mapBiproduct g)
  rw [IsZero.iff_id_eq_zero]
  exact biproduct.hom_ext _ _ fun j ↦ (hg j q).eq_of_tgt _ _

variable (ℱ : X.Modules) {ι : Type u} [Fintype ι] [DecidableEq ι] (V : ι → X.Opens)

/-- The terms of the sheafified Čech complex of a quasi-coherent module are `f_*`-acyclic, for
`f` separated and a family whose finite intersections are affine over `T`. -/
theorem rightAcyclic_cechSheafX (f : X ⟶ T) [IsSeparated f] [HasInjectiveResolutions X.Modules]
    (hV : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineHom ((⨅ l, V (y l)).ι ≫ f))
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (k : ℕ) :
    (pushforward f).rightAcyclic (cechSheafX ℱ V k) := by
  refine rightAcyclic_biproduct _ _ fun y ↦ ?_
  have := hV k y
  have : IsAffineHom (⨅ l, V (y l)).ι := IsAffineHom.of_comp _ f
  have := isGrothendieckAbelian (⨅ l, V (y l)).toScheme
  exact rightAcyclic_pushforward_obj _ f _

/-- **The sheafified Čech complex computes the higher direct images.** For `f : X ⟶ T`
separated, a finite cover `V` of `X` whose finite intersections are affine over `T` and a
quasi-coherent `ℱ`, `R^q f_* ℱ ≅ H^q(f_* 𝒞(V, ℱ))`. -/
noncomputable def higherDirectImageIsoCechSheaf (f : X ⟶ T) [IsSeparated f]
    [HasInjectiveResolutions X.Modules]
    (hV : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineHom ((⨅ l, V (y l)).ι ≫ f))
    (hcov : ⨆ i, V i = ⊤) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    (higherDirectImage f q).obj ℱ ≅
      (((pushforward f).mapHomologicalComplex _).obj (cechSheafComplex ℱ V)).homology q :=
  haveI : Fact (⨆ i, V i = ⊤) := ⟨hcov⟩
  (pushforward f).rightDerivedObjIsoOfResolution (cechSheafι ℱ V)
    (rightAcyclic_cechSheafX ℱ V f hV) q

end AlgebraicGeometry.Scheme.Modules
