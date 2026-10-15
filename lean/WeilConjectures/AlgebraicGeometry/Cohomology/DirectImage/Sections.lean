/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.AlgebraicGeometry.HigherDirectImageSectionDenominators
import Sheaf.AlgebraicGeometry.HigherDirectImageSectionTorsion
import Sheaf.AlgebraicGeometry.ModuleCohomologySourceComparison
import Sheaf.AlgebraicGeometry.LerayDegenerateSections
import Sheaf.AlgebraicGeometry.LocalUniformHigherDirectImageBound
import Sheaf.Topology.RestrictInjectiveResolution
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-!
# Sections of higher direct images over an affine base

Over an affine base, the sections of `R^q f_* ℱ` are the cohomology `H^q(X, ℱ)` for a
quasi-compact separated morphism and a quasi-coherent `ℱ`. Also the compatibility of higher
direct images with flat base change and with restriction to opens, their quasi-coherence, and
their vanishing in high degrees.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}
variable (f : X ⟶ T) (ℱ : X.Modules)

section QuasiCoherence

variable [QuasiCompact f] [QuasiSeparated f] [HasInjectiveResolutions X.Modules]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

set_option backward.isDefEq.respectTransparency.types true in
/-- **Quasi-coherence of the higher direct images.** For `f : X ⟶ T` quasi-compact and
quasi-separated and `ℱ` a quasi-coherent `𝒪_X`-module, the higher direct image `R^q f_* ℱ` is a
quasi-coherent `𝒪_T`-module for every `q` [Stacks, Tag 01XJ].

Proof: the two localization assertions for sections of the higher direct image give the
quasi-coherence criterion `isQuasicoherent_of_forall_isAffineOpen`: sections on a principal
open lift after multiplying by a power of its defining function, and sections restricting
to zero are annihilated by a power. Apply the criterion and restrict to each affine open.
The two assertions are stated in separate acyclic modules, with proofs through localization
of cohomology (Stacks, Tag 09MR) and the cohomology-presheaf description (Tag 01E4).

(blueprint: lem-pc-sections-higher-direct-image-quasi-coherent)
(blueprint: `sk-thm-picard-coherence`)
(blueprint: new-higher-direct-image-affine-local-qcoherent) -/
theorem higherDirectImage_isQuasicoherent_on_affines (q : ℕ) :
    ∀ U : T.affineOpens,
      (((higherDirectImage f q).obj ℱ).over U.1).IsQuasicoherent := by
  have hqc : ((higherDirectImage f q).obj ℱ).IsQuasicoherent :=
    isQuasicoherent_of_forall_isAffineOpen _
      (fun W hW a s ↦ higherDirectImage_section_clearDenominators f ℱ q W hW a s)
      (fun W hW a t ht ↦ higherDirectImage_section_pow_annihilates f ℱ q W hW a t ht)
  intro U
  exact SheafOfModules.isQuasicoherent_over _ U.1

/-- Quasi-coherence is local on affine opens of the base. -/
theorem isQuasicoherent_higherDirectImage (q : ℕ) :
    ((higherDirectImage f q).obj ℱ).IsQuasicoherent := by
  have hU : ∀ U : T.affineOpens, (((higherDirectImage f q).obj ℱ).over U.1).IsQuasicoherent :=
    higherDirectImage_isQuasicoherent_on_affines f ℱ q
  exact SheafOfModules.IsQuasicoherent.of_coversTop
    ((higherDirectImage f q).obj ℱ) (fun U : T.affineOpens => U.1)
    ((Opens.coversTop_iff _ _).mpr (iSup_affineOpens_eq_top T))

end QuasiCoherence

set_option backward.isDefEq.respectTransparency.types true in
private theorem inverse_comp_naturality {C D : Type*} [Category C] [Category D]
    {F G H : C ⥤ D} (τ : F ⟶ G) (c : F ≅ H) {M N : C} (φ : M ⟶ N)
    [IsIso (τ.app M)] [IsIso (τ.app N)] :
    G.map φ ≫ inv (τ.app N) ≫ c.hom.app N =
      inv (τ.app M) ≫ c.hom.app M ≫ H.map φ := by
  have hinv : G.map φ ≫ inv (τ.app N) = inv (τ.app M) ≫ F.map φ := by
    apply (cancel_mono (τ.app N)).1
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.assoc,
      τ.naturality φ, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [← Category.assoc, hinv, Category.assoc, c.hom.naturality]

set_option backward.isDefEq.respectTransparency.types true in
/-- **The sections of the higher direct images over an affine base, naturally.** Over an affine
base, for `f` quasi-compact and separated, the global sections of `R^q f_* ℱ` are the sheaf
cohomology `H^q(X, ℱ)`, by additive isomorphisms natural in the quasi-coherent module `ℱ`.

This is the comparison between the right derived functors of `f_*` inside `X.Modules` and the
`Ext`-groups in abelian sheaves of `AlgebraicGeometry.Scheme.Modules.H`. It holds because
injective `𝒪_X`-modules are flasque, the pushforward of a flasque module is flasque, flasque
sheaves are acyclic for `H`, and, `T` being affine and `R^p f_* ℱ` quasi-coherent, the global
sections functor of `T` is exact on them [Stacks, Tags 01XJ and 0BDY]. -/
theorem exists_addEquiv_sections_higherDirectImage_H [IsAffine T] [QuasiCompact f]
    [IsSeparated f] [HasInjectiveResolutions X.Modules] (q : ℕ) :
    ∃ e : ∀ (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ],
        Γ((higherDirectImage f q).obj ℱ, ⊤) ≃+ ℱ.H q,
      ∀ (ℱ 𝒢 : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
        [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) 𝒢] (φ : ℱ ⟶ 𝒢)
        (x : Γ((higherDirectImage f q).obj ℱ, ⊤)),
        e 𝒢 (((higherDirectImage f q).map φ).app ⊤ x) = H.map φ q (e ℱ x) := by
  classical
  obtain ⟨a, ha⟩ := exists_moduleCohomology_source_comparison X q
  obtain ⟨ε, _, hε⟩ := exists_lerayEdge_isIso_of_vanishing f
  have hvan (M : X.Modules) [M.IsQuasicoherent] (n p : ℕ) (hp : 0 < p) :
      IsZero ((RingedSpace.moduleCohomology T.toRingedSpace p).obj
        ((higherDirectImage f n).obj M)) := by
    have := isQuasicoherent_higherDirectImage f M n
    obtain ⟨b, _⟩ := exists_moduleCohomology_source_comparison T p
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    have hs : Subsingleton (((higherDirectImage f n).obj M).H (k + 1)) :=
      subsingleton_H_succ_of_isAffine ((higherDirectImage f n).obj M) k
    have : Subsingleton ((RingedSpace.moduleCohomology T.toRingedSpace (k + 1)).obj
        ((higherDirectImage f n).obj M)) :=
      (b ((higherDirectImage f n).obj M)).toEquiv.injective
        |>.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  have hi (M : X.Modules) [M.IsQuasicoherent] : IsIso ((ε q).app M) :=
    hε M (hvan M) q
  let e (M : X.Modules) [M.IsQuasicoherent] :
      Γ((higherDirectImage f q).obj M, ⊤) ≃+ M.H q :=
    (asIso ((ε q).app M)).symm.addCommGroupIsoToAddEquiv.trans (a M)
  refine ⟨e, ?_⟩
  intro M N _ _ φ x
  have h := ConcreteCategory.congr_hom
    (inverse_comp_naturality (ε q) (Iso.refl _) φ) x
  change inv ((ε q).app N) (((higherDirectImage f q).map φ).app ⊤ x) =
    ((RingedSpace.moduleCohomology X.toRingedSpace q).map φ).hom
      (inv ((ε q).app M) x) at h
  change a N (inv ((ε q).app N) (((higherDirectImage f q).map φ).app ⊤ x)) = _
  rw [h]
  exact ha M N φ (inv ((ε q).app M) x)

set_option backward.isDefEq.respectTransparency.types true in
/-- **The sections of the higher direct images over an affine base, linearly.** Over an affine
base the global sections of the `q`-th higher direct image are the sheaf cohomology of `ℱ`,
`Γ(T, R^q f_* ℱ) ≅ H^q(X, ℱ)`, by an isomorphism which is linear along `f^♯ : Γ(T, ⊤) → Γ(X, ⊤)`.

This is the comparison between the two cohomology theories used in the Picard-framework block:
the right derived functors of `f_*` inside `X.Modules` on the one hand, and the `Ext`-groups in
abelian sheaves of `AlgebraicGeometry.Scheme.Modules.H` on the other. The additive comparison
is `AlgebraicGeometry.Scheme.Modules.exists_addEquiv_sections_higherDirectImage_H`; being natural
in `ℱ`, it is compatible with multiplication by global functions of `T`, which `R^q f_*` turns
into multiplication by their images in `Γ(X, ⊤)`
(`AlgebraicGeometry.Scheme.Modules.higherDirectImage_map_smulHom`).

Over `T = Spec κ` for a field `κ`, this is the identification of the `q`-th direct image to a
point with `H^q` as `κ`-vector spaces, used in the local model of the proof of
`thm-pc-semicontinuity-base-change`. -/
theorem exists_bijective_semilinearMap_sections_higherDirectImage_H [IsAffine T] [QuasiCompact f]
    [IsSeparated f] [HasInjectiveResolutions X.Modules]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    ∃ e : Γ((higherDirectImage f q).obj ℱ, ⊤) →ₛₗ[f.appTop.hom] ℱ.H q, Function.Bijective e := by
  obtain ⟨e, he⟩ := exists_addEquiv_sections_higherDirectImage_H f q
  refine ⟨{ toFun := e ℱ, map_add' := map_add _, map_smul' := fun a x ↦ ?_ }, (e ℱ).bijective⟩
  have h : a • x = ((higherDirectImage f q).map (ℱ.smulHom (f.appTop a))).app ⊤ x := by
    rw [higherDirectImage_map_smulHom, smulHom_app_apply]
    congr 1
    exact (congrArg (fun φ ↦ φ a) (T.presheaf.map_id _)).symm
  rw [h, he]
  rfl

set_option backward.isDefEq.respectTransparency.types true in
/-- Over an affine base the global sections of the `q`-th higher direct image are the sheaf
cohomology of `ℱ`: `Γ(T, R^q f_* ℱ) ≅ H^q(X, ℱ)`. See
`AlgebraicGeometry.Scheme.Modules.exists_bijective_semilinearMap_sections_higherDirectImage_H`
for the linearity of this isomorphism. -/
theorem nonempty_sections_higherDirectImage_iso_H [IsAffine T] [QuasiCompact f] [IsSeparated f]
    [HasInjectiveResolutions X.Modules]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Nonempty (Γ((higherDirectImage f q).obj ℱ, ⊤) ≃+ ℱ.H q) :=
  have ⟨e, he⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H f ℱ q
  ⟨AddEquiv.ofBijective e.toAddMonoidHom he⟩

set_option backward.isDefEq.respectTransparency.types true in
/-- **The fibre dimension is the dimension of the direct image to the point.** For `f`
quasi-compact and separated, `h^q(t) = dim_{κ(t)} H^q(X_t, ℱ_t)` is the dimension of the global
sections of `R^q (f_t)_* ℱ_t` for the fibre `f_t : X_t ⟶ Spec κ(t)`, as a vector space over the
field `Γ(Spec κ(t), ⊤) ≅ κ(t)`. -/
theorem hFiber_eq_finrank_sections_higherDirectImage [QuasiCompact f] [IsSeparated f] (t : T)
    [HasInjectiveResolutions (f.fiber t).Modules]
    [SheafOfModules.IsQuasicoherent (R := (f.fiber t).ringCatSheaf)
      ((Modules.pullback (f.fiberι t)).obj ℱ)] (q : ℕ) :
    ℱ.hFiber f q t = Module.finrank Γ(Spec (T.residueField t), ⊤)
      Γ((higherDirectImage (f.fiberToSpecResidueField t) q).obj
        ((Modules.pullback (f.fiberι t)).obj ℱ), ⊤) := by
  have : IsSeparated (f.fiberToSpecResidueField t) := by
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  have : QuasiCompact (f.fiberToSpecResidueField t) := by
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  obtain ⟨e, he⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H
    (f.fiberToSpecResidueField t) ((Modules.pullback (f.fiberι t)).obj ℱ) q
  let j := (AddEquiv.ofBijective e.toAddMonoidHom he).symm
  let := f.fiberOverSpecResidueField t
  refine congrArg Cardinal.toNat (rank_eq_of_equiv_equiv _ j
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (T.residueField t)).inv) ?_)
  intro c h
  obtain ⟨y, rfl⟩ := he.2 h
  have hc : c • e y = e ((Scheme.ΓSpecIso (T.residueField t)).inv c • y) := by
    rw [smul_H_eq_globalSectionsRingHom_smul, e.map_smulₛₗ]
    rfl
  have hj (z) : j (e z) = z := (AddEquiv.ofBijective e.toAddMonoidHom he).symm_apply_apply z
  rw [hc, hj, hj]

set_option backward.isDefEq.respectTransparency.types true in
/-- **The direct images to the spectrum of a field.** For a scheme `X` over a field `K`, with
structure morphism quasi-compact and separated, and a quasi-coherent `𝒪_X`-module `ℱ`, the
global sections of `R^q f_* ℱ` are `H^q(X, ℱ)` as `K`-vector spaces. This is
`AlgebraicGeometry.Scheme.Modules.exists_bijective_semilinearMap_sections_higherDirectImage_H`
over `Spec K`, where `K` acts on both sides through `Γ(Spec K, ⊤)`. -/
theorem nonempty_moduleSpecΓFunctor_obj_higherDirectImage_linearEquiv_H (K : Type u) [Field K]
    [X.Over (Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))] [IsSeparated (X ↘ Spec (.of K))]
    [HasInjectiveResolutions X.Modules]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Nonempty ((moduleSpecΓFunctor (R := .of K)).obj
      ((higherDirectImage (X ↘ Spec (.of K)) q).obj ℱ) ≃ₗ[K] ℱ.H q) := by
  obtain ⟨e, he⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H
    (X ↘ Spec (.of K)) ℱ q
  let M := (moduleSpecΓFunctor (R := .of K)).obj ((higherDirectImage (X ↘ Spec (.of K)) q).obj ℱ)
  refine ⟨LinearEquiv.ofBijective (M := M)
    { toFun := e, map_add' := e.map_add, map_smul' := fun c x ↦ ?_ } he⟩
  let y : Γ((higherDirectImage (X ↘ Spec (.of K)) q).obj ℱ, ⊤) := x
  have h : (c • x : M) = (Scheme.ΓSpecIso (.of K)).inv c • y := smul_top_eq (R := .of K) _ c y
  exact (congrArg e h).trans ((e.map_smulₛₗ _ y).trans
    (smul_H_eq_globalSectionsRingHom_smul K ℱ q c (e y)).symm)

open MonoidalCategory in
set_option backward.isDefEq.respectTransparency.types true in
private theorem projection_naturality (N : T.Modules) {M M' : X.Modules} (φ : M ⟶ M') :
    ((pushforward f).map φ ▷ N) ≫ projectionHom f M' N =
      projectionHom f M N ≫ (pushforward f).map (φ ▷ (pullback f).obj N) := by
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification
    ((pushforward f).obj M) N).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 T.ringCatSheaf.obj)).homEquiv
    (((pushforward f).obj M).val ⊗ N.val) _).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply TensorProduct.ext' (R := Γ(T, U.unop))
    (M := Γ((pushforward f).obj M, U.unop)) (N := Γ(N, U.unop))
    (R₂ := Γ(T, U.unop)) (σ₁₂ := RingHom.id _)
    (P₂ := Γ((pushforward f).obj (M' ⊗ (pullback f).obj N), U.unop))
  intro x n
  change (((pushforward f).map φ ▷ N) ≫ projectionHom f M' N).app U.unop
      (tmulSection x n) =
    (projectionHom f M N ≫ (pushforward f).map (φ ▷ (pullback f).obj N)).app U.unop
      (tmulSection x n)
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, whiskerRight_app_tmulSection,
    projectionHom_app_tmulSection]
  exact (whiskerRight_app_tmulSection φ x _).symm

set_option backward.isDefEq.respectTransparency.types true in
private theorem injective_restrict_open {Y Z : Scheme.{u}} (j : Y ⟶ Z)
    [IsOpenImmersion j] (M : Z.Modules) [Injective M] :
    Injective ((restrictFunctor j).obj M) := by
  let U := j.opensRange
  let e := IsOpenImmersion.isoOfRangeEq j U.ι (by simp [U])
  have h₁ : Injective ((SheafOfModules.overFunctor Z.ringCatSheaf U).obj M) :=
    (RingedSpace.restrict_injectiveResolution Z.toRingedSpace U M
      (InjectiveResolution.self M)).2 0
  have : IsIso e.hom := inferInstance
  let E : U.toScheme.Modules ≌ Y.Modules := CategoryTheory.Equivalence.mk
    (restrictFunctor e.hom) (restrictFunctor e.inv)
    ((restrictFunctorId).symm ≪≫ restrictFunctorCongr e.inv_hom_id.symm ≪≫
      restrictFunctorComp e.inv e.hom)
    ((restrictFunctorComp e.hom e.inv).symm ≪≫ restrictFunctorCongr e.hom_inv_id ≪≫
      restrictFunctorId)
  have : (restrictFunctor e.hom).IsEquivalence := E.isEquivalence_functor
  have h₂ := (overEquiv U).functor.injective_obj
    ((SheafOfModules.overFunctor Z.ringCatSheaf U).obj M)
  have hI := (restrictFunctor e.hom).injective_obj
    ((overEquiv U).functor.obj ((SheafOfModules.overFunctor Z.ringCatSheaf U).obj M))
  let c := (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (overFunctorEquiv U) (restrictFunctor e.hom) ≪≫
    (restrictFunctorComp e.hom U.ι).symm ≪≫
    restrictFunctorCongr (IsOpenImmersion.isoOfRangeEq_hom_fac j U.ι _)
  exact Injective.of_iso (c.app M) hI

set_option backward.isDefEq.respectTransparency.types true in
private noncomputable def pushforward_restrict_square {T' X' : Scheme.{u}}
    (g : T' ⟶ T) [IsOpenImmersion g] (g' : X' ⟶ X) [IsOpenImmersion g']
    (f' : X' ⟶ T') (sq : IsPullback g' f' f g) :
    pushforward f ⋙ restrictFunctor g ≅ restrictFunctor g' ⋙ pushforward f' := by
  unfold restrictFunctor pushforward
  refine SheafOfModules.pushforwardComp _ _ ≪≫ ?_ ≪≫
    (SheafOfModules.pushforwardComp _ _).symm
  let e : g.opensFunctor ⋙ Opens.map f.base ≅ Opens.map f'.base ⋙ g'.opensFunctor :=
    NatIso.ofComponents (fun W ↦ eqToIso
      (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback sq.flip W).symm)
  refine SheafOfModules.pushforwardCongr₂ _ e.symm ?_
  ext W x
  change X.presheaf.map
      (eqToHom (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
        sq.flip W.unop)).op
      (f.app (g ''ᵁ W.unop) ((g.appIso W.unop).inv x)) =
    (g'.appIso (f' ⁻¹ᵁ W.unop)).inv (f'.app W.unop x)
  have h : f.app (g ''ᵁ W.unop) ≫
      X.presheaf.map (eqToHom
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
          sq.flip W.unop)).op ≫ (g'.appIso (f' ⁻¹ᵁ W.unop)).hom =
      (g.appIso W.unop).hom ≫ f'.app W.unop := by
    simp only [Scheme.Hom.appIso_hom', Scheme.Hom.app_eq_appLE,
      Scheme.Hom.map_appLE, Scheme.Hom.appLE_comp_appLE]
    congr 1
    exact sq.w
  have hx := ConcreteCategory.congr_hom h ((g.appIso W.unop).inv x)
  apply (ConcreteCategory.bijective_of_isIso (g'.appIso (f' ⁻¹ᵁ W.unop)).hom).1
  simpa only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply,
    Iso.hom_inv_id_apply] using hx

section BaseChange

variable [HasInjectiveResolutions X.Modules]

set_option backward.isDefEq.respectTransparency.types true in
/-- **The higher direct images commute with restriction to an open subscheme of the base.** Let
`g : T' ⟶ T` be an open immersion, and let `f' : X' ⟶ T'` and `g' : X' ⟶ X` be the base change
of `f` along `g`, in the cartesian square `sq`
```
X' --g'--> X
|          |
f'         f
v          v
T' --g---> T
```
Then `R^q f'_* (g'^* ℱ) ≅ (R^q f_* ℱ)|_{T'}` for every `q`.

Source: Stacks, Tags 01E1 and 08FE.
(blueprint: `lem-pc-sections-open-base-change`).

This is flat base change along an open immersion, and holds for any `f` and any `ℱ`: restriction
to an open subscheme preserves injective `𝒪_X`-modules and commutes with the pushforward. -/
theorem nonempty_higherDirectImage_iso_restrict {T' X' : Scheme.{u}} (g : T' ⟶ T)
    [IsOpenImmersion g] (g' : X' ⟶ X) (f' : X' ⟶ T') [HasInjectiveResolutions X'.Modules]
    (sq : IsPullback g' f' f g) (q : ℕ) :
    Nonempty ((higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ) ≅
      ((higherDirectImage f q).obj ℱ).restrict g) := by
  have : IsOpenImmersion g' := MorphismProperty.of_isPullback sq.flip ‹_›
  let A := restrictFunctor g'
  let B := restrictFunctor g
  let I := injectiveResolution ℱ
  let J : InjectiveResolution (A.obj ℱ) :=
    { cocomplex := (A.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
      injective := fun n ↦ injective_restrict_open g' (I.cocomplex.X n)
      ι := (HomologicalComplex.singleMapHomologicalComplex A (.up ℕ) 0).inv.app ℱ ≫
        (A.mapHomologicalComplex (.up ℕ)).map I.ι }
  let e := pushforward_restrict_square f g g' f' sq
  let K := ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let eK := (Functor.mapHomologicalComplexCompIso e (.up ℕ)).app I.cocomplex ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (A ⋙ pushforward f'))
      (.up ℕ)).symm.app I.cocomplex
  exact ⟨(higherDirectImage f' q).mapIso ((restrictFunctorIsoPullback g').app ℱ).symm ≪≫
    J.isoRightDerivedObj (pushforward f') q ≪≫
    (HomologicalComplex.homologyFunctor T'.Modules (.up ℕ) q).mapIso eK.symm ≪≫
    (K.sc q).mapHomologyIso B ≪≫ B.mapIso (I.isoRightDerivedObj (pushforward f) q).symm⟩

open MonoidalCategory in
set_option backward.isDefEq.respectTransparency.types true in
/-- **The projection formula** for an invertible module. For `f : X ⟶ T`, an `𝒪_X`-module `ℱ`
and an invertible `𝒪_T`-module `𝒩`, `R^q f_* (ℱ ⊗ f^* 𝒩) ≅ R^q f_* ℱ ⊗ 𝒩` for every `q`: twisting
by an invertible module pulled back from the base commutes with the higher direct images.

The blueprint states the projection formula `Rf_* E ⊗^𝕃 K ≅ Rf_* (E ⊗^𝕃 Lf^* K)` in the derived
category `D_QCoh` for `f` quasi-compact and quasi-separated, and deduces this case `K = 𝒩[0]`.
There is no derived category of `X.Modules` here, so only this case is stated, through the
higher direct images; it holds for every `f` and `ℱ`, as both sides are computed locally on
`T`, where `𝒩 ≅ 𝒪_T`.

(blueprint: `lem-pc-projection-formula`) -/
theorem nonempty_higherDirectImage_tensorObj_pullback_iso (𝒩 : T.Modules) [𝒩.IsInvertible]
    (q : ℕ) :
    Nonempty ((higherDirectImage f q).obj (ℱ ⊗ (Modules.pullback f).obj 𝒩) ≅
      (higherDirectImage f q).obj ℱ ⊗ 𝒩) := by
  let A := tensorRight ((Modules.pullback f).obj 𝒩)
  let B := tensorRight 𝒩
  have : A.IsEquivalence :=
    (BraidedCategory.tensorRightEquivalence _ _
      (nonempty_tensorObj_dual_iso_unit ((Modules.pullback f).obj 𝒩)).some).isEquivalence_functor
  have : B.IsEquivalence :=
    (BraidedCategory.tensorRightEquivalence _ _
      (nonempty_tensorObj_dual_iso_unit 𝒩).some).isEquivalence_functor
  have : A.Additive := Functor.additive_of_preserves_binary_products A
  have : B.Additive := Functor.additive_of_preserves_binary_products B
  have (M : X.Modules) : IsIso (projectionHom f M 𝒩) := isIso_projectionHom f M 𝒩
  let I := injectiveResolution ℱ
  let J : InjectiveResolution (A.obj ℱ) :=
    { cocomplex := (A.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
      injective := fun n ↦ A.injective_obj (I.cocomplex.X n)
      ι := (HomologicalComplex.singleMapHomologicalComplex A (.up ℕ) 0).inv.app ℱ ≫
        (A.mapHomologicalComplex (.up ℕ)).map I.ι }
  let e : pushforward f ⋙ B ≅ A ⋙ pushforward f :=
    NatIso.ofComponents (fun M ↦ asIso (projectionHom f M 𝒩))
      (fun φ ↦ projection_naturality f 𝒩 φ)
  let K := ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let eK := (Functor.mapHomologicalComplexCompIso e (.up ℕ)).app I.cocomplex ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (A ⋙ pushforward f))
      (.up ℕ)).symm.app I.cocomplex
  exact ⟨J.isoRightDerivedObj (pushforward f) q ≪≫
    (HomologicalComplex.homologyFunctor T.Modules (.up ℕ) q).mapIso eK.symm ≪≫
    (K.sc q).mapHomologyIso B ≪≫ B.mapIso (I.isoRightDerivedObj (pushforward f) q).symm⟩

end BaseChange



section Vanishing

variable [QuasiCompact f] [IsSeparated f] [HasInjectiveResolutions X.Modules]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

set_option backward.isDefEq.respectTransparency.types true in
/-- **Local vanishing of the higher direct images in large degrees.** For `f : X ⟶ T`
quasi-compact and separated and `ℱ` a quasi-coherent `𝒪_X`-module, every point `t` of `T` has an
open neighbourhood `U` and a bound `d` with `R^q f_* ℱ|_U = 0` for all `q ≥ d`.

Take for `U` an affine open neighbourhood of `t`: then `f ⁻¹ᵁ U` is covered by finitely many,
say `d`, affine opens whose intersections are affine, and the Čech complex of this cover
computes `R f_* ℱ|_U` [Stacks, Tag 01XD], so `R^q f_* ℱ|_U = 0` for `q ≥ d`.

The proof specializes the coefficient-independent local bound of Stacks, Tag 01XJ,
`AlgebraicGeometry.exists_local_uniform_higherDirectImage_bound`, to `ℱ`.
(blueprint: `lem-pc-higher-direct-image-local-vanishing`).

The bound is only local on `T`: over `T = ⨆ₙ Spec k` with `X = ⨆ₙ ℙⁿ_k` and `ℱ = 𝒪(-n-1)` on
the `n`-th piece, `R^n f_* ℱ ≠ 0` for every `n`.

(blueprint: `sk-thm-picard-coherence`) -/
theorem exists_isZero_higherDirectImage_restrict (t : T) :
    ∃ (U : T.Opens) (d : ℕ), t ∈ U ∧
      ∀ q ≥ d, IsZero (((higherDirectImage f q).obj ℱ).restrict U.ι) := by
  obtain ⟨U, d, ht, hd⟩ := exists_local_uniform_higherDirectImage_bound f t
  exact ⟨U, d, ht, hd ℱ inferInstance⟩

set_option backward.isDefEq.respectTransparency.types true in
/-- **Vanishing of the higher direct images in large degrees over a quasi-compact base.** In the
situation of `AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_restrict`, if `T`
is quasi-compact then `R^q f_* ℱ = 0` for all large `q`: finitely many of the neighbourhoods
given there cover `T`, and one takes for `N` the maximum of their bounds.

(blueprint: `sk-thm-picard-coherence`) -/
theorem exists_isZero_higherDirectImage [CompactSpace T] :
    ∃ N, ∀ q ≥ N, IsZero ((higherDirectImage f q).obj ℱ) := by
  classical
  choose U d ht hd using exists_isZero_higherDirectImage_restrict f ℱ
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun t ↦ (U t : Set T))
    (fun t ↦ (U t).isOpen) (fun t _ ↦ Set.mem_iUnion.mpr ⟨t, ht t⟩)
  refine ⟨s.sup d, fun q hq ↦ ?_⟩
  refine isZero_of_iSup_eq_top _ (fun t : s ↦ U t) ?_
    (fun t ↦ hd t q ((Finset.le_sup t.property).trans hq))
  apply eq_top_iff.2
  intro t _
  obtain ⟨i, hi, hti⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ t))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hti⟩

end Vanishing

end AlgebraicGeometry.Scheme.Modules
