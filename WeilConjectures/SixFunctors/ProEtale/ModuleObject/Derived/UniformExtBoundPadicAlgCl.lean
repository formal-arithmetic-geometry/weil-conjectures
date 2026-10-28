/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniformExtBoundCompatibilities
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldRestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldBasis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClUnderived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum

/-!
# The uniform `Ext` bound for constructible `ℚ̄_ℓ`-sheaves, from finite subextensions

Blueprint `det-uniform-constructible-ext-rational`, coefficients `ℚ̄_ℓ`. Let `X` be a scheme with
noetherian underlying space. If, for every finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, constructible
`E_X`-modules satisfy the uniform `Ext` bound, so do constructible `ℚ̄_{ℓ,X}`-modules
(`ProEtale.hasUniformConstructibleExtBound_padicAlgClRingObj_of_padicSubfield`).

By the 2-colimit description of `Dᵇc(X, ℚ̄_ℓ)` (blueprint `sk-thm-sfb-qlbar-two-colimit`,
`ProEtale.constructibleCocone_essSurjObj` and `ProEtale.constructibleCocone_homSurj`), a
constructible `ℚ̄_ℓ`-sheaf `M` is `ℚ̄_ℓ ⊗ M_E` for a constructible `E`-sheaf `M_E`, and every
morphism `M ⟶ B[q]` comes from a morphism `H ⊗ M_E ⟶ H ⊗ B_F[q]` over some finite `H ⊇ E, F`. By
the adjunction between extension and restriction of scalars along `E ⊆ H`
(`Mod.derivedExtendMapDerivedCategoryAdjunction`), the latter is a
morphism `M_E ⟶ B'[q]` with `B'` the restriction of scalars of `H ⊗ B_F`, a constructible
`E`-sheaf; so it vanishes for `q` above the bound of `M_E` over `E`, which does not depend on `B`
(`ProEtale.eq_zero_of_derivedExtendScalarsSubfield_obj`).

That the complexes `K_E` with `ℚ̄_ℓ ⊗ᴸ K_E ≅ M[q]` are sheaves placed in degree `q`
(`ProEtale.exists_iso_singleFunctor_of_constructibleToPadicAlgCl_obj_iso`) holds because the
extension of scalars `E_X ⟶ ℚ̄_ℓ,X` is exact and reflects zero objects: its unit
`N ⟶ ℚ̄_ℓ,X ⊗ N` is the filtered colimit of the split monomorphisms `N ⟶ F_X ⊗ N`, `F ⊇ E` finite
(`ProEtale.mono_extendUnitHom_padicSubfieldRingObjToPadicAlgCl`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

section Unit

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable {X : Scheme.{u}}

/-- For finite subextensions `E ≤ F`, the unit `N ⟶ F_X ⊗_{E_X} N`, `m ↦ 1 ⊗ m`, is a
monomorphism of abelian sheaves: `F_X ⊗_{E_X} N` is a direct sum of `[F : E] ≥ 1` copies of `N`
(`Mod.isIso_biproductDesc_extendUnit_smul`). -/
lemma mono_extendUnitHom_padicSubfieldRingObjMap {E F : FiniteIntermediateField ℓ} (h : E ≤ F)
    (N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) :
    Mono (Mod.extendUnitHom (padicSubfieldRingObjMap X ℓ h) N) := by
  have hb := Mod.isIso_biproductDesc_extendUnit_smul (padicSubfieldRingObjMap X ℓ h)
    (padicSubfieldBasisSection X h) (isIso_biproductDesc_padicSubfieldBasisSection X h) N
  have hd : 0 < FiniteIntermediateField.finrankOfLE h := by
    let := FiniteIntermediateField.algebraOfLE h
    have := FiniteIntermediateField.finiteDimensional_algebraOfLE h
    exact Module.finrank_pos
  have hm := (Mod.forget _).map_mono (biproduct.ι _ (⟨0, hd⟩ : Fin _) ≫ biproduct.desc fun i ↦
    (Mod.extendRestrictAdjunction (padicSubfieldRingObjMap X ℓ h)).unit.app N ≫
      (Mod.comap (padicSubfieldRingObjMap X ℓ h)).map
        ((Mod.smulNatTrans (padicSubfieldBasisSection X h i)).app
          ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).obj N)))
  rw [biproduct.ι_desc, Functor.map_comp] at hm
  exact @mono_of_mono _ _ _ _ _ _ _ hm

attribute [local instance] IsFiltered.isConnected in
/-- For a finite subextension `E`, the unit `N ⟶ ℚ̄_ℓ,X ⊗_{E_X} N`, `m ↦ 1 ⊗ m`, is a
monomorphism of abelian sheaves: it is the filtered colimit over the finite `F ⊇ E` of the
monomorphisms `N ⟶ F_X ⊗_{E_X} N` (`ProEtale.isColimitPadicAlgClExtendScalarsCocone`), and
filtered colimits of abelian sheaves are exact. -/
lemma mono_extendUnitHom_padicSubfieldRingObjToPadicAlgCl (E : FiniteIntermediateField ℓ)
    (N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) :
    Mono (Mod.extendUnitHom (padicSubfieldRingObjToPadicAlgCl X ℓ E) N) := by
  let φ : (Functor.const (PadicSubfieldAbove ℓ E)).obj N.X ⟶
      Mod.extendScalarsColimitDiagram (padicSubfieldAboveRingObjFunctor ℓ E X)
        (fun F ↦ padicSubfieldRingObjMap X ℓ F.property)
        (padicSubfieldRingObjMap_comp_padicSubfieldAboveRingObjFunctor_map ℓ E X) N :=
    { app F := Mod.extendUnitHom (padicSubfieldRingObjMap X ℓ F.property) N
      naturality F G g := by simp }
  have (F : PadicSubfieldAbove ℓ E) : Mono (φ.app F) :=
    mono_extendUnitHom_padicSubfieldRingObjMap ℓ F.property N
  have := NatTrans.mono_of_mono_app φ
  have := AB5OfSize_of_univLE.{0, 0} (Sheaf (ProEt.topology X) Ab.{u + 1})
  exact colim.map_mono' φ (isColimitConstCocone _ _)
    (isColimitPadicAlgClExtendScalarsCocone ℓ E X N) _ fun F ↦ by simp [φ]

/-- Extension of scalars along `E_X ⟶ ℚ̄_ℓ,X` reflects zero objects, its unit being a
monomorphism (`ProEtale.mono_extendUnitHom_padicSubfieldRingObjToPadicAlgCl`). -/
lemma isZero_of_isZero_extendScalars_padicSubfieldRingObjToPadicAlgCl
    {E : FiniteIntermediateField ℓ}
    {N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)}
    (hN : IsZero ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj N)) :
    IsZero N := by
  have := mono_extendUnitHom_padicSubfieldRingObjToPadicAlgCl ℓ E N
  have hX : IsZero N.X := IsZero.of_mono
    (Mod.extendUnitHom (padicSubfieldRingObjToPadicAlgCl X ℓ E) N) ((Mod.forget _).map_isZero hN)
  rw [IsZero.iff_id_eq_zero]
  exact Mod.hom_ext _ _ (hX.eq_of_src _ _)

/-- If the extension of scalars `ℚ̄_ℓ,X ⊗ᴸ_{E_X} K` of a complex of `E_X`-modules `K` is a
sheaf placed in degree `n`, then so is `K`: extension of scalars is exact and reflects zero
objects, so `K` has no cohomology outside degree `n`. -/
lemma exists_iso_singleFunctor_of_derivedExtendScalarsToPadicAlgCl_obj_iso
    {E : FiniteIntermediateField ℓ}
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (n : ℤ) (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))
    (e : (derivedExtendScalarsToPadicAlgCl X ℓ E).obj K ≅
      (DerivedCategory.singleFunctor _ n).obj M) :
    ∃ N, Nonempty (K ≅ (DerivedCategory.singleFunctor _ n).obj N) := by
  have hz (i : ℤ) (hi : i ≠ n) : IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
    refine isZero_of_isZero_extendScalars_padicSubfieldRingObjToPadicAlgCl ℓ (IsZero.of_iso ?_
      (((Mod.extendScalars _).leftDerivedFunctorHomologyFunctorIso i).app K))
    refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ i).mapIso e)
    rcases hi.lt_or_gt with hi | hi
    · exact DerivedCategory.isZero_of_isGE _ n i hi
    · exact DerivedCategory.isZero_of_isLE _ n i hi
  have : K.IsGE n := (K.isGE_iff n).2 fun i hi ↦ hz i hi.ne
  have : K.IsLE n := (K.isLE_iff n).2 fun i hi ↦ hz i hi.ne'
  exact K.exists_iso_singleFunctor_obj_of_isGE_of_isLE n

/-- If the extension of scalars `ℚ̄_ℓ,X ⊗ᴸ_{E_X} K` of a bounded constructible complex of
`E_X`-modules `K` is a sheaf placed in degree `n`, then `K` is a constructible sheaf placed in
degree `n`. -/
lemma exists_iso_singleFunctor_of_constructibleToPadicAlgCl_obj_iso
    {E : FiniteIntermediateField ℓ} (K : PadicSubfieldConstructible X ℓ E) (n : ℤ)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))
    (e : ((constructibleToPadicAlgCl X ℓ E).obj K).obj ≅
      (DerivedCategory.singleFunctor _ n).obj M) :
    ∃ N, IsConstructibleModuleObject (padicSubfieldRingObj X ℓ E) N ∧
      Nonempty (K.obj ≅ (DerivedCategory.singleFunctor _ n).obj N) := by
  obtain ⟨N, ⟨e'⟩⟩ :=
    exists_iso_singleFunctor_of_derivedExtendScalarsToPadicAlgCl_obj_iso ℓ K.obj n M e
  exact ⟨N, IsConstructibleModuleObject.of_iso ((DerivedCategory.homologyFunctor _ n).mapIso e' ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ n).app N) (K.property.2 n), ⟨e'⟩⟩

end Unit

/-- At a finite stage `H ⊇ E`: if `K ≅ M_E[0]` for an `E_X`-module `M_E` whose `Ext` groups into
constructible `E_X`-modules vanish in degrees `-n ≥ -N`, then every morphism
`H_X ⊗ᴸ_{E_X} K ⟶ L` vanishes for `L ≅ B[-n]`, `n ≤ N`, `B` a constructible `H_X`-module: by
the adjunction between extension and restriction of scalars it is a morphism
`M_E[0] ⟶ Res(B)[-n]`, and `Res(B)` is a constructible `E_X`-module
(`ProEtale.CondensedRing.isConstructibleModuleObject_comap_padicSubfieldRingObjMap`). -/
lemma eq_zero_of_derivedExtendScalarsSubfield_obj {X : Scheme.{u}}
    {E H : FiniteIntermediateField ℓ} (hE : E ≤ H)
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))}
    {M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)}
    (eK : K ≅ (DerivedCategory.singleFunctor _ 0).obj M) {N : ℤ}
    (hN : ∀ B, IsConstructibleModuleObject (padicSubfieldRingObj X ℓ E) B → ∀ n ≤ N,
      ∀ f : (DerivedCategory.singleFunctor _ 0).obj M ⟶
        (DerivedCategory.singleFunctor _ n).obj B, f = 0)
    {L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ H))}
    {n : ℤ} (hn : n ≤ N)
    {B : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ H)}
    (hB : IsConstructibleModuleObject (padicSubfieldRingObj X ℓ H) B)
    (eL : L ≅ (DerivedCategory.singleFunctor _ n).obj B)
    (g : (derivedExtendScalarsSubfield X ℓ hE).obj K ⟶ L) : g = 0 := by
  have adj := Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldRingObjMap X ℓ hE)
  have := adj.isLeftAdjoint
  have e : (Mod.comap (padicSubfieldRingObjMap X ℓ hE)).mapDerivedCategory.obj L ≅
      (DerivedCategory.singleFunctor _ n).obj
        ((Mod.comap (padicSubfieldRingObjMap X ℓ hE)).obj B) :=
    (Mod.comap _).mapDerivedCategory.mapIso eL ≪≫
      ((Mod.comap _).mapDerivedCategorySingleFunctor n).app B
  have hg : adj.homEquiv K L g = 0 := by
    have h₀ := hN _
      (CondensedRing.isConstructibleModuleObject_comap_padicSubfieldRingObjMap ℓ hE hB)
      n hn (eK.inv ≫ adj.homEquiv K L g ≫ e.hom)
    rw [← Category.assoc, ← cancel_epi eK.hom, ← cancel_mono e.inv] at h₀
    simpa using h₀
  have : (derivedExtendScalarsSubfield X ℓ hE).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  calc g = (adj.homEquiv K L).symm (adj.homEquiv K L g) :=
        ((adj.homEquiv K L).symm_apply_apply g).symm
    _ = (adj.homEquiv K L).symm 0 := congrArg _ hg
    _ = 0 := (adj.homEquiv_counit K L 0).trans ((congrArg (· ≫ adj.counit.app L)
      ((derivedExtendScalarsSubfield X ℓ hE).map_zero _ _)).trans zero_comp)

/-- Blueprint `det-uniform-constructible-ext-rational`, coefficients `ℚ̄_ℓ`: the uniform `Ext`
bound for constructible `ℚ̄_{ℓ,X}`-modules follows from the uniform bound over the finite
subextensions `E ⊆ ℚ̄_ℓ`. -/
theorem hasUniformConstructibleExtBound_padicAlgClRingObj_of_padicSubfield
    {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    (h : ∀ E : FiniteIntermediateField ℓ, HasUniformConstructibleExtBound
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) X)) :
    HasUniformConstructibleExtBound (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X) := by
  intro M hM
  obtain ⟨E, K, ⟨eK⟩⟩ := uniformExtBoundCompat_essSurjObj X ℓ
    (⟨_, CondensedRing.boundedConstructible_singleFunctor_obj _ X 0 M hM⟩ :
      PadicAlgClConstructible X ℓ)
  obtain ⟨M', hM', ⟨eM⟩⟩ :=
    exists_iso_singleFunctor_of_constructibleToPadicAlgCl_obj_iso ℓ K 0 M
      ((ObjectProperty.ι _).mapIso eK)
  obtain ⟨N, hN⟩ := h E M' hM'
  refine ⟨N, fun B hB n hn f ↦ ?_⟩
  obtain ⟨F, L, ⟨eL⟩⟩ := uniformExtBoundCompat_essSurjObj X ℓ
    (⟨_, CondensedRing.boundedConstructible_singleFunctor_obj _ X n B hB⟩ :
      PadicAlgClConstructible X ℓ)
  obtain ⟨H, hE, hF, g, hg⟩ := uniformExtBoundCompat_homSurj X ℓ E F K L
    (eK.hom ≫ ObjectProperty.homMk f ≫ eL.inv)
  obtain ⟨B', hB', ⟨eB'⟩⟩ := exists_iso_singleFunctor_of_constructibleToPadicAlgCl_obj_iso ℓ
    ((constructibleExtendScalars X ℓ hF).obj L) n B
    ((ObjectProperty.ι _).mapIso ((constructibleToPadicAlgClCompIso X ℓ hF).app L ≪≫ eL))
  have hg₀ : g = 0 := ObjectProperty.hom_ext _
    (eq_zero_of_derivedExtendScalarsSubfield_obj ℓ hE eM hN hn hB' eB' g.hom)
  have : (derivedExtendScalarsToPadicAlgCl X ℓ H).PreservesZeroMorphisms := by
    have := (Mod.derivedExtendMapDerivedCategoryAdjunction
      (padicSubfieldRingObjToPadicAlgCl X ℓ H)).isLeftAdjoint
    exact Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have : ((constructibleCocone X ℓ).Φ H).PreservesZeroMorphisms :=
    ⟨fun K L ↦ ObjectProperty.hom_ext _
      ((derivedExtendScalarsToPadicAlgCl X ℓ H).map_zero K.obj L.obj)⟩
  subst hg₀
  rw [Functor.map_zero, zero_comp, comp_zero, ← cancel_epi eK.inv, ← cancel_mono eL.hom]
    at hg
  simpa using congrArg (fun φ ↦ φ.hom) hg

end AlgebraicGeometry.ProEtale
