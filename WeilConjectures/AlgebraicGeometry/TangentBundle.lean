/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import WeilConjectures.Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# Vector bundles of quasi-coherent modules and the relative tangent bundle

For a quasi-coherent `𝒪_X`-module `M`, the *vector bundle* `𝕍(M) = Spec_X Sym_{𝒪_X}(M)` is the
relative spectrum of the symmetric algebra of `M`. It is constructed by gluing the affine schemes
`Spec Sym_{Γ(X, U)} Γ(M, U)` over the affine opens `U` of `X`
(`AlgebraicGeometry.Scheme.AffineZariskiSite.relativeGluingData`); this is possible because the
symmetric algebra commutes with localization (`SymmetricAlgebra.isLocalization_away_mapSemilinear`)
and the sections of a quasi-coherent module over a basic open are a localization
(`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpen`). Its *zero section*
`X ⟶ 𝕍(M)` corresponds to the augmentation `Sym_{𝒪_X}(M) ⟶ 𝒪_X`, which kills `M`.

For a morphism `f : X ⟶ Y`, the sheaf of relative differentials `Ω¹_{X/Y}` is quasi-coherent
(`AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentials`), and the *relative tangent
bundle* is `T_{X/Y} = 𝕍(Ω¹_{X/Y}) = Spec_X Sym_{𝒪_X}(Ω¹_{X/Y})`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.vectorBundle`: the vector bundle `Spec_X Sym_{𝒪_X}(M)`,
  with its projection `vectorBundleProj` and its zero section `vectorBundleZeroSection`.
- `AlgebraicGeometry.Scheme.Hom.tangentBundle`: the relative tangent bundle `T_{X/Y}`, with its
  projection `tangentBundleProj` and its zero section `tangentBundleZeroSection`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.vectorBundleZeroSection_vectorBundleProj` and
  `AlgebraicGeometry.Scheme.Hom.tangentBundleZeroSection_tangentBundleProj`: the zero section is
  a section of the projection.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Every point of `X` has an affine open neighbourhood `V` mapping into an affine open `U` of
`Y`. -/
lemma exists_isAffineOpen_le_preimage (x : X) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V), x ∈ V ∧
      V ≤ f ⁻¹ᵁ U := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ U from hxU) (f ⁻¹ᵁ U).isOpen
  exact ⟨U, hU, V, hV, hxV, hVU⟩

/-- The sheaf of relative differentials `Ω¹_{X/Y}` is quasi-coherent: on an affine open
`V = Spec B` of `X` mapping into an affine open `Spec A` of `Y` it is `Ω_{B/A}^~`
(`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsRestrictFromSpecIso`). -/
instance isQuasicoherent_relativeDifferentials : f.relativeDifferentials.IsQuasicoherent := by
  choose U hU V hV hxV hVU using f.exists_isAffineOpen_le_preimage
  refine Modules.isQuasicoherent_of_iSup_opensRange_eq_top _ (fun x ↦ (hV x).fromSpec)
    (eq_top_iff.2 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2
      ⟨x, by rw [IsAffineOpen.opensRange_fromSpec]; exact hxV x⟩) fun x ↦ ?_
  exact (presentationTilde _ Set.univ (by simp) _ (Submodule.span_eq _)).ofIsIso
    (f.relativeDifferentialsRestrictFromSpecIso (hU x) (hV x) (hVU x)).inv

end Scheme.Hom

namespace Scheme.Modules

open AffineZariskiSite

variable {X : Scheme.{u}} (M : X.Modules)

/-- The restriction map `Γ(M, U) → Γ(M, V)` of an `𝒪_X`-module, as a semilinear map over the
restriction map `Γ(X, U) → Γ(X, V)`. -/
noncomputable def restrictSemilinear {U V : X.Opens} (i : V ⟶ U) :
    Γ(M, U) →ₛₗ[(X.presheaf.map i.op).hom] Γ(M, V) where
  toFun := M.presheaf.map i.op
  map_add' := map_add _
  map_smul' := M.map_smul i

@[simp]
lemma restrictSemilinear_apply {U V : X.Opens} (i : V ⟶ U) (m : Γ(M, U)) :
    M.restrictSemilinear i m = M.presheaf.map i.op m :=
  rfl

/-- The symmetric algebra `Sym_{𝒪_X}(M)` of an `𝒪_X`-module, on the affine opens of `X`. -/
@[simps obj]
noncomputable def symmetricAlgebraPresheaf : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := .of (SymmetricAlgebra Γ(X, U.unop.toOpens) Γ(M, U.unop.toOpens))
  map {U V} i := CommRingCat.ofHom
    (SymmetricAlgebra.mapSemilinear (M.restrictSemilinear ((toOpensFunctor X).map i.unop)))
  map_id U := by
    ext1
    refine SymmetricAlgebra.ringHom_ext (fun r ↦ ?_) fun m ↦ ?_
    · simp
    · change SymmetricAlgebra.ι _ _ (M.presheaf.map (𝟙 _) m) = _
      simp
  map_comp {U V W} i j := by
    ext1
    refine SymmetricAlgebra.ringHom_ext (fun r ↦ ?_) fun m ↦ ?_
    · simp <;> rfl
    · simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
        Function.comp_apply, SymmetricAlgebra.mapSemilinear_ι]
      change SymmetricAlgebra.ι _ _
          (M.presheaf.map ((toOpensFunctor X).map (j.unop ≫ i.unop)).op m) =
        SymmetricAlgebra.ι _ _ (M.presheaf.map ((toOpensFunctor X).map j.unop).op
          (M.presheaf.map ((toOpensFunctor X).map i.unop).op m))
      rw [Functor.map_comp, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- The structure map `𝒪_X ⟶ Sym_{𝒪_X}(M)`. -/
@[simps]
noncomputable def toSymmetricAlgebraPresheaf :
    (toOpensFunctor X).op ⋙ X.presheaf ⟶ M.symmetricAlgebraPresheaf where
  app U := CommRingCat.ofHom (algebraMap Γ(X, U.unop.toOpens)
    (SymmetricAlgebra Γ(X, U.unop.toOpens) Γ(M, U.unop.toOpens)))
  naturality {U V} i := by
    ext r
    simp only [Functor.comp_obj, Functor.op_obj, Functor.comp_map,
      CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply]
    exact (SymmetricAlgebra.mapSemilinear_algebraMap
      (M.restrictSemilinear ((toOpensFunctor X).map i.unop)) (R := Γ(X, U.unop.toOpens))
      (M := Γ(M, U.unop.toOpens)) (S := Γ(X, V.unop.toOpens)) (N := Γ(M, V.unop.toOpens)) r).symm

/-- The augmentation `Sym_{𝒪_X}(M) ⟶ 𝒪_X`, which kills `M`. -/
@[simps]
noncomputable def symmetricAlgebraPresheafAugmentation :
    M.symmetricAlgebraPresheaf ⟶ (toOpensFunctor X).op ⋙ X.presheaf where
  app U := CommRingCat.ofHom (SymmetricAlgebra.algebraMapInv (R := Γ(X, U.unop.toOpens))
    (M := Γ(M, U.unop.toOpens))).toRingHom
  naturality {U V} i := by
    ext1
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    exact SymmetricAlgebra.algebraMapInv_mapSemilinear
      (M.restrictSemilinear ((toOpensFunctor X).map i.unop))

lemma toSymmetricAlgebraPresheaf_comp_augmentation :
    M.toSymmetricAlgebraPresheaf ≫ M.symmetricAlgebraPresheafAugmentation = 𝟙 _ := by
  ext U r
  exact AlgHom.commutes (SymmetricAlgebra.algebraMapInv (R := Γ(X, U.unop.toOpens))
    (M := Γ(M, U.unop.toOpens))) r

variable [M.IsQuasicoherent]

/-- `Sym_{𝒪_X}(M)` is a quasi-coherent `𝒪_X`-algebra: over a basic open `D(g)` of an affine open
`U`, it is the localization of its sections over `U` away from `g`. -/
lemma coequifibered_toSymmetricAlgebraPresheaf : M.toSymmetricAlgebraPresheaf.Coequifibered := by
  rw [coequifibered_iff_forall_isLocalizationAway]
  intro U g
  have := U.2.isLocalization_basicOpen g
  let : Module Γ(X, U.1) Γ(M, X.basicOpen g) :=
    Module.compHom _ (algebraMap Γ(X, U.1) Γ(X, X.basicOpen g))
  have : IsScalarTower Γ(X, U.1) Γ(X, X.basicOpen g) Γ(M, X.basicOpen g) :=
    IsScalarTower.of_compHom _ _ _
  exact SymmetricAlgebra.isLocalization_away_mapSemilinear g _
    (isLocalizedModule_basicOpen M U.2 g)
    (M.restrictSemilinear (homOfLE (X.basicOpen_le g))) fun _ ↦ rfl

/-- The vector bundle `𝕍(M) = Spec_X Sym_{𝒪_X}(M)` of a quasi-coherent `𝒪_X`-module `M`. -/
noncomputable def vectorBundle : Scheme.{u} :=
  (relativeGluingData M.coequifibered_toSymmetricAlgebraPresheaf).glued

/-- The projection `𝕍(M) ⟶ X`. -/
noncomputable def vectorBundleProj : M.vectorBundle ⟶ X :=
  (relativeGluingData M.coequifibered_toSymmetricAlgebraPresheaf).toBase

instance : IsAffineHom M.vectorBundleProj :=
  inferInstanceAs (IsAffineHom
    (relativeGluingData M.coequifibered_toSymmetricAlgebraPresheaf).toBase)

/-- `X` is its own relative spectrum: the structure morphism `Spec_X 𝒪_X ⟶ X` is an
isomorphism. -/
instance isIso_toBase_structurePresheaf (X : Scheme.{u}) :
    IsIso (relativeGluingData
      (NatTrans.Coequifibered.of_isIso (𝟙 ((toOpensFunctor X).op ⋙ X.presheaf)))).toBase :=
  toBase_of_forall _ (MorphismProperty.isomorphisms Scheme) fun U ↦ by
    rw [NatTrans.id_app, Spec.map_id]
    exact inferInstanceAs (IsIso (𝟙 _))

/-- The zero section `X ⟶ 𝕍(M)`, corresponding to the augmentation `Sym_{𝒪_X}(M) ⟶ 𝒪_X`. -/
noncomputable def vectorBundleZeroSection : X ⟶ M.vectorBundle :=
  inv (relativeGluingData
      (NatTrans.Coequifibered.of_isIso (𝟙 ((toOpensFunctor X).op ⋙ X.presheaf)))).toBase ≫
    relativeGluingMap M.coequifibered_toSymmetricAlgebraPresheaf
      (NatTrans.Coequifibered.of_isIso _) M.symmetricAlgebraPresheafAugmentation

/-- The zero section is a section of the projection. -/
@[reassoc (attr := simp)]
lemma vectorBundleZeroSection_vectorBundleProj :
    M.vectorBundleZeroSection ≫ M.vectorBundleProj = 𝟙 X := by
  rw [vectorBundleZeroSection, vectorBundleProj, Category.assoc,
    relativeGluingMap_toBase _ _ _ (by rw [toSymmetricAlgebraPresheaf_comp_augmentation]),
    IsIso.inv_hom_id]

end Scheme.Modules

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Blueprint `pur9-dg-def-tangent`: Relative tangent bundle

The relative tangent bundle `T_{X/Y} = Spec_X Sym_{𝒪_X}(Ω¹_{X/Y})` of a morphism `f : X ⟶ Y`.
The blueprint considers it for smooth `f`, where `Ω¹_{X/Y}` is locally free
(`AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFreeOfRank_relativeDifferentials`), but the
construction makes sense for every morphism. -/
noncomputable def tangentBundle : Scheme.{u} :=
  f.relativeDifferentials.vectorBundle

/-- Blueprint `pur9-dg-def-tangent`: Relative tangent bundle

The projection `T_{X/Y} ⟶ X`. -/
noncomputable def tangentBundleProj : f.tangentBundle ⟶ X :=
  f.relativeDifferentials.vectorBundleProj

/-- Blueprint `pur9-dg-def-tangent`: Relative tangent bundle

The zero section `X ⟶ T_{X/Y}`, corresponding to the augmentation
`Sym_{𝒪_X}(Ω¹_{X/Y}) ⟶ 𝒪_X`. -/
noncomputable def tangentBundleZeroSection : X ⟶ f.tangentBundle :=
  f.relativeDifferentials.vectorBundleZeroSection

/-- The zero section of the relative tangent bundle is a section of its projection. -/
@[reassoc (attr := simp)]
lemma tangentBundleZeroSection_tangentBundleProj :
    f.tangentBundleZeroSection ≫ f.tangentBundleProj = 𝟙 X :=
  f.relativeDifferentials.vectorBundleZeroSection_vectorBundleProj

end Scheme.Hom

end AlgebraicGeometry
