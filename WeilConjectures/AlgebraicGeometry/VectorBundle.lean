/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.RingTheory.Localization.BaseChange
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.Directed
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# The vector bundle of a quasi-coherent module

For a quasi-coherent `𝒪_X`-module `M` on a scheme `X`, the *vector bundle*
`V(M) = Spec_X (Sym_{𝒪_X} M)` is glued (`Scheme.Cover.RelativeGluingData`) from the affine pieces
`Spec (Sym_{Γ(X, U)} Γ(M, U))` over the affine opens `U ⊆ X`, along the inclusions of basic
opens `D(g) ⊆ U` (`AlgebraicGeometry.Scheme.directedBasicAffineCover`): as `M` is quasi-coherent,
`Γ(M, D(g)) = Γ(M, U)_g` is the base change of `Γ(M, U)` along `Γ(X, U) → Γ(X, U)_g`, and
the symmetric algebra commutes with base change. It comes with the projection `V(M) ⟶ X` and
the zero section `X ⟶ V(M)`, given by the augmentation `Sym M ⟶ 𝒪_X`.

When `M` is locally free of constant rank `d`, this is the vector bundle of
blueprint `def-asd-vector-bundle-zero-section`; over an open on which `M` is free the pieces are
`Spec Γ(X, U)[x₁, …, x_d]`, the affine space of dimension `d`.

## Blueprint

- `def-amb-finite-locally-free-module`: `AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank`.
- `def-asd-vector-bundle-zero-section`: `AlgebraicGeometry.Scheme.Modules.vectorBundle`,
  `AlgebraicGeometry.Scheme.Modules.vectorBundleProj`,
  `AlgebraicGeometry.Scheme.Modules.vectorBundleZeroSection`.
- `rem-asd-vector-bundle-comparison`: the purity chapter's vector bundles (relative spectra of
  symmetric algebras of locally free modules of constant rank, with their zero sections) are
  the same construction: `vectorBundle` is the coordinate-free form, and it assumes nothing
  about `f^!`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Blueprint `def-amb-finite-locally-free-module`: Locally free modules of constant finite rank.

An `𝒪_X`-module `M` is *locally free of constant rank `d`* if `X` has a Zariski open cover
`(V_a)` with `M|_{V_a} ≅ 𝒪_{V_a}^{⊕ d}` (`isLocallyFreeOfRank_iff`). In particular it is
quasi-coherent (`isQuasicoherent_of_isLocallyFreeOfRank`). -/
abbrev IsLocallyFreeOfRank (M : X.Modules) (d : ℕ) : Prop :=
  M.IsFiniteLocallyFreeOfRank d

lemma isLocallyFreeOfRank_iff (M : X.Modules) (d : ℕ) :
    M.IsLocallyFreeOfRank d ↔ ∃ (ι : Type u) (U : ι → X.Opens), ⨆ i, U i = ⊤ ∧
      ∀ i, Nonempty (M.restrict (U i).ι ≅ SheafOfModules.free (ULift.{u} (Fin d))) :=
  ⟨fun _ ↦ IsFiniteLocallyFreeOfRank.exists_restrict_iso_free M,
    fun ⟨_, U, hU, h⟩ ↦ isFiniteLocallyFreeOfRank_of_restrict_iso_free M (fun i ↦ (U i).ι)
      (by simpa using hU) h⟩

lemma isQuasicoherent_of_isLocallyFreeOfRank (M : X.Modules) (d : ℕ)
    [M.IsLocallyFreeOfRank d] : M.IsQuasicoherent :=
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree M d
  SheafOfModules.instIsQuasicoherentOfIsLocallyFree M

/-! ### Restriction of sections as a semilinear map -/

section Restriction

variable (M : X.Modules) {U V : X.Opens} (h : U ≤ V)

/-- For opens `U ≤ V`, `Γ(X, U)` is a `Γ(X, V)`-algebra through the restriction map. -/
noncomputable abbrev resAlgebra : Algebra Γ(X, V) Γ(X, U) :=
  (X.presheaf.map (homOfLE h).op).hom.toAlgebra

/-- For opens `U ≤ V`, `Γ(M, U)` is a `Γ(X, V)`-module through the restriction map. -/
noncomputable abbrev resModule : Module Γ(X, V) Γ(M, U) :=
  Module.compHom _ (X.presheaf.map (homOfLE h).op).hom

lemma resIsScalarTower :
    letI := resAlgebra h
    letI := resModule M h
    IsScalarTower Γ(X, V) Γ(X, U) Γ(M, U) :=
  letI := resAlgebra h
  letI := resModule M h
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- The restriction `Γ(M, V) → Γ(M, U)` as a `Γ(X, V)`-linear map. -/
noncomputable def sectionsRes :
    letI := resModule M h
    Γ(M, V) →ₗ[Γ(X, V)] Γ(M, U) :=
  letI := resModule M h
  { toFun := M.presheaf.map (homOfLE h).op
    map_add' := map_add _
    map_smul' := map_smul M _ }

@[simp]
lemma sectionsRes_apply (x : Γ(M, V)) : M.sectionsRes h x = M.presheaf.map (homOfLE h).op x :=
  rfl

lemma isBaseChange_sectionsRes_basicOpen [M.IsQuasicoherent] (hV : IsAffineOpen V) (g : Γ(X, V))
    (h : X.basicOpen g ≤ V) :
    letI := resAlgebra h
    letI := resModule M h
    haveI := resIsScalarTower M h
    IsBaseChange Γ(X, X.basicOpen g) (M.sectionsRes h) := by
  letI := resModule M h
  haveI := resIsScalarTower M h
  have : IsLocalizedModule (Submonoid.powers g) (M.sectionsRes h) :=
    isLocalizedModule_basicOpen M hV g
  haveI := hV.isLocalization_basicOpen g
  exact IsLocalizedModule.isBaseChange (Submonoid.powers g) Γ(X, X.basicOpen g) _

/-- For a quasi-coherent module `M`, an affine open `V` and a basic open `U = D(g)` of `V`, the
restriction `Γ(M, V) → Γ(M, U)` is the base change along `Γ(X, V) → Γ(X, U)`. -/
lemma isBaseChange_sectionsRes [M.IsQuasicoherent] (hV : IsAffineOpen V) (g : Γ(X, V))
    (hg : X.basicOpen g = U) :
    letI := resAlgebra h
    letI := resModule M h
    haveI := resIsScalarTower M h
    IsBaseChange Γ(X, U) (M.sectionsRes h) := by
  subst hg
  exact M.isBaseChange_sectionsRes_basicOpen hV g _

end Restriction

/-! ### The symmetric algebras of the sections -/

section SymAlgebra

variable (M : X.Modules)

/-- The symmetric algebra `Sym_{Γ(X, U)} Γ(M, U)` of the sections over an open `U`. -/
noncomputable def symAlgebra (U : X.Opens) : CommRingCat.{u} :=
  .of (SymmetricAlgebra Γ(X, U) Γ(M, U))

/-- The structure map `Γ(X, U) ⟶ Sym_{Γ(X, U)} Γ(M, U)`. -/
noncomputable def toSymAlgebra (U : X.Opens) : Γ(X, U) ⟶ M.symAlgebra U :=
  CommRingCat.ofHom (algebraMap Γ(X, U) (SymmetricAlgebra Γ(X, U) Γ(M, U)))

/-- The augmentation `Sym_{Γ(X, U)} Γ(M, U) ⟶ Γ(X, U)`, killing `Γ(M, U)`. -/
noncomputable def symAlgebraAugmentation (U : X.Opens) : M.symAlgebra U ⟶ Γ(X, U) :=
  CommRingCat.ofHom (SymmetricAlgebra.algebraMapInv (R := Γ(X, U)) (M := Γ(M, U))).toRingHom

@[reassoc (attr := simp)]
lemma toSymAlgebra_symAlgebraAugmentation (U : X.Opens) :
    M.toSymAlgebra U ≫ M.symAlgebraAugmentation U = 𝟙 _ := by
  ext r
  exact SymmetricAlgebra.algebraMap_leftInverse Γ(M, U) r

lemma symAlgebraAugmentation_surjective (U : X.Opens) :
    Function.Surjective (M.symAlgebraAugmentation U) :=
  fun r ↦ ⟨M.toSymAlgebra U r, congr($(M.toSymAlgebra_symAlgebraAugmentation U) r)⟩

lemma symAlgebra_hom_ext {U : X.Opens} {A : CommRingCat.{u}} {f g : M.symAlgebra U ⟶ A}
    (h₁ : M.toSymAlgebra U ≫ f = M.toSymAlgebra U ≫ g)
    (h₂ : ∀ x : Γ(M, U), f.hom (SymmetricAlgebra.ι _ _ x) = g.hom (SymmetricAlgebra.ι _ _ x)) :
    f = g := by
  ext x
  induction x using SymmetricAlgebra.induction with
  | algebraMap r => exact congr($h₁ r)
  | ι x => exact h₂ x
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

variable {U V : X.Opens} (h : U ≤ V)

/-- The restriction `Sym_{Γ(X, V)} Γ(M, V) ⟶ Sym_{Γ(X, U)} Γ(M, U)` for opens `U ≤ V`. -/
noncomputable def symAlgebraMap : M.symAlgebra V ⟶ M.symAlgebra U :=
  letI := resAlgebra h
  letI := resModule M h
  haveI := resIsScalarTower M h
  CommRingCat.ofHom (SymmetricAlgebra.mapOfIsScalarTower Γ(X, U) (M.sectionsRes h)).toRingHom

@[reassoc]
lemma toSymAlgebra_symAlgebraMap :
    M.toSymAlgebra V ≫ M.symAlgebraMap h = X.presheaf.map (homOfLE h).op ≫ M.toSymAlgebra U := by
  letI := resAlgebra h
  letI := resModule M h
  haveI := resIsScalarTower M h
  ext r
  exact (SymmetricAlgebra.mapOfIsScalarTower Γ(X, U) (M.sectionsRes h)).commutes r

@[simp]
lemma symAlgebraMap_ι (x : Γ(M, V)) :
    (M.symAlgebraMap h).hom (SymmetricAlgebra.ι _ _ x) =
      SymmetricAlgebra.ι _ _ (M.presheaf.map (homOfLE h).op x) :=
  letI := resAlgebra h
  letI := resModule M h
  haveI := resIsScalarTower M h
  SymmetricAlgebra.mapOfIsScalarTower_ι _ _

@[reassoc]
lemma symAlgebraMap_symAlgebraAugmentation :
    M.symAlgebraMap h ≫ M.symAlgebraAugmentation U =
      M.symAlgebraAugmentation V ≫ X.presheaf.map (homOfLE h).op := by
  refine M.symAlgebra_hom_ext ?_ fun x ↦ ?_
  · rw [toSymAlgebra_symAlgebraMap_assoc, toSymAlgebra_symAlgebraAugmentation_assoc,
      toSymAlgebra_symAlgebraAugmentation, Category.comp_id]
  · simp only [symAlgebraAugmentation, CommRingCat.hom_comp, RingHom.comp_apply,
      CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, symAlgebraMap_ι]
    exact (SymmetricAlgebra.algebraMapInv_ι _).trans ((map_zero _).symm.trans
      (congrArg _ (SymmetricAlgebra.algebraMapInv_ι x).symm))

lemma symAlgebraMap_id : M.symAlgebraMap (le_refl U) = 𝟙 _ := by
  refine M.symAlgebra_hom_ext ?_ fun x ↦ ?_
  · rw [toSymAlgebra_symAlgebraMap, Category.comp_id, Subsingleton.elim (homOfLE (le_refl U)) (𝟙 U), op_id,
      X.presheaf.map_id, Category.id_comp]
  · rw [symAlgebraMap_ι, CommRingCat.hom_id, RingHom.id_apply,
      Subsingleton.elim (homOfLE (le_refl U)) (𝟙 U), op_id,
      CategoryTheory.Functor.map_id]
    rfl

lemma symAlgebraMap_comp {W : X.Opens} (hUV : U ≤ V) (hVW : V ≤ W) :
    M.symAlgebraMap hVW ≫ M.symAlgebraMap hUV = M.symAlgebraMap (hUV.trans hVW) := by
  refine M.symAlgebra_hom_ext ?_ fun x ↦ ?_
  · rw [toSymAlgebra_symAlgebraMap_assoc, toSymAlgebra_symAlgebraMap,
      toSymAlgebra_symAlgebraMap, ← Category.assoc, ← Functor.map_comp, ← op_comp]
    rfl
  · rw [CommRingCat.hom_comp, RingHom.comp_apply, symAlgebraMap_ι, symAlgebraMap_ι,
      symAlgebraMap_ι]
    congr 1
    exact (congr($(M.presheaf.map_comp (homOfLE hVW).op (homOfLE hUV).op) x)).symm

/-- For a quasi-coherent `M`, an affine open `V` and a basic open `U = D(g)` of `V`, the square of
rings `Γ(V) ⟶ Γ(U)`, `Γ(V) ⟶ Sym Γ(M, V)`, `Sym Γ(M, V) ⟶ Sym Γ(M, U)`, `Γ(U) ⟶ Sym Γ(M, U)` is
a pushout: `Sym_{Γ(U)} Γ(M, U) = Γ(U) ⊗_{Γ(V)} Sym_{Γ(V)} Γ(M, V)`. -/
lemma isPushout_symAlgebraMap [M.IsQuasicoherent] (hV : IsAffineOpen V) (g : Γ(X, V))
    (hg : X.basicOpen g = U) :
    IsPushout (M.toSymAlgebra V) (X.presheaf.map (homOfLE h).op)
      (M.symAlgebraMap h) (M.toSymAlgebra U) := by
  letI := resAlgebra h
  letI := resModule M h
  haveI := resIsScalarTower M h
  have := SymmetricAlgebra.isPushout_of_isBaseChange (M.isBaseChange_sectionsRes h hV g hg)
  letI := (SymmetricAlgebra.mapOfIsScalarTower Γ(X, U) (M.sectionsRes h)).toAlgebra
  have : IsScalarTower Γ(X, V) (SymmetricAlgebra Γ(X, V) Γ(M, V))
      (SymmetricAlgebra Γ(X, U) Γ(M, U)) :=
    .of_algebraMap_eq fun r ↦
      ((SymmetricAlgebra.mapOfIsScalarTower Γ(X, U) (M.sectionsRes h)).commutes r).symm
  exact (CommRingCat.isPushout_of_isPushout Γ(X, V) Γ(X, U)
    (SymmetricAlgebra Γ(X, V) Γ(M, V)) (SymmetricAlgebra Γ(X, U) Γ(M, U))).flip

end SymAlgebra

/-! ### Gluing the affine pieces -/

section Gluing

variable (M : X.Modules) [M.IsQuasicoherent]

/-- The `Spec` of a restriction map intertwines the canonical isomorphisms `Spec Γ(X, U) ≅ U`
with the inclusion of opens. -/
lemma _root_.AlgebraicGeometry.Scheme.BasicAffineOpens.specMap_res_isoSpec_inv
    {U V : X.BasicAffineOpens} (h : U.opens ≤ V.opens) :
    Spec.map (X.presheaf.map (homOfLE h).op) ≫ V.isAffineOpen.isoSpec.inv =
      U.isAffineOpen.isoSpec.inv ≫ X.homOfLE h :=
  AlgebraicGeometry.specMap_res_isoSpec_inv (U := U.toAffineOpens) (V := V.toAffineOpens) h

/-- The diagram `U ↦ Spec (Sym_{Γ(X, U)} Γ(M, U))` over the affine opens of `X`, ordered by
basic open inclusion. -/
noncomputable def symSpecFunctor : X.BasicAffineOpens ⥤ Scheme.{u} where
  obj U := Spec (M.symAlgebra U.opens)
  map f := Spec.map (M.symAlgebraMap (BasicAffineOpens.opens_le_opens (leOfHom f)))
  map_id U := by
    rw [symAlgebraMap_id, Spec.map_id]
  map_comp f g := by
    rw [← Spec.map_comp, symAlgebraMap_comp]

/-- The structure maps `Spec (Sym_{Γ(X, U)} Γ(M, U)) ⟶ Spec Γ(X, U) ≅ U`. -/
noncomputable def symSpecNatTrans :
    M.symSpecFunctor ⟶ X.directedBasicAffineCover.functorOfLocallyDirected where
  app U := Spec.map (M.toSymAlgebra U.opens) ≫ U.isAffineOpen.isoSpec.inv
  naturality {U V} f := by
    have hG : X.directedBasicAffineCover.functorOfLocallyDirected.map f =
        X.homOfLE (BasicAffineOpens.opens_le_opens (leOfHom f)) := rfl
    rw [hG, Category.assoc, ← BasicAffineOpens.specMap_res_isoSpec_inv]
    dsimp only [symSpecFunctor]
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, toSymAlgebra_symAlgebraMap]

lemma symSpecNatTrans_app (U : X.BasicAffineOpens) :
    M.symSpecNatTrans.app U = Spec.map (M.toSymAlgebra U.opens) ≫ U.isAffineOpen.isoSpec.inv :=
  rfl

lemma symSpecNatTrans_equifibered : M.symSpecNatTrans.Equifibered := by
  intro U V f
  obtain ⟨g, hg⟩ := leOfHom f
  have key := isPullback_SpecMap_of_isPushout _ _ _ _
    (M.isPushout_symAlgebraMap (BasicAffineOpens.opens_le_opens (leOfHom f)) V.isAffineOpen g hg)
  exact key.paste_vert (IsPullback.of_vert_isIso
    ⟨BasicAffineOpens.specMap_res_isoSpec_inv (BasicAffineOpens.opens_le_opens (leOfHom f))⟩)

/-- The relative gluing datum of `V(M) = Spec_X (Sym M)`. -/
noncomputable def symSpecGluingData : X.directedBasicAffineCover.RelativeGluingData where
  functor := M.symSpecFunctor
  natTrans := M.symSpecNatTrans
  equifibered := M.symSpecNatTrans_equifibered

instance : (M.symSpecFunctor ⋙ Scheme.forget).IsLocallyDirected :=
  inferInstanceAs ((M.symSpecGluingData.functor ⋙ Scheme.forget).IsLocallyDirected)

instance : HasColimit M.symSpecFunctor :=
  inferInstanceAs (HasColimit M.symSpecGluingData.functor)

/-- Blueprint `def-asd-vector-bundle-zero-section`: Vector bundle with zero section.

The *vector bundle* `V(M) = Spec_X (Sym_{𝒪_X} M)` of a quasi-coherent `𝒪_X`-module `M`: the
relative spectrum of its symmetric algebra, glued from the affine pieces
`Spec (Sym_{Γ(X, U)} Γ(M, U))` over the affine opens `U ⊆ X`. Its projection is
`vectorBundleProj`, its zero section (given by the augmentation `Sym M → 𝒪_X`) is
`vectorBundleZeroSection`, a closed immersion. When `M` is locally free of constant rank `d`
(`IsLocallyFreeOfRank`), over an affine open `U` on which `M` is free the bundle is
`Spec Γ(X, U)[x₁, …, x_d]` (`vectorBundleι`, `isPullback_vectorBundleι` and
`SymmetricAlgebra.equivMvPolynomial`); changes of trivialization are invertible matrices.

This construction is also the vector bundle of the purity chapter
(blueprint `rem-asd-vector-bundle-comparison`): the two definitions agree, and neither assumes
anything about `f^!`. -/
noncomputable def vectorBundle : Scheme.{u} :=
  M.symSpecGluingData.glued

/-- Blueprint `def-asd-vector-bundle-zero-section`: the projection `π : V(M) ⟶ X`. -/
noncomputable def vectorBundleProj : M.vectorBundle ⟶ X :=
  M.symSpecGluingData.toBase

/-- The inclusion of the affine piece `Spec (Sym_{Γ(X, U)} Γ(M, U))` into `V(M)`. -/
noncomputable def vectorBundleι (U : X.BasicAffineOpens) :
    Spec (M.symAlgebra U.opens) ⟶ M.vectorBundle :=
  colimit.ι M.symSpecFunctor U

instance (U : X.BasicAffineOpens) : IsOpenImmersion (M.vectorBundleι U) :=
  inferInstanceAs (IsOpenImmersion (M.symSpecGluingData.cover.f U))

@[reassoc (attr := simp)]
lemma vectorBundleι_vectorBundleProj (U : X.BasicAffineOpens) :
    M.vectorBundleι U ≫ M.vectorBundleProj =
      Spec.map (M.toSymAlgebra U.opens) ≫ U.isAffineOpen.isoSpec.inv ≫ U.opens.ι :=
  (M.symSpecGluingData.ι_toBase U).trans (Category.assoc _ _ _)

@[reassoc]
lemma specMap_symAlgebraMap_vectorBundleι {U V : X.BasicAffineOpens} (h : U ≤ V) :
    Spec.map (M.symAlgebraMap (BasicAffineOpens.opens_le_opens h)) ≫ M.vectorBundleι V =
      M.vectorBundleι U :=
  colimit.w M.symSpecFunctor (homOfLE h)

/-- Over an affine open `U ⊆ X`, `V(M)` is `Spec (Sym_{Γ(X, U)} Γ(M, U))`: the square

```
Spec (Sym Γ(M, U)) ──vectorBundleι U──▶ V(M)
        │                                │
        ▼                                ▼
        U ──────────────────────────▶    X
```

is cartesian. -/
lemma isPullback_vectorBundleι (U : X.BasicAffineOpens) :
    IsPullback (Spec.map (M.toSymAlgebra U.opens) ≫ U.isAffineOpen.isoSpec.inv)
      (M.vectorBundleι U) U.opens.ι M.vectorBundleProj :=
  M.symSpecGluingData.isPullback_natTrans_ι_toBase U

/-- The local zero section `U ⟶ Spec (Sym_{Γ(X, U)} Γ(M, U))`, given by the augmentation. -/
noncomputable def localZeroSection (U : X.BasicAffineOpens) :
    (U.opens : Scheme.{u}) ⟶ Spec (M.symAlgebra U.opens) :=
  U.isAffineOpen.isoSpec.hom ≫ Spec.map (M.symAlgebraAugmentation U.opens)

@[reassoc (attr := simp)]
lemma localZeroSection_comp (U : X.BasicAffineOpens) :
    M.localZeroSection U ≫ Spec.map (M.toSymAlgebra U.opens) ≫ U.isAffineOpen.isoSpec.inv =
      𝟙 _ := by
  rw [localZeroSection, Category.assoc, ← Spec.map_comp_assoc,
    toSymAlgebra_symAlgebraAugmentation, Spec.map_id, Category.id_comp, Iso.hom_inv_id]

instance (U : X.BasicAffineOpens) : IsClosedImmersion (M.localZeroSection U) := by
  have := IsClosedImmersion.spec_of_surjective _ (M.symAlgebraAugmentation_surjective U.opens)
  rw [localZeroSection]
  infer_instance

/-- Blueprint `def-asd-vector-bundle-zero-section`: the zero section `X ⟶ V(M)`, given on the
affine piece over `U` by the augmentation `Sym_{Γ(X, U)} Γ(M, U) ⟶ Γ(X, U)`. -/
noncomputable def vectorBundleZeroSection : X ⟶ M.vectorBundle :=
  X.directedBasicAffineCover.glueMorphismsOfLocallyDirected
    (fun U ↦ M.localZeroSection U ≫ M.vectorBundleι U)
    fun {U V} f ↦ by
      have h : X.homOfLE (BasicAffineOpens.opens_le_opens (leOfHom f)) ≫
          V.isAffineOpen.isoSpec.hom = U.isAffineOpen.isoSpec.hom ≫
            Spec.map (X.presheaf.map (homOfLE (BasicAffineOpens.opens_le_opens
              (leOfHom f))).op) := by
        rw [← cancel_mono V.isAffineOpen.isoSpec.inv, Category.assoc, Category.assoc,
          Iso.hom_inv_id, Category.comp_id, BasicAffineOpens.specMap_res_isoSpec_inv,
          Iso.hom_inv_id_assoc]
      rw [directedBasicAffineCover_trans, localZeroSection, localZeroSection, Category.assoc,
        reassoc_of% h, ← Spec.map_comp_assoc, ← M.symAlgebraMap_symAlgebraAugmentation,
        Spec.map_comp_assoc, specMap_symAlgebraMap_vectorBundleι]

@[reassoc (attr := simp)]
lemma ι_vectorBundleZeroSection (U : X.BasicAffineOpens) :
    U.opens.ι ≫ M.vectorBundleZeroSection = M.localZeroSection U ≫ M.vectorBundleι U :=
  X.directedBasicAffineCover.map_glueMorphismsOfLocallyDirected _ _ U

/-- The zero section is a section of the projection. -/
@[reassoc (attr := simp)]
lemma vectorBundleZeroSection_vectorBundleProj :
    M.vectorBundleZeroSection ≫ M.vectorBundleProj = 𝟙 X := by
  refine X.directedBasicAffineCover.hom_ext _ _ fun U ↦ ?_
  rw [directedBasicAffineCover_f, ι_vectorBundleZeroSection_assoc,
    vectorBundleι_vectorBundleProj, localZeroSection_comp_assoc,
    Category.comp_id]

/-- Over an affine open `U`, the zero section restricts to the local zero section. -/
lemma isPullback_localZeroSection (U : X.BasicAffineOpens) :
    IsPullback (M.localZeroSection U) U.opens.ι (M.vectorBundleι U)
      M.vectorBundleZeroSection := by
  refine IsPullback.of_right ?_ (M.ι_vectorBundleZeroSection U).symm
    (M.isPullback_vectorBundleι U)
  rw [localZeroSection_comp, vectorBundleZeroSection_vectorBundleProj]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- The zero section of `V(M)` is a closed immersion. -/
instance isClosedImmersion_vectorBundleZeroSection :
    IsClosedImmersion M.vectorBundleZeroSection := by
  refine IsZariskiLocalAtTarget.of_openCover M.symSpecGluingData.cover fun U ↦ ?_
  have e : Arrow.mk (M.symSpecGluingData.cover.pullbackHom M.vectorBundleZeroSection U) ≅
      Arrow.mk (M.localZeroSection U) :=
    Arrow.isoMk (M.isPullback_localZeroSection U).flip.isoPullback.symm (Iso.refl _) (by
      simp only [Cover.pullbackHom, Arrow.mk_hom, Iso.refl_hom, Category.comp_id]
      exact (M.isPullback_localZeroSection U).flip.isoPullback_inv_snd)
  rw [MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) e]
  infer_instance

/-- The arrow `Spec (Sym_{Γ(X, U)} Γ(M, U)) ⟶ U` is the restriction of `V(M) ⟶ X` over `U`. -/
noncomputable def arrowIsoVectorBundleProjPullbackHom (U : X.BasicAffineOpens) :
    Arrow.mk (X.directedBasicAffineCover.pullbackHom M.vectorBundleProj U) ≅
      Arrow.mk (Spec.map (M.toSymAlgebra U.opens) ≫ U.isAffineOpen.isoSpec.inv) :=
  Arrow.isoMk (M.isPullback_vectorBundleι U).flip.isoPullback.symm (Iso.refl _) (by
    simp only [Cover.pullbackHom, Arrow.mk_hom, Iso.refl_hom, Category.comp_id]
    exact (M.isPullback_vectorBundleι U).flip.isoPullback_inv_snd)

/-- The projection `V(M) ⟶ X` is affine. -/
instance isAffineHom_vectorBundleProj : IsAffineHom M.vectorBundleProj := by
  refine IsZariskiLocalAtTarget.of_openCover X.directedBasicAffineCover fun U ↦ ?_
  rw [MorphismProperty.arrow_mk_iso_iff (P := @IsAffineHom)
    (M.arrowIsoVectorBundleProjPullbackHom U)]
  infer_instance

/-- If the sections of `M` over affine opens are finitely generated (e.g. `M` locally free of
finite rank), the projection `V(M) ⟶ X` is locally of finite type. -/
lemma locallyOfFiniteType_vectorBundleProj
    (hM : ∀ U : X.Opens, IsAffineOpen U → Module.Finite Γ(X, U) Γ(M, U)) :
    LocallyOfFiniteType M.vectorBundleProj := by
  refine IsZariskiLocalAtTarget.of_openCover X.directedBasicAffineCover fun U ↦ ?_
  rw [MorphismProperty.arrow_mk_iso_iff (P := @LocallyOfFiniteType)
    (M.arrowIsoVectorBundleProjPullbackHom U)]
  have := hM U.opens U.isAffineOpen
  have : LocallyOfFiniteType (Spec.map (M.toSymAlgebra U.opens)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr (inferInstance :
      Algebra.FiniteType Γ(X, U.opens) (SymmetricAlgebra Γ(X, U.opens) Γ(M, U.opens)))
  infer_instance

end Gluing

end AlgebraicGeometry.Scheme.Modules
