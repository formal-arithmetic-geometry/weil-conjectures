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
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
public import WeilConjectures.AlgebraicGeometry.VectorBundle.Trivialization

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
  let := resModule M h
  have := resIsScalarTower M h
  have : IsLocalizedModule (Submonoid.powers g) (M.sectionsRes h) :=
    isLocalizedModule_basicOpen M hV g
  have := hV.isLocalization_basicOpen g
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
    (h₂ : ∀ x : Γ(M, U),
      f.hom (SymmetricAlgebra.ι _ _ x) = g.hom (SymmetricAlgebra.ι _ _ x)) :
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
    M.toSymAlgebra V ≫ M.symAlgebraMap h =
      X.presheaf.map (homOfLE h).op ≫ M.toSymAlgebra U := by
  let := resAlgebra h
  let := resModule M h
  have := resIsScalarTower M h
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
  · rw [toSymAlgebra_symAlgebraMap, Category.comp_id,
      Subsingleton.elim (homOfLE (le_refl U)) (𝟙 U), op_id, X.presheaf.map_id, Category.id_comp]
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
rings `Γ(V) ⟶ Γ(U)`, `Γ(V) ⟶ Sym Γ(M, V)`, `Sym Γ(M, V) ⟶ Sym Γ(M, U)`, `Γ(U) ⟶ Sym Γ(M, U)`
is a pushout: `Sym_{Γ(U)} Γ(M, U) = Γ(U) ⊗_{Γ(V)} Sym_{Γ(V)} Γ(M, V)`. -/
lemma isPushout_symAlgebraMap [M.IsQuasicoherent] (hV : IsAffineOpen V) (g : Γ(X, V))
    (hg : X.basicOpen g = U) :
    IsPushout (M.toSymAlgebra V) (X.presheaf.map (homOfLE h).op)
      (M.symAlgebraMap h) (M.toSymAlgebra U) := by
  let := resAlgebra h
  let := resModule M h
  have := resIsScalarTower M h
  have := SymmetricAlgebra.isPushout_of_isBaseChange (M.isBaseChange_sectionsRes h hV g hg)
  let := (SymmetricAlgebra.mapOfIsScalarTower Γ(X, U) (M.sectionsRes h)).toAlgebra
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

omit [M.IsQuasicoherent] in
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

omit [M.IsQuasicoherent] in
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
        Spec.map_comp_assoc, M.specMap_symAlgebraMap_vectorBundleι (leOfHom f),
        Category.assoc]

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
/-! ### Trivialisations over affine opens on which the module is free -/

section Trivialization

variable (M : X.Modules)

/-- A basis `b` of `Γ(M, U)` over an affine open `U` identifies the affine piece
`Spec (Sym_{Γ(X, U)} Γ(M, U))` of `V(M)` with the affine space `𝔸(ι; U)`: the coordinate `xᵢ`
corresponds to `bᵢ ∈ Γ(M, U) ⊆ Sym Γ(M, U)` (`SymmetricAlgebra.equivMvPolynomial`). -/
noncomputable def affineSpaceIso (U : X.BasicAffineOpens) {ι : Type u}
    (b : Module.Basis ι Γ(X, U.opens) Γ(M, U.opens)) :
    𝔸(ι; U.opens) ≅ Spec (M.symAlgebra U.opens) :=
  AffineSpace.mapIso ι U.isAffineOpen.isoSpec ≪≫ AffineSpace.SpecIso ι Γ(X, U.opens) ≪≫
    Scheme.Spec.mapIso (SymmetricAlgebra.equivMvPolynomial b).toRingEquiv.toCommRingCatIso.op

lemma symAlgebraAugmentation_ι (U : X.Opens) (x : Γ(M, U)) :
    M.symAlgebraAugmentation U (SymmetricAlgebra.ι _ _ x) = 0 :=
  SymmetricAlgebra.algebraMapInv_ι x

variable {M} {U : X.BasicAffineOpens} {ι : Type u}
  (b : Module.Basis ι Γ(X, U.opens) Γ(M, U.opens))

@[reassoc (attr := simp)]
lemma affineSpaceIso_inv_over :
    (M.affineSpaceIso U b).inv ≫ 𝔸(ι; U.opens) ↘ U.opens =
      Spec.map (M.toSymAlgebra U.opens) ≫ U.isAffineOpen.isoSpec.inv := by
  simp only [affineSpaceIso, Iso.trans_inv, Category.assoc, AffineSpace.mapIso_inv,
    AffineSpace.map_over, AffineSpace.SpecIso_inv_over_assoc]
  rw [Functor.mapIso_inv, Scheme.Spec_map, Iso.op_inv, Quiver.Hom.unop_op,
    ← Spec.map_comp_assoc]
  congr 2
  ext r
  exact (SymmetricAlgebra.equivMvPolynomial b).symm.commutes r

@[reassoc (attr := simp)]
lemma affineSpaceIso_hom_comp :
    (M.affineSpaceIso U b).hom ≫ Spec.map (M.toSymAlgebra U.opens) ≫
      U.isAffineOpen.isoSpec.inv = 𝔸(ι; U.opens) ↘ U.opens := by
  rw [← affineSpaceIso_inv_over, Iso.hom_inv_id_assoc]

lemma affineSpaceIso_inv_appTop_coord (i : ι) :
    (M.affineSpaceIso U b).inv.appTop (AffineSpace.coord U.opens i) =
      (Scheme.ΓSpecIso (M.symAlgebra U.opens)).inv (SymmetricAlgebra.ι _ _ (b i)) := by
  simp only [affineSpaceIso, Iso.trans_inv, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    AffineSpace.mapIso_inv, AffineSpace.map_appTop_coord, AffineSpace.SpecIso_inv_appTop_coord]
  rw [Functor.mapIso_inv, Scheme.Spec_map, Iso.op_inv, Quiver.Hom.unop_op,
    ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  congr 1
  exact SymmetricAlgebra.equivMvPolynomial_symm_X b i

/-- Under a trivialisation, the zero section of `V(M)` over `U` is the zero section of the affine
space. -/
@[reassoc (attr := simp)]
lemma zeroSection_affineSpaceIso_hom :
    AffineSpace.zeroSection ι U.opens ≫ (M.affineSpaceIso U b).hom = M.localZeroSection U := by
  rw [← Iso.eq_comp_inv]
  refine AffineSpace.hom_ext ?_ fun i ↦ ?_
  · rw [AffineSpace.zeroSection_over, Category.assoc, affineSpaceIso_inv_over,
      localZeroSection_comp]
  · rw [AffineSpace.zeroSection_appTop_coord, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      affineSpaceIso_inv_appTop_coord, localZeroSection, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, ← CommRingCat.comp_apply (Scheme.ΓSpecIso _).inv,
      ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply, symAlgebraAugmentation_ι,
      map_zero, map_zero]

variable [Fintype ι]

/-- The matrix of the change of trivialisation from a basis `b` to a basis `b'` of `Γ(M, U)`:
`b' i = ∑ⱼ Aᵢⱼ b j`, as functions on `U`. It is invertible (`Module.Basis.toMatrix`). -/
noncomputable def transitionMatrix (b' : Module.Basis ι Γ(X, U.opens) Γ(M, U.opens)) :
    Matrix ι ι Γ(U.opens, ⊤) :=
  (b.toMatrix b').transpose.map U.opens.topIso.inv

/-- Changes of trivialisation are linear: they are given by the invertible matrix
`transitionMatrix b b'`. -/
lemma affineSpaceIso_inv_linearMap (b' : Module.Basis ι Γ(X, U.opens) Γ(M, U.opens)) :
    (M.affineSpaceIso U b).inv ≫ AffineSpace.linearMap (transitionMatrix b b') =
      (M.affineSpaceIso U b').inv := by
  refine AffineSpace.hom_ext (by simp) fun i ↦ ?_
  have h (c : Γ(X, U.opens)) : (M.affineSpaceIso U b).inv.appTop
      ((𝔸(ι; U.opens) ↘ U.opens).appTop (U.opens.topIso.inv c)) =
      (Scheme.ΓSpecIso (M.symAlgebra U.opens)).inv (M.toSymAlgebra U.opens c) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, affineSpaceIso_inv_over,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, IsAffineOpen.isoSpec_inv_appTop,
      CommRingCat.comp_apply, Iso.inv_hom_id_apply, ← CommRingCat.comp_apply,
      ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.linearMap_appTop_coord,
    map_sum]
  simp only [map_mul, transitionMatrix, Matrix.map_apply, Matrix.transpose_apply, h,
    affineSpaceIso_inv_appTop_coord]
  simp only [← map_mul, ← map_sum]
  refine congrArg _ ?_
  have hb := congrArg (SymmetricAlgebra.ι Γ(X, U.opens) Γ(M, U.opens)) (b.sum_repr (b' i))
  rw [map_sum] at hb
  rw [← hb]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [_root_.map_smul, Algebra.smul_def, Module.Basis.toMatrix_apply]
  rfl

/-- Changes of trivialisation are linear. -/
@[reassoc]
lemma linearMap_affineSpaceIso_hom (b' : Module.Basis ι Γ(X, U.opens) Γ(M, U.opens)) :
    AffineSpace.linearMap (transitionMatrix b b') ≫ (M.affineSpaceIso U b').hom =
      (M.affineSpaceIso U b).hom := by
  rw [← cancel_epi (M.affineSpaceIso U b).inv, reassoc_of% (affineSpaceIso_inv_linearMap b b'),
    Iso.inv_hom_id, Iso.inv_hom_id]

end Trivialization
/-! ### The vector bundle atlas of a locally free module -/

section Atlas

variable {M : X.Modules} [M.IsQuasicoherent] {U D : X.BasicAffineOpens} {ι : Type u}

/-- The restriction to a basic open `D ≤ U` of a basis of `Γ(M, U)`: a basis of
`Γ(M, D) = Γ(X, D) ⊗_{Γ(X, U)} Γ(M, U)`. -/
noncomputable def basisRes (h : D ≤ U) (b : Module.Basis ι Γ(X, U.opens) Γ(M, U.opens)) :
    Module.Basis ι Γ(X, D.opens) Γ(M, D.opens) :=
  letI := resAlgebra (BasicAffineOpens.opens_le_opens h)
  letI := resModule M (BasicAffineOpens.opens_le_opens h)
  haveI := resIsScalarTower M (BasicAffineOpens.opens_le_opens h)
  (M.isBaseChange_sectionsRes (BasicAffineOpens.opens_le_opens h) U.isAffineOpen h.choose
    h.choose_spec).basis b

lemma basisRes_apply (h : D ≤ U) (b : Module.Basis ι Γ(X, U.opens) Γ(M, U.opens)) (i : ι) :
    basisRes h b i = M.presheaf.map (homOfLE (BasicAffineOpens.opens_le_opens h)).op (b i) :=
  letI := resAlgebra (BasicAffineOpens.opens_le_opens h)
  letI := resModule M (BasicAffineOpens.opens_le_opens h)
  haveI := resIsScalarTower M (BasicAffineOpens.opens_le_opens h)
  IsBaseChange.basis_apply _ _ i

/-- The trivialisations over `U` and over a basic open `D ≤ U` are compatible. -/
lemma specMap_symAlgebraMap_affineSpaceIso_inv (h : D ≤ U)
    (b : Module.Basis ι Γ(X, U.opens) Γ(M, U.opens)) :
    Spec.map (M.symAlgebraMap (BasicAffineOpens.opens_le_opens h)) ≫
        (M.affineSpaceIso U b).inv =
      (M.affineSpaceIso D (basisRes h b)).inv ≫
        AffineSpace.map ι (X.homOfLE (BasicAffineOpens.opens_le_opens h)) := by
  refine AffineSpace.hom_ext ?_ fun i ↦ ?_
  · rw [Category.assoc, affineSpaceIso_inv_over, ← Spec.map_comp_assoc,
      toSymAlgebra_symAlgebraMap, Spec.map_comp_assoc,
      BasicAffineOpens.specMap_res_isoSpec_inv, Category.assoc, AffineSpace.map_over,
      affineSpaceIso_inv_over_assoc]
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, affineSpaceIso_inv_appTop_coord,
      ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord,
      affineSpaceIso_inv_appTop_coord, basisRes_apply, symAlgebraMap_ι]

@[reassoc]
lemma map_affineSpaceIso_hom_vectorBundleι (h : D ≤ U)
    (b : Module.Basis ι Γ(X, U.opens) Γ(M, U.opens)) :
    AffineSpace.map ι (X.homOfLE (BasicAffineOpens.opens_le_opens h)) ≫
        (M.affineSpaceIso U b).hom ≫ M.vectorBundleι U =
      (M.affineSpaceIso D (basisRes h b)).hom ≫ M.vectorBundleι D := by
  rw [← cancel_epi (M.affineSpaceIso D (basisRes h b)).inv, ← Category.assoc,
    ← specMap_symAlgebraMap_affineSpaceIso_inv, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id_assoc, M.specMap_symAlgebraMap_vectorBundleι h]

variable (M) {d : ℕ}

/-- Blueprint `def-asd-vector-bundle-zero-section` (trivialisations): a basis `b` of `Γ(M, U)`
of size `d` over an affine open `U` trivialises the vector bundle over `U`:
`V(M)|_U ≅ 𝔸^d_U`, compatibly with the projections and the zero sections. -/
@[simps V j]
noncomputable def vectorBundleTrivialization (U : X.BasicAffineOpens)
    (b : Module.Basis (ULift.{u} (Fin d)) Γ(X, U.opens) Γ(M, U.opens)) :
    VectorBundleTrivialization d M.vectorBundleProj M.vectorBundleZeroSection where
  V := U.opens
  j := U.opens.ι
  ι := (M.affineSpaceIso U b).hom ≫ M.vectorBundleι U
  isPullback := by
    have := (IsPullback.of_horiz_isIso (fst := (M.affineSpaceIso U b).hom)
      (snd := 𝔸(ULift.{u} (Fin d); U.opens) ↘ U.opens)
      (f := Spec.map (M.toSymAlgebra U.opens) ≫ U.isAffineOpen.isoSpec.inv) (g := 𝟙 _)
      ⟨by simp⟩).paste_horiz (M.isPullback_vectorBundleι U).flip
    rwa [Category.id_comp] at this
  zeroSection_ι := by
    rw [zeroSection_affineSpaceIso_hom_assoc, ι_vectorBundleZeroSection]

lemma vectorBundleTrivialization_ι (U : X.BasicAffineOpens)
    (b : Module.Basis (ULift.{u} (Fin d)) Γ(X, U.opens) Γ(M, U.opens)) :
    (M.vectorBundleTrivialization U b).ι = (M.affineSpaceIso U b).hom ≫ M.vectorBundleι U :=
  rfl

/-- The trivialisations of `V(M)` given by bases over affine opens are linearly compatible: on
the overlap, the change of trivialisation is given by `transitionMatrix`. -/
lemma isLinearlyCompatible_vectorBundleTrivialization {U U' : X.BasicAffineOpens}
    (b : Module.Basis (ULift.{u} (Fin d)) Γ(X, U.opens) Γ(M, U.opens))
    (b' : Module.Basis (ULift.{u} (Fin d)) Γ(X, U'.opens) Γ(M, U'.opens)) :
    (M.vectorBundleTrivialization U b).IsLinearlyCompatible
      (M.vectorBundleTrivialization U' b') := by
  intro w
  obtain ⟨D, hDU, hDU', y, hy⟩ :=
    Scheme.Cover.LocallyDirected.directed (𝒰 := X.directedBasicAffineCover) (i := U) (j := U') w
  let D' : X.BasicAffineOpens := D
  have hD : D' ≤ U := leOfHom hDU
  have hD' : D' ≤ U' := leOfHom hDU'
  let h : (D'.opens : Scheme.{u}) ⟶ Limits.pullback (M.vectorBundleTrivialization U b).j
      (M.vectorBundleTrivialization U' b').j :=
    pullback.lift (X.homOfLE (BasicAffineOpens.opens_le_opens hD))
      (X.homOfLE (BasicAffineOpens.opens_le_opens hD')) (by simp [vectorBundleTrivialization_j])
  have : IsOpenImmersion (h ≫ pullback.fst _ _) := by
    rw [pullback.lift_fst]
    infer_instance
  have : IsOpenImmersion h := IsOpenImmersion.of_comp _ (pullback.fst _ _)
  refine ⟨D'.opens, h, this, ⟨y, hy⟩, transitionMatrix (basisRes hD b) (basisRes hD' b'), ?_⟩
  simp only [vectorBundleTrivialization_ι, h, pullback.lift_fst,
    pullback.lift_snd]
  rw [map_affineSpaceIso_hom_vectorBundleι hD' b', map_affineSpaceIso_hom_vectorBundleι hD b,
    linearMap_affineSpaceIso_hom_assoc]

variable {M} in
/-- The vector bundle atlas of `V(M)` given by all bases of size `d` of the sections over affine
opens, provided they cover `X`. -/
noncomputable def vectorBundleAtlas
    (hM : ∀ x : X, ∃ (U : X.BasicAffineOpens) (_ : x ∈ U.opens),
      Nonempty (Module.Basis (ULift.{u} (Fin d)) Γ(X, U.opens) Γ(M, U.opens))) :
    VectorBundleAtlas d M.vectorBundleProj M.vectorBundleZeroSection where
  I := Σ U : X.BasicAffineOpens, Module.Basis (ULift.{u} (Fin d)) Γ(X, U.opens) Γ(M, U.opens)
  trivialization i := M.vectorBundleTrivialization i.1 i.2
  exists_mem_range x := by
    obtain ⟨U, hx, ⟨b⟩⟩ := hM x
    exact ⟨⟨U, b⟩, ⟨x, hx⟩, rfl⟩
  isLinearlyCompatible i k := M.isLinearlyCompatible_vectorBundleTrivialization i.2 k.2

omit [M.IsQuasicoherent] in
/-- If `M` is locally free of rank `d`, every point of `X` has an affine open neighbourhood `U`
over which `Γ(M, U)` is free of rank `d`. -/
lemma exists_basis_of_isLocallyFreeOfRank [M.IsLocallyFreeOfRank d] (x : X) :
    ∃ (U : X.BasicAffineOpens) (_ : x ∈ U.opens),
      Nonempty (Module.Basis (ULift.{u} (Fin d)) Γ(X, U.opens) Γ(M, U.opens)) := by
  obtain ⟨I, Y, hY, he⟩ :=
    SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u, u, u}.1
      ‹M.IsLocallyFreeOfRank d›
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (((Opens.coversTop_iff _ _).1 hY).ge (Set.mem_univ x) : x ∈ ⨆ i, Y i)
  obtain ⟨V, hV, hxV, hVY⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hi
  classical
  exact ⟨BasicAffineOpens.ofAffineOpens ⟨V, hV⟩, hxV,
    ⟨Module.Basis.ofEquivFun (sectionsLinearEquivOfOverIsoFree (he i).some hVY)⟩⟩

/-- The vector bundle of a locally free module of rank `d` is a vector bundle of rank `d`: it is
Zariski locally `𝔸^d` with its zero section, with linear transition maps. In particular it is
stable under base change (`AlgebraicGeometry.IsVectorBundleOfRank.baseChange`). -/
instance isVectorBundleOfRank_vectorBundle [M.IsLocallyFreeOfRank d] :
    IsVectorBundleOfRank d M.vectorBundleProj M.vectorBundleZeroSection :=
  ⟨⟨vectorBundleAtlas M.exists_basis_of_isLocallyFreeOfRank⟩⟩

/-- The projection of the vector bundle of a locally free module of rank `d` is smooth of
relative dimension `d`. -/
instance smoothOfRelativeDimension_vectorBundleProj [M.IsLocallyFreeOfRank d] :
    SmoothOfRelativeDimension d M.vectorBundleProj :=
  IsVectorBundleOfRank.smoothOfRelativeDimension (z := M.vectorBundleZeroSection)

end Atlas

end AlgebraicGeometry.Scheme.Modules
