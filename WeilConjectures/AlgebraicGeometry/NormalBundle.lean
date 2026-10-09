/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import WeilConjectures.Mathlib.RingTheory.Flat.IsBaseChange

/-!
# The normal bundle of a closed immersion

For a quasi-coherent ideal `I` on a scheme `X`, the *relative spectrum of the symmetric algebra*
`V(I) = Spec_X (Sym_{𝒪_X} I)` is glued (`Scheme.Cover.RelativeGluingData`) from the affine
pieces `Spec (Sym_{Γ(U)} I(U))` over the affine opens `U ⊆ X`. It comes with its structure
morphism `V(I) ⟶ X` and the zero section `X ⟶ V(I)`, given by the augmentation
`Sym I ⟶ 𝒪_X`.

For a closed immersion `i : Z ⟶ X` with ideal `I`, the *normal bundle* is

`N_{Z/X} = V(I) ×_X Z = Spec_Z (Sym_{𝒪_Z} (I/I²))`,

since `Sym_{𝒪_X}(I) ⊗_{𝒪_X} 𝒪_Z = Sym_{𝒪_Z}(I ⊗ 𝒪_Z)` and `I ⊗_{𝒪_X} 𝒪_X/I = I/I²`. It is
determined by `i`: over an affine open `U ⊆ X` it is `Spec (Sym_{Γ(U)} I(U)) ×_U i⁻¹U`
(`AlgebraicGeometry.Scheme.Hom.isPullback_normalBundle`). For a regular immersion of pure
codimension `c` the conormal sheaf `I/I²` is locally free of rank `c` and `N_{Z/X}` is a vector
bundle of rank `c` (blueprint `def-pur-normal-bundle`).

## Main definitions

- `AlgebraicGeometry.Scheme.IdealSheafData.symSpec`: `V(I) = Spec_X (Sym I)`, with
  `symSpecMap : V(I) ⟶ X` and `symSpecZeroSection : X ⟶ V(I)`.
- `AlgebraicGeometry.Scheme.Hom.normalBundle`: the normal bundle `N_{Z/X}` of a closed immersion,
  with `normalBundleProj : N_{Z/X} ⟶ Z` and `normalBundleZeroSection : Z ⟶ N_{Z/X}`.

## Main statements

- `AlgebraicGeometry.Scheme.IdealSheafData.isPullback_symSpecι`: over an affine open `U`, `V(I)`
  is `Spec (Sym_{Γ(U)} I(U))`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

namespace IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The restriction map `Γ(X, V) ⟶ Γ(X, U)` of affine opens `U ≤ V` is flat: it is the map on
global sections of the open immersion `U ⟶ V` of affine schemes. -/
lemma flat_presheaf_map {U V : X.affineOpens} (h : U ≤ V) :
    (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom.Flat := by
  rw [← HasRingHomProperty.Spec_iff (P := @Flat)]
  have : Spec.map (X.presheaf.map (homOfLE (X := X.Opens) h).op) =
      U.2.isoSpec.inv ≫ X.homOfLE h ≫ V.2.isoSpec.hom := by
    rw [← Category.assoc, ← specMap_res_isoSpec_inv h, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  rw [this]
  infer_instance

/-- The symmetric algebra `Sym_{Γ(U)} I(U)` of the ideal `I(U)` over an affine open `U`. -/
noncomputable def symAlgebra (U : X.affineOpens) : CommRingCat.{u} :=
  .of (SymmetricAlgebra Γ(X, U) (I.ideal U))

/-- The structure map `Γ(U) ⟶ Sym_{Γ(U)} I(U)`. -/
noncomputable def toSymAlgebra (U : X.affineOpens) : Γ(X, U) ⟶ I.symAlgebra U :=
  CommRingCat.ofHom (algebraMap Γ(X, U) (SymmetricAlgebra Γ(X, U) (I.ideal U)))

/-- The augmentation `Sym_{Γ(U)} I(U) ⟶ Γ(U)`, killing `I(U)`. -/
noncomputable def symAlgebraAugmentation (U : X.affineOpens) : I.symAlgebra U ⟶ Γ(X, U) :=
  CommRingCat.ofHom (SymmetricAlgebra.algebraMapInv (R := Γ(X, U)) (M := I.ideal U)).toRingHom

@[reassoc (attr := simp)]
lemma toSymAlgebra_symAlgebraAugmentation (U : X.affineOpens) :
    I.toSymAlgebra U ≫ I.symAlgebraAugmentation U = 𝟙 _ := by
  ext r
  exact SymmetricAlgebra.algebraMap_leftInverse (I.ideal U) r

section Restriction

variable {U V : X.affineOpens} (h : U ≤ V)

/-- The restriction `I(V) ⟶ I(U)` for affine opens `U ≤ V`, as a `Γ(V)`-linear map; it exhibits
`I(U) = I(V) Γ(U)` as the base change of `I(V)` (`isBaseChange_idealRestrict`). -/
noncomputable def idealRestrict :
    letI := (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom.toAlgebra
    I.ideal V →ₗ[Γ(X, V)] I.ideal U :=
  letI := (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom.toAlgebra
  ((LinearEquiv.ofEq _ _ (I.map_ideal h)).restrictScalars Γ(X, V)).toLinearMap ∘ₗ
    Algebra.idealMap Γ(X, U) (I.ideal V)

@[simp]
lemma coe_idealRestrict_apply (x : I.ideal V) :
    (I.idealRestrict h x : Γ(X, U)) = X.presheaf.map (homOfLE (X := X.Opens) h).op x :=
  rfl

lemma isBaseChange_idealRestrict :
    letI := (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom.toAlgebra
    IsBaseChange Γ(X, U) (I.idealRestrict h) := by
  let := (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom.toAlgebra
  have : Module.Flat Γ(X, V) Γ(X, U) := flat_presheaf_map h
  exact (Algebra.isBaseChange_idealMap Γ(X, U) (I.ideal V)).comp
    (IsBaseChange.ofEquiv (LinearEquiv.ofEq _ _ (I.map_ideal h)))

/-- The restriction `Sym_{Γ(V)} I(V) ⟶ Sym_{Γ(U)} I(U)` for affine opens `U ≤ V`. -/
noncomputable def symAlgebraMap : I.symAlgebra V ⟶ I.symAlgebra U :=
  letI := (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom.toAlgebra
  CommRingCat.ofHom (SymmetricAlgebra.mapOfIsScalarTower Γ(X, U) (I.idealRestrict h)).toRingHom

@[reassoc]
lemma toSymAlgebra_symAlgebraMap :
    I.toSymAlgebra V ≫ I.symAlgebraMap h =
      X.presheaf.map (homOfLE (X := X.Opens) h).op ≫ I.toSymAlgebra U := by
  let := (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom.toAlgebra
  ext r
  exact (SymmetricAlgebra.mapOfIsScalarTower Γ(X, U) (I.idealRestrict h)).commutes r

@[simp]
lemma symAlgebraMap_ι (x : I.ideal V) :
    (I.symAlgebraMap h).hom (SymmetricAlgebra.ι _ _ x) =
      SymmetricAlgebra.ι _ _ (I.idealRestrict h x) :=
  letI := (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom.toAlgebra
  SymmetricAlgebra.mapOfIsScalarTower_ι _ _

@[reassoc]
lemma symAlgebraMap_symAlgebraAugmentation :
    I.symAlgebraMap h ≫ I.symAlgebraAugmentation U =
      I.symAlgebraAugmentation V ≫ X.presheaf.map (homOfLE (X := X.Opens) h).op := by
  ext x
  induction x using SymmetricAlgebra.induction with
  | algebraMap r =>
    have h₁ := congr($(I.toSymAlgebra_symAlgebraMap_assoc h (I.symAlgebraAugmentation U)) r)
    have h₂ := congr($(I.toSymAlgebra_symAlgebraAugmentation_assoc V
      (X.presheaf.map (homOfLE (X := X.Opens) h).op)) r)
    simp only [toSymAlgebra_symAlgebraAugmentation, Category.comp_id] at h₁ h₂
    exact h₁.trans h₂.symm
  | ι x =>
    simp only [symAlgebraAugmentation, CommRingCat.hom_comp, RingHom.comp_apply,
      CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, symAlgebraMap_ι]
    exact (SymmetricAlgebra.algebraMapInv_ι (R := Γ(X, U)) (I.idealRestrict h x)).trans
      ((map_zero _).symm.trans (congrArg _
        (SymmetricAlgebra.algebraMapInv_ι (R := Γ(X, V)) (M := I.ideal V) x).symm))
  | mul a b ha hb => simp only [CommRingCat.hom_comp, RingHom.comp_apply, map_mul] at *; rw [ha, hb]
  | add a b ha hb => simp only [CommRingCat.hom_comp, RingHom.comp_apply, map_add] at *; rw [ha, hb]

/-- The square of rings `Γ(V) ⟶ Γ(U)`, `Γ(V) ⟶ Sym I(V)`, `Sym I(V) ⟶ Sym I(U)`,
`Γ(U) ⟶ Sym I(U)` is a pushout: `Sym_{Γ(U)} I(U) = Γ(U) ⊗_{Γ(V)} Sym_{Γ(V)} I(V)`. -/
lemma isPushout_symAlgebraMap :
    IsPushout (I.toSymAlgebra V) (X.presheaf.map (homOfLE (X := X.Opens) h).op)
      (I.symAlgebraMap h) (I.toSymAlgebra U) := by
  let := (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom.toAlgebra
  have := SymmetricAlgebra.isPushout_of_isBaseChange (I.isBaseChange_idealRestrict h)
  let := (SymmetricAlgebra.mapOfIsScalarTower Γ(X, U) (I.idealRestrict h)).toAlgebra
  have : IsScalarTower Γ(X, V) (SymmetricAlgebra Γ(X, V) (I.ideal V))
      (SymmetricAlgebra Γ(X, U) (I.ideal U)) :=
    .of_algebraMap_eq fun r ↦
      ((SymmetricAlgebra.mapOfIsScalarTower Γ(X, U) (I.idealRestrict h)).commutes r).symm
  exact (CommRingCat.isPushout_of_isPushout Γ(X, V) Γ(X, U)
    (SymmetricAlgebra Γ(X, V) (I.ideal V)) (SymmetricAlgebra Γ(X, U) (I.ideal U))).flip

end Restriction

lemma symAlgebra_hom_ext {U : X.affineOpens} {A : CommRingCat.{u}} {f g : I.symAlgebra U ⟶ A}
    (h₁ : I.toSymAlgebra U ≫ f = I.toSymAlgebra U ≫ g)
    (h₂ : ∀ x : I.ideal U, f.hom (SymmetricAlgebra.ι _ _ x) = g.hom (SymmetricAlgebra.ι _ _ x)) :
    f = g := by
  ext x
  induction x using SymmetricAlgebra.induction with
  | algebraMap r => exact congr($h₁ r)
  | ι x => exact h₂ x
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

lemma symAlgebraMap_id (U : X.affineOpens) : I.symAlgebraMap (le_refl U) = 𝟙 _ := by
  refine I.symAlgebra_hom_ext ?_ fun x ↦ ?_
  · rw [toSymAlgebra_symAlgebraMap, Category.comp_id,
      show homOfLE (X := X.Opens) (le_refl U.1) = 𝟙 _ from rfl, op_id, X.presheaf.map_id,
      Category.id_comp]
  · rw [symAlgebraMap_ι, CommRingCat.hom_id, RingHom.id_apply]
    congr 1
    refine Subtype.ext ?_
    rw [coe_idealRestrict_apply, show homOfLE (X := X.Opens) (le_refl U.1) = 𝟙 _ from rfl,
      op_id, X.presheaf.map_id, CommRingCat.id_apply]

lemma symAlgebraMap_comp {U V W : X.affineOpens} (hUV : U ≤ V) (hVW : V ≤ W) :
    I.symAlgebraMap hVW ≫ I.symAlgebraMap hUV = I.symAlgebraMap (hUV.trans hVW) := by
  refine I.symAlgebra_hom_ext ?_ fun x ↦ ?_
  · rw [toSymAlgebra_symAlgebraMap_assoc, toSymAlgebra_symAlgebraMap,
      toSymAlgebra_symAlgebraMap, ← Category.assoc, ← Functor.map_comp, ← op_comp]
    rfl
  · rw [CommRingCat.hom_comp, RingHom.comp_apply, symAlgebraMap_ι, symAlgebraMap_ι,
      symAlgebraMap_ι]
    congr 1
    refine Subtype.ext ?_
    simp only [coe_idealRestrict_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
    rfl

/-- The diagram `U ↦ Spec (Sym_{Γ(U)} I(U))` over the affine opens of `X`. -/
noncomputable def symSpecFunctor : X.affineOpens ⥤ Scheme.{u} where
  obj U := Spec (I.symAlgebra U)
  map {U V} f := Spec.map (I.symAlgebraMap (leOfHom f))
  map_id U := by
    rw [show leOfHom (𝟙 U) = le_refl U from rfl, symAlgebraMap_id, Spec.map_id]
  map_comp {U V W} f g := by
    rw [← Spec.map_comp, symAlgebraMap_comp]

/-- The structure maps `Spec (Sym_{Γ(U)} I(U)) ⟶ Spec Γ(U) ≅ U`. -/
noncomputable def symSpecNatTrans :
    I.symSpecFunctor ⟶ X.directedAffineCover.functorOfLocallyDirected where
  app U := Spec.map (I.toSymAlgebra U) ≫ U.2.isoSpec.inv
  naturality {U V} f := by
    have hG : X.directedAffineCover.functorOfLocallyDirected.map f =
        X.homOfLE (leOfHom f) := rfl
    rw [hG, Category.assoc, ← specMap_res_isoSpec_inv (leOfHom f)]
    change Spec.map (I.symAlgebraMap (leOfHom f)) ≫ _ = _
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, toSymAlgebra_symAlgebraMap]

lemma symSpecNatTrans_app (U : X.affineOpens) :
    I.symSpecNatTrans.app U = Spec.map (I.toSymAlgebra U) ≫ U.2.isoSpec.inv :=
  rfl

lemma symSpecNatTrans_equifibered : I.symSpecNatTrans.Equifibered := by
  intro U V f
  have key := isPullback_SpecMap_of_isPushout _ _ _ _ (I.isPushout_symAlgebraMap (leOfHom f))
  have w : Spec.map (X.presheaf.map (homOfLE (X := X.Opens) (leOfHom f)).op) ≫
      V.2.isoSpec.inv = U.2.isoSpec.inv ≫ X.homOfLE (leOfHom f) :=
    specMap_res_isoSpec_inv (leOfHom f)
  exact key.paste_vert (IsPullback.of_vert_isIso ⟨w⟩)

/-- The relative gluing datum of `V(I) = Spec_X (Sym I)`. -/
noncomputable def symSpecGluingData : X.directedAffineCover.RelativeGluingData where
  functor := I.symSpecFunctor
  natTrans := I.symSpecNatTrans
  equifibered := I.symSpecNatTrans_equifibered

instance : (I.symSpecFunctor ⋙ Scheme.forget).IsLocallyDirected :=
  inferInstanceAs ((I.symSpecGluingData.functor ⋙ Scheme.forget).IsLocallyDirected)

instance : HasColimit I.symSpecFunctor :=
  inferInstanceAs (HasColimit I.symSpecGluingData.functor)

/-- The relative spectrum `V(I) = Spec_X (Sym_{𝒪_X} I)` of the symmetric algebra of the ideal
`I`, glued from the affine pieces `Spec (Sym_{Γ(U)} I(U))`. -/
noncomputable def symSpec : Scheme.{u} :=
  I.symSpecGluingData.glued

/-- The structure morphism `V(I) ⟶ X`. -/
noncomputable def symSpecMap : I.symSpec ⟶ X :=
  I.symSpecGluingData.toBase

/-- The inclusion of the affine piece `Spec (Sym_{Γ(U)} I(U))` into `V(I)`. -/
noncomputable def symSpecι (U : X.affineOpens) : Spec (I.symAlgebra U) ⟶ I.symSpec :=
  colimit.ι I.symSpecFunctor U

instance (U : X.affineOpens) : IsOpenImmersion (I.symSpecι U) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι I.symSpecGluingData.functor U))

@[reassoc (attr := simp)]
lemma symSpecι_symSpecMap (U : X.affineOpens) :
    I.symSpecι U ≫ I.symSpecMap = Spec.map (I.toSymAlgebra U) ≫ U.2.isoSpec.inv ≫ U.1.ι :=
  (I.symSpecGluingData.ι_toBase U).trans (Category.assoc _ _ _)

@[reassoc]
lemma symSpecMap_comp_symSpecι {U V : X.affineOpens} (h : U ≤ V) :
    Spec.map (I.symAlgebraMap h) ≫ I.symSpecι V = I.symSpecι U :=
  colimit.w I.symSpecFunctor (homOfLE h)

/-- Over an affine open `U ⊆ X`, `V(I)` is `Spec (Sym_{Γ(U)} I(U))`: the square

```
Spec (Sym I(U)) ──symSpecι U──▶ V(I)
       │                          │
       ▼                          ▼
       U ─────────────────────▶   X
```

is cartesian. -/
lemma isPullback_symSpecι (U : X.affineOpens) :
    IsPullback (Spec.map (I.toSymAlgebra U) ≫ U.2.isoSpec.inv) (I.symSpecι U) U.1.ι
      I.symSpecMap :=
  I.symSpecGluingData.isPullback_natTrans_ι_toBase U

/-- The zero section `X ⟶ V(I)`, given on the affine piece over `U` by the augmentation
`Sym_{Γ(U)} I(U) ⟶ Γ(U)`. -/
noncomputable def symSpecZeroSection : X ⟶ I.symSpec :=
  X.directedAffineCover.glueMorphismsOfLocallyDirected
    (fun U ↦ U.2.isoSpec.hom ≫ Spec.map (I.symAlgebraAugmentation U) ≫ I.symSpecι U)
    fun {U V} f ↦ by
      have h : X.homOfLE (leOfHom f) ≫ V.2.isoSpec.hom =
          U.2.isoSpec.hom ≫ Spec.map (X.presheaf.map (homOfLE (X := X.Opens) (leOfHom f)).op) := by
        rw [← cancel_mono V.2.isoSpec.inv, Category.assoc, Category.assoc, Iso.hom_inv_id,
          Category.comp_id, specMap_res_isoSpec_inv, Iso.hom_inv_id_assoc]
      change X.homOfLE (leOfHom f) ≫ _ = _
      rw [reassoc_of% h, ← Spec.map_comp_assoc, ← I.symAlgebraMap_symAlgebraAugmentation,
        Spec.map_comp_assoc, symSpecMap_comp_symSpecι]

@[reassoc (attr := simp)]
lemma ι_symSpecZeroSection (U : X.affineOpens) :
    U.1.ι ≫ I.symSpecZeroSection =
      U.2.isoSpec.hom ≫ Spec.map (I.symAlgebraAugmentation U) ≫ I.symSpecι U :=
  X.directedAffineCover.map_glueMorphismsOfLocallyDirected _ _ U

@[reassoc (attr := simp)]
lemma symSpecZeroSection_symSpecMap : I.symSpecZeroSection ≫ I.symSpecMap = 𝟙 X := by
  refine X.directedAffineCover.hom_ext _ _ fun U ↦ ?_
  change U.1.ι ≫ _ = U.1.ι ≫ _
  rw [ι_symSpecZeroSection_assoc, symSpecι_symSpecMap, ← Spec.map_comp_assoc,
    toSymAlgebra_symAlgebraAugmentation, Spec.map_id, Category.id_comp, Iso.hom_inv_id_assoc,
    Category.comp_id]

end IdealSheafData

end AlgebraicGeometry.Scheme
