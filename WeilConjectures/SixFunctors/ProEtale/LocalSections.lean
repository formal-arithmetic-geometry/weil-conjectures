/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Products
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Local sections of pro-étale sheaves of modules

Let `X` be a scheme and `Λ` a commutative ring. This file records how the sections of some
basic pro-étale sheaves of `Λ`-modules look like locally, i.e. after restriction to the members
of a covering sieve.

* `AlgebraicGeometry.Scheme.ProEt.weqLocallyBijective_moduleCat`: on the small pro-étale site,
  the morphisms of presheaves of modules inverted by sheafification are exactly the locally
  bijective ones. In particular the unit `toSheafify` of sheafification is locally surjective
  and locally injective.
* `AlgebraicGeometry.Scheme.ProEt.exists_of_mem_topology`: a covering sieve of an object `U`
  with `U.left` nonempty contains a morphism.
* `AlgebraicGeometry.ProEtale.exists_sieve_toSheafify_eq`: a section of the sheafification of
  a presheaf `P` is locally the image of a section of `P`.
* `AlgebraicGeometry.ProEtale.exists_sieve_unitSection_eq`: a section of the unit sheaf
  `𝟙_ (Sheaf _ _)` is locally a constant `r : Λ`.
* `AlgebraicGeometry.ProEtale.exists_sieve_sum_tensorSectionMap_eq`: a section of `F ⊗ G` is
  locally a finite sum of images of pure tensors `x ⊗ₜ y` under the canonical map
  `tensorSectionMap F G V : F(V) ⊗ G(V) ⟶ (F ⊗ G)(V)`.
* `AlgebraicGeometry.ProEtale.exists_sieve_sum_sigmaι_eq`: a section of a coproduct `∐ F` is
  locally a finite sum of images of sections of the `F i` under the coproduct injections.
* `AlgebraicGeometry.ProEtale.unitSection_app_injective` and
  `AlgebraicGeometry.ProEtale.constantSheaf_toSheafify_app_injective`: over a nonempty `U`, the
  constant sections of the unit sheaf, and more generally of a constant sheaf, are faithful.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite MonoidalCategory

namespace AlgebraicGeometry

namespace Scheme.ProEt

/-- On a small site with objects in `Type (u + 1)`, the morphisms of presheaves of modules which
become isomorphisms after sheafification are exactly the locally bijective ones. -/
lemma weqLocallyBijective_moduleCat_of_small (Λ : Type (u + 1)) [CommRing Λ] {C : Type (u + 1)}
    [SmallCategory C] (K : GrothendieckTopology C) :
    K.WEqualsLocallyBijective (ModuleCat.{u + 1} Λ) :=
  inferInstance

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]

/-- On the small pro-étale site, the morphisms of presheaves of modules which become
isomorphisms after sheafification are exactly the locally bijective ones. This is transported
from the small model of the essentially small site, where sheafification is the plus
construction. -/
instance weqLocallyBijective_moduleCat :
    (topology X).WEqualsLocallyBijective (ModuleCat.{u + 1} Λ) :=
  have := weqLocallyBijective_moduleCat_of_small Λ
    ((equivSmallModel.{u + 1} X.ProEt).inverse.inducedTopology (topology X))
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1, u + 1, u + 2,
    u + 1, u + 1, u + 1} (topology X)

variable {X}

/-- A covering sieve of a nonempty object of the small pro-étale site is nonempty: pro-étale
covers are jointly surjective. -/
lemma exists_of_mem_topology {U : X.ProEt} [Nonempty U.left] {S : Sieve U}
    (hS : S ∈ topology X U) : ∃ (V : X.ProEt) (f : V ⟶ U), S f := by
  rw [mem_topology_iff] at hS
  obtain ⟨R, hR, hle⟩ := hS
  obtain ⟨ι, Z, φ, rfl⟩ := R.exists_eq_ofArrows
  rw [mem_precoverage_iff, Presieve.map_ofArrows] at hR
  have hR' := (propQCPrecoverage_le_precoverage : proetalePrecoverage.{u} ≤
    Scheme.precoverage @WeaklyEtale) _ hR
  obtain ⟨i, -⟩ :=
    ((Scheme.ofArrows_mem_precoverage_iff _).1 hR').1 (Classical.arbitrary U.left)
  exact ⟨Z i, φ i, hle _ _ (Presieve.ofArrows.mk i)⟩

end Scheme.ProEt

namespace ProEtale

open Scheme.ProEt

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]

/-- A section of the target of a locally surjective morphism `φ : P ⟶ Q` of presheaves of
modules on the small pro-étale site is, after restriction to the members of a covering sieve,
the image of a section of `P`. -/
lemma exists_sieve_eq_of_isLocallySurjective {P Q : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} Λ}
    (φ : P ⟶ Q) [Presheaf.IsLocallySurjective (topology X) φ] {U : X.ProEt}
    (s : Q.obj (op U)) :
    ∃ S ∈ topology X U, ∀ ⦃V : X.ProEt⦄ (f : V ⟶ U), S f →
      ∃ t : P.obj (op V), φ.app (op V) t = Q.map f.op s :=
  ⟨_, Presheaf.imageSieve_mem (topology X) φ s, fun _ _ hf ↦ hf⟩

/-- **Sections of a sheafification.** A section of the sheafification of a presheaf `P` is,
after restriction to the members of a covering sieve, the image of a section of `P` under the
unit `toSheafify`. -/
lemma exists_sieve_toSheafify_eq (P : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} Λ) {U : X.ProEt}
    (s : ((presheafToSheaf (topology X) _).obj P).obj.obj (op U)) :
    ∃ S ∈ topology X U, ∀ ⦃V : X.ProEt⦄ (f : V ⟶ U), S f →
      ∃ t : P.obj (op V), (toSheafify (topology X) P).app (op V) t =
        ((presheafToSheaf (topology X) _).obj P).obj.map f.op s :=
  exists_sieve_eq_of_isLocallySurjective (toSheafify (topology X) P) s

/-- Over a nonempty `U`, the unit `toSheafify` of sheafification is injective on sections over
`U` as soon as all restriction maps of `P` out of `U` are injective: `toSheafify` is locally
injective, and every covering sieve of `U` is nonempty. -/
lemma toSheafify_app_injective (P : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} Λ) {U : X.ProEt}
    [Nonempty U.left] (hP : ∀ ⦃V : X.ProEt⦄ (f : V ⟶ U), Function.Injective (P.map f.op)) :
    Function.Injective ((toSheafify (topology X) P).app (op U)) := by
  intro a b h
  obtain ⟨V, f, hf⟩ := exists_of_mem_topology
    (Presheaf.equalizerSieve_mem (topology X) (toSheafify (topology X) P) a b h)
  exact hP f hf

section Unit

/-- The constant sections of the unit sheaf: the unit of sheafification of the constant
presheaf `Λ`, followed by the identification of its sheafification with `𝟙_ (Sheaf _ _)`. -/
noncomputable def unitSection :
    𝟙_ (X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} Λ) ⟶
      (𝟙_ (Sheaf (topology X) (ModuleCat.{u + 1} Λ))).obj :=
  toSheafify (topology X) _ ≫
    (sheafToPresheaf _ _).map (Functor.Monoidal.εIso (presheafToSheaf (topology X) _)).inv

instance : Presheaf.IsLocallySurjective (topology X) (unitSection (X := X) (Λ := Λ)) := by
  dsimp [unitSection]
  infer_instance

/-- The constant sections of the unit sheaf are compatible with restriction. -/
lemma unitSection_app_map {U V : X.ProEt} (f : V ⟶ U) (r : Λ) :
    (𝟙_ (Sheaf (topology X) (ModuleCat.{u + 1} Λ))).obj.map f.op
        ((unitSection (X := X)).app (op U) r) =
      (unitSection (X := X)).app (op V) r := by
  rw [← NatTrans.naturality_apply]
  rfl

/-- **Sections of the unit sheaf.** A section of `𝟙_ (Sheaf _ _)` is, after restriction to the
members of a covering sieve, a constant `r : Λ`. -/
lemma exists_sieve_unitSection_eq {U : X.ProEt}
    (s : (𝟙_ (Sheaf (topology X) (ModuleCat.{u + 1} Λ))).obj.obj (op U)) :
    ∃ S ∈ topology X U, ∀ ⦃V : X.ProEt⦄ (f : V ⟶ U), S f →
      ∃ r : Λ, (unitSection (X := X)).app (op V) r =
        (𝟙_ (Sheaf (topology X) (ModuleCat.{u + 1} Λ))).obj.map f.op s :=
  exists_sieve_eq_of_isLocallySurjective unitSection s

/-- Over a nonempty `U`, the constant sections `Λ → 𝟙_ (Sheaf _ _)(U)` are injective. -/
lemma unitSection_app_injective {U : X.ProEt} [Nonempty U.left] :
    Function.Injective ((unitSection (X := X) (Λ := Λ)).app (op U)) := by
  intro a b h
  simp only [unitSection, NatTrans.comp_app, ConcreteCategory.comp_apply] at h
  exact toSheafify_app_injective _ (fun _ _ ↦ Function.injective_id)
    ((ConcreteCategory.bijective_of_isIso _).1 h)

/-- Over a nonempty `U`, the constant sections `M → (constantSheaf M)(U)` of the constant sheaf
attached to a `Λ`-module `M` are injective. -/
lemma constantSheaf_toSheafify_app_injective (M : ModuleCat.{u + 1} Λ) {U : X.ProEt}
    [Nonempty U.left] :
    Function.Injective
      ((toSheafify (topology X) ((Functor.const X.ProEtᵒᵖ).obj M)).app (op U) :
        M → ((constantSheaf (topology X) _).obj M).obj.obj (op U)) :=
  toSheafify_app_injective _ fun _ _ ↦ Function.injective_id

end Unit

section Tensor

variable (F G : Sheaf (topology X) (ModuleCat.{u + 1} Λ))

/-- The canonical morphism from the objectwise tensor product of the underlying presheaves of
two sheaves to their tensor product as sheaves. -/
noncomputable def tensorSection : F.obj ⊗ G.obj ⟶ (F ⊗ G).obj :=
  toSheafify (topology X) (F.obj ⊗ G.obj) ≫ (sheafToPresheaf _ _).map
    ((Functor.Monoidal.μIso (presheafToSheaf (topology X) _) F.obj G.obj).inv ≫
      ((sheafificationAdjunction _ _).counit.app F ⊗ₘ
        (sheafificationAdjunction _ _).counit.app G))

instance : Presheaf.IsLocallySurjective (topology X) (tensorSection F G) := by
  dsimp [tensorSection]
  infer_instance

/-- The canonical map `F(V) ⊗ G(V) ⟶ (F ⊗ G)(V)` on sections over `V`. -/
noncomputable def tensorSectionMap (V : X.ProEt) :
    F.obj.obj (op V) ⊗ G.obj.obj (op V) ⟶ (F ⊗ G).obj.obj (op V) :=
  (tensorSection F G).app (op V)

/-- The maps `tensorSectionMap` are natural in `V`. -/
lemma tensorSectionMap_naturality {U V : X.ProEt} (f : V ⟶ U) (x : F.obj.obj (op U))
    (y : G.obj.obj (op U)) :
    (F ⊗ G).obj.map f.op (tensorSectionMap F G U (x ⊗ₜ y)) =
      tensorSectionMap F G V (F.obj.map f.op x ⊗ₜ G.obj.map f.op y) :=
  (NatTrans.naturality_apply (tensorSection F G) f.op (x ⊗ₜ[Λ] y)).symm

/-- **Sections of a tensor product.** A section of `F ⊗ G` is, after restriction to the members
of a covering sieve, a finite sum of images of pure tensors under `tensorSectionMap`. -/
lemma exists_sieve_sum_tensorSectionMap_eq {U : X.ProEt} (s : (F ⊗ G).obj.obj (op U)) :
    ∃ S ∈ topology X U, ∀ ⦃V : X.ProEt⦄ (f : V ⟶ U), S f →
      ∃ (n : ℕ) (x : Fin n → F.obj.obj (op V)) (y : Fin n → G.obj.obj (op V)),
        ∑ k, tensorSectionMap F G V (x k ⊗ₜ y k) = (F ⊗ G).obj.map f.op s := by
  obtain ⟨S, hS, h⟩ := exists_sieve_eq_of_isLocallySurjective (tensorSection F G) s
  refine ⟨S, hS, fun V f hf ↦ ?_⟩
  obtain ⟨t, ht⟩ := h f hf
  obtain ⟨n, x, y, rfl⟩ := TensorProduct.exists_sum_tmul_eq t
  refine ⟨n, x, y, ?_⟩
  rw [← ht, ← map_sum]
  rfl

end Tensor

section Coproduct

variable {ι : Type w} [HasColimitsOfShape (Discrete ι) (ModuleCat.{u + 1} Λ)]
  (F : ι → Sheaf (topology X) (ModuleCat.{u + 1} Λ)) [HasCoproduct F]

/-- The canonical morphism from the coproduct of the underlying presheaves of a family of
sheaves to the underlying presheaf of their coproduct as sheaves. It becomes an isomorphism
after sheafification. -/
noncomputable def sheafSigmaComparison : ∐ (fun i ↦ (F i).obj) ⟶ (∐ F).obj :=
  Sigma.desc fun i ↦ (Sigma.ι F i).hom

/-- The comparison morphism `sheafSigmaComparison F` is inverted by sheafification. -/
lemma W_sheafSigmaComparison : (topology X).W (sheafSigmaComparison F) := by
  intro Q hQ
  let Q' : Sheaf (topology X) (ModuleCat.{u + 1} Λ) := ⟨Q, hQ⟩
  refine ⟨fun g₁ g₂ h ↦ ?_, fun g ↦ ?_⟩
  · have : (ObjectProperty.homMk g₁ : ∐ F ⟶ Q') = ObjectProperty.homMk g₂ :=
      Sigma.hom_ext _ _ fun i ↦ by
        ext1
        simpa [sheafSigmaComparison] using Sigma.ι _ i ≫= h
    exact congr($(this).hom)
  · refine ⟨(Sigma.desc fun i ↦
      (ObjectProperty.homMk (Sigma.ι (fun i ↦ (F i).obj) i ≫ g) : F i ⟶ Q')).hom, ?_⟩
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    simp only [sheafSigmaComparison, Sigma.ι_desc_assoc]
    rw [← ObjectProperty.FullSubcategory.comp_hom, Sigma.ι_desc]
    rfl

instance : Presheaf.IsLocallySurjective (topology X) (sheafSigmaComparison F) :=
  (W_sheafSigmaComparison F).isLocallySurjective

/-- **Sections of a coproduct.** A section of `∐ F` is, after restriction to the members of a
covering sieve, a finite sum of images of sections of the `F i` under the coproduct
injections. -/
lemma exists_sieve_sum_sigmaι_eq {U : X.ProEt} (s : (∐ F).obj.obj (op U)) :
    ∃ S ∈ topology X U, ∀ ⦃V : X.ProEt⦄ (f : V ⟶ U), S f →
      ∃ (t : Finset ι) (x : ∀ i, (F i).obj.obj (op V)),
        ∑ i ∈ t, (Sigma.ι F i).hom.app (op V) (x i) = (∐ F).obj.map f.op s := by
  obtain ⟨S, hS, h⟩ := exists_sieve_eq_of_isLocallySurjective (sheafSigmaComparison F) s
  refine ⟨S, hS, fun V f hf ↦ ?_⟩
  obtain ⟨y, hy⟩ := h f hf
  obtain ⟨t, x, rfl⟩ := ModuleCat.exists_finset_sum_inj_eq_of_isColimit
    (isColimitCofanMkObjOfIsColimit ((evaluation _ _).obj (op V)) _ _
      (coproductIsCoproduct fun i ↦ (F i).obj)) y
  refine ⟨t, x, ?_⟩
  rw [← hy, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app
    (Sigma.ι_desc (fun i ↦ (Sigma.ι F i).hom) i) (op V)) (x i)).symm

end Coproduct

end ProEtale

end AlgebraicGeometry
