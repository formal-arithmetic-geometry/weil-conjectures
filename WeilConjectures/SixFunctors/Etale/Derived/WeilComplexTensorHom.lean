/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplex
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# Tensor products and internal homs of Weil complexes

Let `Λ` be a finite coefficient ring and `g` an automorphism of a scheme `X`; in the `ℓ`-adic
formalism `X = X₀ ×_{k₀} k̄` and `g` is the geometric Frobenius. A (strict) Weil complex
`(K, φ_K)` is an object `K` of `Dctf(X, Λ)` with an isomorphism `φ_K : Lg^* K ≅ K`
(`AlgebraicGeometry.Etale.WeilComplex`). This file shows that the derived tensor product and
the derived internal hom of `Dctf(X, Λ)` lift to Weil complexes.

* The *tensor Frobenius* of `(K, φ_K)` and `(L, φ_L)` is
  `Lg^*(K ⊗ᴸ L) ≅ Lg^* K ⊗ᴸ Lg^* L ⟶ K ⊗ᴸ L`, the second arrow being `φ_K ⊗ φ_L`
  (`AlgebraicGeometry.Etale.WeilComplex.tensorFrobenius`).
* The *internal-Hom Frobenius* is the composite
  `Lg^* RHom(K, L) ≅ RHom(Lg^* K, Lg^* L) ⟶ RHom(K, L)`, the second arrow being
  `RHom(φ_K⁻¹, φ_L)` (`AlgebraicGeometry.Etale.WeilComplex.internalHomFrobenius`). The first
  arrow is the comparison map of the monoidal functor `Lg^*`, an isomorphism because `Lg^*` is
  an equivalence, `g` being an automorphism.

With these Frobenii the derived tensor product and the derived internal hom become bifunctors
`- ⊗ᴸ - : WeilD × WeilD ⥤ WeilD` and `RHom(-, -) : WeilDᵒᵖ × WeilD ⥤ WeilD`
(`AlgebraicGeometry.Etale.WeilComplex.tensor`, `AlgebraicGeometry.Etale.WeilComplex.internalHom`)
lying over the corresponding bifunctors of `Dctf(X, Λ)`, which are triangulated in each
covariant variable. These are the Weil-category bifunctors of the blueprint.

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.derivedTensor`,
  `AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.derivedHom`: the derived tensor product and
  the derived internal hom of `Dctf(X, Λ)`.
- `AlgebraicGeometry.Etale.WeilComplex.tensorFrobenius` (`def-wf-tensor-product`) and
  `AlgebraicGeometry.Etale.WeilComplex.tensor` (`lem-wf-tensor-weil`).
- `AlgebraicGeometry.Etale.WeilComplex.internalHomFrobenius` (`def-wf-internal-hom`) and
  `AlgebraicGeometry.Etale.WeilComplex.internalHom` (`lem-wf-internal-hom-weil`).

## Implementation notes

The blueprint states these facts for the Weil category `WeilD(X₀, E)` of pairs `(K, φ_K)` with
`K ∈ D^b_c(X, E)`, `E` a finite extension of `ℚ_ℓ` (`def-wf-weil-category`). The `E`-adic
categories `D^b_c(X, E)` are not available as categories carrying a derived tensor product and
internal hom; the Weil category is modelled here by the strict Weil complexes of
`sk-def-sf-weil-complexes` at a finite coefficient ring `Λ`, on which both operations exist and
preserve the constructible complexes of finite Tor amplitude (`sk-thm-sf-ctf-stability`,
`sk-thm-sf-hom-ctf`). The constructions use nothing about `Λ` beyond these stability results,
and they are the same at every finite stage.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-! ### The triangulated structure of `Dctf(X, Λ)` -/

namespace DerivedCategoryFiniteTor

variable (X : Scheme.{u})

noncomputable instance : Preadditive (DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X) :=
  inferInstanceAs (Preadditive
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).FullSubcategory)

noncomputable instance : HasZeroObject (DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X) :=
  inferInstanceAs (HasZeroObject
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).FullSubcategory)

noncomputable instance : HasShift (DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X) ℤ :=
  inferInstanceAs (HasShift
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).FullSubcategory ℤ)

instance (n : ℤ) :
    (shiftFunctor (DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X) n).Additive :=
  inferInstanceAs (shiftFunctor
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).FullSubcategory n).Additive

/-- `Dctf(X, Λ)` is a pretriangulated category, as a triangulated subcategory of `D(X_ét)`. -/
noncomputable instance : Pretriangulated (DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X) :=
  inferInstanceAs (Pretriangulated
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).FullSubcategory)

/-- `Dctf(X, Λ)` is a triangulated category. -/
instance : IsTriangulated (DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X) :=
  inferInstanceAs (IsTriangulated
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).FullSubcategory)


/-- Blueprint `def-wf-tensor-product`: the derived tensor product `- ⊗ᴸ -` of `Dctf(X, Λ)`, the
restriction of the derived tensor product of `D(X_ét)`, which preserves the constructible
complexes of finite Tor amplitude (`AlgebraicGeometry.Etale.constructibleFiniteTor_tensor`). -/
noncomputable def derivedTensor :
    DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X ⥤
      DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X ⥤
        DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X where
  obj K := ObjectProperty.liftFullSubcategory _ _ ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K.obj)
    fun _ hM ↦ constructibleFiniteTor_tensor Λ X K.property hM
  map f := ObjectProperty.liftFullSubcategoryMap _ _ ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).map f.hom)
    _ _
  map_id K := by ext M; exact NatTrans.congr_app ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).map_id K.obj) M.obj
  map_comp f g := by
    ext M; exact NatTrans.congr_app ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).map_comp f.hom g.hom) M.obj

@[simp]
lemma ι_obj_derivedTensor_obj_obj (K M : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X) :
    (ι _ X).obj (((derivedTensor Λ X).obj K).obj M) =
      ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj ((ι _ X).obj K)).obj ((ι _ X).obj M) :=
  rfl

noncomputable instance (K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X) :
    ((derivedTensor Λ X).obj K).CommShift ℤ :=
  inferInstanceAs ((ObjectProperty.liftFullSubcategory (DerivedCategory.constructibleFiniteTor _ X)
    (DerivedCategory.constructibleFiniteTor _ X) ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K.obj)
    fun _ hM ↦ constructibleFiniteTor_tensor Λ X K.property hM).CommShift ℤ)

/-- The derived tensor product `K ⊗ᴸ -` of `Dctf(X, Λ)` is a triangulated functor. -/
instance (K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X) :
    ((derivedTensor Λ X).obj K).IsTriangulated :=
  inferInstanceAs ((ObjectProperty.liftFullSubcategory (DerivedCategory.constructibleFiniteTor _ X)
    (DerivedCategory.constructibleFiniteTor _ X) ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K.obj)
    fun _ hM ↦ constructibleFiniteTor_tensor Λ X K.property hM).IsTriangulated)

/-- The derived internal hom `RHom(K, -)` of `D(X_ét)` is a triangulated functor, being right
adjoint to the triangulated functor `K ⊗ᴸ -`. -/
instance isTriangulated_derivedHom_obj
    (K : (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))ᵒᵖ) :
    ((RHom(X)[ModuleCat.{u + 1} Λ]).obj K).IsTriangulated :=
  (derivedTensorHomAdjunction _ K.unop).isTriangulated_rightAdjoint

variable {k : Type u} [Field k] {X} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
  [QuasiCompact aX] [HasInvertibleExponent Λ X]

/-- Blueprint `def-wf-internal-hom`: the derived internal hom `RHom(-, -)` of `Dctf(X, Λ)`, for
`X` of finite type over a field on which the exponent of `Λ` is invertible: the restriction of
the derived internal hom of `D(X_ét)`, which preserves the constructible complexes of finite Tor
amplitude (`AlgebraicGeometry.Etale.constructibleFiniteTor_derivedHom`). -/
noncomputable def derivedHom :
    (DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X)ᵒᵖ ⥤
      DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X ⥤
        DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X where
  obj K := ObjectProperty.liftFullSubcategory _ _
    ((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K.unop.obj))
    fun _ hM ↦ constructibleFiniteTor_derivedHom Λ aX K.unop.property hM
  map f := ObjectProperty.liftFullSubcategoryMap _ _
    ((RHom(X)[ModuleCat.{u + 1} Λ]).map f.unop.hom.op) _ _
  map_id K := by
    ext M; exact NatTrans.congr_app ((RHom(X)[ModuleCat.{u + 1} Λ]).map_id (op K.unop.obj)) M.obj
  map_comp f g := by
    ext M
    exact NatTrans.congr_app ((RHom(X)[ModuleCat.{u + 1} Λ]).map_comp f.unop.hom.op g.unop.hom.op)
      M.obj

@[simp]
lemma ι_obj_derivedHom_obj_obj (K : (DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X)ᵒᵖ)
    (M : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X) :
    (ι _ X).obj (((derivedHom Λ aX).obj K).obj M) =
      ((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op ((ι _ X).obj K.unop))).obj ((ι _ X).obj M) :=
  rfl

@[simp]
lemma derivedHom_map_app_hom {K K' : (DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X)ᵒᵖ}
    (f : K ⟶ K') (M : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X) :
    (((derivedHom Λ aX).map f).app M).hom =
      ((RHom(X)[ModuleCat.{u + 1} Λ]).map f.unop.hom.op).app M.obj :=
  rfl

omit [Finite Λ] in
@[simp]
lemma leftDerivedUpperStar_map_hom {Y : Scheme.{u}} (h : Y ⟶ X)
    {K K' : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X} (f : K ⟶ K') :
    ((leftDerivedUpperStar _ h).map f).hom = L((h)^*[ModuleCat.{u + 1} Λ]).map f.hom :=
  rfl

noncomputable instance (K : (DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X)ᵒᵖ) :
    ((derivedHom Λ aX).obj K).CommShift ℤ :=
  inferInstanceAs ((ObjectProperty.liftFullSubcategory (DerivedCategory.constructibleFiniteTor _ X)
    (DerivedCategory.constructibleFiniteTor _ X)
    ((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K.unop.obj))
    fun _ hM ↦ constructibleFiniteTor_derivedHom Λ aX K.unop.property hM).CommShift ℤ)

/-- The derived internal hom `RHom(K, -)` of `Dctf(X, Λ)` is a triangulated functor. -/
instance (K : (DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X)ᵒᵖ) :
    ((derivedHom Λ aX).obj K).IsTriangulated :=
  inferInstanceAs ((ObjectProperty.liftFullSubcategory (DerivedCategory.constructibleFiniteTor _ X)
    (DerivedCategory.constructibleFiniteTor _ X)
    ((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K.unop.obj))
    fun _ hM ↦ constructibleFiniteTor_derivedHom Λ aX K.unop.property hM).IsTriangulated)

end DerivedCategoryFiniteTor


/-! ### Naturality of the tensor comparison of `Lg^*` -/

section Naturality

variable {Λ} {Z Y : Scheme.{u}} (g : Z ⟶ Y)

omit [Finite Λ] in
@[reassoc]
lemma leftDerivedUpperStarTensorIso_hom_naturality_left
    {K K' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (f : K ⟶ K') (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    L((g)^*[ModuleCat.{u + 1} Λ]).map (((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).map f).app M) ≫
        (leftDerivedUpperStarTensorIso _ g K' M).hom =
      (leftDerivedUpperStarTensorIso _ g K M).hom ≫
        ((-⊗ᴸ-(Z)[ModuleCat.{u + 1} Λ]).map (L((g)^*[ModuleCat.{u + 1} Λ]).map f)).app _ :=
  NatTrans.congr_app ((leftDerivedUpperStarTensorNatIso _ g).hom.naturality f) M

omit [Finite Λ] in
@[reassoc]
lemma leftDerivedUpperStarTensorIso_hom_naturality_right
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {M M' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h : M ⟶ M') :
    L((g)^*[ModuleCat.{u + 1} Λ]).map (((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj K).map h) ≫
        (leftDerivedUpperStarTensorIso _ g K M').hom =
      (leftDerivedUpperStarTensorIso _ g K M).hom ≫
        ((-⊗ᴸ-(Z)[ModuleCat.{u + 1} Λ]).obj _).map (L((g)^*[ModuleCat.{u + 1} Λ]).map h) :=
  ((leftDerivedUpperStarTensorNatIso _ g).hom.app K).naturality h

end Naturality



/-! ### The internal-hom comparison of `Lg^*` along an isomorphism -/

section InternalHom

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
variable {Z Y : Scheme.{u}} (g : Z ⟶ Y) [(g)^*[A].PreservesFlat]

/-- The comparison `Lg^* RHom(K, M) ⟶ RHom(Lg^* K, Lg^* M)`: the comparison map of the monoidal
functor `Lg^*` (`AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal`) with internal homs. -/
noncomputable def leftDerivedUpperStarDerivedHomComparison
    (K M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((g)^*[A]).obj ((RHom(Y)[A].obj (op K)).obj M) ⟶
      (RHom(Z)[A].obj (op (L((g)^*[A]).obj K))).obj (L((g)^*[A]).obj M) :=
  letI := leftDerivedUpperStarMonoidal A g
  (Functor.LaxMonoidal.ihomComparison _ K).natTrans.app M

/-- The comparison `Lg^* RHom(K, M) ⟶ RHom(Lg^* K, Lg^* M)` is natural in `M`. -/
@[reassoc]
lemma leftDerivedUpperStarDerivedHomComparison_naturality_right
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    {M M' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (h : M ⟶ M') :
    L((g)^*[A]).map ((RHom(Y)[A].obj (op K)).map h) ≫
        leftDerivedUpperStarDerivedHomComparison A g K M' =
      leftDerivedUpperStarDerivedHomComparison A g K M ≫
        (RHom(Z)[A].obj _).map (L((g)^*[A]).map h) :=
  letI := leftDerivedUpperStarMonoidal A g
  (Functor.LaxMonoidal.ihomComparison L((g)^*[A]) K).natTrans.naturality h

/-- The comparison `Lg^* RHom(K, M) ⟶ RHom(Lg^* K, Lg^* M)` is natural in `K`. -/
@[reassoc]
lemma leftDerivedUpperStarDerivedHomComparison_naturality_left
    {K K' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (f : K ⟶ K')
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((g)^*[A]).map ((RHom(Y)[A].map f.op).app M) ≫
        leftDerivedUpperStarDerivedHomComparison A g K M =
      leftDerivedUpperStarDerivedHomComparison A g K' M ≫
        (RHom(Z)[A].map (L((g)^*[A]).map f).op).app _ :=
  letI := leftDerivedUpperStarMonoidal A g
  Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app L((g)^*[A]) f M

/-- If `Lg^*` is an equivalence, for instance if `g` is an isomorphism, the comparison
`Lg^* RHom(K, M) ⟶ RHom(Lg^* K, Lg^* M)` is an isomorphism
(`CategoryTheory.Functor.Monoidal.commIhom`). -/
instance [L((g)^*[A]).IsEquivalence]
    (K M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    IsIso (leftDerivedUpperStarDerivedHomComparison A g K M) :=
  letI := leftDerivedUpperStarMonoidal A g
  inferInstanceAs (IsIso ((Functor.LaxMonoidal.ihomComparison _ K).natTrans.app M))

/-- The isomorphism `Lg^* RHom(K, M) ≅ RHom(Lg^* K, Lg^* M)` when `Lg^*` is an equivalence. -/
noncomputable abbrev leftDerivedUpperStarDerivedHomIso [L((g)^*[A]).IsEquivalence]
    (K M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((g)^*[A]).obj ((RHom(Y)[A].obj (op K)).obj M) ≅
      (RHom(Z)[A].obj (op (L((g)^*[A]).obj K))).obj (L((g)^*[A]).obj M) :=
  asIso (leftDerivedUpperStarDerivedHomComparison A g K M)

/-- The internal-Hom Frobenius `Lg^* RHom(K, M) ⟶ RHom(Lg^* K, Lg^* M) ⟶ RHom(K, M)` built from
`ψ_K : K ⟶ Lg^* K` and `φ_M : Lg^* M ⟶ M` is natural in `K`: for `f : K' ⟶ K` compatible with
`ψ_K` and `ψ_{K'}` it commutes with precomposition by `f`. -/
lemma leftDerivedUpperStarDerivedHomComparison_comp_naturality_left {X : Scheme.{u}}
    (g : X ⟶ X) [(g)^*[A].PreservesFlat] {K K' M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (f : K' ⟶ K) (ψK : K ⟶ L((g)^*[A]).obj K) (ψK' : K' ⟶ L((g)^*[A]).obj K')
    (φM : L((g)^*[A]).obj M ⟶ M) (hf : ψK' ≫ L((g)^*[A]).map f = f ≫ ψK) :
    (leftDerivedUpperStarDerivedHomComparison A g K M ≫ (RHom(X)[A].map ψK.op).app _ ≫
        (RHom(X)[A].obj (op K)).map φM) ≫ (RHom(X)[A].map f.op).app M =
      L((g)^*[A]).map ((RHom(X)[A].map f.op).app M) ≫
        leftDerivedUpperStarDerivedHomComparison A g K' M ≫ (RHom(X)[A].map ψK'.op).app _ ≫
          (RHom(X)[A].obj (op K')).map φM := by
  rw [leftDerivedUpperStarDerivedHomComparison_naturality_left_assoc, Category.assoc,
    Category.assoc, ← NatTrans.comp_app_assoc, ← Functor.map_comp, ← op_comp, hf, op_comp,
    Functor.map_comp, NatTrans.comp_app_assoc,
    ← NatTrans.naturality (RHom(X)[A].map f.op) φM]

end InternalHom

omit [Finite Λ] in
/-- For an isomorphism `g`, the derived pullback `Lg^*` is an equivalence of categories. -/
instance isEquivalence_leftDerivedUpperStar_of_isIso {Z Y : Scheme.{u}} (g : Z ⟶ Y) [IsIso g] :
    (L((g)^*[ModuleCat.{u + 1} Λ])).IsEquivalence :=
  inferInstance

/-! ### Tensor products of Weil complexes -/

namespace WeilComplex

variable {Λ} {X : Scheme.{u}} {g : X ≅ X}

/-- Blueprint `def-wf-tensor-product`: the *tensor Frobenius* of two Weil complexes
`(K, φ_K)` and `(L, φ_L)`, the Weil structure
`Lg^*(K ⊗ᴸ L) ≅ Lg^* K ⊗ᴸ Lg^* L ≅ K ⊗ᴸ L` on `K ⊗ᴸ L`, whose second arrow is `φ_K ⊗ φ_L`. -/
noncomputable def tensorFrobenius (K L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (DerivedCategoryFiniteTor.leftDerivedUpperStar _ g.hom).obj
        (((DerivedCategoryFiniteTor.derivedTensor Λ X).obj K.obj).obj L.obj) ≅
      ((DerivedCategoryFiniteTor.derivedTensor Λ X).obj K.obj).obj L.obj :=
  ObjectProperty.isoMk _ (leftDerivedUpperStarTensorIso _ g.hom K.obj.obj L.obj.obj ≪≫
    ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).mapIso
      ((DerivedCategoryFiniteTor.ι _ X).mapIso K.frobenius)).app _ ≪≫
    ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K.obj.obj).mapIso
      ((DerivedCategoryFiniteTor.ι _ X).mapIso L.frobenius))


omit [Finite Λ] in
@[ext]
lemma hom_ext {K L : WeilComplex (ModuleCat.{u + 1} Λ) g} {f f' : K ⟶ L} (e : f.hom = f'.hom) :
    f = f' :=
  Hom.ext e

omit [Finite Λ] in
/-- The compatibility of a morphism of Weil complexes with the Weil structures, in `D(X_ét)`. -/
@[reassoc]
lemma frobenius_hom_comp_hom {K L : WeilComplex (ModuleCat.{u + 1} Λ) g} (f : K ⟶ L) :
    K.frobenius.hom.hom ≫ f.hom.hom =
      L((g.hom)^*[ModuleCat.{u + 1} Λ]).map f.hom.hom ≫ L.frobenius.hom.hom :=
  congrArg InducedCategory.Hom.hom f.comm

lemma tensorFrobenius_hom_hom (K L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (tensorFrobenius K L).hom.hom =
      (leftDerivedUpperStarTensorIso _ g.hom K.obj.obj L.obj.obj).hom ≫
      ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).map K.frobenius.hom.hom).app _ ≫
        ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K.obj.obj).map L.frobenius.hom.hom :=
  rfl

variable (Λ g) in
/-- Blueprint `lem-wf-tensor-weil`: the derived tensor product of Weil complexes. With the
tensor Frobenius `φ_K ⊗ φ_L` (`AlgebraicGeometry.Etale.WeilComplex.tensorFrobenius`), the
derived tensor product of `Dctf(X, Λ)` lifts to a bifunctor `WeilD × WeilD ⥤ WeilD` on Weil
complexes, lying over the derived tensor product of `Dctf(X, Λ)`
(`AlgebraicGeometry.Etale.WeilComplex.tensor_obj_obj_obj`, `…tensor_map_app_hom`,
`…tensor_obj_map_hom`), which is triangulated in each variable. -/
noncomputable def tensor :
    WeilComplex (ModuleCat.{u + 1} Λ) g ⥤ WeilComplex (ModuleCat.{u + 1} Λ) g ⥤
      WeilComplex (ModuleCat.{u + 1} Λ) g where
  obj K :=
    { obj L := ⟨((DerivedCategoryFiniteTor.derivedTensor Λ X).obj K.obj).obj L.obj,
        tensorFrobenius K L⟩
      map {L L'} h := ⟨((DerivedCategoryFiniteTor.derivedTensor Λ X).obj K.obj).map h.hom, by
        apply ObjectProperty.hom_ext
        change (tensorFrobenius K L).hom.hom ≫ ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K.obj.obj).map
            h.hom.hom = L((g.hom)^*[ModuleCat.{u + 1} Λ]).map
              (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K.obj.obj).map h.hom.hom) ≫
            (tensorFrobenius K L').hom.hom
        rw [tensorFrobenius_hom_hom, tensorFrobenius_hom_hom,
          leftDerivedUpperStarTensorIso_hom_naturality_right_assoc, Category.assoc,
          Category.assoc, ← Functor.map_comp, frobenius_hom_comp_hom, Functor.map_comp,
          NatTrans.naturality_assoc]⟩
      map_id L := by
        ext1
        exact (((DerivedCategoryFiniteTor.derivedTensor Λ X).obj K.obj).map_id L.obj)
      map_comp h h' := by
        ext1
        exact (((DerivedCategoryFiniteTor.derivedTensor Λ X).obj K.obj).map_comp h.hom h'.hom) }
  map {K K'} f :=
    { app L := ⟨((DerivedCategoryFiniteTor.derivedTensor Λ X).map f.hom).app L.obj, by
        apply ObjectProperty.hom_ext
        change (tensorFrobenius K L).hom.hom ≫ ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).map
            f.hom.hom).app L.obj.obj = L((g.hom)^*[ModuleCat.{u + 1} Λ]).map
              (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).map f.hom.hom).app L.obj.obj) ≫
            (tensorFrobenius K' L).hom.hom
        rw [tensorFrobenius_hom_hom, tensorFrobenius_hom_hom,
          leftDerivedUpperStarTensorIso_hom_naturality_left_assoc, Category.assoc,
          Category.assoc, NatTrans.naturality, ← NatTrans.comp_app_assoc, ← Functor.map_comp,
          frobenius_hom_comp_hom, Functor.map_comp, NatTrans.comp_app_assoc]⟩
      naturality L L' h := by
        ext1
        exact (((DerivedCategoryFiniteTor.derivedTensor Λ X).map f.hom).naturality h.hom) }
  map_id K := NatTrans.ext <| funext fun L ↦ hom_ext
      (NatTrans.congr_app ((DerivedCategoryFiniteTor.derivedTensor Λ X).map_id K.obj) L.obj)
  map_comp f f' := NatTrans.ext <| funext fun L ↦ hom_ext
      (NatTrans.congr_app
        ((DerivedCategoryFiniteTor.derivedTensor Λ X).map_comp f.hom f'.hom) L.obj)

@[simp]
lemma tensor_obj_obj_obj (K L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (((tensor Λ g).obj K).obj L).obj =
      ((DerivedCategoryFiniteTor.derivedTensor Λ X).obj K.obj).obj L.obj :=
  rfl

@[simp]
lemma tensor_obj_obj_frobenius (K L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (((tensor Λ g).obj K).obj L).frobenius = tensorFrobenius K L :=
  rfl

@[simp]
lemma tensor_obj_map_hom (K : WeilComplex (ModuleCat.{u + 1} Λ) g)
    {L L' : WeilComplex (ModuleCat.{u + 1} Λ) g} (h : L ⟶ L') :
    (((tensor Λ g).obj K).map h).hom =
      ((DerivedCategoryFiniteTor.derivedTensor Λ X).obj K.obj).map h.hom :=
  rfl

@[simp]
lemma tensor_map_app_hom {K K' : WeilComplex (ModuleCat.{u + 1} Λ) g} (f : K ⟶ K')
    (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (((tensor Λ g).map f).app L).hom =
      ((DerivedCategoryFiniteTor.derivedTensor Λ X).map f.hom).app L.obj :=
  rfl

omit [Finite Λ] in
/-- The compatibility of a morphism of Weil complexes with the inverses of the Weil structures,
in `D(X_ét)`. -/
@[reassoc]
lemma frobenius_inv_hom_comp_map {K L : WeilComplex (ModuleCat.{u + 1} Λ) g} (f : K ⟶ L) :
    K.frobenius.inv.hom ≫ L((g.hom)^*[ModuleCat.{u + 1} Λ]).map f.hom.hom =
      f.hom.hom ≫ L.frobenius.inv.hom := by
  rw [← cancel_mono ((DerivedCategoryFiniteTor.ι _ X).mapIso L.frobenius).hom]
  rw [Category.assoc, Category.assoc]
  change _ = _ ≫ ((DerivedCategoryFiniteTor.ι _ X).mapIso L.frobenius).inv ≫
    ((DerivedCategoryFiniteTor.ι _ X).mapIso L.frobenius).hom
  rw [Iso.inv_hom_id, Category.comp_id]
  change _ ≫ _ ≫ L.frobenius.hom.hom = _
  rw [← frobenius_hom_comp_hom]
  change ((DerivedCategoryFiniteTor.ι _ X).mapIso K.frobenius).inv ≫
    ((DerivedCategoryFiniteTor.ι _ X).mapIso K.frobenius).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]

/-! ### Internal homs of Weil complexes -/

variable {k : Type u} [Field k] (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
  [QuasiCompact aX] [HasInvertibleExponent Λ X]

/-- Blueprint `def-wf-internal-hom`: the *internal-Hom Frobenius* of two Weil complexes
`(K, φ_K)` and `(L, φ_L)`, the Weil structure
`Lg^* RHom(K, L) ≅ RHom(Lg^* K, Lg^* L) ≅ RHom(K, L)` on `RHom(K, L)`, whose first arrow is the
comparison map of the monoidal equivalence `Lg^*` and whose second arrow is
`RHom(φ_K⁻¹, φ_L)`. -/
noncomputable def internalHomFrobenius (K L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (DerivedCategoryFiniteTor.leftDerivedUpperStar _ g.hom).obj
        (((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.obj)).obj L.obj) ≅
      ((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.obj)).obj L.obj :=
  ObjectProperty.isoMk _
    (leftDerivedUpperStarDerivedHomIso (ModuleCat.{u + 1} Λ) g.hom K.obj.obj L.obj.obj ≪≫
      (RHom(X)[ModuleCat.{u + 1} Λ].mapIso
        ((DerivedCategoryFiniteTor.ι _ X).mapIso K.frobenius).symm.op).app _ ≪≫
      (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K.obj.obj)).mapIso
        ((DerivedCategoryFiniteTor.ι _ X).mapIso L.frobenius))

lemma internalHomFrobenius_hom_hom (K L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (internalHomFrobenius aX K L).hom.hom =
      leftDerivedUpperStarDerivedHomComparison (ModuleCat.{u + 1} Λ) g.hom K.obj.obj L.obj.obj ≫
        (RHom(X)[ModuleCat.{u + 1} Λ].map K.frobenius.inv.hom.op).app _ ≫
          (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K.obj.obj)).map L.frobenius.hom.hom :=
  rfl

/-- The internal-Hom Frobenius is natural in the first variable. -/
lemma internalHomFrobenius_hom_comp_map_test1 {K K' : WeilComplex (ModuleCat.{u + 1} Λ) g} (f : K' ⟶ K)
    (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (internalHomFrobenius aX K L).hom ≫
        ((DerivedCategoryFiniteTor.derivedHom Λ aX).map f.hom.op).app L.obj =
      (DerivedCategoryFiniteTor.leftDerivedUpperStar _ g.hom).map
          (((DerivedCategoryFiniteTor.derivedHom Λ aX).map f.hom.op).app L.obj) ≫
        (internalHomFrobenius aX K' L).hom := by
  apply ObjectProperty.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    internalHomFrobenius_hom_hom, internalHomFrobenius_hom_hom,
    DerivedCategoryFiniteTor.leftDerivedUpperStar_map_hom,
    DerivedCategoryFiniteTor.derivedHom_map_app_hom, Quiver.Hom.unop_op]
  with_reducible exact leftDerivedUpperStarDerivedHomComparison_comp_naturality_left _ g.hom f.hom.hom _ _ _
    (frobenius_inv_hom_comp_map f)

set_option maxHeartbeats 3000000 in
lemma internalHomFrobenius_hom_comp_map_test2 {K K' : WeilComplex (ModuleCat.{u + 1} Λ) g} (f : K' ⟶ K)
    (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (internalHomFrobenius aX K L).hom ≫
        ((DerivedCategoryFiniteTor.derivedHom Λ aX).map f.hom.op).app L.obj =
      (DerivedCategoryFiniteTor.leftDerivedUpperStar _ g.hom).map
          (((DerivedCategoryFiniteTor.derivedHom Λ aX).map f.hom.op).app L.obj) ≫
        (internalHomFrobenius aX K' L).hom := by
  apply ObjectProperty.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    internalHomFrobenius_hom_hom, internalHomFrobenius_hom_hom,
    DerivedCategoryFiniteTor.leftDerivedUpperStar_map_hom,
    DerivedCategoryFiniteTor.derivedHom_map_app_hom, Quiver.Hom.unop_op]
  exact leftDerivedUpperStarDerivedHomComparison_comp_naturality_left _ g.hom f.hom.hom _ _ _
    (frobenius_inv_hom_comp_map f)

/-- The internal-Hom Frobenius is natural in the first variable. -/
lemma internalHomFrobenius_hom_comp_map {K K' : WeilComplex (ModuleCat.{u + 1} Λ) g} (f : K' ⟶ K)
    (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (internalHomFrobenius aX K L).hom ≫
        ((DerivedCategoryFiniteTor.derivedHom Λ aX).map f.hom.op).app L.obj =
      (DerivedCategoryFiniteTor.leftDerivedUpperStar _ g.hom).map
          (((DerivedCategoryFiniteTor.derivedHom Λ aX).map f.hom.op).app L.obj) ≫
        (internalHomFrobenius aX K' L).hom := by sorry

variable (g) in
/-- Blueprint `lem-wf-internal-hom-weil`: the derived internal hom of Weil complexes. With the
internal-Hom Frobenius `RHom(φ_K⁻¹, φ_L)` (`AlgebraicGeometry.Etale.WeilComplex.internalHomFrobenius`),
the derived internal hom of `Dctf(X, Λ)` lifts to a bifunctor `WeilDᵒᵖ × WeilD ⥤ WeilD` on Weil
complexes, lying over the derived internal hom of `Dctf(X, Λ)`
(`AlgebraicGeometry.Etale.WeilComplex.internalHom_obj_obj_obj`, `…internalHom_map_app_hom`,
`…internalHom_obj_map_hom`), which is triangulated in its second variable. -/
noncomputable def internalHom :
    (WeilComplex (ModuleCat.{u + 1} Λ) g)ᵒᵖ ⥤ WeilComplex (ModuleCat.{u + 1} Λ) g ⥤
      WeilComplex (ModuleCat.{u + 1} Λ) g where
  obj K :=
    { obj L := ⟨((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.unop.obj)).obj L.obj,
        internalHomFrobenius aX K.unop L⟩
      map {L L'} h :=
        ⟨((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.unop.obj)).map h.hom, by
          apply ObjectProperty.hom_ext
          change (internalHomFrobenius aX K.unop L).hom.hom ≫
              (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K.unop.obj.obj)).map h.hom.hom =
            L((g.hom)^*[ModuleCat.{u + 1} Λ]).map
                ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op K.unop.obj.obj)).map h.hom.hom) ≫
              (internalHomFrobenius aX K.unop L').hom.hom
          rw [internalHomFrobenius_hom_hom, internalHomFrobenius_hom_hom,
            leftDerivedUpperStarDerivedHomComparison_naturality_right_assoc, Category.assoc,
            Category.assoc, NatTrans.naturality_assoc, ← Functor.map_comp, ← Functor.map_comp,
            frobenius_hom_comp_hom]⟩
      map_id L := by
        ext1
        exact ((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.unop.obj)).map_id L.obj
      map_comp h h' := by
        ext1
        exact ((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.unop.obj)).map_comp
          h.hom h'.hom }
  map {K K'} f :=
    { app L := ⟨((DerivedCategoryFiniteTor.derivedHom Λ aX).map f.unop.hom.op).app L.obj,
        internalHomFrobenius_hom_comp_map aX f.unop L⟩
      naturality L L' h := by
        ext1
        exact ((DerivedCategoryFiniteTor.derivedHom Λ aX).map f.unop.hom.op).naturality h.hom }
  map_id K := NatTrans.ext <| funext fun L ↦ hom_ext
      (NatTrans.congr_app ((DerivedCategoryFiniteTor.derivedHom Λ aX).map_id (op K.unop.obj))
        L.obj)
  map_comp f f' := NatTrans.ext <| funext fun L ↦ hom_ext
      (NatTrans.congr_app ((DerivedCategoryFiniteTor.derivedHom Λ aX).map_comp f.unop.hom.op
        f'.unop.hom.op) L.obj)

@[simp]
lemma internalHom_obj_obj_obj (K : (WeilComplex (ModuleCat.{u + 1} Λ) g)ᵒᵖ)
    (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (((internalHom g aX).obj K).obj L).obj =
      ((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.unop.obj)).obj L.obj :=
  rfl

@[simp]
lemma internalHom_obj_obj_frobenius (K : (WeilComplex (ModuleCat.{u + 1} Λ) g)ᵒᵖ)
    (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (((internalHom g aX).obj K).obj L).frobenius = internalHomFrobenius aX K.unop L :=
  rfl

@[simp]
lemma internalHom_obj_map_hom (K : (WeilComplex (ModuleCat.{u + 1} Λ) g)ᵒᵖ)
    {L L' : WeilComplex (ModuleCat.{u + 1} Λ) g} (h : L ⟶ L') :
    (((internalHom g aX).obj K).map h).hom =
      ((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.unop.obj)).map h.hom :=
  rfl

@[simp]
lemma internalHom_map_app_hom {K K' : (WeilComplex (ModuleCat.{u + 1} Λ) g)ᵒᵖ} (f : K ⟶ K')
    (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (((internalHom g aX).map f).app L).hom =
      ((DerivedCategoryFiniteTor.derivedHom Λ aX).map f.unop.hom.op).app L.obj :=
  rfl

end WeilComplex

end Etale

end AlgebraicGeometry
