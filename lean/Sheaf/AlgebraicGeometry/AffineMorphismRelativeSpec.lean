/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf

/-! # Affine morphisms and quasi-coherent algebras (relative spectrum)

Source: Stacks Project, Morphisms, Lemmas 01S8 and 01SA; Constructions, Definition 01LW and
Lemma 01LX (blueprint: lem-weil-pbc-affine-morphism-relative-spec).

A quasi-coherent `𝒪_S`-algebra is a landed `S.CommAlgebraSheaf` (`Under S.sheaf`,
def-weil-pbc-comm-algebra-sheaf) whose `toModule` is quasi-coherent. For `f : X ⟶ S` the algebra
`f_* 𝒪_X` is `Under.mk ⟨f.c⟩` (the local notation `𝒪⁎ f`). Schemes affine over `S` are the full
subcategory of `Over S` on `IsAffineHom`. The restriction `𝒜|_V` to an open `V` is Mathlib's
naive sheaf pullback along the open embedding `V.ι`, whose sections over `W` are `𝒜(V.ι ''ᵁ W)`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

set_option hygiene false in
/-- `f_* 𝒪_X` as a sheaf of commutative `𝒪_S`-algebras, through `f^♯ = f.c`. -/
local notation "𝒪⁎" f:max => Under.mk (⟨(f).c⟩ : Scheme.sheaf _ ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} (f).base).obj (Scheme.sheaf _))

/-- (1) For an affine `f : X ⟶ S`, `f_* 𝒪_X` is a quasi-coherent `𝒪_S`-algebra.
(3) An anti-equivalence `E` from schemes affine over `S` to quasi-coherent `𝒪_S`-algebras whose
functor is `f ↦ f_* 𝒪_X` on objects (`hobj`) and `h ↦ f'_* h^♯` on morphisms (sections:
`h.appLE`), with quasi-inverse `𝒜 ↦ Spec_S 𝒜 = E.inverse.obj 𝒜`; (2) for `π = Spec_S 𝒜 ⟶ S`
and `α : 𝒜 ≅ π_* 𝒪` (the counit of `E`), the morphism `π⁻¹ U ⟶ Spec 𝒜(U)` corresponding to
`α_U` (`toSpecΓ ≫ Spec.map α_U`) is an isomorphism for every affine open `U`; for `φ : 𝒜 ⟶ ℬ`
the restriction over an affine `U` of `Spec_S ℬ ⟶ Spec_S 𝒜` is `Spec φ_U` under these charts.
(4) For an open `V`: `ρ : (f_* 𝒪_X)|_V ≅ (f ∣_ V)_* 𝒪` is the canonical identification (sections:
`(f⁻¹ V).ι.appLE`); `Spec_S 𝒜 ×_S V = π⁻¹ V`, and `π ∣_ V` is affine with isomorphic charts for
`𝒜|_V` and `α|_V ≫ ρ` over every affine open `W` of `V`, i.e. `π⁻¹ V = Spec_V (𝒜|_V)`.
Source: Stacks Project, Morphisms, Lemmas 01S8 and 01SA; Constructions, Definition 01LW and
Lemma 01LX (blueprint: lem-weil-pbc-affine-morphism-relative-spec).

Proof: (1) by Stacks 01LC (pushforward of a quasi-coherent module along a quasi-compact
quasi-separated morphism). For (2), on each affine open `U` take `Spec 𝒜(U)`; these are
compatible over inclusions of affine opens and glue by relative gluing (Stacks 01LH) to
`π : Spec_S 𝒜 ⟶ S`, affine with `π⁻¹ U ≅ Spec 𝒜(U)`; `α` is an isomorphism on the affine basis,
hence an isomorphism. For (3), full faithfulness is checked locally on affine opens using
morphisms into affine schemes and Spec on affine pieces, essential surjectivity is (1) with
Stacks 01S8 (`X ≅ Spec_S f_* 𝒪_X`). (4) follows from `isPullback_morphismRestrict` and the
local nature of the construction. -/
theorem affine_morphism_relative_spec (S : Scheme.{u}) :
    (∀ {X : Scheme.{u}} (f : X ⟶ S), IsAffineHom f →
      (Scheme.CommAlgebraSheaf.toModule (𝒪⁎ f)).IsQuasicoherent) ∧
    ∃ (E : (ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom))ᵒᵖ ≌
        ObjectProperty.FullSubcategory
          (fun A : S.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent))
      (hobj : ∀ Y, (E.functor.obj (op Y)).obj = 𝒪⁎ Y.obj.hom)
      (ρ : ∀ (Y : ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom))
          (V : S.Opens),
        ((Under.post (V.ι.isOpenEmbedding.sheafPullback CommRingCat.{u})).obj
          (𝒪⁎ Y.obj.hom) : V.toScheme.CommAlgebraSheaf) ≅ 𝒪⁎ (Y.obj.hom ∣_ V)),
      (∀ (Y Y') (h : Y ⟶ Y') (V : S.Opens),
        (E.functor.map h.op).hom.right.hom.app (op V) =
          eqToHom (by rw [hobj Y']; rfl) ≫
            h.hom.left.appLE (Y'.obj.hom ⁻¹ᵁ V) (Y.obj.hom ⁻¹ᵁ V)
              (by rw [← Over.w h.hom, Scheme.Hom.comp_preimage]) ≫
            eqToHom (by rw [hobj Y]; rfl)) ∧
      (∀ (A) (U : S.Opens), IsAffineOpen U →
        IsIso (((E.inverse.obj A).unop.obj.hom ⁻¹ᵁ U).toSpecΓ ≫
          Spec.map (((E.counitIso.app A).inv.hom ≫
            eqToHom (hobj (E.inverse.obj A).unop)).right.hom.app (op U)))) ∧
      (∀ (A B) (φ : A ⟶ B) (U : S.Opens), IsAffineOpen U →
        (E.inverse.map φ).unop.hom.left.resLE ((E.inverse.obj A).unop.obj.hom ⁻¹ᵁ U)
            ((E.inverse.obj B).unop.obj.hom ⁻¹ᵁ U)
            (by rw [← Scheme.Hom.comp_preimage, Over.w (E.inverse.map φ).unop.hom]) ≫
          ((E.inverse.obj A).unop.obj.hom ⁻¹ᵁ U).toSpecΓ ≫
            Spec.map (((E.counitIso.app A).inv.hom ≫
              eqToHom (hobj (E.inverse.obj A).unop)).right.hom.app (op U)) =
        ((E.inverse.obj B).unop.obj.hom ⁻¹ᵁ U).toSpecΓ ≫
          Spec.map (((E.counitIso.app B).inv.hom ≫
            eqToHom (hobj (E.inverse.obj B).unop)).right.hom.app (op U)) ≫
          Spec.map (φ.hom.right.hom.app (op U))) ∧
      (∀ (Y : ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom))
          (V : S.Opens) (W : V.toScheme.Opens),
        (ρ Y V).hom.right.hom.app (op W) =
          (Y.obj.hom ⁻¹ᵁ V).ι.appLE (Y.obj.hom ⁻¹ᵁ (V.ι ''ᵁ W)) ((Y.obj.hom ∣_ V) ⁻¹ᵁ W)
            (by rw [← Scheme.Hom.comp_preimage, ← morphismRestrict_ι,
              Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq])) ∧
      (∀ (A) (V : S.Opens),
        IsPullback (((E.inverse.obj A).unop.obj.hom ⁻¹ᵁ V).ι)
          ((E.inverse.obj A).unop.obj.hom ∣_ V) (E.inverse.obj A).unop.obj.hom V.ι ∧
        IsAffineHom ((E.inverse.obj A).unop.obj.hom ∣_ V) ∧
        ∀ W : V.toScheme.Opens, IsAffineOpen W →
          IsIso ((((E.inverse.obj A).unop.obj.hom ∣_ V) ⁻¹ᵁ W).toSpecΓ ≫
            Spec.map (((E.counitIso.app A).inv.hom ≫
              eqToHom (hobj (E.inverse.obj A).unop)).right.hom.app (op (V.ι ''ᵁ W)) ≫
              (ρ (E.inverse.obj A).unop V).hom.right.hom.app (op W)))) := by
  sorry

end AlgebraicGeometry
