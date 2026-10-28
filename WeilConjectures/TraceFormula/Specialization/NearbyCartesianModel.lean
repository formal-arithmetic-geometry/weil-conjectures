/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.HomComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessSlice
public import WeilConjectures.TraceFormula.Specialization.NearbySmoothExchangeLocal

/-!

# The cartesian factorization of a morphism of models

Let `φ : M ⟶ N` be a morphism of models (`NearbyCyclesModel.Hom`) over `f : X ⟶ Y` and
`f' : X' ⟶ Y'`, with morphism of total spaces `t : 𝒳 ⟶ 𝒴`. The *cartesian model*
`NearbyCyclesModel.Hom.cartModel` of `φ` is the model of `Y` with special fibre `X'`, total space
`𝒳`, geometric generic fibre the base change `𝒴_η̄ ×_𝒴 𝒳` of the geometric generic fibre of `N`
along `t`, and identification `𝒴_η̄ ×_𝒴 𝒳 ⟶ 𝒴_η̄ ⟶ Y`. The morphism `φ` factors as
```
M ──toCart──> cartModel ──fromCart──> N
```
where `toCart` (over `f` and `𝟙 X'`) is the identity on total spaces, and `fromCart` (over `𝟙 Y`
and `f'`) has a cartesian square of geometric generic fibres
(`NearbyCyclesModel.Hom.isPullback_fromCart_commSq_j`).

By the composition law of pullback exchanges
(`NearbyCyclesModel.Hom.pullbackExchange_comp_app_of_eq`), the pullback exchange of `φ` is a
split monomorphism at `C` as soon as that of `fromCart` is invertible at `C` (a base change
statement for `Rj_*` along `t`) and that of `toCart` is a split monomorphism at `C` (a statement
about the change of geometric generic fibre over a fixed total space)
(`NearbyCyclesModel.Hom.isSplitMono_pullbackExchange_app_of_cart`). For the coordinate slices
of the affine space this is
`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_cart`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Abstract

/-- If `a ≫ e = e' ≫ b ≫ c` with `e`, `e'`, `b` isomorphisms and `c` a split monomorphism, then
`a` is a split monomorphism. -/
lemma isSplitMono_of_comp_eq_comp_comp {C : Type*} [Category C] {x y y' x' z : C}
    {a : x ⟶ y} {e : y ⟶ y'} {e' : x ⟶ x'} {b : x' ⟶ z} {c : z ⟶ y'}
    (h : a ≫ e = e' ≫ b ≫ c) [IsIso e] [IsIso e'] [IsIso b] [IsSplitMono c] :
    IsSplitMono a := by
  have ha : a = e' ≫ b ≫ c ≫ inv e := by
    rw [← cancel_mono e, h]
    simp
  rw [ha]
  infer_instance

/-- A natural transformation which is a split monomorphism at an object is a split monomorphism
at every isomorphic object. -/
lemma NatTrans.isSplitMono_app_of_iso {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (α : F ⟶ G) {A B : C} (e : A ≅ B) [IsSplitMono (α.app B)] : IsSplitMono (α.app A) := by
  have ha : α.app A = F.map e.hom ≫ α.app B ≫ G.map e.inv := by
    rw [α.naturality_assoc, ← G.map_comp, e.hom_inv_id, G.map_id, Category.comp_id]
  rw [ha]
  infer_instance

end Abstract

section General

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

namespace NearbyCyclesModel

variable {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

namespace Hom

variable (φ : M.Hom N f f')

/-- The *cartesian model* of a morphism of models `φ : M ⟶ N`: the model of `Y` with special
fibre `X'`, total space `𝒳` of `M`, geometric generic fibre the base change `𝒴_η̄ ×_𝒴 𝒳` of the
geometric generic fibre of `N` along the morphism of total spaces, and identification
`𝒴_η̄ ×_𝒴 𝒳 ⟶ 𝒴_η̄ ⟶ Y`. -/
@[simps]
noncomputable def cartModel : NearbyCyclesModel Y X' where
  total := M.total
  generic := pullback N.j φ.total
  j := pullback.snd N.j φ.total
  i := M.i
  ε := pullback.fst N.j φ.total ≫ N.ε

/-- The morphism of models `M ⟶ φ.cartModel` over `f` and `𝟙 X'`: the identity on total spaces,
and `(φ.generic, M.j) : 𝒳_η̄ ⟶ 𝒴_η̄ ×_𝒴 𝒳` on geometric generic fibres. -/
@[simps]
noncomputable def toCart : M.Hom φ.cartModel f (𝟙 X') where
  total := 𝟙 _
  generic := pullback.lift φ.generic M.j φ.comm_j
  comm_j := by simp
  comm_i := by simp
  comm_ε := by simp [φ.comm_ε]

/-- The morphism of models `φ.cartModel ⟶ N` over `𝟙 Y` and `f'`: the morphism `φ.total` of total
spaces, and the first projection `𝒴_η̄ ×_𝒴 𝒳 ⟶ 𝒴_η̄` on geometric generic fibres. -/
@[simps]
noncomputable def fromCart : φ.cartModel.Hom N (𝟙 Y) f' where
  total := φ.total
  generic := pullback.fst N.j φ.total
  comm_j := pullback.condition
  comm_i := φ.comm_i
  comm_ε := by simp

/-- The square of geometric generic fibres of `φ.fromCart` is cartesian. -/
lemma isPullback_fromCart_commSq_j :
    IsPullback φ.fromCart.generic φ.cartModel.j N.j φ.fromCart.total :=
  IsPullback.of_hasPullback N.j φ.total

/-- The morphisms of total spaces of `φ.toCart` and `φ.fromCart` compose to that of `φ`. -/
lemma toCart_total_comp_fromCart_total : φ.toCart.total ≫ φ.fromCart.total = φ.total :=
  Category.id_comp _

/-- The morphisms of geometric generic fibres of `φ.toCart` and `φ.fromCart` compose to that
of `φ`. -/
lemma toCart_generic_comp_fromCart_generic :
    φ.toCart.generic ≫ φ.fromCart.generic = φ.generic :=
  pullback.lift_fst _ _ _

/-- **Composition law for the cartesian factorization**: the pullback exchange of `φ` is
`α_φ ∘ c = α_{toCart}(L(𝟙 Y)^*) ∘ L(𝟙 X')^* α_{fromCart} ∘ c'`. -/
lemma pullbackExchange_app_comp_cart
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (φ.pullbackExchange Λ).app C ≫
        (M.nearbyCycles Λ).map ((leftDerivedUpperStarCompOfEq Λ (Category.comp_id f)).hom.app C) =
      (leftDerivedUpperStarCompOfEq Λ (Category.id_comp f')).hom.app ((N.nearbyCycles Λ).obj C) ≫
        L((𝟙 X')^*⟦Λ⟧).map ((φ.fromCart.pullbackExchange Λ).app C) ≫
        (φ.toCart.pullbackExchange Λ).app (L((𝟙 Y)^*⟦Λ⟧).obj C) :=
  φ.toCart.pullbackExchange_comp_app_of_eq Λ φ.fromCart φ (Category.comp_id f)
    (Category.id_comp f') φ.toCart_total_comp_fromCart_total
    φ.toCart_generic_comp_fromCart_generic C

/-- **Gluing along the cartesian factorization**: if the pullback exchange of `φ.fromCart` is
invertible at `C` and that of `φ.toCart` is a split monomorphism at `L(𝟙 Y)^* C`, then the
pullback exchange of `φ` is a split monomorphism at `C`. -/
theorem isSplitMono_pullbackExchange_app_of_cart'
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hfrom : IsIso ((φ.fromCart.pullbackExchange Λ).app C))
    (hto : IsSplitMono ((φ.toCart.pullbackExchange Λ).app (L((𝟙 Y)^*⟦Λ⟧).obj C))) :
    IsSplitMono ((φ.pullbackExchange Λ).app C) :=
  isSplitMono_of_comp_eq_comp_comp (φ.pullbackExchange_app_comp_cart Λ C)

/-- **Gluing along the cartesian factorization**: if the pullback exchange of `φ.fromCart` is
invertible at `C` and that of `φ.toCart` is a split monomorphism at `C`, then the pullback
exchange of `φ` is a split monomorphism at `C`. -/
theorem isSplitMono_pullbackExchange_app_of_cart
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hfrom : IsIso ((φ.fromCart.pullbackExchange Λ).app C))
    (hto : IsSplitMono ((φ.toCart.pullbackExchange Λ).app C)) :
    IsSplitMono ((φ.pullbackExchange Λ).app C) :=
  φ.isSplitMono_pullbackExchange_app_of_cart' Λ C hfrom
    (NatTrans.isSplitMono_app_of_iso (φ.toCart.pullbackExchange Λ) (B := C)
      ((leftDerivedUpperStarId Λ Y).app C))

/-- The pullback exchange of `φ.fromCart` is invertible at `C` if the base change morphism
`Lt^* Rj_{N*} ⟶ Rj'_* Lpr₁^*` of the cartesian square of `N.j` along the morphism `t` of total
spaces is invertible at `Lε_N^* C`. -/
theorem isIso_fromCart_pullbackExchange_app_of_isIso_baseChangeMap_app
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hC : IsIso ((baseChangeMap Λ φ.fromCart.commSq_j).app ((L((N.ε)^*⟦Λ⟧)).obj C))) :
    IsIso ((φ.fromCart.pullbackExchange Λ).app C) :=
  φ.fromCart.isIso_pullbackExchange_app_of_isIso_baseChangeMap_app Λ C hC

end Hom

end NearbyCyclesModel

end General

namespace NearbyCyclesModel

variable {k' : Type u} [Field k']

/-- **The slice exchange from the cartesian factorization**: for a complex `B` on `𝔸ⁿ⁺¹_S`, the
pullback exchange of the morphism of models over the coordinate slice `hᵢ`
(`NearbyCyclesModel.affineSpaceSliceHom`) is a split monomorphism at `B` provided
* the pullback exchange of the cartesian part `fromCart` is invertible at `B` (by
  `NearbyCyclesModel.Hom.isIso_fromCart_pullbackExchange_app_of_isIso_baseChangeMap_app`, this
  is base change of `Rj_*` along `hᵢ` at `Lε^* B`), and
* the pullback exchange of the change of geometric generic fibre `toCart` is a split
  monomorphism at `B`. -/
theorem isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_cart
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (n : ℕ) (i : Fin (n + 1))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj Λ (affineSpaceModel k' (n + 1)).total)))
    (hfrom : IsIso (((affineSpaceSliceHom k' n i).fromCart.pullbackExchange Λ).app B))
    (hto : IsSplitMono (((affineSpaceSliceHom k' n i).toCart.pullbackExchange Λ).app B)) :
    IsSplitMono (((affineSpaceSliceHom k' n i).pullbackExchange Λ).app B) :=
  (affineSpaceSliceHom k' n i).isSplitMono_pullbackExchange_app_of_cart Λ B hfrom hto

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
