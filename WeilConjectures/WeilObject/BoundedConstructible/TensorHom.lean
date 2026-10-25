/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.WeilObject.BoundedConstructible.Defs

/-!

# The derived tensor product and derived hom of Weil objects

Let `Φ : X ⟶ X` be an endomorphism of a scheme over `Spec k`, and write `Φ` also for the
Frobenius pullback `LΦ^*` on `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`
(`WeilConjectures.WeilObject.BoundedConstructible.Defs`).
The tensor product is defined for every endomorphism `Φ`; the internal hom for an automorphism
`e : X ≅ X`, `Φ = e.hom`, for which `LΦ^*` is an equivalence.

* **Tensor product.** The comparison `m_{K,L} : Φ (K ⊗ᴸ L) ≅ Φ K ⊗ᴸ Φ L` is the restriction to
  bounded constructible complexes of the comparison of the derived pullback with the derived
  tensor product (`ProEtale.CondensedRing.leftDerivedUpperStarTensorIso`), and the Weil
  structure of `K ⊗ᴸ L` is
  ```
  Φ (K ⊗ᴸ L) --m--> Φ K ⊗ᴸ Φ L --φ_K ⊗ᴸ φ_L--> K ⊗ᴸ L
  ```
  (`ProEtale.CondensedRing.weilTensor`), the transport of Weil structures along the bifunctor
  `- ⊗ᴸ -` (`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso₂`).
* **Internal hom.** The comparison `h_{K,L} : Φ RHom(K, L) ⟶ RHom(Φ K, Φ L)` is the adjoint, for
  `Φ K ⊗ᴸ - ⊣ RHom(Φ K, -)`, of `Φ K ⊗ᴸ Φ RHom(K, L) --m⁻¹--> Φ (K ⊗ᴸ RHom(K, L)) --Φ ev--> Φ L`
  (`ProEtale.CondensedRing.weilHomComparisonApp`). The Weil structure of `RHom(K, L)` is
  ```
  Φ RHom(K, L) --h--> RHom(Φ K, Φ L) --RHom(φ_K⁻¹, φ_L)--> RHom(K, L)
  ```
  (`ProEtale.CondensedRing.weilHom`), with the inverse of `φ_K` in the contravariant variable.

## Sorried input

- the naturality of `weilTensorComparison`: the naturality of `leftDerivedUpperStarTensorIso`
  and of the compatibility isomorphisms of the restricted functors with the inclusions.
- `ProEtale.CondensedRing.weilHomComparisonApp_naturality`: the naturality of `h` in both
  variables, from the naturality of `m`, of the evaluation and of the adjunction.
- `ProEtale.CondensedRing.isIso_weilHomComparisonApp`: `h` is an isomorphism. `Φ` is an
  equivalence (`isEquivalence_boundedConstructibleUpperStar_of_iso`) and `m` an isomorphism, so
  for every `M` the composite
  `Hom(M, Φ RHom(K, L)) ≅ Hom(Φ⁻¹ M ⊗ᴸ K, L) ≅ Hom(M ⊗ᴸ Φ K, Φ L) ≅ Hom(M, RHom(Φ K, Φ L))`
  is induced by `h`, and Yoneda applies. No dualizability of `K` is needed.

## Main definitions

- `ProEtale.CondensedRing.weilTensorComparison`: the comparison
  `Φ (K ⊗ᴸ L) ≅ Φ K ⊗ᴸ Φ L` on `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`.
- `ProEtale.CondensedRing.weilTensor`: the derived tensor product of Weil objects.
- `ProEtale.CondensedRing.weilHomComparison`: the comparison
  `Φ RHom(K, L) ≅ RHom(Φ K, Φ L)` on `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`.
- `ProEtale.CondensedRing.weilHom`: the derived hom of Weil objects.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-! ### The tensor product -/

section Tensor

variable (Φ : X ⟶ X)

/-- The comparison `m_{K,L} : LΦ^* (K ⊗ᴸ L) ≅ LΦ^* K ⊗ᴸ LΦ^* L` on bounded constructible
`ℚ̄_ℓ`-sheaves, as an isomorphism of functors `Dᵇc × Dᵇc ⥤ Dᵇc`: the restriction along the fully
faithful inclusion of `leftDerivedUpperStarTensorIso`, through the compatibility isomorphisms of
the restricted pullback (`boundedConstructibleUpperStarCompatibility`) and tensor product with
the inclusions. -/
noncomputable def weilTensorComparison :
    Functor.uncurry.obj (boundedConstructibleTensor (Profinite.padicAlgClRingObj ℓ) X) ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ ≅
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).prod
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ) ⋙
        Functor.uncurry.obj (boundedConstructibleTensor (Profinite.padicAlgClRingObj ℓ) X) :=
  NatIso.ofComponents
    (fun KL ↦ (ObjectProperty.fullyFaithfulι _).preimageIso
      ((boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ
          Φ).app _ ≪≫
        ((leftDerivedUpperStarTensorIso (Profinite.padicAlgClRingObj ℓ) Φ.left).app
          KL.1.obj).app KL.2.obj ≪≫
        ((curriedTensor _).mapIso
          ((boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ
            Φ).app KL.1).symm).app _ ≪≫
        ((curriedTensor _).obj _).mapIso
          ((boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ
            Φ).app KL.2).symm))
    sorry

/-- The derived tensor product of Weil objects: a pair of Weil objects `(K, φ_K)` and `(L, φ_L)`
for `Φ` is sent to `K ⊗ᴸ L` with the structure isomorphism
`Φ (K ⊗ᴸ L) ≅ Φ K ⊗ᴸ Φ L ≅ K ⊗ᴸ L` given by `weilTensorComparison` and `φ_K ⊗ᴸ φ_L`. -/
noncomputable def weilTensor :
    WeilBoundedConstructible ℓ Φ ⥤ WeilBoundedConstructible ℓ Φ ⥤
      WeilBoundedConstructible ℓ Φ :=
  IsoAlgebra.mapOfNatIso₂ (boundedConstructibleTensor (Profinite.padicAlgClRingObj ℓ) X)
    (weilTensorComparison ℓ Φ)

@[simp]
lemma weilTensor_obj_obj_carrier (K L : WeilBoundedConstructible ℓ Φ) :
    (((weilTensor ℓ Φ).obj K).obj L).carrier =
      ((boundedConstructibleTensor (Profinite.padicAlgClRingObj ℓ) X).obj K.carrier).obj
        L.carrier :=
  rfl

end Tensor

/-! ### The internal hom -/

section Hom

variable (e : X ≅ X)

/-- The Frobenius pullback `Φ = Le^*` on `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`. -/
noncomputable abbrev weilFrobenius :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ e.hom

/-- The derived hom `RHom(-, -)` on `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`. -/
noncomputable abbrev weilRHom :
    (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)ᵒᵖ ⥤ Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleHom (Profinite.padicAlgClRingObj ℓ) X

/-- The evaluation `K ⊗ᴸ RHom(K, L) ⟶ L` on `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`: the counit of the adjunction
`K ⊗ᴸ - ⊣ RHom(K, -)`. -/
noncomputable def weilEv (K L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleTensor (Profinite.padicAlgClRingObj ℓ) X).obj K).obj
        (((weilRHom ℓ (X := X)).obj (Opposite.op K)).obj L) ⟶ L :=
  (boundedConstructibleTensorHomAdjunction (Profinite.padicAlgClRingObj ℓ) K).counit.app L

/-- The comparison `h_{K,L} : Φ RHom(K, L) ⟶ RHom(Φ K, Φ L)` on `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`: the adjoint, for
`Φ K ⊗ᴸ - ⊣ RHom(Φ K, -)`, of the composite
```
Φ K ⊗ᴸ Φ RHom(K, L) --m⁻¹--> Φ (K ⊗ᴸ RHom(K, L)) --Φ ev--> Φ L.
```
-/
noncomputable def weilHomComparisonApp (K L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (weilFrobenius ℓ e).obj (((weilRHom ℓ).obj (Opposite.op K)).obj L) ⟶
      ((weilRHom ℓ).obj (Opposite.op ((weilFrobenius ℓ e).obj K))).obj
        ((weilFrobenius ℓ e).obj L) :=
  (boundedConstructibleTensorHomAdjunction (Profinite.padicAlgClRingObj ℓ)
      ((weilFrobenius ℓ e).obj K)).homEquiv _ _
    ((weilTensorComparison ℓ e.hom).inv.app (K, ((weilRHom ℓ).obj (Opposite.op K)).obj L) ≫
      (weilFrobenius ℓ e).map (weilEv ℓ K L))

/-- The comparison `h_{K,L}` is natural in `K` (contravariantly) and in `L`. -/
lemma weilHomComparisonApp_naturality {K K' L L' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : K' ⟶ K) (ψ : L ⟶ L') :
    (weilFrobenius ℓ e).map
          (((weilRHom ℓ).map φ.op).app L ≫ ((weilRHom ℓ).obj (Opposite.op K')).map ψ) ≫
        weilHomComparisonApp ℓ e K' L' =
      weilHomComparisonApp ℓ e K L ≫
        (((weilRHom ℓ).map ((weilFrobenius ℓ e).map φ).op).app
            ((weilFrobenius ℓ e).obj L) ≫
          ((weilRHom ℓ).obj (Opposite.op ((weilFrobenius ℓ e).obj K'))).map
            ((weilFrobenius ℓ e).map ψ)) :=
  sorry

/-- The comparison `h_{K,L}` is an isomorphism: `Φ` is a strong monoidal equivalence. See the
module docstring. -/
instance isIso_weilHomComparisonApp (K L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (weilHomComparisonApp ℓ e K L) :=
  sorry

/-- The comparison `h : Φ RHom(K, L) ≅ RHom(Φ K, Φ L)` as an isomorphism of functors
`Dᵇc(X)ᵒᵖ × Dᵇc(X) ⥤ Dᵇc(X)`, for the endofunctor `Φ.op × Φ` of the source. -/
noncomputable def weilHomComparison :
    Functor.uncurry.obj (weilRHom ℓ (X := X)) ⋙ weilFrobenius ℓ e ≅
      (weilFrobenius ℓ e).op.prod (weilFrobenius ℓ e) ⋙
        Functor.uncurry.obj (weilRHom ℓ (X := X)) :=
  NatIso.ofComponents (fun KL ↦ asIso (weilHomComparisonApp ℓ e KL.1.unop KL.2))
    fun {KL KL'} φ ↦ by
      have := weilHomComparisonApp_naturality ℓ e φ.1.unop φ.2
      simpa using this

/-- The derived hom of Weil objects: for Weil objects `(K, φ_K)` and `(L, φ_L)` for `e`, the
object `RHom(K, L)` with the structure isomorphism
```
Φ RHom(K, L) --h--> RHom(Φ K, Φ L) --RHom(φ_K⁻¹, φ_L)--> RHom(K, L),
```
the inverse of `φ_K` entering through the contravariant variable
(`CategoryTheory.Endofunctor.IsoAlgebra.opFunctor`). -/
noncomputable def weilHom :
    (WeilBoundedConstructible ℓ e.hom)ᵒᵖ ⥤ WeilBoundedConstructible ℓ e.hom ⥤
      WeilBoundedConstructible ℓ e.hom :=
  IsoAlgebra.opFunctor ⋙ IsoAlgebra.mapOfNatIso₂ (weilRHom ℓ (X := X))
    (weilHomComparison ℓ e)

@[simp]
lemma weilHom_obj_obj_carrier (K : (WeilBoundedConstructible ℓ e.hom)ᵒᵖ)
    (L : WeilBoundedConstructible ℓ e.hom) :
    (((weilHom ℓ e).obj K).obj L).carrier =
      ((weilRHom ℓ).obj (Opposite.op K.unop.carrier)).obj L.carrier :=
  rfl

end Hom

end AlgebraicGeometry.ProEtale.CondensedRing
