/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.SectionsWithSupport
public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport

/-!
# Sections with closed support for `ℓ`-adic sheaves

Let `i : Z ⟶ X` be a closed immersion with quasi-compact open complement `j : U ⟶ X`. For a sheaf
`M` of modules over the constant `ℓ`-adic sheaf `ℚ̄_ℓ,X` on `X_proét`, the sheaf of sections with
support in `Z` is `Γ_Z(M) = i^* ker(M ⟶ j_* j^* M)`
(`AlgebraicGeometry.ProEtale.adicSectionsWithSupport`). This file proves blueprint
`det-lem-formal-closed-support-adjunction` for these sheaves (the coefficient ring
`Λ = ℚ̄_ℓ`, in the Bhatt–Scholze model), by the abstract argument of
`WeilConjectures.CategoryTheory.Abelian.SectionsWithSupport`, which only uses that `i_*` and
`j_!` are exact, `i_*` and `j_*` are fully faithful, `j^* i_* = 0`, `i^* j_! = 0`, and that
`i^*`, `j^*` jointly detect zero objects:

1. `ker(M ⟶ j_* j^* M) ≅ i_* Γ_Z(M)`, and `Γ_Z` is right adjoint to `i_*` and left exact;
2. `RΓ_Z` is right adjoint to `i_*` on the unbounded derived categories;
3. for an injective `I`, the unit `I ⟶ j_* j^* I` is an epimorphism;
4. the counit `i_* RΓ_Z K ⟶ K` and the unit `K ⟶ Rj_* j^* K` extend to a distinguished triangle
   with a unique third map, and `RΓ_Z K ≅ i^* fib(K ⟶ Rj_* j^* K)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable (l : ℕ) [Fact l.Prime] {Z U X : Scheme.{u}}
  (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  (hij : IsCompl (Set.range i.base) (Set.range j.base))

/-- Blueprint `det-lem-formal-closed-support-adjunction`: the functor of **sections with support
in `Z`**, `Γ_Z(M) = i^* ker(M ⟶ j_* j^* M)`, on sheaves of `ℚ̄_ℓ,X`-modules. -/
noncomputable def adicSectionsWithSupport : AdicSheaf l X ⥤ AdicSheaf l Z :=
  SectionsWithSupport.functor (adicUpperStarLowerStarAdjunction l i)
    (adicUpperStarLowerStarAdjunction l j)
    (isZero_adicUpperStar_obj_adicLowerStar_obj i j hij.disjoint)
    (AdicSheaf.isZero_of_isZero_adicUpperStar_of_isCompl i j hij)

/-- Blueprint `det-lem-formal-closed-support-adjunction` (1): `Γ_Z(M)` is `i^*` of the kernel of
the unit `M ⟶ j_* j^* M`. -/
lemma adicSectionsWithSupport_obj (M : AdicSheaf l X) :
    (adicSectionsWithSupport l i j hij).obj M =
      (i)^*ᵃ[l].obj (kernel ((adicUpperStarLowerStarAdjunction l j).unit.app M)) :=
  rfl

/-- Blueprint `det-lem-formal-closed-support-adjunction` (1): `i_* ⊣ Γ_Z`. -/
noncomputable def adicSectionsWithSupportAdjunction :
    (i)_*ᵃ[l] ⊣ adicSectionsWithSupport l i j hij :=
  SectionsWithSupport.adjunction _ _ _ _

/-- Blueprint `det-lem-formal-closed-support-adjunction` (1): `Γ_Z` is left exact. -/
lemma preservesFiniteLimits_adicSectionsWithSupport :
    PreservesFiniteLimits (adicSectionsWithSupport l i j hij) :=
  SectionsWithSupport.preservesFiniteLimits_functor _ _ _ _

/-- Blueprint `det-lem-formal-closed-support-adjunction` (1):
`ker(M ⟶ j_* j^* M) ≅ i_* Γ_Z(M)`. -/
noncomputable def kernelIsoAdicLowerStarAdicSectionsWithSupport (M : AdicSheaf l X) :
    kernel ((adicUpperStarLowerStarAdjunction l j).unit.app M) ≅
      (i)_*ᵃ[l].obj ((adicSectionsWithSupport l i j hij).obj M) :=
  SectionsWithSupport.kernelIso _ _ _ _ M

/-- Blueprint `det-lem-formal-closed-support-adjunction` (3): for an injective sheaf `I`, the
unit `I ⟶ j_* j^* I` is an epimorphism. -/
lemma epi_adicUpperStarLowerStarAdjunction_unit_app_of_injective (I : AdicSheaf l X)
    [Injective I] : Epi ((adicUpperStarLowerStarAdjunction l j).unit.app I) :=
  SectionsWithSupport.epi_unit_app_of_injective (adicUpperStarLowerStarAdjunction l i)
    (adicUpperStarLowerStarAdjunction l j)
    (isZero_adicUpperStar_obj_adicLowerStar_obj i j hij.disjoint)
    (AdicSheaf.isZero_of_isZero_adicUpperStar_of_isCompl i j hij)
    (adicOpenImmersionLowerShriekAdjunction l j)
    (fun V ↦ isZero_adicUpperStar_adicOpenImmersionLowerShriek j i
      (Set.disjoint_iff_inter_eq_empty.1 hij.symm.disjoint) V) I

section Derived

/-- Blueprint `det-lem-formal-closed-support-adjunction` (2): `RΓ_Z` is right adjoint to `i_*`
on the unbounded derived categories. -/
noncomputable def adicDerivedSectionsWithSupportAdjunction :
    ((i)_*ᵃ[l]).mapDerivedCategory ⊣ (adicSectionsWithSupport l i j hij).rightDerivedFunctor :=
  have := preservesFiniteColimits_adicLowerStar_of_isCompl (l := l) i j hij
  SectionsWithSupport.derivedAdjunction _ _ _ _

/-- Blueprint `det-lem-formal-closed-support-adjunction` (4): for `K` in `D(X_proét, ℚ̄_ℓ)`, the
counit `i_* RΓ_Z K ⟶ K` and the unit `K ⟶ Rj_* j^* K` extend to a distinguished triangle
`i_* RΓ_Z K ⟶ K ⟶ Rj_* j^* K ⟶ (i_* RΓ_Z K)[1]`, with a unique third map; it is natural in `K`
(`CategoryTheory.Pretriangulated.Recollement.exists_triangleHom`). -/
theorem existsUnique_distTriang_adicSectionsWithSupport (K : DerivedCategory (AdicSheaf l X)) :
    ∃! w, Recollement.triangle (adicDerivedUpperStarLowerStarAdjunction l j)
      (adicDerivedSectionsWithSupportAdjunction l i j hij) K w ∈ distTriang _ :=
  have := preservesFiniteColimits_adicLowerStar_of_isCompl (l := l) i j hij
  SectionsWithSupport.existsUnique_distTriang _ _ _ _ K

/-- Blueprint `det-lem-formal-closed-support-adjunction` (4):
`RΓ_Z K ≅ i^* fib(K ⟶ Rj_* j^* K)`: for a distinguished triangle `F ⟶ K ⟶ Rj_* j^* K ⟶ F[1]`
whose second map is the unit, `i^* F ≅ RΓ_Z K`. -/
theorem nonempty_iso_adicUpperStar_fib (K : DerivedCategory (AdicSheaf l X))
    {F : DerivedCategory (AdicSheaf l X)} (a : F ⟶ K)
    (δ : ((j)_*ᵃ[l]).rightDerivedFunctor.obj (((j)^*ᵃ[l]).mapDerivedCategory.obj K) ⟶
      F⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a ((adicDerivedUpperStarLowerStarAdjunction l j).unit.app K) δ ∈
      distTriang _) :
    Nonempty (((i)^*ᵃ[l]).mapDerivedCategory.obj F ≅
      (adicSectionsWithSupport l i j hij).rightDerivedFunctor.obj K) :=
  have := preservesFiniteColimits_adicLowerStar_of_isCompl (l := l) i j hij
  SectionsWithSupport.nonempty_iso_upperStar_fib _ _ _ _ K a δ hT

end Derived

end ProEtale

end AlgebraicGeometry
