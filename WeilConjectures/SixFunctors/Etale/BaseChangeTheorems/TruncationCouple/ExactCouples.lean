/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TruncationCouple.ExchangeTriangulated
public import WeilConjectures.Algebra.Homology.ExactCouple.TruncationCoupleFunctor

/-!
# The truncation exact couples of the exchange map

Let `g' ≫ f = f' ≫ g` be a commutative square of schemes and `K ∈ D⁺(X_ét)`. Write
`Φ = R f_*⁺ ⋙ D g^*⁺` and `Ψ = D g'^*⁺ ⋙ R f'_*⁺ : D⁺(X_ét) ⥤ D⁺(Y'_ét)`. Applying `Φ` and `Ψ`
to the truncation triangles `τ_{≤ q - 1} K ⟶ τ_{≤ q} K ⟶ Hᵠ(K)[-q] ⟶ (τ_{≤ q - 1} K)⟦1⟧` and
taking cohomology sheaves gives the two truncation exact couples, indexed by filtration degree
`p` and total degree `n = p + q`,
```
  D_Φ^{p,n} = Hⁿ(g^* R f_* τ_{≤ q} K),   E_Φ^{p,n} = Hⁿ(g^* R f_* (Hᵠ(K)[-q])),
  D_Ψ^{p,n} = Hⁿ(R f'_* g'^* τ_{≤ q} K),  E_Ψ^{p,n} = Hⁿ(R f'_* g'^* (Hᵠ(K)[-q]))
```
(`AlgebraicGeometry.Etale.truncationCoupleSource`,
`AlgebraicGeometry.Etale.truncationCoupleTarget`, instances of the truncation couple
`DerivedCategory.Plus.functorTruncationCouple` of a triangulated functor), and the derived
exchange map `Ex : Φ ⟶ Ψ` induces a morphism of exact couples
(`AlgebraicGeometry.Etale.truncationCoupleExchange`). This is blueprint
`def-weil-pbc-truncation-exact-couples` and `lem-weil-pbc-truncation-couple-morphism`.

The morphism induces morphisms of all the pages of the two spectral sequences commuting with
all the differentials, and its component on the first page in bidegree `(p, q)` is the exchange
map `Hᵖ(Ex_{Hᵠ(K)}) : Hᵖ(g^* R f_* Hᵠ(K)) ⟶ Hᵖ(R f'_* g'^* Hᵠ(K))`
(`AlgebraicGeometry.Etale.truncationCoupleExchange_derivedIter_comm_d`,
`AlgebraicGeometry.Etale.truncationCoupleExchange_τE`, blueprint
`lem-weil-pbc-exact-couple-differential`).

Finally the couples are finite in every total degree, and the map on abutments is
`Hⁿ(Ex_K) : Hⁿ(g^* R f_* K) ⟶ Hⁿ(R f'_* g'^* K)`, compatible with the filtrations by the
images of `Hⁿ(Φ τ_{≤ q} K)` and `Hⁿ(Ψ τ_{≤ q} K)` (blueprint
`lemma-weil-pbc-exact-couple-abutment`).

The truncation functors on the derived category are those of its canonical t-structure; their
descent from complexes uses the universal property of the localization (blueprint
`lem-weil-pbc-localization-universal-property`, Mathlib's `CategoryTheory.Localization.lift`).
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Pretriangulated

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

open Etale DerivedCategory.Plus

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

section Couples

omit [HasSmallSiteSheafify A]

/-- The truncation exact couple of `Φ = R f_*⁺ ⋙ D g^*⁺` at `K`:
`D^{p,n} = Hⁿ(g^* R f_* τ_{≤ n - p} K)` and `E^{p,n} = Hⁿ(g^* R f_* (Hⁿ⁻ᵖ(K)[p - n]))`, the
couple `(A_q, G_q)` of blueprint `def-weil-pbc-truncation-exact-couples`. That it is an exact
couple is part (1) of blueprint `lem-weil-pbc-truncation-couple-morphism`. -/
noncomputable def Etale.truncationCoupleSource (f : X ⟶ Y) (g : Y' ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    ExactCouple (Sheaf Y'.smallEtaleTopology A) ((-1, 0) : ℤ × ℤ) (2, 1) 0 :=
  functorTruncationCouple ((f)_*[A].rightDerivedFunctorPlus ⋙ ((g)^*[A]).mapDerivedCategoryPlus) K

/-- The truncation exact couple of `Ψ = D g'^*⁺ ⋙ R f'_*⁺` at `K`:
`D^{p,n} = Hⁿ(R f'_* g'^* τ_{≤ n - p} K)` and `E^{p,n} = Hⁿ(R f'_* g'^* (Hⁿ⁻ᵖ(K)[p - n]))`,
the couple `(B_q, H_q)` of blueprint `def-weil-pbc-truncation-exact-couples`. That it is an
exact couple is part (1) of blueprint `lem-weil-pbc-truncation-couple-morphism`. -/
noncomputable def Etale.truncationCoupleTarget (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    ExactCouple (Sheaf Y'.smallEtaleTopology A) ((-1, 0) : ℤ × ℤ) (2, 1) 0 :=
  functorTruncationCouple
    (((g')^*[A]).mapDerivedCategoryPlus ⋙ (f')_*[A].rightDerivedFunctorPlus) K

variable (sq : CommSq g' f' f g) (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))

/-- This is blueprint `def-weil-pbc-truncation-exact-couples`: the morphism between the two
truncation exact couples induced by the derived exchange map `Ex : Φ ⟶ Ψ` on the truncation
triangles. That it is a morphism of exact couples is part (2) of blueprint
`lem-weil-pbc-truncation-couple-morphism`. -/
noncomputable def Etale.truncationCoupleExchange :
    ExactCouple.Hom (Etale.truncationCoupleSource A f g K)
      (Etale.truncationCoupleTarget A g' f' K) :=
  functorTruncationCoupleHom (Etale.derivedBaseChangeMapPlus A sq) K

/-- Blueprint `lem-weil-pbc-truncation-couple-morphism` (2): the component of the morphism of
truncation couples on `D^{p,n}` is `Hⁿ(Ex_{τ_{≤ n - p} K})`. -/
lemma Etale.truncationCoupleExchange_τD (p n : ℤ) :
    (Etale.truncationCoupleExchange A sq K).τD (p, n) =
      (homologyFunctor _ n).map
        ((Etale.derivedBaseChangeMapPlus A sq).app ((truncLETower K).X (n - p))) :=
  rfl

/-- Blueprint `lem-weil-pbc-truncation-couple-morphism` (2): the component of the morphism of
truncation couples on `E^{p,n}` is `Hⁿ(Ex_{Hⁿ⁻ᵖ(K)[p - n]})`. -/
lemma Etale.truncationCoupleExchange_τE' (p n : ℤ) :
    (Etale.truncationCoupleExchange A sq K).τE (p, n) =
      (homologyFunctor _ n).map
        ((Etale.derivedBaseChangeMapPlus A sq).app ((truncLETower K).Y (n - p))) :=
  rfl

/-- This is blueprint `lem-weil-pbc-truncation-couple-morphism` (3) and the last assertion of
`def-weil-pbc-truncation-exact-couples`: under the identifications
`E_Φ^{p,n} ≅ Hᵖ(g^* R f_* Hᵠ(K))` and `E_Ψ^{p,n} ≅ Hᵖ(R f'_* g'^* Hᵠ(K))` (`q = n - p`) given by
the shift isomorphisms, the component of the morphism of truncation couples on `E^{p,n}` is the
degree `p` exchange map `Hᵖ(Ex_{Hᵠ(K)})` of the sheaf `Hᵠ(K)`. -/
lemma Etale.truncationCoupleExchange_τE (p n : ℤ) :
    (Etale.truncationCoupleExchange A sq K).τE (p, n) =
      (functorTruncationCoupleEIso _ K p n).hom ≫ (homologyFunctor _ p).map
        ((Etale.derivedBaseChangeMapPlus A sq).app
          ((singleFunctor _ 0).obj ((homologyFunctor _ (n - p)).obj K))) ≫
        (functorTruncationCoupleEIso _ K p n).inv := by
  rw [← functorTruncationCoupleHom_τE_comp_eIso_hom_assoc, Iso.hom_inv_id, comp_id]
  rfl

/-- The connecting maps `f` of the two exact couples (the connecting morphisms of the long exact
cohomology sequences of the images of the truncation triangles) commute with the exchange maps
(blueprint `lem-weil-pbc-exact-couple-differential`). -/
lemma Etale.truncationCoupleExchange_comm_f (i j : ℤ × ℤ) :
    (Etale.truncationCoupleSource A f g K).f i j ≫
        (Etale.truncationCoupleExchange A sq K).τD j =
      (Etale.truncationCoupleExchange A sq K).τE i ≫
        (Etale.truncationCoupleTarget A g' f' K).f i j :=
  (Etale.truncationCoupleExchange A sq K).commf i j

/-- This is blueprint `lem-weil-pbc-exact-couple-differential`: the morphism of truncation
couples induces morphisms `(Etale.truncationCoupleExchange A sq K).derivedIter N` between all
the iterated derived couples, i.e. between all the pages of the two spectral sequences (the
page `N = 0`, the `E₂`-page, being the morphism of exact couples itself, whose `E`-component is
the exchange map `Hᵖ(Ex_{Hᵠ(K)})`, `AlgebraicGeometry.Etale.truncationCoupleExchange_τE`), and
these commute with all the differentials. -/
lemma Etale.truncationCoupleExchange_derivedIter_comm_d (N : ℕ) (i j : ℤ × ℤ) :
    ((Etale.truncationCoupleSource A f g K).derivedIter N).d i j ≫
        ((Etale.truncationCoupleExchange A sq K).derivedIter N).τE j =
      ((Etale.truncationCoupleExchange A sq K).derivedIter N).τE i ≫
        ((Etale.truncationCoupleTarget A g' f' K).derivedIter N).d i j :=
  (((Etale.truncationCoupleExchange A sq K).derivedIter N).dMap.comm i j).symm

/-- The morphism of spectral sequences, starting on page `2`, induced by the morphism of
truncation couples (blueprint `lem-weil-pbc-exact-couple-differential`). -/
noncomputable def Etale.truncationCoupleExchangeSpectralSequenceMap :
    (Etale.truncationCoupleSource A f g K).spectralSequence 2 ⟶
      (Etale.truncationCoupleTarget A g' f' K).spectralSequence 2 :=
  (Etale.truncationCoupleExchange A sq K).spectralSequenceMap 2

end Couples

section Abutment

omit [HasSmallSiteSheafify A]

/-- `Φ = R f_*⁺ ⋙ D g^*⁺` does not lower the cohomological degree. -/
lemma Etale.isZero_homologyFunctor_rightDerivedFunctorPlus_comp_upperStar
    (X₀ : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) (n : ℤ) [X₀.IsGE n] (q : ℤ)
    (hq : q < n) :
    IsZero ((homologyFunctor _ q).obj
      (((f)_*[A].rightDerivedFunctorPlus ⋙ ((g)^*[A]).mapDerivedCategoryPlus).obj X₀)) :=
  ((g)^*[A].map_isZero
    ((f)_*[A].isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE X₀ n hq)).of_iso
    ((((g)^*[A]).mapDerivedCategoryPlusHomologyFunctorIso q).symm.app _)

/-- `Ψ = D g'^*⁺ ⋙ R f'_*⁺` does not lower the cohomological degree. -/
lemma Etale.isZero_homologyFunctor_upperStar_comp_rightDerivedFunctorPlus
    (X₀ : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) (n : ℤ) [X₀.IsGE n] (q : ℤ)
    (hq : q < n) :
    IsZero ((homologyFunctor _ q).obj
      ((((g')^*[A]).mapDerivedCategoryPlus ⋙ (f')_*[A].rightDerivedFunctorPlus).obj X₀)) := by
  have : (ι.obj X₀).IsGE n := inferInstance
  have := ((g')^*[A]).isGE_mapDerivedCategory_obj (ι.obj X₀) n
  have : (((g')^*[A]).mapDerivedCategoryPlus.obj X₀).IsGE n := (isGE_ι_obj_iff _ n).1 this
  exact (f')_*[A].isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ n hq

variable (sq : CommSq g' f' f g) (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))

/-- Blueprint `lemma-weil-pbc-exact-couple-abutment`: if `Hᵠ(K) = 0` for `q < a`, the two
truncation couples are half-plane couples: `D^{p,n}` vanishes for `n - p < a`, and `E^{p,n}`
vanishes unless `p ≥ 0` and `n - p ≥ a`, so that in total degree `n` only `a ≤ q ≤ n` occurs. -/
lemma Etale.isHalfPlane_truncationCouple (a : ℤ) [K.IsGE a] :
    (Etale.truncationCoupleSource A f g K).IsHalfPlane a ∧
      (Etale.truncationCoupleTarget A g' f' K).IsHalfPlane a :=
  ⟨functorTruncationCouple_isHalfPlane _ K
      (fun X₀ n _ q hq ↦
        Etale.isZero_homologyFunctor_rightDerivedFunctorPlus_comp_upperStar A X₀ n q hq) a,
    functorTruncationCouple_isHalfPlane _ K
      (fun X₀ n _ q hq ↦
        Etale.isZero_homologyFunctor_upperStar_comp_rightDerivedFunctorPlus A X₀ n q hq) a⟩

/-- Blueprint `lemma-weil-pbc-exact-couple-abutment`: for `p ≤ 0` the abutment maps
`D^{p,n} = Hⁿ(Φ τ_{≤ n - p} K) ⟶ Hⁿ(Φ K)` and `D^{p,n} = Hⁿ(Ψ τ_{≤ n - p} K) ⟶ Hⁿ(Ψ K)` are
isomorphisms, and the morphism of truncation couples is compatible with the abutment maps, the
map on the abutments being the exchange map `Hⁿ(Ex_K) : Hⁿ(g^* R f_* K) ⟶ Hⁿ(R f'_* g'^* K)`;
it respects the image filtrations of the abutments. -/
lemma Etale.truncationCoupleExchange_abutment (p n : ℤ) :
    (p ≤ 0 → IsIso (functorTruncationCoupleι
        ((f)_*[A].rightDerivedFunctorPlus ⋙ ((g)^*[A]).mapDerivedCategoryPlus) K p n)) ∧
      (p ≤ 0 → IsIso (functorTruncationCoupleι
        (((g')^*[A]).mapDerivedCategoryPlus ⋙ (f')_*[A].rightDerivedFunctorPlus) K p n)) ∧
      (Etale.truncationCoupleExchange A sq K).τD (p, n) ≫ functorTruncationCoupleι _ K p n =
        functorTruncationCoupleι _ K p n ≫
          (homologyFunctor _ n).map ((Etale.derivedBaseChangeMapPlus A sq).app K) ∧
      imageSubobject (((functorTruncationCoupleFiltration _ K n).F p).arrow ≫
          (homologyFunctor _ n).map ((Etale.derivedBaseChangeMapPlus A sq).app K)) ≤
        (functorTruncationCoupleFiltration
          (((g')^*[A]).mapDerivedCategoryPlus ⋙ (f')_*[A].rightDerivedFunctorPlus) K n).F p :=
  ⟨fun hp ↦ isIso_functorTruncationCoupleι _ K
      (fun X₀ n _ q hq ↦
        Etale.isZero_homologyFunctor_rightDerivedFunctorPlus_comp_upperStar A X₀ n q hq) p n hp,
    fun hp ↦ isIso_functorTruncationCoupleι _ K
      (fun X₀ n _ q hq ↦
        Etale.isZero_homologyFunctor_upperStar_comp_rightDerivedFunctorPlus A X₀ n q hq) p n hp,
    functorTruncationCoupleHom_τD_ι _ K p n,
    imageSubobject_functorTruncationCoupleFiltration_le _ K n p⟩

end Abutment

end AlgebraicGeometry
