/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TruncationCouple.ExchangeTriangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.TruncationCoupleAbutment
public import WeilConjectures.CategoryTheory.SpectralSequence.ExactCouple.DerivedFunctor

/-!
# The truncation exact couples of the exchange map

Let `g' ≫ f = f' ≫ g` be a commutative square of schemes and `K ∈ D⁺(X_ét)`. Write
`Φ = R f_*⁺ ⋙ D g^*⁺` and `Ψ = D g'^*⁺ ⋙ R f'_*⁺ : D⁺(X_ét) ⥤ D⁺(Y'_ét)`. Applying `Φ` and `Ψ`
to the truncation triangles `τ_{≤ q-1} K ⟶ τ_{≤ q} K ⟶ H^q(K)[-q] ⟶ (τ_{≤ q-1} K)⟦1⟧` and
taking cohomology sheaves gives the two truncation exact couples
```
  D_Φ^{p,q} = H^{p+q}(g^* R f_* τ_{≤ q} K),   E_Φ^{p,q} = H^{p+q}(g^* R f_* (H^q(K)[-q])),
  D_Ψ^{p,q} = H^{p+q}(R f'_* g'^* τ_{≤ q} K),  E_Ψ^{p,q} = H^{p+q}(R f'_* g'^* (H^q(K)[-q]))
```
(`AlgebraicGeometry.Etale.truncationCoupleSource`, `AlgebraicGeometry.Etale.truncationCoupleTarget`),
and the derived exchange map `Ex : Φ ⟶ Ψ` induces a morphism of exact couples
(`AlgebraicGeometry.Etale.truncationCoupleExchange`). This is blueprint
`def-weil-pbc-truncation-exact-couples` and `lem-weil-pbc-truncation-couple-morphism`.

The morphism induces morphisms of all the pages of the two spectral sequences commuting with
all the differentials, and its component on the first page in bidegree `(p, q)` is the exchange
map `H^p(Ex_{H^q(K)}) : H^p(g^* R f_* H^q(K)) ⟶ H^p(R f'_* g'^* H^q(K))`
(`AlgebraicGeometry.Etale.truncationCoupleExchange_iter_comm_d`,
`AlgebraicGeometry.Etale.truncationCoupleExchange_hE`, blueprint
`lem-weil-pbc-exact-couple-differential`).

Finally the couples are finite in every total degree, and the map on abutments is
`H^n(Ex_K) : H^n(g^* R f_* K) ⟶ H^n(R f'_* g'^* K)`, compatible with the filtrations by the
images of `H^n(Φ τ_{≤ q} K)` and `H^n(Ψ τ_{≤ q} K)` (blueprint
`lemma-weil-pbc-exact-couple-abutment`).
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
`D^{p,q} = H^{p+q}(g^* R f_* τ_{≤ q} K)` and `E^{p,q} = H^{p+q}(g^* R f_* (H^q(K)[-q]))`, the
couple `(A_q, G_q)` of blueprint `def-weil-pbc-truncation-exact-couples`. That it is an exact
couple is part (1) of blueprint `lem-weil-pbc-truncation-couple-morphism`. -/
noncomputable def Etale.truncationCoupleSource (f : X ⟶ Y) (g : Y' ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    ExactCouple (Sheaf Y'.smallEtaleTopology A) 0 :=
  truncationCouple ((f)_*[A].rightDerivedFunctorPlus ⋙ ((g)^*[A]).mapDerivedCategoryPlus) K

/-- The truncation exact couple of `Ψ = D g'^*⁺ ⋙ R f'_*⁺` at `K`:
`D^{p,q} = H^{p+q}(R f'_* g'^* τ_{≤ q} K)` and `E^{p,q} = H^{p+q}(R f'_* g'^* (H^q(K)[-q]))`, the
couple `(B_q, H_q)` of blueprint `def-weil-pbc-truncation-exact-couples`. That it is an exact
couple is part (1) of blueprint `lem-weil-pbc-truncation-couple-morphism`. -/
noncomputable def Etale.truncationCoupleTarget (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    ExactCouple (Sheaf Y'.smallEtaleTopology A) 0 :=
  truncationCouple (((g')^*[A]).mapDerivedCategoryPlus ⋙ (f')_*[A].rightDerivedFunctorPlus) K

variable (sq : CommSq g' f' f g) (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))

/-- This is blueprint `def-weil-pbc-truncation-exact-couples`: the morphism between the two
truncation exact couples induced by the derived exchange map `Ex : Φ ⟶ Ψ` on the truncation
triangles. That it is a morphism of exact couples is part (2) of blueprint
`lem-weil-pbc-truncation-couple-morphism`. -/
noncomputable def Etale.truncationCoupleExchange :
    Etale.truncationCoupleSource A f g K ⟶ Etale.truncationCoupleTarget A g' f' K :=
  truncationCoupleMap (Etale.derivedBaseChangeMapPlus A sq) K

/-- Blueprint `lem-weil-pbc-truncation-couple-morphism` (2): the component of the morphism of
truncation couples on `D^{p,q}` is `H^{p+q}(Ex_{τ_{≤ q} K})`. -/
lemma Etale.truncationCoupleExchange_hD (p q : ℤ) :
    (Etale.truncationCoupleExchange A sq K).hD p q =
      ((homologyFunctor _ 0).shift (p + q)).map
        ((Etale.derivedBaseChangeMapPlus A sq).app ((truncLE _ q).obj K)) :=
  rfl

/-- Blueprint `lem-weil-pbc-truncation-couple-morphism` (2): the component of the morphism of
truncation couples on `E^{p,q}` is `H^{p+q}(Ex_{H^q(K)[-q]})`. -/
lemma Etale.truncationCoupleExchange_hE' (p q : ℤ) :
    (Etale.truncationCoupleExchange A sq K).hE p q =
      ((homologyFunctor _ 0).shift (p + q)).map
        ((Etale.derivedBaseChangeMapPlus A sq).app ((homologySingleFunctor _ q).obj K)) :=
  rfl

/-- This is blueprint `lem-weil-pbc-truncation-couple-morphism` (3) and the last assertion of
`def-weil-pbc-truncation-exact-couples`: under the identifications
`E_Φ^{p,q} ≅ H^p(g^* R f_* H^q(K))` and `E_Ψ^{p,q} ≅ H^p(R f'_* g'^* H^q(K))` given by the
shift isomorphisms, the component of the morphism of truncation couples on `E^{p,q}` is the
degree `p` exchange map `H^p(Ex_{H^q(K)})` of the sheaf `H^q(K)`. -/
lemma Etale.truncationCoupleExchange_hE (p q : ℤ) :
    (Etale.truncationCoupleExchange A sq K).hE p q =
      (truncationCoupleEIso _ K p q).hom ≫ ((homologyFunctor _ 0).shift p).map
        ((Etale.derivedBaseChangeMapPlus A sq).app
          ((singleFunctor _ 0).obj ((homologyFunctor _ q).obj K))) ≫
        (truncationCoupleEIso _ K p q).inv :=
  truncationCoupleMap_hE_eq _ K p q

/-- This is blueprint `lem-weil-pbc-exact-couple-differential`: the morphism of truncation
couples induces morphisms `(Etale.truncationCoupleExchange A sq K).iter k` between all the
pages of the two spectral sequences (the page `k = 0` being the morphism of exact couples
itself, whose `E`-component is the exchange map `H^p(Ex_{H^q(K)})`,
`AlgebraicGeometry.Etale.truncationCoupleExchange_hE`), and these commute with all the
differentials. -/
lemma Etale.truncationCoupleExchange_iter_comm_d (k : ℕ) (p q p' q' : ℤ)
    (hp : p + k + 2 = p') (hq : q' + k + 1 = q) :
    ((Etale.truncationCoupleSource A f g K).iter k).d p q p' q' ≫
        ((Etale.truncationCoupleExchange A sq K).iter k).hE p' q' =
      ((Etale.truncationCoupleExchange A sq K).iter k).hE p q ≫
        ((Etale.truncationCoupleTarget A g' f' K).iter k).d p q p' q' :=
  ExactCouple.Hom.iter_comm_d _ k p q p' q' hp hq

/-- The connecting maps `f` of the two exact couples (the connecting morphisms of the long exact
cohomology sequences of the images of the truncation triangles) commute with the exchange maps
(blueprint `lem-weil-pbc-exact-couple-differential`). -/
lemma Etale.truncationCoupleExchange_comm_f (p q p' q' : ℤ) (hp : p + 2 = p')
    (hq : q' + 1 = q) :
    (Etale.truncationCoupleSource A f g K).f p q p' q' ≫
        (Etale.truncationCoupleExchange A sq K).hD p' q' =
      (Etale.truncationCoupleExchange A sq K).hE p q ≫
        (Etale.truncationCoupleTarget A g' f' K).f p q p' q' :=
  (Etale.truncationCoupleExchange A sq K).comm_f p q p' q' hp hq

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

/-- Blueprint `lemma-weil-pbc-exact-couple-abutment`: if `H^q(K) = 0` for `q < a`, the terms
`D^{p,q}` and `E^{p,q}` of the truncation couple of `Φ` vanish for `q < a`, and `E^{p,q}`
vanishes for `p < 0`. -/
lemma Etale.isZero_truncationCoupleSource (a : ℤ) [K.IsGE a] (p q : ℤ) :
    (q < a → IsZero ((Etale.truncationCoupleSource A f g K).D p q)) ∧
      (q < a → IsZero ((Etale.truncationCoupleSource A f g K).E p q)) ∧
      (p < 0 → IsZero ((Etale.truncationCoupleSource A f g K).E p q)) :=
  ⟨isZero_truncationCouple_D_of_lt _ K a p q, isZero_truncationCouple_E_of_lt _ K a p q,
    isZero_truncationCouple_E_of_neg _ K
      (fun X₀ n _ q hq ↦
        Etale.isZero_homologyFunctor_rightDerivedFunctorPlus_comp_upperStar A X₀ n q hq) p q⟩

/-- Blueprint `lemma-weil-pbc-exact-couple-abutment`: if `H^q(K) = 0` for `q < a`, the terms
`D^{p,q}` and `E^{p,q}` of the truncation couple of `Ψ` vanish for `q < a`, and `E^{p,q}`
vanishes for `p < 0`. -/
lemma Etale.isZero_truncationCoupleTarget (a : ℤ) [K.IsGE a] (p q : ℤ) :
    (q < a → IsZero ((Etale.truncationCoupleTarget A g' f' K).D p q)) ∧
      (q < a → IsZero ((Etale.truncationCoupleTarget A g' f' K).E p q)) ∧
      (p < 0 → IsZero ((Etale.truncationCoupleTarget A g' f' K).E p q)) :=
  ⟨isZero_truncationCouple_D_of_lt _ K a p q, isZero_truncationCouple_E_of_lt _ K a p q,
    isZero_truncationCouple_E_of_neg _ K
      (fun X₀ n _ q hq ↦
        Etale.isZero_homologyFunctor_upperStar_comp_rightDerivedFunctorPlus A X₀ n q hq) p q⟩

/-- Blueprint `lemma-weil-pbc-exact-couple-abutment`: for `p ≤ 0` the abutment maps
`D^{p,q} = H^{p+q}(Φ τ_{≤ q} K) ⟶ H^{p+q}(Φ K)` and
`D^{p,q} = H^{p+q}(Ψ τ_{≤ q} K) ⟶ H^{p+q}(Ψ K)` are isomorphisms, and the morphism of truncation
couples is compatible with them, the map on the abutments being the exchange map
`H^{p+q}(Ex_K) : H^{p+q}(g^* R f_* K) ⟶ H^{p+q}(R f'_* g'^* K)`. -/
lemma Etale.truncationCoupleExchange_abutment (p q : ℤ) (hp : p ≤ 0) :
    IsIso (truncationCoupleAbutmentMap
        ((f)_*[A].rightDerivedFunctorPlus ⋙ ((g)^*[A]).mapDerivedCategoryPlus) K p q) ∧
      IsIso (truncationCoupleAbutmentMap
        (((g')^*[A]).mapDerivedCategoryPlus ⋙ (f')_*[A].rightDerivedFunctorPlus) K p q) ∧
      (Etale.truncationCoupleExchange A sq K).hD p q ≫
          truncationCoupleAbutmentMap _ K p q =
        truncationCoupleAbutmentMap _ K p q ≫
          ((homologyFunctor _ 0).shift (p + q)).map ((Etale.derivedBaseChangeMapPlus A sq).app K) :=
  ⟨isIso_truncationCoupleAbutmentMap _ K
      (fun X₀ n _ q hq ↦
        Etale.isZero_homologyFunctor_rightDerivedFunctorPlus_comp_upperStar A X₀ n q hq) p q hp,
    isIso_truncationCoupleAbutmentMap _ K
      (fun X₀ n _ q hq ↦
        Etale.isZero_homologyFunctor_upperStar_comp_rightDerivedFunctorPlus A X₀ n q hq) p q hp,
    truncationCoupleMap_hD_comp_abutmentMap _ K p q⟩

/-- Blueprint `lemma-weil-pbc-exact-couple-abutment`: the exchange map
`H^n(Ex_K) : H^n(g^* R f_* K) ⟶ H^n(R f'_* g'^* K)` maps the image filtration of
`H^n(g^* R f_* τ_{≤ q} K) ⟶ H^n(g^* R f_* K)` into the image filtration of
`H^n(R f'_* g'^* τ_{≤ q} K) ⟶ H^n(R f'_* g'^* K)`. -/
lemma Etale.truncationCoupleExchange_filtration (n q : ℤ) :
    imageSubobject (((homologyFunctor _ 0).shift n).map
        (((f)_*[A].rightDerivedFunctorPlus ⋙ ((g)^*[A]).mapDerivedCategoryPlus).map
          ((truncLEι _ q).app K)) ≫
      ((homologyFunctor _ 0).shift n).map ((Etale.derivedBaseChangeMapPlus A sq).app K)) ≤
      truncationCoupleFiltration
        (((g')^*[A]).mapDerivedCategoryPlus ⋙ (f')_*[A].rightDerivedFunctorPlus) K n q :=
  imageSubobject_truncationCoupleFiltration_le _ K n q

end Abutment

end AlgebraicGeometry
