/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2, Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal

/-!
# The exchange morphism along a commuting cube

Consider a commuting cube of schemes: an original square `g' ≫ f = f' ≫ g` with
`f : X ⟶ S`, `g : T ⟶ S`, a square over `jA : S₀ ⟶ S` restricting `f` to `f₀ : X₀ ⟶ S₀`, a
local square over `g₀ : T₀ ⟶ S₀`, and a square over `jB : T₀ ⟶ T` restricting `f'`, with
`jB ≫ g = g₀ ≫ jA` and `b ≫ g' = p₁ ≫ p₀`. Restricting the source and target of the exchange
morphism `g^* Rf_* ⟶ Rf'_* g'^*` of the original square along `jB` gives maps to the source and
target of the exchange morphism of the local square
(`AlgebraicGeometry.Etale.exchangeCubeSourceComparison`,
`AlgebraicGeometry.Etale.exchangeCubeTargetComparison`); on the degree-`q` homology stalks at
geometric points `t` of `T₀` and `t ≫ jB` of `T`, the two exchange morphisms commute with these
comparisons (`AlgebraicGeometry.Etale.exchangeCube_stalk_square`). This is a formal
consequence of the horizontal pasting law for the derived exchange morphism; no invertibility
is asserted.

## Main definitions

- `AlgebraicGeometry.Etale.derivedStalkComparison`: the map of homology stalks induced by a
  morphism `a^* K ⟶ L` in the bounded below derived category.

## Main statements

- `AlgebraicGeometry.Etale.exchangeCube_stalk_square`: the homology stalk square of the cube.

## References

- Stacks Project, Tags 03Q9 and 095T.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

/-- Apply homology and the inverse-image stalk comparison to a derived morphism:
for `a : Z ⟶ Y`, geometric points `t` of `Z` and `s = t ≫ a` of `Y`, and `m : a^* K ⟶ L`, the
map `ℋ^q(K)_s ≅ (a^* ℋ^q(K))_t ≅ ℋ^q(a^* K)_t ⟶ ℋ^q(L)_t`. -/
noncomputable def derivedStalkComparison
    {Y Z : Scheme.{u}} (a : Z ⟶ Y)
    {k : Type u} [Field k] [IsSepClosed k]
    (t : Spec (.of k) ⟶ Z) (s : Spec (.of k) ⟶ Y) (h : t ≫ a = s)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A))
    (L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A))
    (m : (D+((a)^*[A])).obj K ⟶ L) (q : ℤ) :
    (pointSmallEtale s).sheafFiber.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj K) ⟶
      (pointSmallEtale t).sheafFiber.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj L) := by
  subst s
  exact (upperStarCompSheafFiberIso A a t).inv.app _ ≫
    (pointSmallEtale t).sheafFiber.map
      ((Functor.mapDerivedCategoryPlusHomologyFunctorIso
        ((a)^*[A]) q).hom.app K ≫
        (DerivedCategory.Plus.homologyFunctor _ q).map m)

variable {S T X X' S₀ T₀ X₀ X₁ : Scheme.{u}}
  {g : T ⟶ S} {f : X ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ T}
  {jA : S₀ ⟶ S} {jB : T₀ ⟶ T} {g₀ : T₀ ⟶ S₀}
  {p₀ : X₀ ⟶ X} {f₀ : X₀ ⟶ S₀} {p₁ : X₁ ⟶ X₀} {f₁ : X₁ ⟶ T₀}
  {b : X₁ ⟶ X'}

/-- Restrict the source of exchange: commute the two inverse images, use the
base-change map for `f`, and identify the pulled-back single complex. -/
noncomputable def exchangeCubeSourceComparison
    (sq₀ : CommSq p₀ f₀ f jA) (h : jB ≫ g = g₀ ≫ jA)
    (G : Sheaf X.smallEtaleTopology A) :
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((p₀)^*[A]).obj G)
    (D+((jB)^*[A])).obj
      ((R+((f)_*[A]) ⋙ D+((g)^*[A])).obj K) ⟶
    (R+((f₀)_*[A]) ⋙ D+((g₀)^*[A])).obj K₀ :=
  (upperStarCompDerivedPlus A jB g).inv.app _ ≫
    eqToHom (congrArg (fun a ↦ (D+((a)^*[A])).obj
      ((R+((f)_*[A])).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) h) ≫
    (upperStarCompDerivedPlus A g₀ jA).hom.app _ ≫
    (D+((g₀)^*[A])).map
      ((derivedBaseChangeMapPlus A sq₀).app _ ≫
        (R+((f₀)_*[A])).map
          ((Functor.mapDerivedCategoryPlusSingleFunctor
            ((p₀)^*[A]) 0).hom.app G))

/-- Restrict the target of exchange: use the base-change map for `f'`, then commute
inverse images and identify the pulled-back single complex. -/
noncomputable def exchangeCubeTargetComparison
    (sqB : CommSq b f₁ f' jB) (hb : b ≫ g' = p₁ ≫ p₀)
    (G : Sheaf X.smallEtaleTopology A) :
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((p₀)^*[A]).obj G)
    (D+((jB)^*[A])).obj
      ((D+((g')^*[A]) ⋙ R+((f')_*[A])).obj K) ⟶
    (D+((p₁)^*[A]) ⋙ R+((f₁)_*[A])).obj K₀ :=
  (derivedBaseChangeMapPlus A sqB).app _ ≫
    (R+((f₁)_*[A])).map
      ((upperStarCompDerivedPlus A b g').inv.app _ ≫
        eqToHom (congrArg (fun a ↦ (D+((a)^*[A])).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) hb) ≫
        (upperStarCompDerivedPlus A p₁ p₀).hom.app _ ≫
        (D+((p₁)^*[A])).map
          ((Functor.mapDerivedCategoryPlusSingleFunctor
            ((p₀)^*[A]) 0).hom.app G))

omit [HasSmallSiteSheafify A] in
private theorem derivedExchange_transport
    {S T X Y : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T}
    {a a' : T ⟶ S} {b b' : Y ⟶ X}
    (sq : CommSq b f' f a) (sq' : CommSq b' f' f a')
    (ha : a = a') (hb : b = b')
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    eqToHom (congrArg (fun c ↦ (D+((c)^*[A])).obj
        ((R+((f)_*[A])).obj K)) ha) ≫
      (derivedBaseChangeMapPlus A sq').app K =
    (derivedBaseChangeMapPlus A sq).app K ≫
      (R+((f')_*[A])).map
        (eqToHom (congrArg (fun c ↦ (D+((c)^*[A])).obj K) hb)) := by
  subst a' b'
  simp

/-- The two factorizations of the outer derived mate agree after the
inverse-image composition identifications of the commuting cube.

Proof: form the horizontal composite of `sq` and `sqB`, and the horizontal
composite of `sq₀` and `sq₁`. Apply `derivedBaseChangeMapPlus_paste_horiz` to
each composite at `K`. The outer horizontal maps are identified by `h` and
`hb`, so transport one outer square along these equalities; its commutativity
proof agrees with the other by proof irrelevance. Naturality of the
inverse-image composition isomorphisms transports the resulting mate.
Precompose by the inverse of the composition isomorphism for `jB,g`, and
postcompose by the direct-image of the composition isomorphism for `p₁,p₀`.
Cancel each adjacent hom/inv pair using the isomorphism identities and
functoriality. The displayed equality is the remaining composite. This
argument concerns arbitrary complexes and commuting squares, so it needs
no properness, cartesianness, degree, or stalk assumptions; it also applies
to zero complexes and identity cubes. -/
private theorem derivedExchangeCube_pasting
    (sq : CommSq g' f' f g) (sq₀ : CommSq p₀ f₀ f jA)
    (sq₁ : CommSq p₁ f₁ f₀ g₀) (sqB : CommSq b f₁ f' jB)
    (h : jB ≫ g = g₀ ≫ jA) (hb : b ≫ g' = p₁ ≫ p₀)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (D+((jB)^*[A])).map
        ((derivedBaseChangeMapPlus A sq).app K) ≫
      (derivedBaseChangeMapPlus A sqB).app
        ((D+((g')^*[A])).obj K) ≫
      (R+((f₁)_*[A])).map
        ((upperStarCompDerivedPlus A b g').inv.app K ≫
          eqToHom (congrArg (fun a ↦ (D+((a)^*[A])).obj K) hb) ≫
          (upperStarCompDerivedPlus A p₁ p₀).hom.app K) =
    (upperStarCompDerivedPlus A jB g).inv.app _ ≫
      eqToHom (congrArg (fun a ↦ (D+((a)^*[A])).obj
        ((R+((f)_*[A])).obj K)) h) ≫
      (upperStarCompDerivedPlus A g₀ jA).hom.app _ ≫
      (D+((g₀)^*[A])).map
        ((derivedBaseChangeMapPlus A sq₀).app K) ≫
      (derivedBaseChangeMapPlus A sq₁).app
        ((D+((p₀)^*[A])).obj K) := by
  let outerA : CommSq (b ≫ g') f₁ f (jB ≫ g) := ⟨by
    rw [Category.assoc, sq.w, ← Category.assoc, sqB.w, Category.assoc]⟩
  let outerB : CommSq (p₁ ≫ p₀) f₁ f (g₀ ≫ jA) := ⟨by
    rw [Category.assoc, sq₀.w, ← Category.assoc, sq₁.w, Category.assoc]⟩
  have hpA := NatTrans.congr_app
    (derivedBaseChangeMapPlus_paste_horiz A sq sqB outerA) K
  have hpB := NatTrans.congr_app
    (derivedBaseChangeMapPlus_paste_horiz A sq₀ sq₁ outerB) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
    Category.id_comp] at hpA hpB
  have ht := derivedExchange_transport outerA outerB h hb K
  rw [hpA, hpB] at ht
  have hw := congrArg (fun m ↦
    (upperStarCompDerivedPlus A jB g).inv.app
        ((R+((f)_*[A])).obj K) ≫ m ≫
      (R+((f₁)_*[A])).map
        ((upperStarCompDerivedPlus A p₁ p₀).hom.app K)) ht
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app] at hw
  erw [(R+((f₁)_*[A])).map_id] at hw
  simpa only [Category.comp_id] using hw.symm


omit [HasSmallSiteSheafify A] in
/-- Naturality of the stalk comparison in its target morphism. -/
private theorem derivedStalkComparison_postcomp
    {Y Z : Scheme.{u}} (a : Z ⟶ Y)
    {k : Type u} [Field k] [IsSepClosed k]
    (t : Spec (.of k) ⟶ Z) (s : Spec (.of k) ⟶ Y) (h : t ≫ a = s)
    (K₁ : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A))
    (K₂ K₃ : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A))
    (u : (D+((a)^*[A])).obj K₁ ⟶ K₂) (v : K₂ ⟶ K₃) (q : ℤ) :
    derivedStalkComparison a t s h K₁ K₃ (u ≫ v) q =
      derivedStalkComparison a t s h K₁ K₂ u q ≫
        (pointSmallEtale t).sheafFiber.map
          ((DerivedCategory.Plus.homologyFunctor _ q).map v) := by
  subst s
  simp [derivedStalkComparison, Functor.map_comp, Category.assoc]

omit [HasSmallSiteSheafify A] in
/-- Naturality of the stalk comparison in its source morphism. -/
private theorem derivedStalkComparison_precomp
    {Y Z : Scheme.{u}} (a : Z ⟶ Y)
    {k : Type u} [Field k] [IsSepClosed k]
    (t : Spec (.of k) ⟶ Z) (s : Spec (.of k) ⟶ Y) (h : t ≫ a = s)
    (K₁ K₂ : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A))
    (K₃ : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A))
    (w : K₁ ⟶ K₂) (v : (D+((a)^*[A])).obj K₂ ⟶ K₃) (q : ℤ) :
    (pointSmallEtale s).sheafFiber.map
          ((DerivedCategory.Plus.homologyFunctor _ q).map w) ≫
        derivedStalkComparison a t s h K₂ K₃ v q =
      derivedStalkComparison a t s h K₁ K₃
        (((D+((a)^*[A])).map w) ≫ v) q := by
  subst s
  simp only [derivedStalkComparison, Functor.map_comp]
  rw [← Category.assoc]
  rw [(upperStarCompSheafFiberIso A a t).inv.naturality
    ((DerivedCategory.Plus.homologyFunctor _ q).map w)]
  simp only [Category.assoc]
  change _ ≫ (pointSmallEtale t).sheafFiber.map
      (((a)^*[A]).map
        ((DerivedCategory.Plus.homologyFunctor _ q).map w)) ≫ _ ≫ _ = _
  rw [← Functor.map_comp_assoc]
  have hn := (Functor.mapDerivedCategoryPlusHomologyFunctorIso
    ((a)^*[A]) q).hom.naturality w
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [hn]
  simp [Functor.map_comp, Category.assoc]

/-- Insert the single-complex comparison by naturality of the local mate. -/
private theorem exchangeCube_derived_square
    (sq : CommSq g' f' f g) (sq₀ : CommSq p₀ f₀ f jA)
    (sq₁ : CommSq p₁ f₁ f₀ g₀) (sqB : CommSq b f₁ f' jB)
    (h : jB ≫ g = g₀ ≫ jA) (hb : b ≫ g' = p₁ ≫ p₀)
    (G : Sheaf X.smallEtaleTopology A) :
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((p₀)^*[A]).obj G)
    (D+((jB)^*[A])).map
        ((derivedBaseChangeMapPlus A sq).app K) ≫
      exchangeCubeTargetComparison sqB hb G =
      exchangeCubeSourceComparison sq₀ h G ≫
        (derivedBaseChangeMapPlus A sq₁).app K₀ := by
  dsimp only
  have hp := derivedExchangeCube_pasting sq sq₀ sq₁ sqB h hb
    ((DerivedCategory.Plus.singleFunctor _ 0).obj G)
  have hn := (derivedBaseChangeMapPlus A sq₁).naturality
    ((Functor.mapDerivedCategoryPlusSingleFunctor
      ((p₀)^*[A]) 0).hom.app G)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [exchangeCubeSourceComparison, exchangeCubeTargetComparison,
    Functor.map_comp, Category.assoc]
  simp only [Functor.map_comp] at hp
  rw [hn]
  exact (reassoc_of% hp) _

/-- The exchange square commutes after restriction along a commuting cube and on
homology stalks. This is a compatibility assertion only, with no invertibility claim.
(blueprint: `lem-weil-pbc-abelian-exchange-cube-comparisons`)

Proof: paste the original square with the square over jB, and paste the square over
jA with the local square over g₀. The resulting outer squares have equal horizontal
maps by h and hb. The horizontal pasting law for the derived base-change map gives
the same outer mate from each factorization. Cancel the inverse-image composition
isomorphisms to get the square between the two comparison morphisms above. Naturality
of the inverse-image/single-complex isomorphism inserts the identification of K₀.
Apply H^q, then the point fibre functor. Naturality of the exact inverse-image/homology
isomorphism and of the inverse-image stalk isomorphism identifies the source with the
stalk at s and gives the displayed square. No cartesianness, properness, torsion, or
strict locality is required; the argument also applies to q = 0 and zero sheaves. -/
theorem exchangeCube_stalk_square
    (sq : CommSq g' f' f g) (sq₀ : CommSq p₀ f₀ f jA)
    (sq₁ : CommSq p₁ f₁ f₀ g₀) (sqB : CommSq b f₁ f' jB)
    (h : jB ≫ g = g₀ ≫ jA) (hb : b ≫ g' = p₁ ≫ p₀)
    {k : Type u} [Field k] [IsSepClosed k]
    (t : Spec (.of k) ⟶ T₀) (s : Spec (.of k) ⟶ T) (ht : t ≫ jB = s)
    (G : Sheaf X.smallEtaleTopology A) (q : ℤ) :
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((p₀)^*[A]).obj G)
    let M₁ := (R+((f)_*[A]) ⋙
      D+((g)^*[A])).obj K
    let M₂ := (D+((g')^*[A]) ⋙
      R+((f')_*[A])).obj K
    let N₁ := (R+((f₀)_*[A]) ⋙
      D+((g₀)^*[A])).obj K₀
    let N₂ := (D+((p₁)^*[A]) ⋙
      R+((f₁)_*[A])).obj K₀
    let H := DerivedCategory.Plus.homologyFunctor _ q
    derivedStalkComparison jB t s ht M₁ N₁ (exchangeCubeSourceComparison sq₀ h G) q ≫
        (pointSmallEtale t).sheafFiber.map
          (H.map ((derivedBaseChangeMapPlus A sq₁).app K₀)) =
      (pointSmallEtale s).sheafFiber.map
          ((DerivedCategory.Plus.homologyFunctor _ q).map
            ((derivedBaseChangeMapPlus A sq).app K)) ≫
        derivedStalkComparison jB t s ht M₂ N₂
          (exchangeCubeTargetComparison sqB hb G) q := by
  dsimp only
  rw [← derivedStalkComparison_postcomp, derivedStalkComparison_precomp]
  rw [exchangeCube_derived_square sq sq₀ sq₁ sqB h hb G]

end AlgebraicGeometry.Etale
