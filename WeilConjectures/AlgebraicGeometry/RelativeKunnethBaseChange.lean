/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap
import WeilConjectures.AlgebraicGeometry.RelativeKunnethCompositorBaseChange
import WeilConjectures.AlgebraicGeometry.RelativeKunnethInnerBaseChange
import WeilConjectures.AlgebraicGeometry.RelativeKunnethOuterBaseChange

/-! # Pasting the relative compact-support product base-change square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance high] SymmetricCategory.toBraidedCategory

set_option maxHeartbeats 400000 in
-- The full derived comparison word exceeds the default elaboration budget.
/-- The specified relative Künneth word commutes with arbitrary Cartesian base change.
Source: thm-sf-kunneth-relative, base-change clause and proof Step 5.
(blueprint: lem-sf-relative-kunneth-base-change-pasting).

Proof: tensor naturality interchanges the two output exchange factors. The outside
projection/symmetry square moves the second exchange inside the outer pushforward.
Naturality of the projection and symmetry moves the first exchange there too. Naturality
of exchange moves the inner Künneth word through the outer exchange; its base-change
square then replaces that word by the new word and the exterior-product comparison.
The compositor square and its naturality move the latter comparison to the input.
The remaining factors are precisely the new relative Künneth word. -/
theorem relativeKunneth_baseChange_pasting
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B B' X X' Y Y' T T' : Scheme.{u}}
    {f : X ⟶ B} {f' : X' ⟶ B'} {g : Y ⟶ B} {g' : Y' ⟶ B'}
    {p : T ⟶ X} {q : T ⟶ Y} {p' : T' ⟶ X'} {q' : T' ⟶ Y'}
    {a : X' ⟶ X} {b : B' ⟶ B} {c : Y' ⟶ Y} {d : T' ⟶ T}
    {h : T ⟶ B} {h' : T' ⟶ B'} (w : q ≫ g = h) (w' : q' ≫ g' = h')
    [HasCompactification f] [HasCompactification f']
    [HasCompactification g] [HasCompactification g']
    [HasCompactification q] [HasCompactification q']
    [HasCompactification h] [HasCompactification h']
    [QuasiCompact f] [QuasiCompact f'] [QuasiCompact g] [QuasiCompact g']
    [QuasiCompact q] [QuasiCompact q'] [QuasiCompact h] [QuasiCompact h']
    (sq : IsPullback p q f g) (sq' : IsPullback p' q' f' g')
    (sqf : IsPullback a f' f b) (sqg : IsPullback c g' g b)
    (sqq : IsPullback d q' q c) (sqp : CommSq d p' p a)
    (sqh : IsPullback d h' h b)
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    let C := ModuleCat.{u + 1} A
    let K' := (L((a)^*[C])).obj K
    let L' := (L((c)^*[C])).obj L
    let F := (R(f)_![C]).obj K
    let G := (R(g)_![C]).obj L
    let P := (L((p)^*[C])).obj K
    let H := ((derivedTensor C T).obj P).obj ((L((q)^*[C])).obj L)
    let eX := (derivedSquareUpperStarIso C sqp).inv.app K
    let eY := (derivedSquareUpperStarIso C sqq.toCommSq).inv.app L
    let ext := (leftDerivedUpperStarTensorIso C d P ((L((q)^*[C])).obj L)).hom ≫
      ((derivedTensor C T').map eX).app ((L((d)^*[C])).obj ((L((q)^*[C])).obj L)) ≫
      ((derivedTensor C T').obj ((L((p')^*[C])).obj K')).map eY
    (L((b)^*[C])).map (relativeKunnethIsoOfIsPullback A sq h w K L).hom ≫
      (leftDerivedUpperStarTensorIso C b F G).hom ≫
      ((derivedTensor C B').map ((rightDerivedLowerShriekBaseChangeMap A sqf).app K)).app
        ((L((b)^*[C])).obj G) ≫
      ((derivedTensor C B').obj ((R(f')_![C]).obj K')).map
        ((rightDerivedLowerShriekBaseChangeMap A sqg).app L) =
    (rightDerivedLowerShriekBaseChangeMap A sqh).app H ≫
      (R(h')_![C]).map ext ≫
      (relativeKunnethIsoOfIsPullback A sq' h' w' K' L').hom := by
  dsimp only
  have hc := relativeKunneth_compositorOfEq_baseChange A w w' sqq sqg sqh
    (((derivedTensor (ModuleCat.{u + 1} A) T).obj
      ((L((p)^*[ModuleCat.{u + 1} A])).obj K)).obj
        ((L((q)^*[ModuleCat.{u + 1} A])).obj L))
  simp only [rightDerivedLowerShriekCompIsoApp, Iso.app_hom] at hc
  have hi := relativeKunneth_inner_baseChange A sq sq' sqf sqg sqq sqp K L
  have ho := relativeKunneth_outer_baseChange A sqg L
    ((R(f)_![ModuleCat.{u + 1} A]).obj K)
  have hs := ((derivedTensor (ModuleCat.{u + 1} A) B').map
    ((rightDerivedLowerShriekBaseChangeMap A sqf).app K)).naturality
      ((rightDerivedLowerShriekBaseChangeMap A sqg).app L)
  dsimp only at hi
  have hi' := congrArg (fun z ↦ (R(g')_![ModuleCat.{u + 1} A]).map z) hi
  simp only [Functor.map_comp, Category.assoc] at hi' ho
  let e := (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) d
      ((L((p)^*[ModuleCat.{u + 1} A])).obj K)
      ((L((q)^*[ModuleCat.{u + 1} A])).obj L)).hom ≫
    ((derivedTensor (ModuleCat.{u + 1} A) T').map
      ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqp).inv.app K)).app
        ((L((d)^*[ModuleCat.{u + 1} A])).obj
          ((L((q)^*[ModuleCat.{u + 1} A])).obj L)) ≫
    ((derivedTensor (ModuleCat.{u + 1} A) T').obj
      ((L((p')^*[ModuleCat.{u + 1} A])).obj
        ((L((a)^*[ModuleCat.{u + 1} A])).obj K))).map
          ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqq.toCommSq).inv.app L)
  have hn := (rightDerivedLowerShriekCompIsoOfEq A q' g' h' w').hom.naturality e
  simp only [e, Functor.comp_map, Functor.map_comp, Category.assoc] at hn
  simp only [relativeKunnethIsoOfIsPullback, rightDerivedLowerShriekCompIsoApp,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj] at hs hc hi' ho hn ⊢
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [← hs]
  conv_lhs =>
    enter [2, 2]
    rw [reassoc_of% ho]
  simp only [derivedSquareUpperStarIsoInvApp]
  have hb := derivedTensorBraidingIso_hom_naturality_right
    (A := ModuleCat.{u + 1} A) (X := B')
    ((R(g')_![ModuleCat.{u + 1} A]).obj ((L((c)^*[ModuleCat.{u + 1} A])).obj L))
    ((rightDerivedLowerShriekBaseChangeMap A sqf).app K)
  dsimp only [Functor.comp_obj] at hb ⊢
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [← hb]
  have hp := projectionIsoApp_inv_naturality_right A g'
    ((L((c)^*[ModuleCat.{u + 1} A])).obj L)
    ((rightDerivedLowerShriekBaseChangeMap A sqf).app K)
  dsimp only [Functor.comp_obj] at hp ⊢
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [← reassoc_of% hp]
  have hNat := (rightDerivedLowerShriekBaseChangeMap A sqg).naturality
    (relativeKunnethInnerIso A sq K L).hom
  dsimp only [Functor.comp_map, Functor.comp_obj] at hNat
  conv_lhs =>
    enter [2]
    rw [reassoc_of% hNat]
  conv_lhs =>
    enter [2, 2]
    rw [reassoc_of% hi']
  rw [reassoc_of% hc]
  conv_lhs =>
    enter [2]
    rw [← reassoc_of% hn]

end AlgebraicGeometry.Etale
