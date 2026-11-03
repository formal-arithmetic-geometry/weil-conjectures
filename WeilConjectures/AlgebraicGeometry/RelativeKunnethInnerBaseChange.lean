/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap
import WeilConjectures.AlgebraicGeometry.RelativeKunnethProjectionBaseChange
import all WeilConjectures.AlgebraicGeometry.RelativeKunnethExchangeBaseChange
import all WeilConjectures.AlgebraicGeometry.RelativeKunnethOuterBaseChange

/-! # Base change for the inner relative compact-support product -/

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
-- Pasting three native derived comparisons exceeds the default elaboration budget.
/-- The inverse projection, inverse exchange and symmetry inside the outer pushforward
commute with change of base. Source: thm-sf-kunneth-relative, base-change clause.
(blueprint: lem-sf-relative-kunneth-inner-base-change).

Proof: expand the three-factor inner word. Braided pullback moves the symmetry across
the pullback tensor comparison. Tensor naturality moves the inverse exchange across
that comparison. The exchange cube identifies its composite with the two new exchange
maps and the pullback path comparison. Apply the inverse projection/exchange square,
then its naturality in the first input. Tensor naturality reorders the two input
comparisons into the exterior-product comparison in the statement. -/
theorem relativeKunneth_inner_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B B' X X' Y Y' T T' : Scheme.{u}}
    {f : X ⟶ B} {f' : X' ⟶ B'} {g : Y ⟶ B} {g' : Y' ⟶ B'}
    {p : T ⟶ X} {q : T ⟶ Y} {p' : T' ⟶ X'} {q' : T' ⟶ Y'}
    {a : X' ⟶ X} {b : B' ⟶ B} {c : Y' ⟶ Y} {d : T' ⟶ T}
    [HasCompactification f] [HasCompactification f']
    [HasCompactification q] [HasCompactification q']
    [QuasiCompact f] [QuasiCompact f'] [QuasiCompact q] [QuasiCompact q']
    (sq : IsPullback p q f g) (sq' : IsPullback p' q' f' g')
    (sqf : IsPullback a f' f b) (sqg : IsPullback c g' g b)
    (sqq : IsPullback d q' q c) (sqp : CommSq d p' p a)
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    let C := ModuleCat.{u + 1} A
    let K' := (L((a)^*[C])).obj K
    let L' := (L((c)^*[C])).obj L
    let P := (L((p)^*[C])).obj K
    let F := (R(f)_![C]).obj K
    let eX := (derivedSquareUpperStarIso C sqp).inv.app K
    let eY := (derivedSquareUpperStarIso C sqq.toCommSq).inv.app L
    let eta := (derivedSquareUpperStarIso C sqg.toCommSq).inv.app F ≫
      (L((g')^*[C])).map ((rightDerivedLowerShriekBaseChangeMap A sqf).app K)
    let ext := (leftDerivedUpperStarTensorIso C d P ((L((q)^*[C])).obj L)).hom ≫
      ((derivedTensor C T').map eX).app ((L((d)^*[C])).obj ((L((q)^*[C])).obj L)) ≫
      ((derivedTensor C T').obj ((L((p')^*[C])).obj K')).map eY
    (L((c)^*[C])).map (relativeKunnethInnerIso A sq K L).hom ≫
      (leftDerivedUpperStarTensorIso C c L ((L((g)^*[C])).obj F)).hom ≫
      ((derivedTensor C Y').obj L').map eta =
    (rightDerivedLowerShriekBaseChangeMap A sqq).app
        (((derivedTensor C T).obj P).obj ((L((q)^*[C])).obj L)) ≫
      (R(q')_![C]).map ext ≫ (relativeKunnethInnerIso A sq' K' L').hom := by
  dsimp only
  have he := relativeKunneth_exchange_cube_inv A sq sq' sqf sqg sqq sqp K
  simp only [relativeKunnethInnerIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (kunneth_pull_braiding A c _ _)]
  rw [← derivedTensorBraidingIso_hom_naturality_left_assoc,
    ← derivedTensorBraidingIso_hom_naturality_left]
  have ht := leftDerivedUpperStarTensorIso_hom_naturality_left
    (A := ModuleCat.{u + 1} A) c (rightDerivedLowerShriekBaseChangeIso A sq K).inv L
  conv_lhs =>
    enter [2]
    rw [reassoc_of% ht]
  simp only [← NatTrans.comp_app_assoc, ← Functor.map_comp]
  have heT := congrArg (fun z ↦ ((derivedTensor (ModuleCat.{u + 1} A) Y').map z).app
    ((L((c)^*[ModuleCat.{u + 1} A])).obj L)) he
  conv_lhs =>
    enter [2, 2]
    rw [reassoc_of% heT]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  have hbc := relativeKunneth_projection_inv_baseChange A sqq
    ((L((p)^*[ModuleCat.{u + 1} A])).obj K) L
  rw [reassoc_of% hbc]
  have hp := projectionIsoApp_inv_naturality_left A q'
    ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqp).inv.app K)
    ((L((c)^*[ModuleCat.{u + 1} A])).obj L)
  rw [← reassoc_of% hp]
  have hn := ((derivedTensor (ModuleCat.{u + 1} A) T').map
    ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqp).inv.app K)).naturality
      ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqq.toCommSq).inv.app L)
  have hn' := congrArg (fun z ↦ (R(q')_![ModuleCat.{u + 1} A]).map z) hn
  simp only [Functor.map_comp] at hn'
  dsimp only [derivedSquareUpperStarIsoInvApp]
  conv_lhs =>
    enter [2, 2]
    rw [reassoc_of% hn']
  rfl

end AlgebraicGeometry.Etale
