/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H8
-/
module

public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
public import Sheaf.Paper.ProjectionFactorCoordinates

/-! # Scalar compatibility of the normalized proper/open projection

Source: prop-sf-pf-reduction, proper/open pasting calculation;
Stacks Tags 07A4, 07A6, 0E48 and 0GL1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurCompactSupport

/-- Paste the separate proper and open projection squares.
Source: prop-sf-pf-reduction, pasting paragraph
(blueprint: lem-sf-projection-scalar-square).
Proof: expand the compactification projection and coefficient comparison. Apply
naturality of the proper coefficient map, then the open square, then the proper
square. Naturality of the reduced proper projection recombines the first input. -/
theorem projection_scalar_square
    {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hR : R.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (R.ring Y) (R.ring c.Z) (R.ring X) (R.pull c.g) (R.pull c.i))
    (hS : S.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (S.ring Y) (S.ring c.Z) (S.ring X) (S.pull c.g) (S.pull c.i))
    (aX : ProEtaleTensorModel X (R.ring X))
    (aZ : ProEtaleTensorModel c.Z (R.ring c.Z))
    (aY : ProEtaleTensorModel Y (R.ring Y))
    (bX : ProEtaleTensorModel X (S.ring X))
    (bZ : ProEtaleTensorModel c.Z (S.ring c.Z))
    (bY : ProEtaleTensorModel Y (S.ring Y))
    (K : DerivedCategory (proEtaleRingModules X (R.ring X)))
    (L : DerivedCategory (proEtaleRingModules Y (R.ring Y)))
    (hi : ProjectionFactorIdentities a c hR hS aX aZ aY bX bZ bY K L) :
    (pbcDerivedExtend (a.map Y)).map
        (((projectionMap R c aX aZ aY hR).app K).app L) ≫
      (comparison a c).app (aX.tensor.obj (K, (pull R f).obj L)) ≫
      (image S c).map (mixedChange a f aX bX K L) =
    (scalarTensor (a.map Y) aY bY).hom.app ((image R c).obj K, L) ≫
      bY.tensor.map (Prod.mkHom ((comparison a c).app K) (𝟙 _)) ≫
      ((projectionMap S c bX bZ bY hS).app
        ((pbcDerivedExtend (a.map X)).obj K)).app
        ((pbcDerivedExtend (a.map Y)).obj L) := by
  let M := (openExtension R c.i).mapDerivedCategory.obj K
  let H := aX.tensor.obj (K, (pull R f).obj L)
  let N := aZ.tensor.obj (M, (pull R c.g).obj L)
  let LB := (pbcDerivedExtend (a.map Y)).obj L
  let MB := (pbcDerivedExtend (a.map c.Z)).obj M
  let KB := (pbcDerivedExtend (a.map X)).obj K
  let gamma := (projectionOpenFactor R c aX aZ hR K L).hom
  let pi := ((properProjectionData R c aX aZ aY hR).app M).app L
  let gammaB := (projectionOpenFactor S c bX bZ hS KB LB).hom
  let piB := ((properProjectionData S c bX bZ bY hS).app MB).app LB
  have hp : ((projectionMap R c aX aZ aY hR).app K).app L =
      pi ≫ (push R c.g).map gamma := by
    let data := (projectionComparisons_existsUnique R c aX aZ aY hR).exists.choose
    change pi ≫ (push R c.g).map ((data.openProjection.hom.app K).app L) = _
    rw [data.openProjection_eq]
  have hpB : ((projectionMap S c bX bZ bY hS).app KB).app LB =
      ((properProjectionData S c bX bZ bY hS).app
        ((openExtension S c.i).mapDerivedCategory.obj KB)).app LB ≫
      (push S c.g).map gammaB := by
    let data := (projectionComparisons_existsUnique S c bX bZ bY hS).exists.choose
    change ((properProjectionData S c bX bZ bY hS).app
        ((openExtension S c.i).mapDerivedCategory.obj KB)).app LB ≫
      (push S c.g).map ((data.openProjection.hom.app KB).app LB) = _
    rw [data.openProjection_eq]
  have hn := (properComparison a c.g).naturality gamma
  have ht := hi.1
  have ho := hi.2
  change (pbcDerivedExtend (a.map Y)).map pi ≫
      (properComparison a c.g).app N ≫
      (push S c.g).map (mixedChange a c.g aZ bZ M L) =
    (scalarTensor (a.map Y) aY bY).hom.app ((push R c.g).obj M, L) ≫
      bY.tensor.map (Prod.mkHom ((properComparison a c.g).app M) (𝟙 _)) ≫ piB at ht
  change (pbcDerivedExtend (a.map c.Z)).map gamma ≫
      (openComparison a c.i).app H ≫
      (openExtension S c.i).mapDerivedCategory.map (mixedChange a f aX bX K L) =
    mixedChange a c.g aZ bZ M L ≫
      bZ.tensor.map (Prod.mkHom ((openComparison a c.i).app K) (𝟙 _)) ≫ gammaB at ho
  rw [hp, comparison_factorization, comparison_factorization, hpB]
  change (pbcDerivedExtend (a.map Y)).map
      (pi ≫ (push R c.g).map gamma) ≫
      ((properComparison a c.g).app
          ((openExtension R c.i).mapDerivedCategory.obj H) ≫
        (push S c.g).map ((openComparison a c.i).app H)) ≫
      (push S c.g).map
        ((openExtension S c.i).mapDerivedCategory.map (mixedChange a f aX bX K L)) =
    (scalarTensor (a.map Y) aY bY).hom.app ((push R c.g).obj M, L) ≫
      bY.tensor.map (Prod.mkHom
        ((properComparison a c.g).app M ≫
          (push S c.g).map ((openComparison a c.i).app K)) (𝟙 LB)) ≫
      (((properProjectionData S c bX bZ bY hS).app
        ((openExtension S c.i).mapDerivedCategory.obj KB)).app LB ≫
          (push S c.g).map gammaB)
  change (pbcDerivedExtend (a.map Y)).map ((push R c.g).map gamma) ≫
      (properComparison a c.g).app
        ((openExtension R c.i).mapDerivedCategory.obj H) =
    (properComparison a c.g).app N ≫
      (push S c.g).map ((pbcDerivedExtend (a.map c.Z)).map gamma) at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  rw [← (push S c.g).map_comp_assoc, ← (push S c.g).map_comp]
  simp only [Category.assoc]
  rw [ho]
  simp only [Functor.map_comp]
  rw [reassoc_of% ht]
  have hnB := NatTrans.congr_app
    ((properProjectionData S c bX bZ bY hS).naturality
      ((openComparison a c.i).app K)) LB
  change bY.tensor.map (Prod.mkHom
      ((push S c.g).map ((openComparison a c.i).app K)) (𝟙 LB)) ≫
      ((properProjectionData S c bX bZ bY hS).app
        ((openExtension S c.i).mapDerivedCategory.obj KB)).app LB =
    piB ≫ (push S c.g).map
      (bZ.tensor.map (Prod.mkHom ((openComparison a c.i).app K) (𝟙 _))) at hnB
  erw [← reassoc_of% hnB]
  rw [← bY.tensor.map_comp_assoc]
  rfl

end WeilConjectures.PurCompactSupport
