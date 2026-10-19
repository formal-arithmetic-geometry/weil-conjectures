/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageColimits
import Sheaf.Paper.KunBcMapOnCohomology
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact

/-!
# Higher direct images along limits of cartesian squares

Source: Stacks Project, Tag 0EZT, second assertion, and Tag 0EYM
(blueprint: lem-kun-0ezt).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A compatible inverse system of cartesian squares preserves a degreewise étale
base-change isomorphism on passing to its limit.

Source: Stacks Project, Tag 0EZT, second assertion (blueprint: lem-kun-0ezt).
The maps `φ` satisfy the identity and composition laws on the varying sites. The
isomorphisms `ιF` identify the forward diagram `D` with the pullbacks of these sheaves;
`hD` requires precisely the transition maps induced by `φ` and the cone projections.

Proof:
1. The limit square is Cartesian by the four limit universal properties. Each `hᵢ` is
   quasi-compact and quasi-separated by base change of `gᵢ`
   (lem-weil-pbc-qcqs-morphism-permanence). Inverse-image composition and preservation
   of colimits identify `e⁻¹F` with the colimit of the pullbacks of `eᵢ⁻¹Fᵢ`
   (lem-weil-pbc-derived-inverse-image-composition,
   lem-weil-pbc-inverse-image-preserves-colimits).
2. Apply Tag 0EYM (lem-kun-0eym) to `gᵢ` and then pull back by `f`. This identifies
   `f⁻¹Rᵠg_*F` with the colimit of the pulled-back stage source sheaves.
3. Apply Tag 0EYM to `hᵢ` and `eᵢ⁻¹Fᵢ`. This identifies `Rᵠh_*e⁻¹F` with the colimit
   of the pulled-back stage target sheaves.
4. The stage exchange maps commute with the transition maps and with the two continuity
   legs. On bounded below derived categories this is mate pasting for the transition
   and projection squares (lem-weil-pbc-mate-pasting, def-weil-pbc-derived-exchange).
   Associativity of inverse-image composition identifies the two pasted square maps;
   naturality moves each coefficient transition or colimit leg through exchange.
   Take degree-`q` cohomology using exact inverse image, its cohomology comparison,
   and lem-kun-bc-map-on-cohomology (prop-weil-pbc-inverse-image-exact,
   lem-weil-pbc-exact-functor-complex-cohomology).
5. The stage isomorphisms and their inverses therefore form diagram morphisms. The
   colimit universal property (def-weil-pbc-category-colimit) gives inverse maps on
   colimits. The leg equations in step 4 identify the limit exchange with this
   isomorphism conjugated by the two continuity isomorphisms from steps 2 and 3.
-/
theorem higherDirectImage_baseChange_of_limit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (DX DY DS DT : Iᵒᵖ ⥤ Scheme.{u})
    (cX : Cone DX) (hcX : IsLimit cX)
    (cY : Cone DY) (hcY : IsLimit cY)
    (cS : Cone DS) (hcS : IsLimit cS)
    (cT : Cone DT) (hcT : IsLimit cT)
    (ηf : DX ⟶ DS) (ηe : DY ⟶ DT) (ηg : DT ⟶ DS) (ηh : DY ⟶ DX)
    (f : cX.pt ⟶ cS.pt) (e : cY.pt ⟶ cT.pt)
    (g : cT.pt ⟶ cS.pt) (h : cY.pt ⟶ cX.pt)
    (hf : ∀ i : Iᵒᵖ, cX.π.app i ≫ ηf.app i = f ≫ cS.π.app i)
    (he : ∀ i : Iᵒᵖ, cY.π.app i ≫ ηe.app i = e ≫ cT.π.app i)
    (hg : ∀ i : Iᵒᵖ, cT.π.app i ≫ ηg.app i = g ≫ cS.π.app i)
    (hh : ∀ i : Iᵒᵖ, cY.π.app i ≫ ηh.app i = h ≫ cX.π.app i)
    (sq : ChosenCartesianSquare e h g f)
    (sqi : ∀ i : Iᵒᵖ,
      ChosenCartesianSquare (ηe.app i) (ηh.app i) (ηg.app i) (ηf.app i))
    [∀ i : Iᵒᵖ, QuasiCompact (ηg.app i)] [∀ i : Iᵒᵖ, QuasiSeparated (ηg.app i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DY.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DT.map a)]
    (Fi : ∀ i : Iᵒᵖ,
      Sheaf (DT.obj i).smallEtaleTopology AddCommGrpCat.{u + 1})
    (torsionFi : ∀ i : Iᵒᵖ, CategoryTheory.Sheaf.IsTorsion (Fi i))
    (φ : ∀ {i j : I} (a : i ⟶ j),
      (Etale.upperStar AddCommGrpCat.{u + 1} (DT.map a.op)).obj (Fi (op i)) ⟶ Fi (op j))
    (hφid : ∀ i : I,
      φ (𝟙 i) = eqToHom (congrArg
        (fun a : DT.obj (op i) ⟶ DT.obj (op i) ↦
          (Etale.upperStar AddCommGrpCat.{u + 1} a).obj (Fi (op i)))
        (DT.map_id (op i))) ≫
        (Etale.upperStarId AddCommGrpCat.{u + 1} (DT.obj (op i))).hom.app (Fi (op i)))
    (hφcomp : ∀ {i j k : I} (a : i ⟶ j) (b : j ⟶ k),
      φ (a ≫ b) = (Etale.upperStarComp AddCommGrpCat.{u + 1}
        (DT.map b.op) (DT.map a.op) (DT.map (a ≫ b).op)
        (DT.map_comp b.op a.op)).hom.app (Fi (op i)) ≫
        (Etale.upperStar AddCommGrpCat.{u + 1} (DT.map b.op)).map (φ a) ≫ φ b)
    (D : I ⥤ Sheaf cT.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (ιF : ∀ i : I, D.obj i ≅
      (Etale.upperStar AddCommGrpCat.{u + 1} (cT.π.app (op i))).obj (Fi (op i)))
    (hD : ∀ {i j : I} (a : i ⟶ j),
      D.map a ≫ (ιF j).hom = (ιF i).hom ≫
        (Etale.upperStarComp AddCommGrpCat.{u + 1} (cT.π.app (op j))
          (DT.map a.op) (cT.π.app (op i)) (cT.w a.op).symm).hom.app (Fi (op i)) ≫
        (Etale.upperStar AddCommGrpCat.{u + 1} (cT.π.app (op j))).map (φ a))
    (cF : Cocone D) (hcF : IsColimit cF)
    (q : ℕ)
    (hbase : ∀ i : Iᵒᵖ, IsIso ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (DX.obj i).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        (sqi i).toCommSq).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf (DT.obj i).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
          (Fi i))))) :
    IsIso ((DerivedCategory.Plus.homologyFunctor
      (Sheaf cX.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf cT.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj cF.pt))) := by
  sorry

end AlgebraicGeometry
