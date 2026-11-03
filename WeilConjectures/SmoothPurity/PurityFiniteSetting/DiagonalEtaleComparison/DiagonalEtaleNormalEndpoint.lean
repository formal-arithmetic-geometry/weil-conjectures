/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalEtaleFactorization
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionReesMapComposition
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionBaseComparisonLaws
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionEtaleRestriction

/-! # The normal endpoint of the Cartesian-centre span

Source: diagonal-dualizing proof Step 1; orientation-charts proof Steps 2--3.
(blueprint: lem-pur-diagonal-etale-span-normal-endpoint).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.DiagonalEtaleComparison
open SectionRestriction

private def isoSquare {B : Scheme.{u}} {d : ℕ} {X' X : Pair B d}
    (a : EtaleMap X' X) [IsIso a.map] : BaseChange (𝟙 B) X' X :=
  ⟨a.map, IsPullback.of_horiz_isIso ⟨by rw [a.over_eq, Category.comp_id]⟩,
    by rw [a.section_eq, Category.id_comp]⟩

private theorem isoSquare_exchange (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB]
    {d : ℕ} {X' X : Pair B d} (a : EtaleMap X' X) [IsIso a.map] :
    baseComparison P aB aB (isoSquare a) ≪≫ restriction P aB a =
      (ProEtale.leftDerivedUpperStarId
        (ModuleCat.{u + 1} P.Coefficient) B).app (invariant P aB X) := by
  let C := ModuleCat.{u + 1} P.Coefficient
  have hh := restriction_baseComparison P aB aB a (EtaleMap.id X')
    (isoSquare a) (BaseChange.id X') (by simp [EtaleMap.id, isoSquare, BaseChange.id])
  rw [((coherence P).1 B aB d).1 X', baseComparison_id] at hh
  have hn := (ProEtale.leftDerivedUpperStarId C B).hom.naturality
    (restriction P aB a).hom
  have h := congrArg Iso.hom hh
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.refl_hom, Category.comp_id,
    Iso.app_hom] at h
  apply Iso.ext
  apply (cancel_epi ((ProEtale.upperStar C (𝟙 B)).leftDerivedFunctor.map
    (restriction P aB a).hom)).mp
  simp only [Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, h]
  simpa only [Functor.id_map] using hn.symm

private theorem normal_span_map (P : PurityFiniteSetting.{u}) {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ X) [Etale e] (w : e ≫ g = h) (D : CentreSpan d g h e w) :
    SectionRestriction.normalMap P (h ≫ aY) D.left ≫ normalMap d g h e w =
      SectionRestriction.normalMap P (h ≫ aY) D.right ≫
        normalBaseMap P (g ≫ aY) (h ≫ aY) (baseSquare d g e) := by
  let A := diagonalPair d h
  let B := basePair d g e
  let C := diagonalPair d g
  have hgeomA := geometry P (h ≫ aY) D.left
  have hgeomB := geometry P (h ≫ aY) D.right
  have hzero := Scheme.Hom.isPullback_normalConeToDeformationSpace C.g C.s
  let : IsClosedImmersion C.s.ker.normalConeToDeformationSpace :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hzero.flip inferInstance
  have ha := hgeomA.2.2.2.2.2.2.2.2.2.2.2
  have hb := hgeomB.2.2.2.2.2.2.2.2.2.2.2
  have hs : A.s ≫ selfMap d g h e w = e ≫ C.s := by
    apply pullback.hom_ext <;> simp [A, C, diagonalPair, selfMap]
  have hm : D.left.map ≫ selfMap d g h e w =
      D.right.map ≫ (baseSquare d g e).map := by
    rw [← D.factorization]
    simp only [baseSquare, sourceLift, Category.assoc, pullback.lift_fst]
  have hra := rees_pairMap_comp C.s A.s D.pair.s (selfMap d g h e w)
    D.left.map e (𝟙 U) hs
    (D.left.section_eq.trans (Category.id_comp _).symm)
  have hrb := rees_pairMap_comp C.s B.s D.pair.s (baseSquare d g e).map
    D.right.map e (𝟙 U) (baseSquare d g e).section_eq
    (D.right.section_eq.trans (Category.id_comp _).symm)
  have hr : deformationMap D.left ≫ deformation d g h e w =
      deformationMap D.right ≫ reesBaseMap (baseSquare d g e) := by
    change SectionReesBaseChange.pairMap A.s D.pair.s D.left.map (𝟙 U)
          (D.left.section_eq.trans (Category.id_comp _).symm) ≫
        SectionReesBaseChange.pairMap C.s A.s (selfMap d g h e w) e hs =
      SectionReesBaseChange.pairMap B.s D.pair.s D.right.map (𝟙 U)
          (D.right.section_eq.trans (Category.id_comp _).symm) ≫
        SectionReesBaseChange.pairMap C.s B.s (baseSquare d g e).map e (baseSquare d g e).section_eq
    rw [← hra, ← hrb]
    congr 1
  have hact : normalMap d g h e w ≫
      (pullback.diagonal g).ker.normalConeToDeformationSpace =
        (pullback.diagonal h).ker.normalConeToDeformationSpace ≫ deformation d g h e w :=
    (Scheme.Hom.isPullback_normalConeToDeformationSpace
      (pullback.fst g g) (pullback.diagonal g)).lift_fst _ _ _
  have hbase : normalBaseMap P (g ≫ aY) (h ≫ aY) (baseSquare d g e) ≫
      C.s.ker.normalConeToDeformationSpace =
        B.s.ker.normalConeToDeformationSpace ≫ reesBaseMap (baseSquare d g e) :=
    hzero.lift_fst _ _ _
  apply (cancel_mono C.s.ker.normalConeToDeformationSpace).mp
  calc
    _ = SectionRestriction.normalMap P (h ≫ aY) D.left ≫
        ((pullback.diagonal h).ker.normalConeToDeformationSpace ≫
          deformation d g h e w) := by
      simpa only [Category.assoc, C, diagonalPair] using
        congrArg (fun q ↦ SectionRestriction.normalMap P (h ≫ aY) D.left ≫ q) hact
    _ = D.pair.s.ker.normalConeToDeformationSpace ≫
        (deformationMap D.left ≫ deformation d g h e w) := by
      simpa only [Category.assoc, C, diagonalPair] using
        congrArg (fun q ↦ q ≫ deformation d g h e w) ha.symm
    _ = D.pair.s.ker.normalConeToDeformationSpace ≫
        (deformationMap D.right ≫ reesBaseMap (baseSquare d g e)) :=
      congrArg (fun q ↦ D.pair.s.ker.normalConeToDeformationSpace ≫ q) hr
    _ = SectionRestriction.normalMap P (h ≫ aY) D.right ≫
        (B.s.ker.normalConeToDeformationSpace ≫ reesBaseMap (baseSquare d g e)) := by
      simpa only [Category.assoc, C, diagonalPair] using
        congrArg (fun q ↦ q ≫ reesBaseMap (baseSquare d g e)) hb
    _ = _ := by
      simpa only [Category.assoc, C, diagonalPair] using
        congrArg (fun q ↦ SectionRestriction.normalMap P (h ≫ aY) D.right ≫ q)
          hbase.symm

/-- The normal endpoint is inverse smooth exchange along the actual Rees normal map.
No deformation comparison or Tate orientation occurs in this statement.
Source: diagonal-dualizing Step 1; orientation-charts Steps 2--3.

Proof: the normal maps of D.left and D.right are isomorphisms over U, because the
centre squares are Cartesian and the maps are etale. On Rees algebras all maps fix t
and send a/t to its pullback divided by t. Apply this formula to D.factorization;
after restriction to zero it identifies normal(left) followed by the specified
normalMap with normal(right) followed by the normal base-change map. Equality is
checked after the closed zero-fibre inclusion, which is monic. Replace the two
normal restrictions by inverse smooth section exchange for these isomorphisms;
the counit normalization identifies these maps without a scalar. Paste the three
Cartesian normal squares. Smooth exchange composition and the coefficient-unit
and site-comparison composition equations cancel the two intermediate normal
objects and yield precisely the inverse exchange defining normal. This argument
uses neither positive rank nor a nonempty base.
(blueprint: lem-pur-diagonal-etale-span-normal-endpoint). -/
theorem span_normal_endpoint (P : PurityFiniteSetting.{u}) {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated (h ≫ aY)]
    (e : U ⟶ X) [Etale e] (w : e ≫ g = h)
    (D : CentreSpan d g h e w) :
    (restriction P (h ≫ aY) (normalEtaleMap P (h ≫ aY) D.left)).symm ≪≫
        restriction P (h ≫ aY) (normalEtaleMap P (h ≫ aY) D.right) ≪≫
        (baseComparison P (g ≫ aY) (h ≫ aY)
          (normalBaseChange P (g ≫ aY) (h ≫ aY) (baseSquare d g e))).symm =
      normal P d g h aY e w := by
  let aU := h ≫ aY
  let aX := g ≫ aY
  let A := normalPair P aU (diagonalPair d h)
  let B := normalPair P aU (basePair d g e)
  let C := normalPair P aX (diagonalPair d g)
  let a := normalEtaleMap P aU D.left
  let b := normalEtaleMap P aU D.right
  let : IsIso a.map := (geometry P aU D.left).2.2.2.2.2.2.1
  let : IsIso b.map := (geometry P aU D.right).2.2.2.2.2.2.1
  let sqN : BaseChange e A C :=
    ⟨normalMap d g h e w, (normalGeometry d g h e w).1,
      (normalGeometry d g h e w).2⟩
  let sqC := normalBaseChange P aX aU (baseSquare d g e)
  have heq : baseComparison P aX aU ((isoSquare a).comp sqN) =
      baseComparison P aX aU ((isoSquare b).comp sqC) := by
    have hh := baseComparison_congr P aX aU ((isoSquare a).comp sqN)
      ((isoSquare b).comp sqC) rfl (normal_span_map P d g h aY e w D)
    rw [ProEtale.leftDerivedUpperStarCongr_rfl] at hh
    change _ = Iso.refl _ ≪≫ _ at hh
    simpa only [Iso.refl_trans] using hh
  rw [baseComparison_comp P aX aU aU sqN (isoSquare a),
    baseComparison_comp P aX aU aU sqC (isoSquare b)] at heq
  let R := restriction P aU a
  let S := restriction P aU b
  let EN := baseComparison P aX aU sqN
  let EC := baseComparison P aX aU sqC
  let EA := baseComparison P aU aU (isoSquare a)
  let EB := baseComparison P aU aU (isoSquare b)
  let M := ModuleCat.{u + 1} P.Coefficient
  let F := (ProEtale.upperStar M (𝟙 U)).leftDerivedFunctor
  let I := ProEtale.leftDerivedUpperStarId M U
  have hA : EA.hom = I.hom.app (invariant P aU A) ≫ R.inv := by
    apply R.eq_comp_inv.mpr
    exact congrArg Iso.hom (isoSquare_exchange P aU a)
  have hB : EB.hom = I.hom.app (invariant P aU B) ≫ S.inv := by
    apply S.eq_comp_inv.mpr
    exact congrArg Iso.hom (isoSquare_exchange P aU b)
  have hh : F.map EN.hom ≫ EA.hom = F.map EC.hom ≫ EB.hom := by
    apply (cancel_epi ((ProEtale.leftDerivedUpperStarComp M (𝟙 U) e).hom.app
      (invariant P aX (normalPair P aX (diagonalPair d g))))).mp
    exact congrArg Iso.hom heq
  rw [hA, hB, ← Category.assoc, ← Category.assoc,
    I.hom.naturality EN.hom, I.hom.naturality EC.hom] at hh
  have hh' : EN.hom ≫ R.inv = EC.hom ≫ S.inv := by
    apply (cancel_epi (I.hom.app
      ((OrientationRefinement.pull P e).obj (invariant P aX C)))).mp
    simpa only [Category.assoc, Functor.id_map] using hh
  have hn : EN.symm = normal P d g h aY e w := by
    simp only [EN, sqN, baseComparison, normal, Iso.trans_symm,
      Functor.mapIso_symm, Iso.symm_symm_eq, Iso.trans_assoc]
    rfl
  rw [← hn]
  change R.symm ≪≫ S ≪≫ EC.symm = EN.symm
  apply Iso.ext
  apply (cancel_epi EN.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id]
  rw [← Category.assoc, ← Category.assoc, hh']
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]

end WeilConjectures.PurityFiniteSetting.DiagonalEtaleComparison
