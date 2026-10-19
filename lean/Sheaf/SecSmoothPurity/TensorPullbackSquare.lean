/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized
public import Sheaf.AlgebraicGeometry.OpenImmersionSquare
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.FourCorners
public import Sheaf.Paper.StratumScalarExtension
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Sheaf.SecSmoothPurity.OrdinaryRestrictionPullbackSquare

/-! Normalization data for the scalar/open exchange argument. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

local notation "CR" => Scheme.proEtaleConstantRing
local notation "PB" => Scheme.proEtaleConstantRingDerivedPullback
local notation "AD" => Scheme.proEtaleRingDerivedOpenAdjunction
local notation "CC" => Scheme.proEtaleConstantRingComparison
local notation "OE" => Scheme.proEtaleRingDerivedOpenExtension

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mateCube
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    {S₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {S₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
    {S₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂} {S₃ : C₃ ⥤ D₃} {R₃ : D₃ ⥤ C₃}
    (a₀ : S₀ ⊣ R₀) (a₁ : S₁ ⊣ R₁) (a₂ : S₂ ⊣ R₂) (a₃ : S₃ ⊣ R₃)
    {J : C₀ ⥤ C₁} {H : C₁ ⥤ C₃} {G : C₀ ⥤ C₂} {I : C₂ ⥤ C₃}
    {J' : D₀ ⥤ D₁} {H' : D₁ ⥤ D₃} {G' : D₀ ⥤ D₂} {I' : D₂ ⥤ D₃}
    (qJ : R₀ ⋙ J ⟶ J' ⋙ R₁) (qH : R₁ ⋙ H ⟶ H' ⋙ R₃)
    (qG : R₀ ⋙ G ⟶ G' ⋙ R₂) (qI : R₂ ⋙ I ⟶ I' ⋙ R₃)
    (c : J ⋙ H ⟶ G ⋙ I) (d : J' ⋙ H' ⟶ G' ⋙ I')
    (hc : ∀ M, c.app (R₀.obj M) ≫ I.map (qG.app M) ≫ qI.app (G'.obj M) =
      H.map (qJ.app M) ≫ qH.app (J'.obj M) ≫ R₃.map (d.app M))
    (N : C₀) :
    S₃.map (c.app N) ≫
        ((mateEquiv a₂ a₃).symm (TwoSquare.mk _ _ _ _ qI)).app (G.obj N) ≫
        I'.map (((mateEquiv a₀ a₂).symm (TwoSquare.mk _ _ _ _ qG)).app N) =
      ((mateEquiv a₁ a₃).symm (TwoSquare.mk _ _ _ _ qH)).app (J.obj N) ≫
        H'.map (((mateEquiv a₀ a₁).symm (TwoSquare.mk _ _ _ _ qJ)).app N) ≫
        d.app (S₀.obj N) := by
  let lJ := ((mateEquiv a₀ a₁).symm (TwoSquare.mk _ _ _ _ qJ)).natTrans
  let lH := ((mateEquiv a₁ a₃).symm (TwoSquare.mk _ _ _ _ qH)).natTrans
  let lG := ((mateEquiv a₀ a₂).symm (TwoSquare.mk _ _ _ _ qG)).natTrans
  let lI := ((mateEquiv a₂ a₃).symm (TwoSquare.mk _ _ _ _ qI)).natTrans
  have hj (K : C₀) : J.map (a₀.unit.app K) ≫ qJ.app (S₀.obj K) =
      a₁.unit.app (J.obj K) ≫ R₁.map (lJ.app K) :=
    unit_mateEquiv_symm a₀ a₁ (TwoSquare.mk _ _ _ _ qJ) K
  have hh (K : C₁) : H.map (a₁.unit.app K) ≫ qH.app (S₁.obj K) =
      a₃.unit.app (H.obj K) ≫ R₃.map (lH.app K) :=
    unit_mateEquiv_symm a₁ a₃ (TwoSquare.mk _ _ _ _ qH) K
  have hg (K : C₀) : G.map (a₀.unit.app K) ≫ qG.app (S₀.obj K) =
      a₂.unit.app (G.obj K) ≫ R₂.map (lG.app K) :=
    unit_mateEquiv_symm a₀ a₂ (TwoSquare.mk _ _ _ _ qG) K
  have hi (K : C₂) : I.map (a₂.unit.app K) ≫ qI.app (S₂.obj K) =
      a₃.unit.app (I.obj K) ≫ R₃.map (lI.app K) :=
    unit_mateEquiv_symm a₂ a₃ (TwoSquare.mk _ _ _ _ qI) K
  change S₃.map (c.app N) ≫ lI.app (G.obj N) ≫ I'.map (lG.app N) =
    lH.app (J.obj N) ≫ H'.map (lJ.app N) ≫ d.app (S₀.obj N)
  apply (a₃.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_obj]
  have hn := a₃.unit.naturality (c.app N)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn, ← reassoc_of% (hi (G.obj N))]
  have hq := qI.naturality (lG.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hq
  rw [← hq, ← I.map_comp_assoc, ← hg, I.map_comp]
  have hcn := c.naturality (a₀.unit.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hcn
  simp only [Category.assoc, Functor.id_obj] at hcn ⊢
  rw [← reassoc_of% hcn, hc]
  rw [← reassoc_of% (hh (J.obj N))]
  have hqn := qH.naturality (lJ.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hqn
  rw [← reassoc_of% hqn, ← H.map_comp_assoc, hj]
  simp only [Functor.map_comp, Category.assoc]

section ExactCoherence
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  [Abelian C] [Abelian D] [Abelian E] [Abelian F]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasDerivedCategory F]
  (L : C ⥤ D) (M : D ⥤ E) (N : E ⥤ F)
  [L.Additive] [M.Additive] [N.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits M] [PreservesFiniteColimits M]
  [PreservesFiniteLimits N] [PreservesFiniteColimits N]

private noncomputable abbrev tripleComparison :
    (L ⋙ M ⋙ N).mapDerivedCategory ≅
      L.mapDerivedCategory ⋙ M.mapDerivedCategory ⋙ N.mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso (L ⋙ M) N ≪≫
    isoWhiskerRight (Functor.mapDerivedCategoryCompIso L M) N.mapDerivedCategory

private lemma tripleComparison_hom :
    (tripleComparison L M N).hom =
      (Functor.mapDerivedCategoryCompIso L (M ⋙ N)).hom ≫
        Functor.whiskerLeft L.mapDerivedCategory (Functor.mapDerivedCategoryCompIso M N).hom :=
  (Functor.mapDerivedCategoryCompIso_assoc L M N).symm

variable {L M N}
  {D' : Type*} [Category D'] [Abelian D'] [HasDerivedCategory D']
  {L' : C ⥤ D'} {M' : D' ⥤ E}
  [L'.Additive] [M'.Additive]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits M'] [PreservesFiniteColimits M']

private lemma tripleComparison_right (e : L ⋙ M ≅ L' ⋙ M') :
    (tripleComparison L M N).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategorySquareIso e).hom
          N.mapDerivedCategory =
      (Functor.mapDerivedCategoryNatIso (isoWhiskerRight e N)).hom ≫
        (tripleComparison L' M' N).hom := by
  dsimp only [tripleComparison, Functor.mapDerivedCategorySquareIso]
  simp only [Iso.trans_hom, Iso.symm_hom,
    isoWhiskerRight_hom, Functor.whiskerRight_comp, Category.assoc]
  rw [← reassoc_of% (Functor.whiskerRight_comp
    (Functor.mapDerivedCategoryCompIso L M).hom
    (Functor.mapDerivedCategoryCompIso L M).inv N.mapDerivedCategory), Iso.hom_inv_id]
  simp only [Functor.whiskerRight_id', Category.id_comp]
  rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerRight e N)]

variable {E' : Type*} [Category E'] [Abelian E'] [HasDerivedCategory E']
  {M'' : D ⥤ E'} {N' : E' ⥤ F}
  [M''.Additive] [N'.Additive]
  [PreservesFiniteLimits M''] [PreservesFiniteColimits M'']
  [PreservesFiniteLimits N'] [PreservesFiniteColimits N']

private lemma tripleComparison_left (e : M ⋙ N ≅ M'' ⋙ N') :
    (tripleComparison L M N).hom ≫
        Functor.whiskerLeft L.mapDerivedCategory
          (Functor.mapDerivedCategorySquareIso e).hom =
      (Functor.mapDerivedCategoryNatIso (isoWhiskerLeft L e)).hom ≫
        (tripleComparison L M'' N').hom := by
  rw [tripleComparison_hom, tripleComparison_hom]
  dsimp only [Functor.mapDerivedCategorySquareIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.whiskerLeft_comp, Category.assoc]
  rw [← reassoc_of% (Functor.whiskerLeft_comp L.mapDerivedCategory
    (Functor.mapDerivedCategoryCompIso M N).hom
    (Functor.mapDerivedCategoryCompIso M N).inv), Iso.hom_inv_id]
  simp only [Functor.whiskerLeft_id', Category.id_comp]
  rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft L e)]

end ExactCoherence

section DerivedCube
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
  [Category C₀] [Category C₁] [Category C₂] [Category C₃]
  [Category D₀] [Category D₁] [Category D₂] [Category D₃]
  [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
  [Abelian D₀] [Abelian D₁] [Abelian D₂] [Abelian D₃]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁]
  [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁]
  [HasDerivedCategory D₂] [HasDerivedCategory D₃]
  {R₀ : D₀ ⥤ C₀} {R₁ : D₁ ⥤ C₁} {R₂ : D₂ ⥤ C₂} {R₃ : D₃ ⥤ C₃}
  {J : C₀ ⥤ C₁} {H : C₁ ⥤ C₃} {G : C₀ ⥤ C₂} {I : C₂ ⥤ C₃}
  {J' : D₀ ⥤ D₁} {H' : D₁ ⥤ D₃} {G' : D₀ ⥤ D₂} {I' : D₂ ⥤ D₃}
  [R₀.Additive] [R₁.Additive] [R₂.Additive] [R₃.Additive]
  [J.Additive] [H.Additive] [G.Additive] [I.Additive]
  [J'.Additive] [H'.Additive] [G'.Additive] [I'.Additive]
  [PreservesFiniteLimits R₀] [PreservesFiniteColimits R₀]
  [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  [PreservesFiniteLimits R₃] [PreservesFiniteColimits R₃]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
  [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
  [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits I'] [PreservesFiniteColimits I']

private lemma derivedCube
    (qJ : R₀ ⋙ J ≅ J' ⋙ R₁) (qH : R₁ ⋙ H ≅ H' ⋙ R₃)
    (qG : R₀ ⋙ G ≅ G' ⋙ R₂) (qI : R₂ ⋙ I ≅ I' ⋙ R₃)
    (c : J ⋙ H ≅ G ⋙ I) (d : J' ⋙ H' ≅ G' ⋙ I')
    (hc : ∀ M, c.hom.app (R₀.obj M) ≫ I.map (qG.hom.app M) ≫ qI.hom.app (G'.obj M) =
      H.map (qJ.hom.app M) ≫ qH.hom.app (J'.obj M) ≫ R₃.map (d.hom.app M))
    (M : DerivedCategory D₀) :
    (Functor.mapDerivedCategorySquareIso c).hom.app (R₀.mapDerivedCategory.obj M) ≫
        I.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso qG).hom.app M) ≫
        (Functor.mapDerivedCategorySquareIso qI).hom.app (G'.mapDerivedCategory.obj M) =
      H.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso qJ).hom.app M) ≫
        (Functor.mapDerivedCategorySquareIso qH).hom.app (J'.mapDerivedCategory.obj M) ≫
        R₃.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso d).hom.app M) := by
  let pL := isoWhiskerLeft R₀ c ≪≫ isoWhiskerRight qG I ≪≫ isoWhiskerLeft G' qI
  let pR := isoWhiskerRight qJ H ≪≫ isoWhiskerLeft J' qH ≪≫ isoWhiskerRight d R₃
  have hp : pL = pR := by
    apply Iso.ext
    ext K
    exact hc K
  have hL : (tripleComparison R₀ J H).hom ≫
      Functor.whiskerLeft R₀.mapDerivedCategory
        (Functor.mapDerivedCategorySquareIso c).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso qG).hom
        I.mapDerivedCategory ≫
      Functor.whiskerLeft G'.mapDerivedCategory
        (Functor.mapDerivedCategorySquareIso qI).hom =
      (Functor.mapDerivedCategoryNatIso pL).hom ≫ (tripleComparison G' I' R₃).hom := by
    rw [reassoc_of% (tripleComparison_left c),
      reassoc_of% (tripleComparison_right qG), tripleComparison_left qI]
    simp only [pL, Functor.mapDerivedCategoryNatIso_trans, Category.assoc]
  have hR : (tripleComparison R₀ J H).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso qJ).hom
        H.mapDerivedCategory ≫
      Functor.whiskerLeft J'.mapDerivedCategory
        (Functor.mapDerivedCategorySquareIso qH).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso d).hom
        R₃.mapDerivedCategory =
      (Functor.mapDerivedCategoryNatIso pR).hom ≫ (tripleComparison G' I' R₃).hom := by
    rw [reassoc_of% (tripleComparison_right qJ),
      reassoc_of% (tripleComparison_left qH), tripleComparison_right d]
    simp only [pR, Functor.mapDerivedCategoryNatIso_trans, Category.assoc]
  have h := hL.trans ((congrArg (fun p ↦
    (Functor.mapDerivedCategoryNatIso p).hom ≫ (tripleComparison G' I' R₃).hom) hp).trans hR.symm)
  have h' := (cancel_epi (tripleComparison R₀ J H).hom).1 h
  exact congr_app h' M

end DerivedCube

/-- The tensor/pullback comparisons commute around a square, with its specified
inverse-image compositor. This involves no open extension and no base-change mate.
Source: Stacks Tags 07A4 and 0G7E; the tensor composition calculation in
`lem-fix-open-scalar-exchange`, proof step 2.
(blueprint: lem-fix-tensor-pullback-square)
Proof: ordinary restriction of scalars commutes with the specified pullback-square
compositor, by ordinaryRestrictionPullbackSquare. Exact derived-functor composition
coherence transports this ordinary cube through localization: the triple-comparison
associativity and whiskering identities identify both descended pastings. Apply the
four scalar extension/restriction adjunctions to this derived cube. Injectivity of the
last scalar Hom equivalence, the four mate-unit identities, and naturality give the
same cube for the left mates. By the definition of proEtaleReductionPullbackIso,
these left mates are the inverse tensor comparisons in the statement. The argument
includes empty schemes and zero coefficient rings and uses no flatness of B over A. -/
theorem tensorPullbackSquare {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B)
    {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    (N : DerivedCategory (Scheme.proEtaleRingModules X (CR X A))) :
    let S (T : Scheme.{u}) := Scheme.proEtaleRingDerivedExtension
      (Scheme.proEtaleConstantRingMap (T := T) φ)
    let c (R : Type u) [CommRing R] := Functor.mapDerivedCategorySquareIso
      (StrictTower.moduleSquareG (ULift.{u + 1, u} R) gU j' j g sq.toCommSq.w)
    let lam {V W : Scheme.{u}} (f : V ⟶ W) :=
      Scheme.proEtaleReductionPullbackIso f (CR W A) (CR W B) (CR V A) (CR V B)
        (Scheme.proEtaleConstantRingMap (T := W) φ)
        (Scheme.proEtaleConstantRingMap (T := V) φ) (CC f A) (CC f B) (by
          simpa [Scheme.proEtaleConstantRingComparison, Scheme.proEtaleConstantRingMap] using
            (Scheme.proEtaleConstantInverseImageMap_naturality f
              (a := CommRingCat.ofHom (RingHom.ulift φ))).symm)
    (S U').map ((c A).inv.app N) ≫
      (lam j').inv.app ((PB A g).obj N) ≫ (PB B j').map ((lam g).inv.app N) =
    (lam gU).inv.app ((PB A j).obj N) ≫
      (PB B gU).map ((lam j).inv.app N) ≫ (c B).inv.app ((S X).obj N) := by
  let R (T : Scheme.{u}) := Scheme.proEtaleRingRestrictScalars
    (Scheme.proEtaleConstantRingMap (T := T) φ)
  let P (R : Type u) [CommRing R] {V W : Scheme.{u}} (f : V ⟶ W) :=
    StrictTower.modulePullback (ULift.{u + 1, u} R) f
  let c (R : Type u) [CommRing R] :=
    StrictTower.moduleSquareG (ULift.{u + 1, u} R) gU j' j g sq.toCommSq.w
  let q {V W : Scheme.{u}} (f : V ⟶ W) :=
    Scheme.proEtaleRingRestrictionPullbackInv f
      (CR W A) (CR W B) (CR V A) (CR V B)
      (Scheme.proEtaleConstantRingMap (T := W) φ)
      (Scheme.proEtaleConstantRingMap (T := V) φ) (CC f A) (CC f B) (by
        simpa [Scheme.proEtaleConstantRingComparison, Scheme.proEtaleConstantRingMap] using
          (Scheme.proEtaleConstantInverseImageMap_naturality f
            (a := CommRingCat.ofHom (RingHom.ulift φ))).symm)
  have hq {V W : Scheme.{u}} (f : V ⟶ W) : IsIso (q f) :=
    Scheme.proEtaleRingRestrictionPullbackInv_isIso _ _ _ _ _ _ _ _ _ _
  let qi {V W : Scheme.{u}} (f : V ⟶ W) := @asIso _ _ _ _ (q f) (hq f)
  have hc (M : DerivedCategory (Scheme.proEtaleRingModules X (CR X B))) :=
    derivedCube (qi j) (qi gU) (qi g) (qi j') (c A).symm (c B).symm
      (ordinaryRestrictionPullbackSquare φ gU j' j g sq) M
  let adj (T : Scheme.{u}) := Scheme.proEtaleRingDerivedExtensionAdjunction
    (Scheme.proEtaleConstantRingMap (T := T) φ)
  have hm := mateCube (adj X) (adj U) (adj X') (adj U')
    (Functor.mapDerivedCategorySquareIso (qi j)).hom
    (Functor.mapDerivedCategorySquareIso (qi gU)).hom
    (Functor.mapDerivedCategorySquareIso (qi g)).hom
    (Functor.mapDerivedCategorySquareIso (qi j')).hom
    (Functor.mapDerivedCategorySquareIso (c A).symm).hom
    (Functor.mapDerivedCategorySquareIso (c B).symm).hom hc N
  simpa only [Scheme.proEtaleReductionPullbackIso, Scheme.proEtaleReductionPullbackInv,
    Scheme.proEtaleRingRestrictionDerivedPullback, Functor.mapDerivedCategorySquareIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    ← Functor.mapDerivedCategoryNatIso_symm, Iso.symm_symm_eq, Category.assoc,
    asIso_hom, qi, q, c, P, R, adj] using hm


end AlgebraicGeometry.ProEtale
