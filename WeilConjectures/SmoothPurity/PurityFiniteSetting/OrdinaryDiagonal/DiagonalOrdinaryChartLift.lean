/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalOrientationRefinement
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-! # Ordinary presentation of one diagonal orientation

Source: latest blueprint, diagonal-dualizing proof, Steps 1--2 and combining paragraph.
(blueprint: lem-pur-diagonal-ordinary-chart-lift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.OrdinaryDiagonal

/-- Exact ordinary restriction, in the coordinates used for degree-zero gluing.
Source: Stacks 06XS (blueprint: lem-pur-diagonal-ordinary-chart-lift). -/
abbrev restrict (P : PurityFiniteSetting.{u}) {T S : Scheme.{u}} (j : T ⟶ S) :=
  (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) j).mapDerivedCategory

/-- The unit conversion on the exceptional inverse image.
Source: blueprint coefficient convention (blueprint: lem-pur-diagonal-ordinary-chart-lift). -/
def unit (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    Etale.dualizingComplex P.Coefficient f ≅
      P.diagonalOrdinaryDualizing f :=
  (Etale.rightDerivedUpperShriek P.Coefficient f).mapIso
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) Y).symm

/-- Restriction commutes with comparison, keeping ordinary restriction exact.
Source: blueprint site comparison (blueprint: lem-pur-diagonal-ordinary-chart-lift). -/
def comparison (P : PurityFiniteSetting.{u}) {T S : Scheme.{u}} (j : T ⟶ S) :
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) S).mapDerivedCategory ⋙
        OrientationRefinement.pull P j ≅
      restrict P j ⋙ (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory :=
  Functor.isoWhiskerLeft _
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory _ j) ≪≫
    ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso _ j

/-- Realize a local ordinary arrow in the precise coordinates of theta.
Source: blueprint combining paragraph (blueprint: lem-pur-diagonal-ordinary-chart-lift). -/
def realize (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) (V : Y.affineOpens)
    (b : (restrict P (f ⁻¹ᵁ V.1).ι).obj (P.diagonalOrdinaryDualizing f) ≅
      (restrict P (f ⁻¹ᵁ V.1).ι).obj (P.diagonalTwistEtale X d)) :=
  (OrientationRefinement.pull P (f ⁻¹ᵁ V.1).ι).mapIso
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso (unit P f)) ≪≫
    (comparison P (f ⁻¹ᵁ V.1).ι).app (P.diagonalOrdinaryDualizing f) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) (f ⁻¹ᵁ V.1).toScheme).mapDerivedCategory.mapIso b ≪≫
    ((comparison P (f ⁻¹ᵁ V.1).ι).app (P.diagonalTwistEtale X d)).symm ≪≫
    OrientationRefinement.tate P (f ⁻¹ᵁ V.1).ι (f ≫ aY) d

private theorem base_normal_form (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    Nonempty (Etale.affineLinearBaseCoefficient A N hA S d ≅
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A N S hA (d : ℤ)))⟦2 * (d : ℤ)⟧) := by
  let E := fun d : ℕ ↦ Scheme.finiteEtaleTateSheaf A N S hA (d : ℤ)
  have hflat (d : ℕ) : ObjectProperty.flat (E d) := by
    apply (ObjectProperty.flat_iff_preservesFiniteLimits _).2
    exact (Scheme.finite_etale_torsion_twist_line S N hN
      (fun x ↦ by
        simpa only [map_natCast] using hS.map (S.presheaf.germ ⊤ x (by trivial)).hom)
      A hA d).2.2.1
  let t := Scheme.finiteEtaleTwistPullbackData A N hN hA
  induction d with
  | zero =>
    exact ⟨(Iso.refl _) ≪≫ (shiftFunctorZero _ ℤ).symm.app _⟩
  | succ d ih =>
    obtain ⟨e⟩ := ih
    let prod : E d ⊗ E 1 ≅ E (d + 1) :=
      t.p S hS d 1 ≪≫ eqToIso (congrArg (Scheme.finiteEtaleTateSheaf A N S hA)
        (by omega))
    refine ⟨((Etale.derivedTensorRight (ModuleCat.{u + 1} A) S
      ((Etale.ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).mapIso e) ≪≫ ?_⟩
    exact Etale.derivedTensorShiftIso (ModuleCat.{u + 1} A) _ _ (2 * (d : ℤ)) 2 ≪≫
      (shiftFunctor _ (2 * (d : ℤ) + 2)).mapIso
        (Etale.singleProductGeneral (ModuleCat.{u + 1} A) S (E d) (E 1) (E (d + 1))
          (hflat d) prod) ≪≫
      eqToIso (congrArg (fun a : ℤ ↦
        ((_root_.DerivedCategory.singleFunctor _ 0).obj (E (d + 1)))⟦a⟧) (by omega))

/-- Removing the even shift leaves the finite Tate sheaf in degree zero.
Source: coefficient twists (blueprint: lem-pur-diagonal-ordinary-chart-lift). -/
theorem twist_concentrated (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (d : ℕ) :
    _root_.DerivedCategory.homologyConcentratedIn 0 0
      ((P.diagonalTwistEtale X d)⟦-(2 * (d : ℤ))⟧) := by
  obtain ⟨e⟩ := base_normal_form P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates X (P.diagonalExponent_isUnit aX) d
  let e' := (shiftFunctor _ (-(2 * (d : ℤ)))).mapIso e ≪≫
    shiftShiftNeg _ (2 * (d : ℤ))
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso e'.symm 0,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e'.symm 0⟩

/-- Concentration is invariant under an isomorphism.
Source: Stacks 0118 (blueprint: lem-pur-diagonal-ordinary-chart-lift). -/
theorem concentrated_iso {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {K L : _root_.DerivedCategory C} (e : K ≅ L)
    (h : _root_.DerivedCategory.homologyConcentratedIn 0 0 K) :
    _root_.DerivedCategory.homologyConcentratedIn 0 0 L := by
  have := h.1
  have := h.2
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso e 0,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e 0⟩

private theorem plus_of_concentrated_shift
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (K : _root_.DerivedCategory C) (n : ℤ)
    (h : _root_.DerivedCategory.homologyConcentratedIn 0 0 (K⟦n⟧)) :
    _root_.DerivedCategory.TStructure.t.plus K := by
  have := h.1
  have := _root_.DerivedCategory.TStructure.t.isGE_shift (K⟦n⟧) 0 (-n) n (by omega)
  exact ⟨n, _root_.DerivedCategory.TStructure.t.isGE_of_iso (shiftShiftNeg K n) n⟩

private theorem lift_iso (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : _root_.DerivedCategory.TStructure.t.plus M)
    (hN : _root_.DerivedCategory.TStructure.t.plus N)
    (e : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj M ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj N) :
    ∃ b : M ≅ N, (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso b = e := by
  let F := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  obtain ⟨g, hg⟩ :=
    (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map M N hN).surjective e.hom
  obtain ⟨g', hg'⟩ :=
    (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map N M hM).surjective e.inv
  change F.map g = e.hom at hg
  change F.map g' = e.inv at hg'
  refine ⟨⟨g, g', ?_, ?_⟩, Iso.ext hg⟩
  · apply (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map M M hM).injective
    change F.map (g ≫ g') = F.map (𝟙 M)
    rw [F.map_comp, hg, hg', e.hom_inv_id, F.map_id]
  · apply (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map N N hN).injective
    change F.map (g' ≫ g) = F.map (𝟙 N)
    rw [F.map_comp, hg, hg', e.inv_hom_id, F.map_id]

/-- Each single diagonal/DNC/vector composite has an ordinary presentation. This is
local: there is no family of charts, compatibility assumption, or global isomorphism.
Source: latest blueprint thm-pur-diagonal-dualizing-object.proof.md, Steps 1--2;
ordinary presentations in thm-pur-dnc-invariance and Stacks 099V.
(blueprint: lem-pur-diagonal-ordinary-chart-lift).

Proof: conjugate theta by the specified source unit conversion and the natural
restriction/site comparison, obtaining nu*M isomorphic to nu*N. Tensor induction
identifies the Tate target N, after removing the even shift, with a sheaf in degree
zero; the finite Tate lines are flat. Exact ordinary restriction preserves this
concentration. Exact comparison preserves and, being faithful on sheaves, reflects
cohomology vanishing. Thus the shifted M is concentrated as well. In particular M
and N are bounded below. Lift the comparison isomorphism and its inverse by the
existing bounded-below comparison Hom bijection. Injectivity on endomorphisms gives
both inverse identities. Cancellation of the conjugating source and target
comparisons gives the prescribed realization equation. This argument uses theta
as a local isomorphism and does not need to identify its four factors separately.
Only one affine target open is involved. Empty charts and dimension zero use the
same concentration and comparison arguments. -/
theorem chart_lift (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] (V : Y.affineOpens)
    (D : OrientationRefinement.Chart P f aY d V) :
    ∃ b : (restrict P (f ⁻¹ᵁ V.1).ι).obj (P.diagonalOrdinaryDualizing f) ≅
      (restrict P (f ⁻¹ᵁ V.1).ι).obj (P.diagonalTwistEtale X d),
      realize P f aY d V b =
        OrientationRefinement.theta P f aY d V D.geometry D.betaEtale := by
  let j := (f ⁻¹ᵁ V.1).ι
  let M := (restrict P j).obj (P.diagonalOrdinaryDualizing f)
  let N := (restrict P j).obj (P.diagonalTwistEtale X d)
  let F := ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) (f ⁻¹ᵁ V.1).toScheme
  let n : ℤ := -(2 * (d : ℤ))
  let c := (OrientationRefinement.pull P j).mapIso
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso (unit P f)) ≪≫
    (comparison P j).app (P.diagonalOrdinaryDualizing f)
  let t := ((comparison P j).app (P.diagonalTwistEtale X d)).symm ≪≫
    OrientationRefinement.tate P j (f ≫ aY) d
  let e : F.mapDerivedCategory.obj M ≅ F.mapDerivedCategory.obj N :=
    c.symm ≪≫ OrientationRefinement.theta P f aY d V D.geometry D.betaEtale ≪≫ t.symm
  have hn := Functor.homologyConcentratedIn_mapDerivedCategory_obj
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) j) (twist_concentrated P X (f ≫ aY) d)
  let en := ((restrict P j).commShiftIso n).app (P.diagonalTwistEtale X d)
  have hN : _root_.DerivedCategory.homologyConcentratedIn 0 0 (N⟦n⟧) :=
    concentrated_iso en hn
  have hFN := F.homologyConcentratedIn_mapDerivedCategory_obj hN
  let em := (F.mapDerivedCategory.commShiftIso n).app M ≪≫
    (shiftFunctor _ n).mapIso e ≪≫ ((F.mapDerivedCategory.commShiftIso n).app N).symm
  have hFM : _root_.DerivedCategory.homologyConcentratedIn 0 0
      (F.mapDerivedCategory.obj (M⟦n⟧)) := concentrated_iso em.symm hFN
  have hM := F.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj hFM
  obtain ⟨b, hb⟩ := lift_iso P (f ⁻¹ᵁ V.1).toScheme M N
    (plus_of_concentrated_shift M n hM) (plus_of_concentrated_shift N n hN) e
  refine ⟨b, ?_⟩
  have hreal : c ≪≫ F.mapDerivedCategory.mapIso b ≪≫ t =
      OrientationRefinement.theta P f aY d V D.geometry D.betaEtale := by
    rw [hb]
    apply Iso.ext
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
  simpa only [realize, c, t, Iso.trans_assoc] using hreal

end WeilConjectures.PurityFiniteSetting.OrdinaryDiagonal
