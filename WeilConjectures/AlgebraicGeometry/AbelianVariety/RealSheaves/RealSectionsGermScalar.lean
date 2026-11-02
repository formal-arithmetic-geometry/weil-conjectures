/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.WeilSheaf.RealSheaves.Setup.RealSheavesSetup
public import WeilConjectures.WeilSheaf.RealSheaves.Setup.RealWeilSheaves
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.RealCondensedFibre.RealCondensedFibreFunctoriality
public import WeilConjectures.AlgebraicGeometry.LisseQlbar.LisseQlbarRepresentations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Germ
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.RestrictionWeilGroup

/-! # Generic germ and scalar comparison

Source: `literature/blueprint/latest/blueprint/sec-purity-real-sheaves/
sk-lem-wrp-hc2/p-real-sections.md`, displayed global-sections identification
and proof first four sentences
(blueprint: real-sections-germ-scalar).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open RealSheaves
open scoped CategoryTheory.Obj
namespace RealSheaves

/-- Ordinary pro-etale sections of the actual pulled-back internal module.
Source: p-real-sections, displayed global-sections identification.
(blueprint: real-sections-germ-scalar) -/
abbrev condensedSections (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) (U₀ : C₀.Opens)
    (j : D.geometricCurve U₀.toScheme ⟶ D.geometricCurve C₀)
    (L : AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed.WeilModule
      (Profinite.padicAlgClRingObj D.l) (D.weilFrobenius C₀ hC))
    (_hL : CondensedRing.LocallyFree (condensedRingObj (Profinite.padicAlgClRingObj D.l)
      (D.geometricCurve C₀)) L.carrier) : Type (u + 1) :=
  let M := (CondensedRing.upperStar (Profinite.padicAlgClRingObj D.l) j).obj L.carrier
  (M.X.obj.obj (op (Scheme.ProEt.mk (𝟙 (D.geometricCurve U₀.toScheme))))).carrier

/-- The canonical base-changed open immersion.
Source: p-real-sections, notation U and its inclusion in C.
(blueprint: real-sections-germ-scalar) -/
def realOpenMap (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (U₀ : C₀.Opens) :
    D.geometricCurve U₀.toScheme ⟶ D.geometricCurve C₀ :=
  Limits.pullback.map _ _ _ _ U₀.ι (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- Multiplication of sections by the pulled-back constant coefficient c.
Source: p-real-sections proof, evaluation at 1 and linearity; LisseQlbar.scalarEnd.
(blueprint: real-sections-germ-scalar) -/
def scalarSections (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) (U₀ : C₀.Opens)
    (L : AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed.WeilModule
      (Profinite.padicAlgClRingObj D.l) (D.weilFrobenius C₀ hC))
    (hL : CondensedRing.LocallyFree (condensedRingObj (Profinite.padicAlgClRingObj D.l)
      (D.geometricCurve C₀)) L.carrier)
    (c : condensedScalarRing (Profinite.padicAlgClRingObj D.l))
    (s : condensedSections D C₀ hC U₀ (realOpenMap D C₀ U₀) L hL) :
    condensedSections D C₀ hC U₀ (realOpenMap D C₀ U₀) L hL :=
  ((CondensedRing.upperStarObjXIso (Profinite.padicAlgClRingObj D.l)
      (realOpenMap D C₀ U₀) L.carrier).inv.hom.app
    (op (Scheme.ProEt.mk (𝟙 (D.geometricCurve U₀.toScheme))))
    (((ProEtale.upperStar Ab.{u + 1} (realOpenMap D C₀ U₀)).map
      (AlgebraicGeometry.ProEtale.LisseQlbar.scalarEnd
        (Profinite.padicAlgClRingObj D.l) (D.geometricCurve C₀) c L.carrier)).hom.app
      (op (Scheme.ProEt.mk (𝟙 (D.geometricCurve U₀.toScheme))))
      ((CondensedRing.upperStarObjXIso (Profinite.padicAlgClRingObj D.l)
        (realOpenMap D C₀ U₀) L.carrier).hom.hom.app
        (op (Scheme.ProEt.mk (𝟙 (D.geometricCurve U₀.toScheme)))) s)))

/-- Ordinary sections map to their actual geometric germ by the inverse-image unit.
Source: p-real-sections, germ formula; ProEtale.germ.
(blueprint: real-sections-germ-scalar) -/
@[irreducible] def realAbelianGerm {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ X) (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
    F.obj.obj (op (ProEt.mk (𝟙 X))) ⟶ (LisseQlbar.abFibre x).obj F :=
  let t : ProEt.mk (𝟙 (Spec (.of Ω))) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ x).obj (ProEt.mk (𝟙 X)) :=
    MorphismProperty.Over.homMk (Limits.pullback.lift x (𝟙 _))
  AlgebraicGeometry.ProEtale.germ Ab.{u + 1} x F t ≫
    (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId _)).hom.app
      ((x)^*[Ab.{u + 1}].obj F)

/-- The same germ in the actual internal-module fibre, through its underlying-sheaf iso.
Source: p-real-sections, germ formula; thm-lisse-qlbar-representations, Fibres.
(blueprint: real-sections-germ-scalar) -/
@[irreducible] def realModuleGerm
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    M.X.obj.obj (op (ProEt.mk (𝟙 X))) ⟶ AddCommGrpCat.of ((LisseQlbar.fibre Λ x).obj M) :=
  realAbelianGerm x M.X ≫ (LisseQlbar.fibreUnderlyingIso Λ x M).inv

end RealSheaves
