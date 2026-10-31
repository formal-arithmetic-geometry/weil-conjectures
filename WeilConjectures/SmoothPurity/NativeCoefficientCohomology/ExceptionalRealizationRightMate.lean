/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.ExceptionalRealizationLeftModels
public import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.ForgetfulRepresentingPairRightMate
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences

/-! # Invertibility of the ordinary exceptional right mate

This assertion concerns the ordinary right mate only. Its Frobenius compatibility
is derived separately from the left square and the counit equation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
attribute [local instance 1100] CategoryTheory.instOverClass
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.ConstantPurityFrobenius
namespace WeilConjectures.NativeCoefficientCohomology

variable (P : PurityFiniteSetting.{u})
  (X₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [Fact (ringChar P.field.k₀ ≠ P.coefficients.l)]
  (c₀ : Compactification X₀.hom)
  (S : systems P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar X₀)

attribute [local instance] nativeStructureOver pointFiniteType pointQuasiCompact
  pointSeparated pointMapSeparated pointMapFiniteType pointMapQuasiCompact
  sourceFiniteType sourceQuasiCompact targetFiniteType targetQuasiCompact
  geometricMapOver geometricMapSeparated geometricMapFiniteType geometricMapQuasiCompact
  sourceUnits targetUnits

/-- A normalized comparison with an existing right mate transports invertibility.
The proof uses the two counit transpose formulas, so it does not assume that native
forgetting is faithful or that its derived category is a category of ordinary pairs. -/
private theorem right_mate_isIso_of_reference
    {WX WY CX CY DX DY : Type*}
    [Category WX] [Category WY] [Category CX] [Category CY] [Category DX] [Category DY]
    {FW : WX ⥤ WY} {GW : WY ⥤ WX} (adjW : FW ⊣ GW)
    {F : CX ⥤ CY} {G : CY ⥤ CX} (adj : F ⊣ G)
    {F' : DX ⥤ DY} {G' : DY ⥤ DX} (adj' : F' ⊣ G')
    {UX : WX ⥤ CX} {UY : WY ⥤ CY} {VX : WX ⥤ DX} {VY : WY ⥤ DY}
    (EX : CX ≌ DX) (EY : CY ≌ DY)
    (x : UX ⋙ EX.functor ≅ VX) (y : UY ⋙ EY.functor ≅ VY)
    (a : FW ⋙ UY ≅ UX ⋙ F) (a' : FW ⋙ VY ≅ VX ⋙ F')
    (c : EX.functor ⋙ F' ≅ F ⋙ EY.functor)
    (h : ∀ K : WX,
      EY.functor.map (a.inv.app K) ≫ y.hom.app (FW.obj K) =
        c.inv.app (UX.obj K) ≫ F'.map (x.hom.app K) ≫ a'.inv.app K)
    [IsIso (Adjunction.forgetfulRightMate adjW adj' a')] :
    IsIso (Adjunction.forgetfulRightMate adjW adj a) := by
  let γ := Adjunction.forgetfulRightMate adjW adj a
  let γ' := Adjunction.forgetfulRightMate adjW adj' a'
  let b := (mateEquiv adj adj' c.hom).natTrans
  have : IsIso b :=
    isIso_mateEquiv_of_isEquivalence_of_fullyFaithful adj adj' EX.functor EY.functor c
  have hc (L : WY) : F.map (γ.app L) ≫ adj.counit.app (UY.obj L) =
      a.inv.app (GW.obj L) ≫ UY.map (adjW.counit.app L) :=
    mateEquiv_counit adjW adj (TwoSquare.mk _ _ _ _ a.inv) L
  have hc' (L : WY) : F'.map (γ'.app L) ≫ adj'.counit.app (VY.obj L) =
      a'.inv.app (GW.obj L) ≫ VY.map (adjW.counit.app L) :=
    mateEquiv_counit adjW adj' (TwoSquare.mk _ _ _ _ a'.inv) L
  have hb (L : CY) : F'.map (b.app L) ≫ adj'.counit.app (EY.functor.obj L) =
      c.hom.app (G.obj L) ≫ EY.functor.map (adj.counit.app L) :=
    mateEquiv_counit adj adj' c.hom L
  have factor (L : WY) :
      EX.functor.map (γ.app L) ≫ b.app (UY.obj L) =
        x.hom.app (GW.obj L) ≫ γ'.app L ≫ G'.map (y.inv.app L) := by
    apply (adj'.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    calc
      F'.map (EX.functor.map (γ.app L)) ≫ F'.map (b.app (UY.obj L)) ≫
          adj'.counit.app (EY.functor.obj (UY.obj L)) =
        F'.map (EX.functor.map (γ.app L)) ≫ c.hom.app (G.obj (UY.obj L)) ≫
          EY.functor.map (adj.counit.app (UY.obj L))  := by
        simpa only [Category.assoc] using congrArg
          (fun z ↦ F'.map (EX.functor.map (γ.app L)) ≫ z) (hb (UY.obj L))
      _ = c.hom.app (UX.obj (GW.obj L)) ≫
          EY.functor.map (F.map (γ.app L) ≫ adj.counit.app (UY.obj L)) := by
        have hn := c.hom.naturality (γ.app L)
        simpa only [Functor.comp_obj, Functor.id_obj, Functor.comp_map,
          Functor.map_comp, Category.assoc] using
          congrArg (fun z ↦ z ≫ EY.functor.map (adj.counit.app (UY.obj L))) hn
      _ = c.hom.app (UX.obj (GW.obj L)) ≫
          EY.functor.map (a.inv.app (GW.obj L)) ≫
          EY.functor.map (UY.map (adjW.counit.app L)) := by rw [hc, EY.functor.map_comp]
      _ = c.hom.app (UX.obj (GW.obj L)) ≫
          EY.functor.map (a.inv.app (GW.obj L)) ≫ y.hom.app (FW.obj (GW.obj L)) ≫
          VY.map (adjW.counit.app L) ≫ y.inv.app L := by
        have hy : EY.functor.map (UY.map (adjW.counit.app L)) =
            y.hom.app (FW.obj (GW.obj L)) ≫
              VY.map (adjW.counit.app L) ≫ y.inv.app L := by
          simpa only [Functor.comp_obj, Functor.id_obj, Functor.comp_map,
            Category.assoc, Iso.hom_inv_id_app,
            Category.comp_id] using congrArg (fun z ↦ z ≫ y.inv.app L)
              (y.hom.naturality (adjW.counit.app L))
        rw [hy]
      _ = F'.map (x.hom.app (GW.obj L)) ≫ a'.inv.app (GW.obj L) ≫
          VY.map (adjW.counit.app L) ≫ y.inv.app L := by
        rw [← Category.assoc (EY.functor.map _), h]
        simp
      _ = F'.map (x.hom.app (GW.obj L)) ≫ F'.map (γ'.app L) ≫
          F'.map (G'.map (y.inv.app L)) ≫
            adj'.counit.app (EY.functor.obj (UY.obj L)) := by
        have hy : F'.map (G'.map (y.inv.app L)) ≫
            adj'.counit.app (EY.functor.obj (UY.obj L)) =
              adj'.counit.app (VY.obj L) ≫ y.inv.app L :=
          adj'.counit.naturality (y.inv.app L)
        rw [hy]
        simpa only [Category.assoc] using congrArg
          (fun z ↦ F'.map (x.hom.app (GW.obj L)) ≫ z ≫ y.inv.app L) (hc' L).symm
  have (L : WY) : IsIso (γ.app L) := by
    have hi : IsIso (EX.functor.map (γ.app L) ≫ b.app (UY.obj L)) := by
      rw [factor]
      infer_instance
    have : IsIso (EX.functor.map (γ.app L)) :=
      (isIso_comp_right_iff (EX.functor.map (γ.app L)) (b.app (UY.obj L))).mp hi
    exact isIso_of_reflects_iso (γ.app L) EX.functor
  exact NatIso.isIso_of_isIso_app γ

/-- The ordinary right mate of the normalized left comparison is invertible.
Source: cor-coef-verdier-weil-equivariance.proof.md, exceptional-adjunction
sentence; native_exceptional_forgetful, representing-counit construction.
(blueprint: lem-sf-exceptional-realization-right-mate-isIso)

Proof: let B be A.referencePackage and compare the two ordinary coefficient
adjunctions using A.sourceEquivalence, A.targetEquivalence and functorComparison.
The right mate of functorComparison is invertible because both coefficient-change
functors are equivalences. The native-to-reference right mate is invertible by B's
right comparison and its counit equation. The two counit transpose formulas and
left_reference identify the coefficient-change image of the required mate,
followed by the invertible coefficient mate, with that reference right comparison
conjugated by sourceModelComparison and targetModelComparison. This composite is
invertible. Cancel the coefficient mate and reflect invertibility through the
source coefficient equivalence. This proves the actual right mate invertible;
it neither assumes nor proves its Frobenius square at this stage. -/
theorem exceptional_realization_right_mate_isIso
    (A : ExceptionalRealizationLeftData P X₀ c₀ S)
    (J : WeilComplex P.field.k₀ P.coefficients.l (Spec (.of P.field.k₀)) ⥤
      WeilComplex P.field.k₀ P.coefficients.l X₀.left)
    (adj : WeilComplex.derivedLowerShriek P.field.k₀ P.coefficients.l X₀.hom ⊣ J) :
    IsIso (Adjunction.forgetfulRightMate adj
      (operation P.field P.coefficients.l P.coefficients.different
        P.coefficients.Qbar X₀ (point P.field) (pointMap P.field X₀) c₀ S .closed).adjunction
      A.left) := by
  let : Fact (P.coefficients.l ≠ P.field.p) := ⟨P.coefficients.different⟩
  let c := FrobeniusExchange.geometricCompactification P.field (pointMap P.field X₀) c₀
  let C := A.referencePackage.comparison (exceptionalReferenceSpace P X₀)
    (NativeExceptionalForgetful.point P.field) (pointMap P.field X₀) A.referenceSystem c J adj
  let O := A.referenceSystem.ring.operation c .closed
  have hr : Adjunction.forgetfulRightMate adj O.adjunction C.left = C.right.hom := by
    apply NatTrans.ext
    funext L
    apply (O.adjunction.homEquiv _ _).symm.injective
    exact (mateEquiv_counit adj O.adjunction
      (TwoSquare.mk _ _ _ _ C.left.inv) L).trans (C.counit L).symm
  have : IsIso (Adjunction.forgetfulRightMate adj O.adjunction C.left) := by
    rw [hr]
    infer_instance
  exact right_mate_isIso_of_reference adj _ O.adjunction
    A.sourceEquivalence A.targetEquivalence
    A.sourceModelComparison A.targetModelComparison A.left C.left
    A.functorComparison (A.left_reference J adj)

end WeilConjectures.NativeCoefficientCohomology
