/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralTateLineConstructible
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseExtensionConstructible

/-! # Constructibility of the positive rational Tate line

This is the degree-zero generator assertion used in the projective-line argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.RationalP1

/-- The positive Tate line, in degree zero, has finite constant local models.
Source: blueprint latest, rational projective-line unit/counit proof,
Well-definedness (2)--(3), and definition-tate-twists, local-generator paragraph.
(blueprint: lem-sfb-rational-p1-positive-line-constructible).

Proof: invertibility of ell gives the common pro-etale cover with compatible roots
of unity in `spTwists_commonCover`. The root basis identifies the positive rational
line on every member with the regular coefficient module, both for a finite
extension and for the finite-subextension-valued algebraic closure. The latter
identification is the sheafified filtered colimit of these compatible bases.
The regular scalar module has its rank-one finite presentation. Thus these bases
are finite constant local models, and the one-stratum stratification gives
constant-model constructibility on a qcqs scheme. This also works on the empty
scheme, with the empty covering. The degree-zero single complex is bounded; its
zeroth cohomology is the line, and all other cohomology objects are zero, so it is
bounded constructible. -/
theorem positiveLine_boundedConstructible
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (Z : Scheme.{u}) [CompactSpace Z] [QuasiSeparatedSpace Z]
    (hl : ∀ x : Z, IsUnit (l : Z.residueField x)) :
    constantModelBoundedConstructible (coefficient l c).X Z
      ((DerivedCategory.singleFunctor (DiagonalCoefficients.Modules (coefficient l c).X Z) 0).obj
        (line l c Z)) := by
  classical
  let R := (coefficient l c).X
  let L := line l c Z
  let : ∀ x : Z, Invertible (l : Z.residueField x) := fun x ↦ (hl x).invertible
  obtain ⟨I, U, f, _, _, hc, _, _, _, hrat, hcl⟩ := spTwists_commonCover Z l
  have he (i : I) : Nonempty
      (((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (Scheme.ProEt.topology Z) (condensedRingObj R Z)).functor.obj L).over (U i) ≅
        (SheafOfModules.unit _).over (U i)) := by
    cases c with
    | none =>
      simpa only [R, L, coefficient, line, spSignedTwist,
        WeilConjectures.coefficientTwistLine, WeilConjectures.coefficientTwistPower,
        SheafOfModules.scalarTensorPower] using hcl i
    | some E =>
      simpa only [R, L, coefficient, line, spSignedTwist,
        WeilConjectures.coefficientTwistLine, WeilConjectures.coefficientTwistPower,
        SheafOfModules.scalarTensorPower] using (hrat E i).2
  have hfree := CondensedRing.IntegralRestriction.locallyFree_of_trivial_cover
    Z (condensedRingObj R Z) L U f hc he
  have hLisse : IsLisseCoefficientModule R L := by
    obtain ⟨C, hC⟩ := hfree
    refine ⟨C, fun i ↦ ?_⟩
    obtain ⟨n, ⟨b⟩⟩ := hC i
    let α := condensedPullbackHom R (C.f i)
    let G := Mod.extendScalars α
    let e : G.obj (Mod.regular ((ProEtale.upperStar Ab.{u + 1} (C.f i)).obj
        (condensedRingObj R Z))) ≅ Mod.regular (condensedRingObj R (C.X i)) :=
      (Mod.extendScalarsIsoComapInv α).app _ ≪≫ Mod.regularIsoOfIsIso α
    exact ⟨n, ⟨G.mapIso b ≪≫ G.mapBiproduct _ ≪≫
      CategoryTheory.Limits.biproduct.mapIso (fun _ ↦ e)⟩⟩
  have hmodel := lisse_finiteModel R Z L hLisse
  have hstrat := stratified_of_finiteModel R Z L hmodel
  have hconstruct : IsConstantModelConstructible R Z L := by
    rw [IsConstantModelConstructible, ite_eq_left
      (show CompactSpace Z ∧ QuasiSeparatedSpace Z from ⟨inferInstance, inferInstance⟩)]
    exact hstrat
  exact single_constructible R Z L hconstruct

end AlgebraicGeometry.ProEtale.RationalP1
