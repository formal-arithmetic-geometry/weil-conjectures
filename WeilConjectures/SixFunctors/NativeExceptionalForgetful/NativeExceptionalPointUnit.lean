/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalForgetfulData
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # NativeExceptionalPointUnit

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures WeilConjectures.AdicQbarRealization
namespace WeilConjectures.NativeExceptionalForgetful
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]

/-- Forgetting the native constant at the finite-field point gives the regular
coefficient module in degree zero, in the specified section-module presentation.
Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, point-unit
specialization; Constant.lean, ProEtaleWeilSheaf.adicConstant.
(blueprint: lem-sf-native-exceptional-point-unit).

Proof: the native constant is IsoAlgebra.mk of AdicSheaf.unit and its canonical
Frobenius isomorphism. Exact forgetting commutes with the single complex in degree
zero. The direct image along closureMap is exact because that map is an isomorphism;
on sections it carries the regular coefficient module to the regular coefficient
module, with its multiplication action. Its right derivation agrees with its exact
termwise derivation, including the derived-unit comparison. The section-module
presentation sends this module to the sectionwise ring acting on itself. Apply the
single-complex and localization comparisons to obtain precisely coefficientUnit.
This works on the point with any chosen algebraic closure; no discrete replacement
of the coefficient sheaf is used. -/
theorem native_exceptional_point_unit (R : Family l D) :
    Nonempty ((U D l R (point D)).obj (constant D l (point D)) ≅
      coefficientUnit D l R (point D)) := by
  let := (R.data (geometric D (point D))).realization.commutative
  let := (R.data (geometric D (point D))).realization.sectionsAdditive
  let := (R.data (geometric D (point D))).realization.sectionsLimits
  let := (R.data (geometric D (point D))).realization.sectionsColimits
  have hi : IsIso (closureMap D (point D)) := by
    let e := (IsAlgClosure.equiv D.k₀ D.k (AlgebraicClosure D.k₀)).toRingEquiv.toCommRingCatIso
    have : IsIso (CommRingCat.ofHom
        (IsAlgClosure.equiv D.k₀ D.k (AlgebraicClosure D.k₀)).toRingHom) := e.isIso_hom
    unfold closureMap
    infer_instance
  let F := CategoryTheory.Endofunctor.IsoAlgebra.forget
    (WeilSheaf.frobeniusPullback D.k₀ l (point D).base.left)
  let G := ProEtale.adicLowerStar l (closureMap D (point D))
  let S := sectionFunctor l (geometric D (point D)).base.left
    (R.data (geometric D (point D))).realization
  let A := ProEtaleWeilSheaf.adicConstant D.k₀ l (point D).base.left
  have : S.Additive := (R.data (geometric D (point D))).realization.sectionsAdditive
  have : PreservesFiniteLimits S :=
    (R.data (geometric D (point D))).realization.sectionsLimits
  have : PreservesFiniteColimits S :=
    (R.data (geometric D (point D))).realization.sectionsColimits
  have regular : S.obj (ProEtale.AdicSheaf.unit l (geometric D (point D)).base.left) ≅
      SheafOfModules.unit ((sheafCompose (ProEt.topology (geometric D (point D)).base.left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (ring l (geometric D (point D)).base.left
            (R.data (geometric D (point D))).realization)) := eqToIso (by rfl)
  refine ⟨S.mapDerivedCategory.mapIso
      (G.rightDerivedFunctor.mapIso ((F.mapDerivedCategorySingleFunctor 0).app A) ≪≫
        G.singleFunctorCompRightDerivedFunctorIso.app (F.obj A) ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          (ProEtale.adicLowerStarUnitIso l (asIso (closureMap D (point D))))) ≪≫
      (S.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso regular ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).app _⟩

end WeilConjectures.NativeExceptionalForgetful
