/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates
public import WeilConjectures.SixFunctors.SfProEtaleProjection.SfProEtaleProjectionFormula
import all WeilConjectures.SixFunctors.SfProEtaleProjection.SfProEtaleProjectionFormula
import WeilConjectures.SixFunctors.Integral.IntegralProperOperationProjection

/-! # Integral projection in ordinary completed-ring coordinates

Source: fix-prop-projection-formula.proof.md, integral reconstruction, and
def-exchange-projection, the proper-counit/open projection construction.
(blueprint: lem-sf-integral-projection-operation-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  ProjectionRestriction.derived SemilinearSections.abelianSheafify
  SemilinearSections.locallyBijective SemilinearSections.sequenceSmall
  SemilinearSections.sliceSmall integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall
  constructibleTensorSiteSmall in
private theorem tensorPresentation
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{u}) [CompactSpace W] [QuasiSeparatedSpace W]
    [∀ w : W, Invertible (l : W.residueField w)]
    (a : SfProEtaleProjection.TensorModel l E W)
    (M N : DerivedCategory (integralTowerModules l E W))
    (hM : sfIntegralConstructible l E W M) (hN : sfIntegralConstructible l E W N) :
    Nonempty (a.tensor.obj (M, N) ≅ (integralCompletedTensor l E W).obj (M, N)) := by
  have presentation := constructibleTensorCompletion l E W
  let T := presentation.choose
  let e := presentation.choose_spec.choose
  let hchi := presentation.choose_spec.choose_spec.choose_spec
  let tau := hchi.2.2.choose
  have ht := hchi.2.2.choose_spec.2
  obtain ⟨P, ⟨p⟩⟩ := SfProEtaleProjection.goodRepresentative l E W M
  obtain ⟨Q, ⟨q⟩⟩ := SfProEtaleProjection.goodRepresentative l E W N
  have hP : proEtaleFlatRepresentatives W ((PurCompactSupport.completed l E).ring W)
      P.obj := P.property
  have hQ : proEtaleFlatRepresentatives W ((PurCompactSupport.completed l E).ring W)
      Q.obj := Q.property
  let z : a.tensor.obj (M, N) ≅ T.obj (M, N) :=
    a.tensor.mapIso (Iso.prod p q).symm ≪≫
      (a.representative.app (⟨P.obj, hP⟩, ⟨Q.obj, hQ⟩)).symm ≪≫
      e.app (P, Q) ≪≫ T.mapIso (Iso.prod p q)
  have htau : IsIso (tau.app (M, N)) := (ht M N hM hN).2
  exact ⟨z ≪≫ @asIso _ _ _ _ (tau.app (M, N)) htau⟩

end WeilConjectures
