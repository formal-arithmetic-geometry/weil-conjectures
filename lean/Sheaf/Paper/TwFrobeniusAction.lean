/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q87
-/
module

public import Sheaf.Paper.TwConventions
public import Sheaf.Paper.IntrinsicQbarCategory
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.ConstantWeilStructure
public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.SixFunctors.FrobeniusCohomologyTransport
public import Sheaf.Paper.GlobalGeometricFrobenius
public import Sheaf.SixFunctors.FrobeniusCohomologyTransportIso

/-! # Geometric Frobenius action

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
sk-rem-sf-pf-done/def-tw-frobenius-action.md (blueprint: def-tw-frobenius-action).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- The ordinary global Frobenius isomorphism before taking homology. Source: Weil blueprint,
node def-tw-frobenius-action (blueprint: def-tw-frobenius-action). -/
def twFrobeniusOrdinaryIso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (c₀ : Compactification Y₀.hom)
    (W : sfCommonStageWeilComplex D l hl Y₀ Ω) :
    (frobeniusCohomologyQbarFunctor D l hl Y₀ Ω c₀ false).obj W.carrier ≅
      (frobeniusCohomologyQbarFunctor D l hl Y₀ Ω c₀ false).obj W.carrier := by
  letI : HasDerivedCategory.{(max u v) + 1} (ModuleCat.{max u v} Ω) :=
    HasDerivedCategory.standard _
  let F := frobeniusCohomologyQbarFunctor D l hl Y₀ Ω c₀ false
  let τ := frobeniusCohomologyTransport D l hl Y₀ Ω c₀ W.carrier
  let h := (frobeniusCohomologyTransport_isIso D l hl Y₀ Ω c₀ W.carrier).1
  letI := h.2.2.2.2.1
  letI := h.2.2.2.2.2.1
  exact eqToIso (frobeniusCohomologyQbarSourceEq D l hl Y₀ Ω c₀ false W.carrier) ≪≫
    asIso τ.1 ≪≫
    (eqToIso (frobeniusCohomologyQbarTargetEq D l hl Y₀ Ω c₀ false W.carrier)).symm ≪≫
    F.mapIso W.str

/-- The compact-support global Frobenius isomorphism before taking homology. Source: Weil
blueprint, node def-tw-frobenius-action (blueprint: def-tw-frobenius-action). -/
def twFrobeniusCompactIso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (c₀ : Compactification Y₀.hom)
    (W : sfCommonStageWeilComplex D l hl Y₀ Ω) :
    (frobeniusCohomologyQbarFunctor D l hl Y₀ Ω c₀ true).obj W.carrier ≅
      (frobeniusCohomologyQbarFunctor D l hl Y₀ Ω c₀ true).obj W.carrier := by
  letI : HasDerivedCategory.{(max u v) + 1} (ModuleCat.{max u v} Ω) :=
    HasDerivedCategory.standard _
  let F := frobeniusCohomologyQbarFunctor D l hl Y₀ Ω c₀ true
  let τ := frobeniusCohomologyTransport D l hl Y₀ Ω c₀ W.carrier
  let h := (frobeniusCohomologyTransport_isIso D l hl Y₀ Ω c₀ W.carrier).1
  letI := h.2.2.2.2.1
  letI := h.2.2.2.2.2.1
  exact eqToIso (frobeniusCohomologyQbarSourceEq D l hl Y₀ Ω c₀ true W.carrier) ≪≫
    asIso τ.2 ≪≫
    (eqToIso (frobeniusCohomologyQbarTargetEq D l hl Y₀ Ω c₀ true W.carrier)).symm ≪≫
    F.mapIso W.str

/-- The pair of ordinary and compact-support Frobenius isomorphisms. Source: Weil blueprint,
node def-tw-frobenius-action (blueprint: def-tw-frobenius-action). -/
def twFrobeniusComplex
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (c₀ : Compactification Y₀.hom) :=
  let W := constantWeilAlgebraicallyClosedComplex l D hl Y₀ Ω
  (twFrobeniusOrdinaryIso D l hl Y₀ Ω c₀ W, twFrobeniusCompactIso D l hl Y₀ Ω c₀ W)

/-- The ordinary and compact-support Qbar-linear automorphisms Phi_X^* and Phi_X,c^*
in every integer degree, obtained by taking H^i of the two global operators.
Source: Weil blueprint, node def-tw-frobenius-action, the two displayed automorphisms
(blueprint: def-tw-frobenius-action). -/
def twFrobeniusAction
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (c₀ : Compactification Y₀.hom) (i : ℤ) :=
  letI : HasDerivedCategory.{(max u v) + 1} (ModuleCat.{max u v} Ω) :=
    HasDerivedCategory.standard _
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} Ω) i
  let F := twFrobeniusComplex D l hl Y₀ Ω c₀
  (H.mapIso F.1, H.mapIso F.2)

end WeilConjectures
