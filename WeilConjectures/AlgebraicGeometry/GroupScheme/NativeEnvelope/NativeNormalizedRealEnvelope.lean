/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstantWeil.CondensedConstantWeilTwist
public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedFibreLinearCurrent.CondensedFibreLinearOperationsStatement

/-! # The normalized real envelope on actual condensed modules

Source: latest blueprint, sk-prop-wrp-real-envelope/def-wf-normalized-real-envelope.md,
constant twist and direct sum with its contragredient
(blueprint: def-wf-normalized-real-envelope).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.NativeEnvelope

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [IsSeparated X₀.hom]

/-- F^0 is tensor with the recorded constant Weil line B_b, including its scalar structure.
Source: latest blueprint, normalized real envelope, first display
(blueprint: def-wf-normalized-real-envelope). -/
def normalizedTwist (hl : l ≠ D.p)
    (F : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) (b : (PadicAlgCl l)ˣ) :=
  CondensedFibreLinearCurrent.tensorWeil l (D.geometricFrobenius X₀) F
    (CondensedRing.ConstantWeil.lineModule l D X₀ hl b)

/-- F^0 direct sum (F^0)^vee, with the evaluation-transpose contragredient Weil map.
The finite product is the standard finite direct sum in the abelian module category.
No purity, nonvanishing, chosen basis or coefficient realization is part of the data.
Source: latest blueprint, normalized real envelope, second display
(blueprint: def-wf-normalized-real-envelope). -/
def realEnvelope (hl : l ≠ D.p)
    (F : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) (b : (PadicAlgCl l)ˣ) :=
  let F₀ := normalizedTwist D l X₀ hl F b
  CondensedFibreLinearCurrent.sumWeil l (D.geometricFrobenius X₀) 2
    (fun j ↦ if j.val = 0 then F₀ else
      CondensedFibreLinearCurrent.dualWeil l (D.geometricFrobenius X₀) F₀)

end WeilConjectures.NativeEnvelope
