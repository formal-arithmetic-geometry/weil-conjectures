/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleObjects
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree

/-! # Integral lisse lattices over pulled-back condensed coefficients

Source: latest blueprint, sec-purity-real-sheaves/sk-lem-wrp-hc2/
lem-a1-affine-hc0.proof.md, first paragraph, and sk-p-real-integral/p-real-integral.md,
final paragraph (blueprint: def-a1-common-stage-lisse-lattice).

The algebraic closure is the existing `PadicAlgCl ℓ` coefficient model. The integral
coefficient ring and its map to the finite-subextension-valued condensed algebraic
closure are pulled back from the point. Scalar extension is ordinary module-object
scalar extension. No compatibility with an additional Weil structure is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The canonical coefficient inclusion `𝒪_{E,X} ⟶ Ω_X`, obtained by pulling back
`𝒪̲_E ⟶ E̲ ⟶ Ω̲` from the point. Both arrows are the existing continuous-function
inclusions, with the second landing in finite-subextension-valued sections.
Source: latest blueprint, p-real-integral.md, final paragraph
(blueprint: def-a1-common-stage-lisse-lattice). -/
def integralLisseLatticeCoefficientMap (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    coefficientRing X (Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ⟶
      coefficientRing X (Mon.mk (Profinite.padicAlgClRingObj ℓ)) :=
  (upperStarFromPoint X).mapMon.map (Mon.ofHom
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing ℓ E.1) ≫
      Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E))

/-- Ordinary scalar extension along the canonical integral coefficient inclusion.
The existing commutativity proof for the pulled-back integral ring is supplied
explicitly through the bundled coefficient-ring interface.
Source: latest blueprint, p-real-integral.md, final paragraph
(blueprint: def-a1-common-stage-lisse-lattice). -/
def integralLisseLatticeExtension (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    condensedModuleCategory X (Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ⥤
      condensedModuleCategory X (Mon.mk (Profinite.padicAlgClRingObj ℓ)) :=
  letI : IsCommMonObj
      (coefficientRing X (Mon.mk (Profinite.padicIntegersRingObj ℓ E.1))).X :=
    isCommMonObj_condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X
  Mod.extendScalars (integralLisseLatticeCoefficientMap ℓ X E).hom

end AlgebraicGeometry.ProEtale
