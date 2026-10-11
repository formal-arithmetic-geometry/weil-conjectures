/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint
import Sheaf.AlgebraicGeometry.GlobalDerivedHom
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Products.Basic

/-!
# Global derived Hom adjunction

Source: Stacks Project, Duality for Schemes, Tag 0B6I, lemma-iso-global-hom
(blueprint: lem-pc-global-hom-adjunction).
-/

universe u wX wY wAX wAY

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Global derived Hom adjunction for a qcqs morphism between qcqs schemes, natural
contravariantly in P and covariantly in K. The left side has scalars restricted along
Γ(Y,O_Y) → Γ(X,O_X). The preservation witness and right adjoint exist by
`schemeDerivedDirectImage_qcqs_hasRightAdjoint`.
Source: Stacks Project, Tag 0B6I, lemma-iso-global-hom
(blueprint: lem-pc-global-hom-adjunction).

Proof:
1. The qcqs hypotheses give preservation of quasi-coherent cohomology and a right adjoint
by `lem-pc-qcqs-derived-direct-image-right-adjoint`. Its counit induces the natural
internal-Hom comparison of `lem-pc-qcqs-sheaf-rhom-adjunction`, an isomorphism after DQ_Y.
2. Apply derived global sections. The composition isomorphism of
`lem-pc-ringed-spaces-derived-direct-image-composition`, applied to p_Y ∘ f = r ∘ p_X,
identifies RΓ(Y,Rf_* -) with restriction of scalars of RΓ(X,-). Here r is the map of
one-point ringed spaces induced by f.appTop, and restriction of scalars is exact.
By `def-pc-global-derived-rhom` these are the two global derived Hom functors below.
By `lem-pc-dq-coherator-adjunction`, H^i(Y,E) = Hom(O_Y[-i],DQ_Y E), since O_Y[-i]
is quasi-coherent. Thus a comparison that becomes an isomorphism after DQ_Y gives a
quasi-isomorphism on RΓ(Y,-). All constructions are natural in P and K. -/
theorem schemeGlobalDerivedHom_adjunction (X Y : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wAX}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    [HasDerivedCategory.{wAY}
      (ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hpres : ∀ E : schemeDerivedCategory X, schemeDerivedQCohProperty X E →
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E))
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (_adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ hpres E.obj E.property) ⊣ a) :
    Nonempty
      (((schemeDerivedQCohProperty X).ι.op.prod
          (a ⋙ (schemeDerivedQCohProperty X).ι) ⋙ schemeGlobalDerivedHom X ⋙
          (ModuleCat.restrictScalars.{u}
            (R := (moduleRings Y.toRingedSpace).obj.obj (op ⊤))
            (S := (moduleRings X.toRingedSpace).obj.obj (op ⊤))
            f.appTop.hom).mapDerivedCategory.{wAX, wAY}) ≅
        (((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f).op.prod
          (schemeDerivedQCohProperty Y).ι ⋙ schemeGlobalDerivedHom Y)) := by
  sorry

end AlgebraicGeometry
