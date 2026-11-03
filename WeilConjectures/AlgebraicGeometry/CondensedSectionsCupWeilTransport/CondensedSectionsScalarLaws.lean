/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedSectionsCupWeilTransport.CondensedSectionsCupWeilTransportDefs

/-! Exact scalar point component of the condensed sections transport argument.

Source: the cup/sections sub-step of `sk-thm-frobenius` in blueprint latest.
(blueprint: lem-pod-condensed-sections-scalar-laws). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
attribute [local instance] AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj
attribute [local instance 30000] CategoryTheory.Functor.monObjObj
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian

namespace AlgebraicGeometry.ProEtale.CondensedSectionsCupWeilTransport

/-- Exact scalar sections part of the condensed Frobenius transport package.
Source: sk-thm-frobenius, cohomology and coefficient normalization, Steps 5--6
of the parent node.
(blueprint: lem-pod-condensed-sections-scalar-laws).

Proof: the proved degree-zero line trivialization supplies a global frame.
The point coefficient theorem identifies the coefficient unit with the regular
module, and the single-complex homology comparison gives the recorded unit map.
Transport the normalized point-sections theorem along
the canonical ring equivalence from native coefficient sections to Lambda(*),
and along the specified heart-fiber comparison. The tensor identity for restriction gives
the displayed point-pullback tensor
equation for the specified derived monoidal comparison. The degreewise cross product followed by the
ordinary projection is invertible for a line; its inverse is normalized by
every temporary frame. More explicitly, a section written as a times a frame
sends a class z to the class of a*z tensored with that frame, followed by the
ordinary projection. Rescaling the frame by a unit rescales its coordinate
inversely, so the resulting map is unchanged. This proves normalization for
every frame. Naturality of the cross product and the supplied ordinary
intertwining square yield exactly the tensor-product Frobenius. -/
theorem condensedSectionsScalarLaws
    {D₀ : WeilConjectures.FiniteFieldDatum.{u}}
    (C₀ : D₀.CoefficientDatum)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : CondensedRing.IsAdmissibleCoefficientFor C₀ (Mon.mk Λ))
    (T₀ : Over (Spec (.of D₀.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
    (c : Compactification (D₀.geometricFiber T₀).hom)
    (L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of D₀.k))) Ab.{u + 1})
        (condensedRingObj Λ (Spec (.of D₀.k)))))
    (hL : DegreeZeroLine L)
    (φL : (AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed.action Λ
      (StrictWeilCondensed.pointFrobenius D₀)).obj L ≅ L)
    : ScalarLaws C₀ Λ
        (localizingAdmissibleCoefficientOfAdmissible C₀ Λ hΛ)
        T₀ c L hL φL := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedSectionsCupWeilTransport
