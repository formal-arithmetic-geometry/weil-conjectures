/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedSectionsCupWeilTransport.CondensedSectionsCupWeilTransportDefs

/-! Native geometric component of the condensed sections transport argument.

Source: the cup/sections sub-step of `sk-thm-frobenius` in blueprint latest.
(blueprint: lem-pod-condensed-sections-geometric-laws). -/

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

/-- Native geometric part of the condensed Frobenius transport package.
Source: sk-thm-frobenius, cup/sections lift, Steps 1--5 of the parent node.
(blueprint: lem-pod-condensed-sections-geometric-laws).

Proof: choose a compactification over k0 and base change it to k, as in the
blueprint. Use the all-admissible-coefficient localizing compactification comparison
between that model compactification and the arbitrary supplied compactification;
identify its maps with the clopen refinements before proper pushforward: full
faithfulness of extension by zero identifies the unit/counit maps on the source
open. Proper composition gives the desired native refinement equation. The
cocycle law extends its normalization to every common refinement.
Specialize the native cup-intertwining theorem to the descended compact exchange;
its projection/counit construction gives the mixed cup. Apply the termwise
pullback tensor comparison to the signed tensor-shift map: on degrees i and j
both composites multiply by (-1)^(s*i), since Frobenius has degree zero.
Localization preserves the equation and the two shift comparisons.
For a degree-zero coefficient line,
use a temporary trivialization and the ordinary and compact line projection
coordinate equations. Naturality and refinement descent remove this temporary
trivialization and identify the maps for the selected compactification. In a
line frame the compact projection is the right unitor, hence invertible.
An arbitrary line datum acts by a scalar in that frame; linearity proves the
squares without requiring the frame to be Frobenius invariant. -/
theorem condensedSectionsGeometricLaws
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
    : GeometricLaws C₀ Λ
        (localizingAdmissibleCoefficientOfAdmissible C₀ Λ hΛ)
        T₀ c L hL φL := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedSectionsCupWeilTransport
