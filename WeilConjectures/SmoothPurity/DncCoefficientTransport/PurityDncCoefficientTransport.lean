/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.DncCoefficientTransport.DncCoefficientTransportData
import WeilConjectures.AlgebraicGeometry.NoetherianSectionSpecialization.FiniteSectionFamilyConstancy
import WeilConjectures.AlgebraicGeometry.Finite.Smooth.FiniteSmoothDualizingScalar
import WeilConjectures.SixFunctors.DncCoefficientTransport.SectionScalarBaseChange
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarSectionCompositor
import all WeilConjectures.AlgebraicGeometry.AffineLineNormalizedDescent.EtaleShiftedLineNormalizedDescent
import all WeilConjectures.AlgebraicGeometry.NoetherianSectionSpecialization.NoetherianEtaleSectionSpecialization
import Mathlib.Algebra.CharP.CharAndCard

/-! # Finite coefficient transport for the actual smooth-section deformation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

attribute [local instance] Scheme.Etale.essentiallySmall

attribute [local irreducible] DncCoefficientTransport.dualizingMap
  DncCoefficientTransport.sectionMap DncCoefficientTransport.realizedSectionMap
  ProEtale.reductionEtaleChartRightIso ProEtale.reductionEtaleChartScalarIso

namespace DncCoefficientTransport

/-- The domain facts follow from the source hypotheses, rather than being additional
hypotheses of the coefficient theorem.
Source: Proof (2) Step 1, sk-lem-geometry (blueprint: lem-pur-dnc-coefficient-transport).
Proof: finite type over the field makes S and V Noetherian. A closed section of a
smooth relative-dimension d map is regular of codimension d. On its extended-Rees
charts x_i=t*u_i the deformation projection is smooth of dimension d; its zero
fibre is the actual rank-d normal bundle. The projections are separated finite type,
and Nagata gives the three coefficient-independent compactifications. -/
theorem geometry (D : FiniteFieldDatum.{u}) {V S : Scheme.{u}}
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    (aS : S ⟶ Spec (.of D.k)) [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S) : Geometry g s := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian aS
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace aS
  have := SmoothOfRelativeDimension.smooth d g
  have : HasCompactification g := (NagataCompactification g).hasCompactification
  have := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g s hs
  have : QuasiCompact (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) inferInstance
  have : IsSeparated (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @IsSeparated)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) inferInstance
  have : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g s) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) inferInstance
  have := SmoothOfRelativeDimension.smooth d (Scheme.Hom.normalConeProj g s)
  exact ⟨inferInstance, Scheme.Hom.hasCompactification_deformationSpaceProj g s d hs,
    (NagataCompactification (Scheme.Hom.normalConeProj g s)).hasCompactification,
    inferInstance⟩

end DncCoefficientTransport

end WeilConjectures
