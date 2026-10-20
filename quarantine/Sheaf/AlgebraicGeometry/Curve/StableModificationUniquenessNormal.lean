/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
import WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal
import Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange
import Sheaf.TraceFormula.StableCurveDiagramNoetherianModel
import Sheaf.TraceFormula.ValuationSemistableDominatesStable
import Sheaf.TraceFormula.ValuativeDominationEtaNormal

/-! # Uniqueness of stable modifications over a normal integral base

Source: Temkin, *Stable modification of relative curves*, Theorem 1.2 and Corollary 1.3(i),
with the proof in §5, printed p. 35.
(blueprint: lem-trf-stable-modification-uniqueness-normal)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Temkin

/-- Stable eta-modifications of a multipointed curve are uniquely isomorphic over that
pair. The equations over the original pair force the identity under the given generic
identifications, since both member maps are isomorphisms on the generic fibre.

Source: Temkin, Theorem 1.2, Corollary 1.3(i), and proof in §5, printed p. 35.
(blueprint: lem-trf-stable-modification-uniqueness-normal)

Proof plan:
1. On an affine base chart, flatness gives injectivity into the generic localization.
   Apply lem-sc-flat-invertible-sections-torsion-free to the structure sheaf on each affine
   source chart. The equalizer of two maps over the original curve is closed, since the
   target modification is proper and hence separated over the curve. If the maps agree
   generically, its ideal is zero by that injectivity. The same applies to markings.
2. Apply lem-trf-stable-curve-diagram-noetherian-model to the two stable modifications.
   This models the pair and both arrows over a normal integral affine finite-type scheme
   over the integers, preserving semistability, stability, reducedness and generic
   identifications, and giving a common dense isomorphism open.
3. Apply lem-trf-geometrically-reduced-eta-normal to the two semistable source curves.
   Their nodal geometric fibres are reduced, so both source curves are eta-normal.
4. For each finite-height centred valuation of the base function field, use
   lem-trf-semistable-marked-base-change and lem-weil-pbc-proper-fp-permanence to pull back
   the semistable pairs and proper maps. The dense base open from step 2 pulls back to an
   open containing the generic fibre. Flatness over the valuation domain makes its source
   and target preimages schematically dense. Apply
   lem-trf-valuation-semistable-dominates-stable in both directions; that node permits the
   actual function field without a separable-closedness assumption.
5. Apply lem-trf-valuative-domination-eta-normal in both directions to obtain maps of
   source curves over the original curve with their prescribed generic maps. Step 1 makes
   both composites identities, giving an isomorphism of curves.
6. Pull the ideal of the second marking back along this isomorphism restricted to the first
   marking. Its generic restriction vanishes, hence it vanishes by flatness as in step 1.
   The closed-immersion quotient property gives the marking map. Its map to the original
   marking is the required one by monicity of that marking's inclusion. Do the same for
   the inverse. Finally pull back the finite-type comparisons to the original affine base
   charts; step 1 makes them agree on overlaps and glue uniquely. The generic maps are
   exactly the comparisons induced by the specified generic isomorphisms. -/
theorem stableModificationUniquenessNormal
    {T : Scheme.{u}} [IsIntegral T] [CompactSpace T] [QuasiSeparatedSpace T]
    (hT : ∀ x : T, IsDomain (T.presheaf.stalk x) ∧ IsIntegrallyClosed (T.presheaf.stalk x))
    (C : MultipointedCurve T)
    (hX : Smooth (pullback.snd C.x T.fromSpecFunctionField))
    (hD : Etale (pullback.snd C.d T.fromSpecFunctionField))
    {C₁ C₂ : MultipointedCurve T} (f₁ : C₁.Hom C) (f₂ : C₂.Hom C)
    (hf₁ : f₁.IsStable T.fromSpecFunctionField)
    (hf₂ : f₂.IsStable T.fromSpecFunctionField) :
    ∃! α : (C₁.X ≅ C₂.X) × (C₁.D ≅ C₂.D),
      α.2.hom ≫ C₂.i = C₁.i ≫ α.1.hom ∧
      α.1.hom ≫ f₂.curve = f₁.curve ∧ α.2.hom ≫ f₂.marking = f₁.marking := by
  sorry

end AlgebraicGeometry.Temkin
