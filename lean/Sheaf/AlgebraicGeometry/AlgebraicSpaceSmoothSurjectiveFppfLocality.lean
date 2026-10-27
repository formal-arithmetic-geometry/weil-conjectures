/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Smoothness and surjectivity under base change and fppf descent

Source: Stacks Project, Spaces Descent, Tags 0429 and 041Q;
Morphisms of Spaces, Tags 03ZE and 03MH
(blueprint: lem-sfb-space-smooth-surjective-fppf-locality).

Smoothness uses the existing universal etale scheme-chart test. Surjectivity uses
field-extension lifting through a singleton family, without a representability condition.
The base changes are the existing projections of actual sheaf fibre products.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Smoothness and point-surjectivity separately survive arbitrary space base change
and are separately local for fppf coverings of a scheme target.
Source: Stacks, Spaces Descent, Tags 0429 and 041Q; Morphisms of Spaces, Tags 03ZE
and 03MH (blueprint: lem-sfb-space-smooth-surjective-fppf-locality).

Proof:
1. For smooth base change, choose a surjective etale scheme atlas V of Y, then an
   atlas U of X ×_Y V. The composite U → X is surjective etale by
   lem-trf-space-representable-etale-scheme-tests. The scheme map U → V is smooth
   by lem-sfb-space-etale-presentation-property-criterion and
   lem-sfb-scheme-etale-source-target-properties. For Y' → Y choose an atlas V'
   of Y' ×_Y V. Scheme smooth base change (lem-pc-proper-base-change) makes
   U ×_V V' → V' smooth. Matching triples identify this source with the required
   atlas of X ×_Y Y'; the presentation criterion concludes.
2. For a field-valued point y' of Y', lift its image in Y to X after a field
   extension using def-trf-algebraic-space-jointly-surjective-family. The lift and
   the restriction of y' are compatible sections, hence a section of the sheaf
   pullback by lem-trf-space-fibre-products-etale-covers. This proves point-surjectivity
   after base change; no lift over the original field is required.
3. Smoothness of scheme maps descends along an fpqc family by
   lem-galois-fpqc-family-descent-of-local-property: base-change stability is
   lem-pc-proper-base-change and descent along a flat quasi-compact surjection is
   lem-trf-smooth-fpqc-base-descent. For Zariski target locality, choose an open
   containing the image of a given source point. Its inclusions are etale by
   lem-weil-pbc-open-immersion-etale; the pointwise clause of
   lem-sfb-scheme-etale-source-target-properties then gives smoothness.
4. For fppf descent choose a scheme atlas U → X. The maps U ×_Y Y_i → Y_i
   are smooth by the presentation criterion and representable-etale calculus.
   The family is fpqc by lem-trf-fppf-covering-is-fpqc. Step 3 makes U → Y smooth,
   and the presentation criterion makes f smooth. The converse is step 1.
5. For surjectivity descent, pull the fppf family back along Spec K → Y using
   lem-trf-fppf-covering-base-change. A point of a covering member gives a residue
   field extension L of K (def-weil-residue-field). Local surjectivity lifts this
   point after a further field extension M of L. Projection to X lifts the
   original point after K → M, using the point-class interpretation of
   def-a1-algebraic-space-point-classes. The converse is step 2. For an empty
   covering the target is empty, so both tests are vacuous; empty covering
   members likewise cause no change. -/
theorem smooth_surjective_fppf_locality {S : Scheme.{u}} :
    (∀ {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y),
      MapIsLocally (@Smooth) f → MapIsLocally (@Smooth) (enlargedFibreProductFst g f)) ∧
    (∀ {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y),
      IsJointlySurjective (fun _ : Unit ↦ f.hom.hom) →
        IsJointlySurjective (fun _ : Unit ↦ (enlargedFibreProductFst g f).hom.hom)) ∧
    (∀ {I : Type w} (T : Over S) (X : AlgebraicSpace S) (f : X ⟶ schemeSpace T)
      (Tᵢ : I → Over S) (g : ∀ i : I, Tᵢ i ⟶ T),
      Presieve.ofArrows (fun i : I ↦ (Tᵢ i).left) (fun i : I ↦ (g i).left) ∈
        Scheme.fppfPrecoverage T.left →
      (MapIsLocally (@Smooth) f ↔ ∀ i : I,
        MapIsLocally (@Smooth) (enlargedFibreProductFst
          (ObjectProperty.homMk ⟨yoneda.map (g i)⟩ : schemeSpace (Tᵢ i) ⟶ schemeSpace T)
          f))) ∧
    (∀ {I : Type w} (T : Over S) (X : AlgebraicSpace S) (f : X ⟶ schemeSpace T)
      (Tᵢ : I → Over S) (g : ∀ i : I, Tᵢ i ⟶ T),
      Presieve.ofArrows (fun i : I ↦ (Tᵢ i).left) (fun i : I ↦ (g i).left) ∈
        Scheme.fppfPrecoverage T.left →
      (IsJointlySurjective (fun _ : Unit ↦ f.hom.hom) ↔ ∀ i : I,
        IsJointlySurjective (fun _ : Unit ↦ (enlargedFibreProductFst
          (ObjectProperty.homMk ⟨yoneda.map (g i)⟩ : schemeSpace (Tᵢ i) ⟶ schemeSpace T)
          f).hom.hom))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
