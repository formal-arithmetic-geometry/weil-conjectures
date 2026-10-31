/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import WeilConjectures.AlgebraicGeometry.EnlargedEtaleRingedSite
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.FppfAffineRefinement
import WeilConjectures.AlgebraicGeometry.FpqcClosedImmersionDescent
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFlatLfpUniversallyOpen
import WeilConjectures.AlgebraicGeometry.ChartwiseEtalePermanence
import WeilConjectures.AlgebraicGeometry.FlatOfFpqcCover
import WeilConjectures.AlgebraicGeometry.LocallyOfFinitePresentationFpqcDescent
import WeilConjectures.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFpqcCover
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Base change and fppf locality of flatness, properness and finite presentation

Source: Stacks Project, Spaces Descent, Tags 041V, 041W and 0422;
Morphisms of Spaces, Tags 03XR, 03MO and 04WP
(blueprint: lem-sfb-space-flat-proper-fp-locality).

Finite presentation is written as local finite presentation, quasi-compactness and
quasi-compactness of the relative diagonal, using the existing predicates throughout.
The property parameter selects one property at a time.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Flatness, properness and finite presentation are each preserved by arbitrary
algebraic-space base change and are each local on a scheme target for fppf coverings.
Finite presentation includes quasi-separatedness; the other two properties are never
additional assumptions on the morphism under consideration.
Source: Stacks, Spaces Descent, Tags 041V, 041W, 0422; Morphisms of Spaces,
Tags 03XR, 03MO, 04WP (blueprint: lem-sfb-space-flat-proper-fp-locality).

Proof:
1. Matching point classes of two spaces over a third have representatives agreeing
   after a common field extension. They define a point of the sheaf fibre product.
   Thus the map from its points onto the fibre product of point sets is surjective,
   and jointly surjective families remain so after base change. This uses
   def-trf-algebraic-space-jointly-surjective-family and
   lem-trf-space-fibre-products-etale-covers, without identifying these point sets.
2. For a chartwise property P among flat, locally finitely presented and locally
   finite type, choose compatible surjective etale scheme charts U → V for f.
   After any space base change choose a scheme atlas V' of the pullback of V.
   The composite V' → Y' is surjective etale by
   lem-trf-space-chartwise-etale-permanence. The compatible chart U ×_V V' → V'
   has P by the scheme base-change lemmas lem-weil-pbc-flat-morphism-base-change,
   lem-weil-pbc-qcqs-morphism-permanence and lem-weil-pbc-lft-base-change.
   The chart-test lemma lem-sfb-space-local-properties-chart-test gives P downstairs.
3. Quasi-compactness is stable under base change by
   lem-sfb-space-quasicompact-fppf-local. The new relative diagonal is the pullback
   of the old diagonal: on sections its pairs are (x, ((x,x),y')), hence (x,y').
   Quasi-compactness of the diagonal is therefore preserved, giving finite
   presentation together with step 2. The same diagonal identification preserves
   separatedness on every scheme test, and pullback associativity preserves universal
   closedness. With step 2 and quasi-compactness this gives proper base change.
4. Every scheme fppf cover is fpqc: restrict to an affine open of the target using
   lem-trf-fppf-covering-base-change, then use lem-pc-fppf-affine-refinement for
   a finite affine refinement covering that open. These are the quasi-compact
   refinements required by def-weil-pbc-fpqc-covering.
5. To descend any one of the three chartwise properties, take a scheme atlas U → X.
   Each U ×_T T_i → T_i has the property by the chart-test lemma. Apply respectively
   lem-weil-pbc-fpqc-descend-flat,
   lem-weil-pbc-fpqc-descend-locally-finite-presentation or
   lem-weil-pbc-fpqc-descend-locally-finite-type to U → T using step 4.
   The chart-test lemma then gives the corresponding property of f.
6. Quasi-compactness descends by lem-sfb-space-quasicompact-fppf-local. Apply it also
   to the relative diagonal and the flat locally finitely presented covering
   (X ×_T X) ×_T T_i → X ×_T X. The diagonal calculation of step 3 identifies its
   pullbacks with the local diagonals. This descends quasi-separatedness, and
   together with step 5 descends finite presentation.
7. For separatedness, every scheme test Z of the relative diagonal is also a test
   of the absolute representable diagonal X → X ×_S X. Indeed both pullbacks have
   sections (x,z) with both X-coordinates of z equal to x. Its source is therefore
   a scheme. Pull back Z by the fppf cover T_i → T. The resulting scheme maps are
   closed immersions by the local separatedness hypotheses. Apply
   lem-pc-fpqc-descend-closed-immersion using step 4 to conclude on Z.
8. For universal closedness take any T' → T and closed C in |X ×_T T'|. The maps
   p_i : T' ×_T T_i → T' are jointly surjective by step 1 and open by step 2 and
   lem-sfb-flat-lfp-space-universally-open. If A is the image of C, local universal
   closedness and step 1 show p_i⁻¹(A) is closed: it is exactly the image of the
   inverse image of C. The union of the open images of their complements is the
   complement of A. Thus A is closed, for every C and every T'.
9. Local properness supplies separatedness, quasi-compactness, local finite type
   and universal closedness. Steps 5–8 descend these four constituents separately.
   Steps 5–6 descend flatness and finite presentation independently. The forward
   implications are steps 2–3. Empty covers force an empty target and source;
   the empty atlases, diagonals and closed subsets satisfy the same arguments. -/
theorem flat_proper_fp_locality {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    (hP : P = @MapIsFlat S ∨ P = @MapIsProper S ∨
      P = fun _ _ f ↦ MapIsLocallyOfFinitePresentation f ∧
        MapIsQuasiCompact f.hom.hom ∧ MapIsQuasiCompact (pullback.diagonal f.hom.hom)) :
    (∀ {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y),
      P f → P (enlargedFibreProductFst g f)) ∧
    (∀ {I : Type w} (T : Over S) (X : AlgebraicSpace S) (f : X ⟶ schemeSpace T)
      (Tᵢ : I → Over S) (g : ∀ i : I, Tᵢ i ⟶ T),
      Presieve.ofArrows (fun i : I ↦ (Tᵢ i).left) (fun i : I ↦ (g i).left) ∈
        Scheme.fppfPrecoverage T.left →
      (P f ↔ ∀ i : I,
        P (enlargedFibreProductFst
          (ObjectProperty.homMk ⟨yoneda.map (g i)⟩ : schemeSpace (Tᵢ i) ⟶ schemeSpace T)
          f))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
