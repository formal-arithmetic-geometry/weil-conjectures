/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.FlatSmoothPointBaseChange

/-!
# The smooth locus of a flat algebraic-space family

Source: Stacks Project, Morphisms, Tags 02V4(1) and 01V9; Morphisms of Spaces,
Tag 0DZI (blueprint: lem-sfb-flat-space-smooth-locus).

Smoothness on an open subspace is tested on its representable étale scheme charts.
Base changes are specified by their cartesian squares, so the statement applies to
any realization of the fibre product, with its specified projections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A flat locally finitely presented algebraic-space family has a largest smooth open,
and this open commutes with arbitrary scheme base change. The base-changed family is
smooth exactly when the inverse image of the complement of the original open is empty.

Source: Stacks Project, Morphisms, Tags 02V4(1) and 01V9; Morphisms of Spaces,
Tag 0DZI (blueprint: lem-sfb-flat-space-smooth-locus).

Proof:
1. Choose a representable surjective étale scheme atlas U of X
   (def-trf-algebraic-space). The composite U → T is flat and locally finitely
   presented by the chart hypotheses. Take the union V of its smooth open
   neighbourhoods. By lem-weil-pbc-smooth-local-on-source its restriction to V
   is smooth, also if V is empty. The map V → X is representable étale by
   lem-weil-pbc-etale-composition-cancellation. By lem-a1-space-etale-open-image
   its image is an open subspace W, covered surjectively and étale by V.
2. For any étale scheme chart Z → W, the fibre product P = Z ×_W V is a scheme
   and P → Z is surjective étale, by lem-trf-space-fibre-products-etale-covers.
   The pointwise clause of lem-trf-etale-source-smoothness makes P → T smooth
   near every point; lem-weil-pbc-smooth-local-on-source makes it smooth.
   The covering clause of lem-trf-etale-source-smoothness gives Z → T smooth.
   This is exactly the displayed chart test for the restriction to W.
3. Any smooth open B of X pulls back to a smooth open of U, hence lies in V.
   The surjective étale cover U ×_X B → B therefore gives containment of its
   point image in that of W. By lem-a1-space-point-open-calculus this is B ≤ W.
   The construction and maximality argument apply also after base change.
4. For any h : T' → T, the pullback U' = U ×_T T' is an atlas of X', by
   lem-trf-space-fibre-products-etale-covers and pullback associativity.
   The smooth locus of U' → T' is the inverse image of V by
   lem-sfb-scheme-flat-smooth-point-base-change, with no flatness assumption on h.
   By lem-a1-space-etale-open-image, the image open of this pulled-back atlas
   restriction is the subfunctor preimage of W. Thus it is the largest smooth
   open W' of X', with the literal equality of subfunctors stated below.
5. The complement of its point image is the inverse image of the complement of
   the point image of W (lem-a1-space-point-open-calculus). This is empty iff
   W' has full point image, hence equals X'. Maximality and smoothness of W'
   identify this with smoothness of the whole base-changed map. Empty sources
   and empty base changes are included. No properness or dimension bound is used. -/
theorem exists_smooth_open_of_flat_locallyOfFinitePresentation
    {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Over S)
    (f : X.obj.obj ⟶ yoneda.obj T)
    (hf : MapToSchemeIsLocally (@Flat) X T f)
    (hfp : MapToSchemeIsLocally (@LocallyOfFinitePresentation) X T f) :
    ∃ W : OpenSubspace X,
      (∀ (U : Over S) (a : yoneda.obj U ⟶ W.val.toFunctor), IsEtale a →
        Smooth (yoneda.preimage (a ≫ W.val.ι ≫ f)).left) ∧
      (∀ B : OpenSubspace X,
        (∀ (U : Over S) (a : yoneda.obj U ⟶ B.val.toFunctor), IsEtale a →
          Smooth (yoneda.preimage (a ≫ B.val.ι ≫ f)).left) → B ≤ W) ∧
      ∀ (T' : Over S) (h : T' ⟶ T) (X' : AlgebraicSpace S) (p : X' ⟶ X)
        (f' : X'.obj.obj ⟶ yoneda.obj T'),
        IsPullback p.hom.hom f' f (yoneda.map h) →
        ∃ W' : OpenSubspace X',
          W'.val = W.val.preimage p.hom.hom ∧
          (∀ (U : Over S) (a : yoneda.obj U ⟶ W'.val.toFunctor), IsEtale a →
            Smooth (yoneda.preimage (a ≫ W'.val.ι ≫ f')).left) ∧
          (∀ B : OpenSubspace X',
            (∀ (U : Over S) (a : yoneda.obj U ⟶ B.val.toFunctor), IsEtale a →
              Smooth (yoneda.preimage (a ≫ B.val.ι ≫ f')).left) → B ≤ W') ∧
          (MapToSchemeIsLocally (@Smooth) X' T' f' ↔
            mapPoint p.hom.hom ⁻¹' (pointImage W.val.ι)ᶜ = ∅) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
