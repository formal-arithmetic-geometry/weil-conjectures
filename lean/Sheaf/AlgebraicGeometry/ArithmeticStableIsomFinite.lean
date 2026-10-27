/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.StableFiberCurve
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Comma.Over.Pullback

import Sheaf.AlgebraicGeometry.StablePointedCurve
import Mathlib.CategoryTheory.Yoneda
import Sheaf.AlgebraicGeometry.CurveLimitPreservation
import Sheaf.AlgebraicGeometry.NoetherianDvrProperness
import Sheaf.AlgebraicGeometry.SchemeUnramifiedEtaleLocality
import Sheaf.TraceFormula.ProjectiveBundleProper
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Arithmetic finite unramified Isom schemes for stable curves

Source: Stacks Project, moduli-curves.tex, Tags 0DSQ, 0E7A and 0E9A;
spaces-morphisms.tex, Tag 0418; spaces-more-morphisms.tex, Tag 0A4X
(blueprint: lem-sfb-arithmetic-stable-isom-finite).

The universal-element formulation gives representing bijections on all test schemes.
The displayed equation is precisely pullback of the universal isomorphism, expressed
using its projection to the original target curve. Uniqueness gives naturality under
all base changes, and the pullback of the representative represents the changed functor.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.StablePointedModuli

/-- Stable unpointed genus-`g` families over any scheme have a finite unramified
Isom scheme with its universal isomorphism, natural on every test scheme.
Source: Stacks Project, Tags 0DSQ, 0E7A, 0E9A, 0418 and 0A4X
(blueprint: lem-sfb-arithmetic-stable-isom-finite).

Proof:
1. Cover the base by affine opens. The projective stable families are proper
   (`lem-trf-projective-bundle-proper`) and flat finitely presented curves
   (`def-sfb-stable-pointed-curve`). Express each affine base as the small directed
   limit of finite-type integer stages (`lemma-nagata-noetherian-inverse-system-affine`).
   Descend both families and their pullback identifications to a common stage using
   `lem-sfb-curve-limit-preservation`.
2. Restrict the stage to the intersection of the stable genus-`g` opens supplied by
   `lem-sfb-arithmetic-stable-open-bounded`. The original base factors through this
   intersection. This stage is locally Noetherian by
   `lem-weil-pbc-finite-type-over-noetherian` and `pqf-def-locnoeth`.
3. Apply `lem-sfb-labelled-stable-isom-unramified` with zero labels. Its separated
   finite-type unramified Isom scheme satisfies unique lifting for every DVR square:
   the generic isomorphism extends uniquely by `lem-sfb-stable-labelled-isom-trait-extension`.
   Naturality identifies this extension with the required lift. Apply
   `lem-sfb-noetherian-dvr-properness` to get properness.
4. Unramified implies locally quasi-finite by
   `lem-weil-pbc-unramified-quasi-finite-at-points`. Proper plus locally quasi-finite
   is finite (`pqf-lem-proper-lqf-finite`). Pull back to the original affine open;
   `lem-weil-pbc-finite-morphism-permanence` and
   `lem-weil-pbc-unramified-base-change-open` preserve these properties.
5. The fibre-product universal property (`def-pc-fibre-product`) and the stage's
   representing bijections identify this pullback with the Isom functor on every
   test scheme. Conjugate by the chosen identifications of descended families.
6. On overlaps use `lem-galois-yoneda-fully-faithful` to get the unique transition
   isomorphisms; faithfulness gives the cocycle. Glue the schemes with
   `lem-weil-pbc-glue-schemes` and their structure maps with
   `lem-weil-pbc-scheme-morphism-gluing`.
7. For any test scheme, pull back the affine cover, glue local curve maps and their
   inverses (`lem-weil-pbc-scheme-morphism-gluing`), and use local uniqueness to
   identify both composites with identities. Conversely glue the local parameter
   maps. These operations are inverse and natural by uniqueness, including on
   disconnected and nonreduced tests.
8. Finiteness is local on the target (`lem-weil-pbc-finite-local-on-target`).
   Unramifiedness follows from `lem-sfb-scheme-unramified-etale-locality` using
   open charts and `lem-weil-pbc-open-immersion-etale`. Fibre-product universality
   identifies the pulled-back representative after every base change. Evaluate at
   its identity to obtain the universal isomorphism; naturality says every
   represented isomorphism is its pullback. The empty base uses the empty cover.
-/
theorem arithmetic_stable_isom_finite (T : Scheme.{u}) (g : ℕ) (hg : 2 ≤ g)
    (C D : Fiber T g 0 (Over.mk (𝟙 T))) :
    ∃ I : Over T, IsFinite I.hom ∧ IsUnramified I.hom ∧
      ∃ e : (Over.pullback I.hom).obj (fiberCurve C) ≅
        (Over.pullback I.hom).obj (fiberCurve D),
        ∀ (V : Over T)
          (eV : (Over.pullback V.hom).obj (fiberCurve C) ≅
            (Over.pullback V.hom).obj (fiberCurve D)),
          ∃! b : V ⟶ I,
            eV.hom.left ≫ pullback.fst (fiberCurve D).hom V.hom =
              pullback.map (fiberCurve C).hom V.hom (fiberCurve C).hom I.hom
                (𝟙 _) b.left (𝟙 _)
                ((Category.comp_id _).trans (Category.id_comp _).symm)
                ((Category.comp_id _).trans (Over.w b).symm) ≫
                  e.hom.left ≫ pullback.fst (fiberCurve D).hom I.hom := by
  sorry

end AlgebraicGeometry.StablePointedModuli
