/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FiniteApproximation
public import WeilConjectures.Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism

/-!
# Descent of the normalization immersion to a finite stage

Source: the blueprint, sec-nagata-compactification, sk-prop-nagata-sketch-zmt,
node thm-pqf-immersion-descent; Stacks Project, Tags 01Z4, 081B, 01QV, 05K0
(blueprint: thm-pqf-immersion-descent).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- The canonical immersion into the relative normalization descends to a finite stage
(blueprint: thm-pqf-immersion-descent), with the factorization equation and the locally
Noetherian finite-presentation refinement. Source: the blueprint's Steps 1--4; Stacks
Project, Tags 01Z4, 081B, 01QV, 05K0.

Proof:
1. The finite approximation of `f.fromNormalization` is the presentation supplied by
   lem-weil-pbc-integral-morphism-limit-of-finite. Its finite stages are qcqs over the qcqs
   base (lem-weil-pbc-qcqs-morphism-permanence). The canonical map `f.toNormalization`
   is a quasi-compact open immersion (pqf-lem-normalization-open), and `X` is compact
   because `f` is quasi-compact over compact `S`. Descend its compact open image to a stage
   and identify that image with the limit of the inverse-image opens
   (pqf-lem-limit-qc-open-descends, Stacks 01Z4).
2. The isomorphism from `X` onto this image is a closed immersion into that limit.
   Since `X` is locally of finite type over `S`, its projection into one of the descended
   opens is a closed immersion (pqf-lem-limit-immersion-descends, Stacks 081B).
3. The composite into the finite stage is a quasi-compact immersion. Factor it as an open
   immersion followed by a closed immersion (lem-pqf-qc-immersion-open-closed-factor,
   Stacks 01QV). The intermediate scheme is quasi-separated, so the open immersion from
   compact `X` is quasi-compact (lem-weil-pbc-qcqs-morphism-permanence). This factorization
   preserves the original projection, giving the displayed equation.
4. Over locally Noetherian `S`, a finite stage is of finite presentation
   (pqf-lem-finite-fp-locnoeth). Finite morphisms are already quasi-compact and
   quasi-separated, so only local finite presentation remains in the final clause. -/
theorem exists_normalization_immersion_at_finite_stage
    {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hf : f.IsLocallyQuasiFinite) [CompactSpace S] [QuasiSeparatedSpace S]
    (F : f.fromNormalization.FiniteApproximation) :
    ∃ (l₀ : F.I) (T : AlgebraicGeometry.Scheme.{u}) (j : X ⟶ T)
      (i : T ⟶ F.D.obj l₀),
      IsOpenImmersion j ∧ QuasiCompact j ∧ IsClosedImmersion i ∧
      j ≫ i = f.toNormalization ≫ F.π.app l₀ ∧
      (IsLocallyNoetherian S → LocallyOfFinitePresentation (F.p l₀)) := by
  sorry

end AlgebraicGeometry.Scheme.Hom
