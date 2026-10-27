/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Pullback to a projective bundle reflects line isomorphism classes

Source: EGA II, Remark 4.2.7; Stacks, Tags 04TN, 01XS.
(blueprint: lem-sfb-projective-bundle-pullback-line-reflection)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProjectiveBundlePicardClassification

open Scheme.Modules ProjectiveBundleQuotientGeometry

/-- Isomorphic pullbacks of two base lines imply that the base lines are isomorphic.

Source: EGA II, Remark 4.2.7, printed p.75; Stacks, sheaves.tex, Tag 04TN;
coherent.tex, Tag 01XS.
(blueprint: lem-sfb-projective-bundle-pullback-line-reflection)

Proof: take a common open covering of the base trivializing both lines. The given
isomorphism is multiplication by a unit on the inverse image of each covering open.
The constant monomial calculation on affine frames of E identifies the canonical
map on functions with an isomorphism of rings. Thus each unit descends uniquely to
a unit on the base open. On overlaps the change-of-basis equations descend by
injectivity of that function map. Glue the resulting scalar maps and their inverses
to an isomorphism of the base lines. This includes empty covering opens and the
empty base, and does not require a section of the projective bundle projection. -/
theorem projective_bundle_pullback_line_reflection (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (hr : 0 < r)
    (N N' : S.Modules) (hN : N.IsInvertible) (hN' : N'.IsInvertible)
    (e : Nonempty ((tensorPullback
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).obj N ≅
        (tensorPullback (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).obj N')) :
    Nonempty (N ≅ N') := by
  sorry

end AlgebraicGeometry.ProjectiveBundlePicardClassification
