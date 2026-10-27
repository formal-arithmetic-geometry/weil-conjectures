/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.ProjectiveBundleTrivialLineGluing

/-!
# Descent of relatively trivial modules on projective bundles

Source: EGA II, Remark 4.2.7; Stacks, Tags 00AL, 00AM, 01XS.
(blueprint: lem-sfb-projective-bundle-relatively-trivial-line-descent)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProjectiveBundlePicardClassification

open Scheme.Modules ProjectiveBundleQuotientGeometry

/-- A module trivial above a base neighbourhood of every point descends to a base line.

Source: EGA II, Remark 4.2.7, printed p.75; Stacks, sheaves.tex, Tags 00AL, 00AM,
04TN; coherent.tex, Tag 01XS.
(blueprint: lem-sfb-projective-bundle-relatively-trivial-line-descent)

Proof: choose the displayed neighbourhoods and trivializations. On each overlap the
change of basis is a unit section on the projective bundle. The canonical map from
base functions to functions on the bundle is an isomorphism: on affine opens
trivializing E, the constant monomial computation gives H^0(P^(r-1), O) = R,
with the identification induced by the structure map; restrictions agree and the
local identifications glue on arbitrary base opens. Descend each transition unit
uniquely through this ring isomorphism. The cocycle equations descend by injectivity.
Glue the trivial base modules using these units to obtain an invertible N. The
chosen local trivializations agree with the pulled-back transitions, so they and
their inverses glue to an isomorphism F = p^*N. On the empty base the empty covering
and its unique glued maps apply. No quasi-compactness or reducedness is used. -/
theorem projective_bundle_relatively_trivial_line_descent (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (hr : 0 < r)
    (F : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Modules)
    (hF : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      Nonempty ((tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U).ι).obj F ≅
          𝟙_ (((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U).toScheme.Modules))) :
    ∃ N : S.Modules, N.IsInvertible ∧
      Nonempty (F ≅ (tensorPullback
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).obj N) := by
  sorry

end AlgebraicGeometry.ProjectiveBundlePicardClassification
