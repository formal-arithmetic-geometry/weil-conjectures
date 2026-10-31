/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ProperBaseChange.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit

import WeilConjectures.AlgebraicGeometry.ClosedImmersionIdealTensorSections
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ProperBaseChange.ProjectiveSpaceHomOfGeneratingSections
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.Modules.HomSection
import WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism

@[expose] public section

/-!
# Sections vanishing on a closed subscheme

Source: Stacks Project, varieties.tex, Tag 0FD5, lemma-generate-over-complement
(blueprint: lem-zl-bertini-sections).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

open Scheme.Modules MonoidalCategory Opposite

-- Cache the site instances used repeatedly by free sheaves in this proof.
attribute [local instance] cachedSheafify cachedWEquals

private theorem finite_sections (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (M : X.Modules) [M.IsInvertible] :
    letI : Module k Γ(M, ⊤) := Module.compHom _ (Scheme.globalSectionsRingHom (X := X) k)
    FiniteDimensional k Γ(M, ⊤) := by
  let : Module k Γ(M, ⊤) := Module.compHom _ (Scheme.globalSectionsRingHom (X := X) k)
  have := IsInvertible.sheafOfModules_isInvertible M
  have := finiteDimensional_H_of_isProper M 0 (k := k)
  let e : M.H 0 ≃ₗ[k] Γ(M, ⊤) :=
    { H.zeroLinearEquiv M with
      map_smul' a x := (H.zeroLinearEquiv M).map_smul
        (Scheme.globalSectionsRingHom (X := X) k a) x }
  exact FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end AlgebraicGeometry
