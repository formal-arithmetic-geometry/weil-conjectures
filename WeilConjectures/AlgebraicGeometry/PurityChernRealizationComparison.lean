/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleCoefficientComparison
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleBaseChangeTheta

/-! # Normalized comparison of two projective-bundle realizations

Source: Stacks Project, Tags 01OB, 01O3 and 01NR; the projective-bundle definition
of ordinary Chern classes in localized-top-Chern Step 4 (L4).
(blueprint: lem-pur-chern-realization-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry

/-- Two normalized realizations of the same symmetric algebra have a normalized
base-change comparison over the identity, whose scheme map is an isomorphism.
The comparison includes the actual degree-one twist and quotient equation.
Source: Stacks Tags 01OB, 01O3 and 01NR.
Proof: apply the normalized coefficient-comparison construction to the identity
base map and the canonical module pullback identity. The twist-comparison theorem
supplies its degree-one isomorphism and quotient square. These are exactly the
fields of ProjectiveBundleBaseChangeDatum. Its scheme square is a pullback of the
identity, hence its top map is an isomorphism. The construction applies over the
empty scheme as well; finite rank and positive rank are unnecessary here.
(blueprint: lem-pur-chern-realization-comparison). -/
theorem exists_projectiveBundleRealizationComparison {T : Scheme.{u}} {F : T.Modules}
    [F.IsQuasicoherent] (D D' : ProjectiveBundleRealization T F) :
    ∃ c : ProjectiveBundleBaseChangeDatum D D' (𝟙 T)
      ((projectiveBundlePullbackId T).app F).symm, IsIso c.map := by
  obtain ⟨b, hb⟩ := exists_projectiveBundleCoefficientComparison
    (F := F) (F' := F) (𝟙 T)
    ((projectiveBundlePullbackId T).app F).symm D.A D'.A
  obtain ⟨theta, htheta⟩ := exists_projectiveBundleBaseChangeTheta D D' (𝟙 T)
    ((projectiveBundlePullbackId T).app F).symm b hb
  let c : ProjectiveBundleBaseChangeDatum D D' (𝟙 T)
      ((projectiveBundlePullbackId T).app F).symm :=
    { comparison := b
      generator := fun h x ↦ hb _ _ h x
      map := b.relProjComparison
      map_eq := rfl
      over := b.isPullback.w
      theta := theta
      theta_quotient := htheta }
  exact ⟨c, b.isPullback.isIso_fst_of_isIso⟩

end AlgebraicGeometry
