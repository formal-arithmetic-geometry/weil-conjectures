/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-! # Coefficients for quotient images of a common source section
(blueprint: lem-pur-projective-bundle-realization-pullback-atlas-coefficients).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- Equal cross tensors give equal coefficients against a common quotient generator.

Source: Stacks Project, Tags 01NR and 01OB.
(blueprint: lem-pur-projective-bundle-realization-pullback-atlas-coefficients).

Proof: extract the coefficient using the first free generator. Tensoring with that generator
is injective, and the cross-tensor identity gives the same coefficient for the second map.
The two frames are images of the same section m; independent rescaling is therefore excluded. -/
theorem exists_projectiveBundleRealizationPullbackAtlas_coefficients
    {T : Scheme.{u}} {M P Q : T.Modules} (q : M ⟶ P) (q' : M ⟶ Q)
    (hcross : ∀ (V : T.Opens) (m n : Γ(M, V)),
      Scheme.Modules.tmulSection (q.app V m) (q'.app V n) =
        Scheme.Modules.tmulSection (q.app V n) (q'.app V m))
    {U : T.Opens} (m : Γ(M, U)) (hm : Scheme.Modules.IsFreeGenerator (q.app U m))
    (V : T.Opens) (hV : V ≤ U) (n : Γ(M, V)) :
    ∃ c : Γ(T, V), q.app V n = c • P.presheaf.map (homOfLE hV).op (q.app U m) ∧
      q'.app V n = c • Q.presheaf.map (homOfLE hV).op (q'.app U m) := by
  obtain ⟨c, hc⟩ := (hm.map hV).exists_smul_eq (q.app V n)
  refine ⟨c, hc.symm, ?_⟩
  apply (hm.bijective_tmulSection_left hV).injective
  dsimp only
  rw [Scheme.Modules.tmulSection_smul, ← Scheme.Modules.smul_tmulSection, hc]
  have h := hcross V (M.presheaf.map (homOfLE hV).op m) n
  simpa only [Scheme.Modules.Hom.app_presheaf_map] using h

end AlgebraicGeometry
