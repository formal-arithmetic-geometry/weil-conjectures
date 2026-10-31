/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius

/-! # Projective-line squares over opens of a geometric fiber -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- An arbitrary base change of the geometric relative projective line is the relative
projective line of that base.
Source: current blueprint, `thm-amb-p1-decomposition.proof.md`, base change to the base.
(blueprint: lem-pur-projective-line-geometric-base-change).

Proof: both the geometric fiber of the relative projective line and the relative
projective line of the geometric fiber are pullbacks of the original projection along
the geometric-fiber projection. Uniqueness of pullbacks identifies them over the base.
Paste this isomorphism square with the ordinary projective-space base-change square.
The resulting square is cartesian, including over empty bases.
-/
theorem exists_projectiveLine_geometric_baseChange
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    {U : Scheme.{u}} (j : U ⟶ (X ↘ Spec (.of k)).geometricFiber) :
    ∃ a : ProjectiveLine U ⟶ (ProjectiveLine X ↘ Spec (.of k)).geometricFiber,
      IsPullback (ProjectiveLine U ↘ U) a j
        (Scheme.Hom.geometricFiberMap (ProjectiveLine X ↘ X)
          (comp_over (ProjectiveLine X ↘ X) (Spec (.of k)))) := by
  let f := X ↘ Spec (.of k)
  let q := ProjectiveLine X ↘ X
  let h := comp_over q (Spec (.of k))
  let qb := Scheme.Hom.geometricFiberMap q h
  let hp := ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) f.geometricFiberProj
  let hg := (Scheme.Hom.isPullback_geometricFiberMap q h).flip
  let e := hp.isoIsPullback _ _ hg
  have he : e.hom ≫ qb = (ProjectiveLine f.geometricFiber ↘ f.geometricFiber) :=
    hp.isoIsPullback_hom_snd _ _ hg
  have hi : IsPullback e.hom (ProjectiveLine f.geometricFiber ↘ f.geometricFiber)
      qb (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simpa using he⟩
  refine ⟨ProjectiveSpace.map (ULift.{u} (Fin 2)) j ≫ e.hom, ?_⟩
  have hs := ((ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) j).paste_horiz hi).flip
  change IsPullback (ProjectiveLine U ↘ U)
    (ProjectiveSpace.map (ULift.{u} (Fin 2)) j ≫ e.hom) (j ≫ 𝟙 _) qb at hs
  rw [Category.comp_id] at hs
  exact hs

end AlgebraicGeometry
