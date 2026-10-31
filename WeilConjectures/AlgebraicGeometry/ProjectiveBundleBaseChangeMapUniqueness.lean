/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleTautologicalData
import WeilConjectures.AlgebraicGeometry.ProjectiveBundlePullbackIdentitySection

/-! # Uniqueness of the normalized projective-bundle comparison map

Source: Stacks Project, Constructions, Tags 01OB and 01O3.
(blueprint: lem-pur-projective-bundle-base-change-map-uniqueness).
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- The prescribed generator equation determines the full coefficient pullback data.
Source: Stacks Project, Tags 01OB and 01O3.
Proof: coefficientwise base change fixes scalars, and the normalization fixes generators.
Symmetric induction determines each component map; proof irrelevance determines the remaining
fields of the pullback-data record.
(blueprint: lem-pur-projective-bundle-base-change-map-uniqueness). -/
theorem projectiveBundleCoefficientComparison_unique
    {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    (D : ProjectiveBundleRealization B F) (D' : ProjectiveBundleRealization B' F')
    (g : B' ⟶ B) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F)
    (a b : Scheme.GradedAlgebraData.PullbackData g D.A.data D'.A.data)
    (ha : ∀ {U : B.affineOpens} {U' : B'.affineOpens} (h : U'.1 ≤ g ⁻¹ᵁ U.1)
      (x : F.val.obj (op U.1)),
      a.map h (D.A.sectionEquiv U (SymmetricAlgebra.ι _ _ x)) =
        D'.A.sectionEquiv U' (SymmetricAlgebra.ι _ _ (e.inv.app U'.1
          (((Scheme.Modules.tensorPullback g).obj F).presheaf.map (homOfLE h).op
            (projectiveBundlePullbackSection g x)))))
    (hb : ∀ {U : B.affineOpens} {U' : B'.affineOpens} (h : U'.1 ≤ g ⁻¹ᵁ U.1)
      (x : F.val.obj (op U.1)),
      b.map h (D.A.sectionEquiv U (SymmetricAlgebra.ι _ _ x)) =
        D'.A.sectionEquiv U' (SymmetricAlgebra.ι _ _ (e.inv.app U'.1
          (((Scheme.Modules.tensorPullback g).obj F).presheaf.map (homOfLE h).op
            (projectiveBundlePullbackSection g x))))) : a = b := by
  have hm : ∀ (U' : B'.affineOpens) (U : B.affineOpens)
      (h : U'.1 ≤ g ⁻¹ᵁ U.1), a.map h = b.map h := by
    intro U' U h
    apply GradedRingHom.ext
    intro z
    obtain ⟨z, rfl⟩ := (D.A.sectionEquiv U).surjective z
    induction z using SymmetricAlgebra.induction with
    | algebraMap r =>
      rw [AlgEquiv.commutes,
        (a.isGradedBaseChangeAlong h).map_algebraMap,
        (b.isGradedBaseChangeAlong h).map_algebraMap]
    | ι m => rw [ha, hb]
    | mul x y hx hy => simp only [map_mul, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  have ext (ca cb : Scheme.GradedAlgebraData.PullbackData g D.A.data D'.A.data)
      (hfun : @ca.map = @cb.map) : ca = cb := by
    cases ca
    cases cb
    congr 1
  apply ext
  funext U' U h
  exact hm U' U h

/-- The prescribed degree-one generator equation determines the comparison map.
Source: Stacks Project, Tags 01OB and 01O3.
Proof: the coefficientwise base-change condition determines each map on scalars. The
normalization determines it on degree-one generators. Symmetric-algebra induction therefore
identifies the maps on every affine pair. Proof irrelevance identifies the remaining fields
of the pullback data, and hence their specified relative-Proj comparison maps.
(blueprint: lem-pur-projective-bundle-base-change-map-uniqueness). -/
theorem projectiveBundleBaseChangeMap_unique
    {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    {D : ProjectiveBundleRealization B F} {D' : ProjectiveBundleRealization B' F'}
    {g : B' ⟶ B} {e : F' ≅ (Scheme.Modules.tensorPullback g).obj F}
    (a b : ProjectiveBundleBaseChangeDatum D D' g e) : a.map = b.map := by
  have hc := projectiveBundleCoefficientComparison_unique D D' g e a.comparison b.comparison
    (fun h x ↦ a.generator h x) (fun h x ↦ b.generator h x)
  rw [a.map_eq, b.map_eq, hc]

/-- The comparison for the identity module pullback induces the identity Proj map.
Source: Stacks Project, Tag 01O3.
Proof: on a diagonal affine pair the normalized pullback identity fixes each generator, and
the scalar map is the identity. Symmetric-algebra induction identifies the graded map with
identity. The relative Proj chart equation then identifies the global map with identity.
(blueprint: lem-pur-projective-bundle-base-change-map-uniqueness). -/
theorem projectiveBundleBaseChangeMap_identity
    {B : Scheme.{u}} {F : B.Modules} (D : ProjectiveBundleRealization B F)
    (a : ProjectiveBundleBaseChangeDatum D D (𝟙 B)
      ((projectiveBundlePullbackId B).app F).symm) :
    a.map = 𝟙 D.A.data.relProj := by
  have hm (U : B.affineOpens) :
      a.comparison.map (U' := U) (U := U) (by simp) = GradedRingHom.id _ := by
    apply GradedRingHom.ext
    intro z
    obtain ⟨z, rfl⟩ := (D.A.sectionEquiv U).surjective z
    induction z using SymmetricAlgebra.induction with
    | algebraMap r =>
      have hid : (𝟙 B : B ⟶ B).appLE U.1 U.1 (by simp) = 𝟙 _ :=
        (Scheme.Hom.appLE_eq_app (𝟙 B)).trans (Scheme.Hom.id_app U.1)
      calc
        _ = a.comparison.map (U' := U) (U := U) (by simp)
            (algebraMap Γ(B, U.1) _ r) :=
          congrArg (a.comparison.map (U' := U) (U := U) (by simp))
            ((D.A.sectionEquiv U).commutes r)
        _ = algebraMap Γ(B, U.1) _ ((𝟙 B : B ⟶ B).appLE U.1 U.1 (by simp) r) :=
          (a.comparison.isGradedBaseChangeAlong (U' := U) (U := U) (by simp)).map_algebraMap r
        _ = algebraMap Γ(B, U.1) _ r := congrArg (algebraMap Γ(B, U.1) _)
          (congrArg (fun k : Γ(B, U.1) ⟶ Γ(B, U.1) ↦ k r) hid)
        _ = _ := ((D.A.sectionEquiv U).commutes r).symm
    | ι m =>
      change a.comparison.map (U' := U) (U := U) (by simp)
        (D.A.sectionEquiv U (SymmetricAlgebra.ι _ _ m)) =
          D.A.sectionEquiv U (SymmetricAlgebra.ι _ _ m)
      have h := a.generator (U := U) (U' := U) (by simp) m
      have hr : ((Scheme.Modules.tensorPullback (𝟙 B)).obj F).presheaf.map
          (homOfLE (show U.1 ≤ (𝟙 B) ⁻¹ᵁ U.1 by simp)).op
          (projectiveBundlePullbackSection (𝟙 B) m) =
          projectiveBundlePullbackSection (𝟙 B) m := by
        exact CategoryTheory.Functor.map_id_apply _ _ _
      exact h.trans (congrArg (fun t ↦ D.A.sectionEquiv U (SymmetricAlgebra.ι _ _ t))
        ((congrArg (fun t ↦ ((projectiveBundlePullbackId B).hom.app F).app U.1 t) hr).trans
          (projectiveBundlePullbackId_section B F U.1 m)))
    | mul x y hx hy => simp only [map_mul, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [a.map_eq]
  refine CategoryTheory.Limits.colimit.hom_ext fun U ↦ ?_
  change D.A.data.relProjι U ≫ _ = D.A.data.relProjι U ≫ _
  rw [a.comparison.relProjι_relProjComparison (U' := U) (U := U) (by simp),
    Category.comp_id, Scheme.GradedAlgebraData.PullbackData.localComparison]
  rw [Proj.map_congr (hm U) _ (by simp), Proj.map_id, Category.id_comp]

end AlgebraicGeometry
