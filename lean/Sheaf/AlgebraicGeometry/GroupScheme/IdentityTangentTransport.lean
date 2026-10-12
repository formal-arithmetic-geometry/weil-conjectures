/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
public import Sheaf.AlgebraicGeometry.SchemeTangentSpace
import Sheaf.AlgebraicGeometry.GroupScheme.LieCotangentDualResidue

/-!
# Transport of infinitesimal points to tangent vectors at the identity

Source: blueprint `sk-d-tangent` and the identity tangent-space argument of
`lem-wf-same-lie-closed-subgroup` (blueprint: lem-ag-identity-tangent-transport).
-/

@[expose] public section

universe u
open CategoryTheory
open scoped MonObj
namespace AlgebraicGeometry.GrpObj

set_option backward.isDefEq.respectTransparency false in
/-- Transport both coefficients by the structural identity residue map.
Source: blueprint `sk-d-tangent`, and `lem-wf-same-lie-closed-subgroup`, Dimension paragraph.
(blueprint: lem-ag-identity-tangent-transport)

Proof: Let `a` be the structural residue map. `identity_residue_rational` proves that
it is bijective and that `Spec.map a` followed by the unit section is the canonical
residue point. The functor `CommRingCat.dualNumber` sends its ring isomorphism to an
isomorphism of dual-number rings. Precompose the point supplied by
`infPointsEquivTangentGroup` with the spectrum of this isomorphism. Naturality of
`dualNumberFst` gives the closed-point condition. Naturality of `dualNumberInl`, the
over-morphism equation, and `unitSection_comp_hom` give the base condition.
Conversely precompose a tangent vector by the inverse dual-number isomorphism.
The same naturality equations give an over-morphism reducing to the unit section,
hence an element of `tangentGroup G`. Apply `infPointsEquivTangentGroup.symm`.
Both composites are identities by the two isomorphism cancellation equations.
This is only an equivalence of types; no compatibility with addition is asserted. -/
theorem exists_identity_tangent_transport
    {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] :
    let x := unitSection G (IsLocalRing.closedPoint k)
    let r : k →+* G.left.residueField x :=
      (StructureSheaf.toStalk k (G.hom x) ≫ G.hom.stalkMap x ≫ G.left.residue x).hom
    ∃ e : infPoints G ≃ schemeTangentSpace k G.left G.hom x,
      ∀ v : infPoints G, (e v).val =
        Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom r)) ≫
          (infPointsEquivTangentGroup G v).val.left := by
  let x := unitSection G (IsLocalRing.closedPoint k)
  let K := G.left.residueField x
  let a : CommRingCat.of k ⟶ K :=
    StructureSheaf.toStalk k (G.hom x) ≫ G.hom.stalkMap x ≫ G.left.residue x
  obtain ⟨ha, he⟩ := identity_residue_rational G
  change Function.Bijective a.hom at ha
  change Spec.map a ≫ unitSection G = G.left.fromSpecResidueField x at he
  let ae := (RingEquiv.ofBijective a.hom ha).toCommRingCatIso
  have : IsIso a := by
    change IsIso ae.hom
    infer_instance
  let b := Spec.map a
  let d := Spec.map (CommRingCat.dualNumber.map a)
  let ck := Spec.map (CommRingCat.dualNumberFst.app (.of k))
  let cK := Spec.map (CommRingCat.dualNumberFst.app K)
  let qk := Spec.map (CommRingCat.dualNumberInl.app (.of k))
  let qK := Spec.map (CommRingCat.dualNumberInl.app K)
  have : IsIso b := by dsimp [b]; infer_instance
  have : IsIso d := by dsimp [d]; infer_instance
  have hc : cK ≫ d = b ≫ ck := by
    dsimp only [cK, ck, b, d]
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.dualNumberFst.naturality a)
  have hq : d ≫ qk = qK ≫ b := by
    dsimp only [qK, qk, b, d]
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.dualNumberInl.naturality a).symm
  have hp : G.left.fromSpecResidueField x ≫ G.hom = b := by
    rw [← he, Category.assoc, unitSection_comp_hom, Category.comp_id]
  have h1 : (1 : points G k).left = unitSection G := by
    change Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ unitSection G = _
    change Spec.map (𝟙 (CommRingCat.of k)) ≫ unitSection G = _
    rw [Spec.map_id, Category.id_comp]
  have ht (v : tangentGroup G) : ck ≫ v.val.left = unitSection G := by
    have h := congrArg (fun f ↦ f.left) ((mem_tangentGroup G).1 v.property)
    change ck ≫ v.val.left = (1 : points G k).left at h
    exact h.trans h1
  let f : tangentGroup G → schemeTangentSpace k G.left G.hom x := fun v ↦
    ⟨d ≫ v.val.left, by
      constructor
      · change cK ≫ d ≫ v.val.left = _
        rw [← Category.assoc, hc, Category.assoc, ht v]
        exact he
      · change (d ≫ v.val.left) ≫ G.hom = qK ≫ _ ≫ G.hom
        rw [Category.assoc, Over.w, hp]
        exact hq⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w h
      apply Subtype.ext
      apply Over.OverMorphism.ext
      exact (cancel_epi d).1 (congrArg Subtype.val h)
    · intro θ
      let v : points G (DualNumber k) := Over.homMk (inv d ≫ θ.val) (by
        change (inv d ≫ θ.val) ≫ G.hom = qk
        have hθ : θ.val ≫ G.hom = qK ≫ G.left.fromSpecResidueField x ≫ G.hom :=
          θ.property.2
        rw [Category.assoc, hθ, hp, ← hq]
        simp only [IsIso.inv_hom_id_assoc])
      have hv : v ∈ tangentGroup G := by
        rw [mem_tangentGroup]
        apply Over.OverMorphism.ext
        change ck ≫ inv d ≫ θ.val = (1 : points G k).left
        have hc' : ck ≫ inv d = inv b ≫ cK := by
          apply (cancel_epi b).1
          rw [IsIso.hom_inv_id_assoc, ← Category.assoc, ← hc]
          simp
        have hθ : cK ≫ θ.val = G.left.fromSpecResidueField x := θ.property.1
        rw [← Category.assoc, hc', Category.assoc, hθ, ← he]
        rw [h1]
        change inv b ≫ b ≫ unitSection G = unitSection G
        simp only [IsIso.inv_hom_id_assoc]
      refine ⟨⟨v, hv⟩, ?_⟩
      apply Subtype.ext
      change d ≫ inv d ≫ θ.val = θ.val
      simp only [IsIso.hom_inv_id_assoc]
  let e := (infPointsEquivTangentGroup G).toEquiv.trans (Equiv.ofBijective f hf)
  exact ⟨e, fun _ ↦ rfl⟩

end AlgebraicGeometry.GrpObj
