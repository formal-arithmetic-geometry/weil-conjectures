/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.AlgebraicGeometry.StandardSingleBaseChangeMap
import Sheaf.AlgebraicGeometry.RelativeMVCoverHomotopyData
import Sheaf.AlgebraicGeometry.StandardSingleOpenRelativeArrow

/-! # Homotopy representatives of the resolved cover comparison -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private lemma transport_arrow_comparison
    {E : Type*} [Category E] {X X' : E} {a b : Arrow E}
    (k : X ⟶ X') (e : X ≅ a.left) (e' : X' ≅ a.right)
    (h : k ≫ e'.hom = e.hom ≫ a.hom) (s : a ≅ b) :
    k ≫ (e' ≪≫ Arrow.rightFunc.mapIso s).hom =
      (e ≪≫ Arrow.leftFunc.mapIso s).hom ≫ b.hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  change k ≫ e'.hom ≫ s.hom.right = (e.hom ≫ s.hom.left) ≫ b.hom
  rw [← Category.assoc, h, Category.assoc, ← Arrow.w, ← Category.assoc]

private noncomputable def biprod_arrow_iso
    {E : Type*} [Category E] [Preadditive E] [HasBinaryBiproducts E]
    {a b c d : Arrow E} (s : a ≅ c) (r : b ≅ d) :
    Arrow.mk (biprod.map a.hom b.hom) ≅ Arrow.mk (biprod.map c.hom d.hom) :=
  Arrow.isoMk (biprod.mapIso (Arrow.leftFunc.mapIso s) (Arrow.leftFunc.mapIso r))
    (biprod.mapIso (Arrow.rightFunc.mapIso s) (Arrow.rightFunc.mapIso r)) (by
      change biprod.map s.hom.left r.hom.left ≫ biprod.map c.hom d.hom =
        biprod.map a.hom b.hom ≫ biprod.map s.hom.right r.hom.right
      apply biprod.hom_ext
      · simpa only [Category.assoc, biprod.map_fst, biprod.map_fst_assoc] using
          congrArg (fun k ↦ (biprod.fst : a.left ⊞ b.left ⟶ a.left) ≫ k) (Arrow.w s.hom)
      · simpa only [Category.assoc, biprod.map_snd, biprod.map_snd_assoc] using
          congrArg (fun k ↦ (biprod.snd : a.left ⊞ b.left ⟶ b.left) ≫ k) (Arrow.w r.hom))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- The cover and coefficient comparisons involve several transported derived functors.
/-- The resolved cover comparison before cylinder rectification.
Source: Stacks Project, Tags 08BV, 08HZ, 08FE, 08HY and 0DJ9.
(blueprint: lem-pc-standard-single-union-homotopy-chain-data).

Proof: Put W = U union V and pull its cover back to W_A. Resolve N[0] and
its ordinary pullback by functorial injective-term K-injective complexes. The
restriction-pair and restriction-difference rows are exact: sheaf gluing gives
the kernel, and injectivity gives the surjection onto the overlap. Apply the
relative direct-image computation to these rows. Resolve the source diagram
K-flatly before applying derived pullback, keeping the restriction maps and
the homotopies of the finite diagram. The derived-to-ordinary pullback counit,
transposed under the pullback/direct-image adjunction, induces the comparison
of the two resolved diagrams. Naturality of the restriction units and the
underived open counit square supply a specified homotopy H of its first square.
The induced cone map is mapOfHomotopy H: the homotopy term must be retained,
rather than choosing an arbitrary third map between distinguished triangles.
Identify the six objects using the short exact rows, direct-image composition,
exact open restriction and the additive biproduct comparison. Expand the
single-module comparison as the base-change mate followed by the single
pullback counit. Pasting counits and the adjunction triangle identities gives
the three displayed equations, including the equation for mapOfHomotopy H.
No cylinder rectification is done here. Empty opens and zero coefficients
produce zero rows; repeated or contained opens produce split rows. These
constructions therefore require neither flatness nor quasi-coherence. -/
theorem standardSingle_union_homotopy_chain_data
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (g : A ⟶ B) (U V : Y.Opens)
    (N : (U ⊔ V).toScheme.Modules) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let a := Arrow.mk (standardSingleBaseChangeMap ((U ⊔ V).ι ≫ p) N g)
    let aU := Arrow.mk (standardSingleBaseChangeMap (U.ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE le_sup_left) N) g)
    let aV := Arrow.mk (standardSingleBaseChangeMap (V.ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE le_sup_right) N) g)
    let aUV := Arrow.mk (standardSingleBaseChangeMap ((U ⊓ V).ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE (inf_le_left.trans le_sup_left)) N) g)
    ∃ (C D C' D' : CochainComplex
        (SheafOfModules.{u} (moduleRings A.toRingedSpace)) ℤ)
      (t : C ⟶ D) (t' : C' ⟶ D') (α : C ⟶ C') (β : D ⟶ D'),
      ∃ (H : Homotopy (t ≫ β) (α ≫ t'))
        (e₁ : DerivedCategory.Q.obj C ≅ a.left)
        (e₂ : DerivedCategory.Q.obj D ≅ aU.left ⊞ aV.left)
        (e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅ aUV.left)
        (e₁' : DerivedCategory.Q.obj C' ≅ a.right)
        (e₂' : DerivedCategory.Q.obj D' ≅ aU.right ⊞ aV.right)
        (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅ aUV.right),
        DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
        DerivedCategory.Q.map β ≫ e₂'.hom = e₂.hom ≫ biprod.map aU.hom aV.hom ∧
        DerivedCategory.Q.map (CochainComplex.mappingCone.mapOfHomotopy H) ≫ e₃'.hom =
          e₃.hom ≫ aUV.hom := by
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let W := U ⊔ V
  let f := W.ι ≫ p
  let K := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) 0).obj N
  let K' := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
      (Scheme.Modules.tensorPullbackObj (pullback.fst f g) N)
  let φ := Scheme.picardTermwiseSingleMap (pullback.fst f g) N
  let T := W.ι ⁻¹ᵁ U
  let R := W.ι ⁻¹ᵁ V
  have hcover : T ⊔ R = ⊤ := by
    rw [← Scheme.Hom.preimage_sup]
    exact W.ι_preimage_self
  obtain ⟨C, D, C', D', t, t', α, β, H, e₁, e₂, e₃, e₁', e₂', e₃', hα, hβ, hcone⟩ :=
    relativeMV_cover_homotopy_data f (pullback.snd f g) g (pullback.fst f g)
      (IsPullback.of_hasPullback f g) K K' φ T R hcover
  obtain ⟨sU⟩ := standardSingle_open_relative_arrow p g W U le_sup_left N
  obtain ⟨sV⟩ := standardSingle_open_relative_arrow p g W V le_sup_right N
  obtain ⟨sUV⟩ := standardSingle_open_relative_arrow p g W (U ⊓ V)
    (inf_le_left.trans le_sup_left) N
  have hi : W.ι ⁻¹ᵁ (U ⊓ V) = T ⊓ R := Scheme.Hom.preimage_inf W.ι
  rw [hi] at sUV
  let s₂ := biprod_arrow_iso sU sV
  refine ⟨C, D, C', D', t, t', α, β, H, e₁,
    e₂ ≪≫ Arrow.leftFunc.mapIso s₂, e₃ ≪≫ Arrow.leftFunc.mapIso sUV,
    e₁', e₂' ≪≫ Arrow.rightFunc.mapIso s₂, e₃' ≪≫ Arrow.rightFunc.mapIso sUV,
    hα, ?_, ?_⟩
  · exact transport_arrow_comparison (DerivedCategory.Q.map β) e₂ e₂' hβ s₂
  · exact transport_arrow_comparison _ e₃ e₃' hcone sUV


end AlgebraicGeometry
