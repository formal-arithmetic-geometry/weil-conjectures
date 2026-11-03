/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalEtaleSourceTransport
import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalEtaleSourceEndpoint
import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalEtaleNormalEndpoint
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionEtaleRestriction

/-! # Inverse deformation on an etale diagonal correspondence

Source: diagonal-dualizing proof Steps 1--2 and orientation-charts proof Step 3.
(blueprint: lem-pur-diagonal-etale-inverse-deformation-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

private theorem span_square {C : Type*} [Category C]
    {T Y Z X NT NY NZ NX : C}
    (a : T ≅ Y) (b : T ≅ Z) (c : X ≅ Z)
    (an : NT ≅ NY) (bn : NT ≅ NZ) (cn : NX ≅ NZ)
    (dt : T ≅ NT) (dy : Y ≅ NY) (dz : Z ≅ NZ) (dx : X ≅ NX)
    (ha : dt.hom ≫ an.hom = a.hom ≫ dy.hom)
    (hb : dt.hom ≫ bn.hom = b.hom ≫ dz.hom)
    (hc : dx.hom ≫ cn.hom = c.hom ≫ dz.hom) :
    dy.hom ≫ (an.inv ≫ bn.hom ≫ cn.inv) =
      (a.inv ≫ b.hom ≫ c.inv) ≫ dx.hom := by
  have ha' : dy.hom ≫ an.inv = a.inv ≫ dt.hom := by
    apply (a.eq_inv_comp).2
    rw [← Category.assoc, ← ha, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hc' : dz.hom ≫ cn.inv = c.inv ≫ dx.hom := by
    apply (c.eq_inv_comp).2
    rw [← Category.assoc, ← hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  calc
    _ = a.inv ≫ dt.hom ≫ bn.hom ≫ cn.inv := by
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ bn.hom ≫ cn.inv) ha'
    _ = a.inv ≫ b.hom ≫ dz.hom ≫ cn.inv := by
      simpa only [Category.assoc] using congrArg (fun k ↦ a.inv ≫ k ≫ cn.inv) hb
    _ = _ := by rw [hc']; simp only [Category.assoc]

private theorem diagonal_square (P : PurityFiniteSetting.{u}) {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated (g ≫ aY)] [IsSeparated (h ≫ aY)]
    (e : U ⟶ X) [Etale e] (w : e ≫ g = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    (SectionRestriction.delta P (h ≫ aY)
        (DiagonalEtaleComparison.diagonalPair d h)).hom ≫
        (DiagonalEtaleComparison.normal P d g h aY e w).hom =
      (DiagonalEtaleComparison.source P d g h aY e w N).hom ≫
        (OrientationRefinement.pull P e).map
          (SectionRestriction.delta P (g ≫ aY)
            (DiagonalEtaleComparison.diagonalPair d g)).hom := by
  let := P.noetherian (h ≫ aY)
  obtain ⟨D⟩ := DiagonalEtaleComparison.centreSpan_nonempty d g h e w
  have he : e ≫ (g ≫ aY) = h ≫ aY := by rw [← Category.assoc, w]
  have ha := ((SectionRestriction.coherence P).2.2.1 U (h ≫ aY) d
    D.pair (DiagonalEtaleComparison.diagonalPair d h) D.left).2.2
  have hb := ((SectionRestriction.coherence P).2.2.1 U (h ≫ aY) d
    D.pair (DiagonalEtaleComparison.basePair d g e) D.right).2.2
  have hc := ((SectionRestriction.coherence P).2.2.2.1 X U (g ≫ aY) (h ≫ aY)
    e he d (DiagonalEtaleComparison.diagonalPair d g)
    (DiagonalEtaleComparison.basePair d g e)
    (DiagonalEtaleComparison.baseSquare d g e)).2.2
  have hs := DiagonalEtaleComparison.span_source_endpoint P d g h aY e w N D
  have hn := DiagonalEtaleComparison.span_normal_endpoint P d g h aY e w D
  have H := span_square _ _ _ _ _ _ _ _ _ _
    (congrArg Iso.hom ha) (congrArg Iso.hom hb) (congrArg Iso.hom hc)
  rw [← hs, ← hn]
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] using H

private theorem delta_eq (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (d : ℕ) (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens) (H : P.AffineDiagonalGeometry f aY d V) :
    letI := H.smoothDimension
    letI := H.baseFiniteType
    letI := H.baseQuasiCompact
    letI := H.sourceSeparated
    OrientationRefinement.delta P f aY d V H =
      SectionRestriction.delta P ((f ∣_ V.1) ≫ V.1.ι ≫ aY)
        (DiagonalEtaleComparison.diagonalPair d (f ∣_ V.1)) := by
  let := H.smoothDimension
  let := H.baseFiniteType
  let := H.baseQuasiCompact
  let := H.sourceSeparated
  let pair := DiagonalEtaleComparison.diagonalPair d (f ∣_ V.1)
  let aB := (f ∣_ V.1) ≫ V.1.ι ≫ aY
  apply (Dnc.existsUnique_dncInvariance P d pair.g aB pair.s pair.section_eq).unique
  · exact (Dnc.existsUnique_dncInvariance P d pair.g aB pair.s
      pair.section_eq).exists.choose_spec
  · exact (Classical.choose_spec (Dnc.existsUnique_dncInvariance P d pair.g aB
      pair.s pair.section_eq)).1

/-- Inverse deformation commutes with the source and actual Rees-normal transports.
This compares only the one and zero endpoints; it contains no alpha, rho or dualizing
locality square.
Source: diagonal-dualizing proof Step 1 and canonicity paragraph;
orientation-charts proof Step 3.

Proof: for each restricted etale map e over the affine target, factor the self-product
map through the pullback of the target diagonal projection. Delete the complementary
clopen inverse image of the diagonal to make both centre squares Cartesian. Apply
SectionRestriction.coherence's Endpoints to the two etale maps out of this open,
and NormalizedBase to the Cartesian factor. The restrictions at one are the
counit-normalized locality followed by inverse smooth base change in source.
The restrictions at zero are the smooth section exchanges in normal: composing the
Rees maps fixes t and takes a/t to e*a/t, so cancellation of the closed zero-fibre
inclusion identifies their composite with the specified normalMap. Identify the
locality maps with those for N using the normalized sum-extension counit equation.
The two endpoint squares give delta_h followed by normal = source followed by
pullback(delta_g). Invert delta and compose the equations for jO and vO through
the same h=jO followed by f restricted to V. The common delta_h cancels, yielding
the displayed inverse-deformation square. Neither a vector model nor a coefficient
orientation enters. Rank zero uses the normalized identity family; on the empty
open the same exchange and endpoint equations hold.
(blueprint: lem-pur-diagonal-etale-inverse-deformation-square). -/
theorem diagonalEtaleInverseDeformation (P : PurityFiniteSetting.{u})
    {X Z Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens)
    (H : P.AffineDiagonalGeometry f aY d V)
    (K : P.AffineDiagonalGeometry g aY d V)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (U : Scheme.{u}) [IsNoetherian U]
    (j : U ⟶ X) [Etale j] [IsSeparated j]
    (v : U ⟶ Z) [Etale v] [IsSeparated v]
    (w : v ≫ g = j ≫ f)
    (O : U.Opens) (jO : O.toScheme ⟶ (f ⁻¹ᵁ V.1).toScheme)
    (vO : O.toScheme ⟶ (g ⁻¹ᵁ V.1).toScheme)
    (hj : jO ≫ (f ⁻¹ᵁ V.1).ι = O.ι ≫ j)
    (hv : vO ≫ (g ⁻¹ᵁ V.1).ι = O.ι ≫ v) :
    let n := DiagonalEtaleComparison.normalTransport P d f g aY V H K U j v w
      O jO vO hj hv
    let s := DiagonalEtaleComparison.sourceTransport P d f g aY V H K N U j v w
      O jO vO hj hv
    n.hom ≫ (OrientationRefinement.pull P vO).map
        (OrientationRefinement.delta P g aY d V K).inv =
      (OrientationRefinement.pull P jO).map
        (OrientationRefinement.delta P f aY d V H).inv ≫ s.hom := by
  let := H.baseFiniteType
  let := H.baseQuasiCompact
  let := H.sourceSeparated
  let := K.sourceSeparated
  let := H.smoothDimension
  let := K.smoothDimension
  have : Etale (jO ≫ (f ⁻¹ᵁ V.1).ι) := by rw [hj]; infer_instance
  have : Etale jO := Etale.of_comp jO (f ⁻¹ᵁ V.1).ι
  have : Etale (vO ≫ (g ⁻¹ᵁ V.1).ι) := by rw [hv]; infer_instance
  have : Etale vO := Etale.of_comp vO (g ⁻¹ᵁ V.1).ι
  have : IsSeparated (jO ≫ (f ⁻¹ᵁ V.1).ι) := by rw [hj]; infer_instance
  have : IsSeparated jO := IsSeparated.of_comp jO (f ⁻¹ᵁ V.1).ι
  have : IsSeparated (vO ≫ (g ⁻¹ᵁ V.1).ι) := by rw [hv]; infer_instance
  have : IsSeparated vO := IsSeparated.of_comp vO (g ⁻¹ᵁ V.1).ι
  have : QuasiCompact jO := inferInstance
  have : QuasiCompact vO := inferInstance
  have : SmoothOfRelativeDimension 0 jO :=
    (Etale.iff_smoothOfRelativeDimension_zero jO).mp inferInstance
  let h := jO ≫ (f ∣_ V.1)
  have hdim : SmoothOfRelativeDimension (0 + d) h :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + d) (jO ≫ (f ∣_ V.1)))
  have : SmoothOfRelativeDimension d h :=
    Eq.mp (congrArg (fun n => SmoothOfRelativeDimension n h) (Nat.zero_add d)) hdim
  have he : vO ≫ (g ∣_ V.1) = h := by
    apply (cancel_mono V.1.ι).mp
    dsimp only [h]
    rw [Category.assoc, Category.assoc, morphismRestrict_ι, morphismRestrict_ι,
      ← Category.assoc, hv, ← Category.assoc, hj]
    simp only [Category.assoc, w]
  have hf := diagonal_square P d (f ∣_ V.1) h (V.1.ι ≫ aY) jO rfl N
  have hg := diagonal_square P d (g ∣_ V.1) h (V.1.ι ≫ aY) vO he N
  rw [← delta_eq P d f aY V H] at hf
  rw [← delta_eq P d g aY V K] at hg
  let nf := DiagonalEtaleComparison.normal P d (f ∣_ V.1) h (V.1.ι ≫ aY) jO rfl
  let ng := DiagonalEtaleComparison.normal P d (g ∣_ V.1) h (V.1.ι ≫ aY) vO he
  let sf := DiagonalEtaleComparison.source P d (f ∣_ V.1) h (V.1.ι ≫ aY) jO rfl N
  let sg := DiagonalEtaleComparison.source P d (g ∣_ V.1) h (V.1.ι ≫ aY) vO he N
  let df := (OrientationRefinement.pull P jO).mapIso
    (OrientationRefinement.delta P f aY d V H)
  let dg := (OrientationRefinement.pull P vO).mapIso
    (OrientationRefinement.delta P g aY d V K)
  let dh := SectionRestriction.delta P (h ≫ V.1.ι ≫ aY)
    (DiagonalEtaleComparison.diagonalPair d h)
  change dh.hom ≫ nf.hom = sf.hom ≫ df.hom at hf
  change dh.hom ≫ ng.hom = sg.hom ≫ dg.hom at hg
  change (nf.inv ≫ ng.hom) ≫ dg.inv = df.inv ≫ (sf.inv ≫ sg.hom)
  apply df.eq_inv_comp.mpr
  apply (cancel_epi sf.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change sf.hom ≫ df.hom ≫ nf.inv ≫ ng.hom ≫ dg.inv = sg.hom
  rw [← reassoc_of% hf]
  simp only [Iso.hom_inv_id_assoc]
  rw [reassoc_of% hg]
  simp only [Iso.hom_inv_id, Category.comp_id]

end WeilConjectures.PurityFiniteSetting
