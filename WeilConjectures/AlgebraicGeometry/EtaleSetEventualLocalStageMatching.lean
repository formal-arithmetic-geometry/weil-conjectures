/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetSheafComparison
public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
import WeilConjectures.AlgebraicGeometry.EtaleSetEventualLocalStageCompatibility
import WeilConjectures.AlgebraicGeometry.EtaleSetLocalStageImageEquations
import WeilConjectures.AlgebraicGeometry.AffineEtaleInverseImageComparison
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.FullAffineEtaleTopos
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Eventual matching of local stage representatives

## References

* Stacks Project, Tags 0A35 and 09YQ
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Local representatives whose images match at the limit become a matching
family after refinement to a later stage. The finite family is transported by
base change, not replaced by a global section (Stacks, Tags 0A35 and 09YQ). -/
theorem etaleSet_eventualLocalStageMatching
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W : (D.obj (op i₀)).FullAffineEtale)
    (t : ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W.obj))) :
    let H := fun j : Over (op i₀) ↦ (Scheme.etaleSetPullback (D.map j.hom)).obj G
    let L := (Scheme.etaleSetPullback (c.π.app (op i₀))).obj G
    let B := fun j : Over (op i₀) ↦ MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j.left)
    let Y := fun j : Over (op i₀) ↦
      (MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W.obj
    let e := fun j : Over (op i₀) ↦
      (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        (c.π.app j.left) (D.map j.hom) (c.π.app (op i₀)) (c.w j.hom).symm).app W.obj
    let β := fun j : Over (op i₀) ↦
      etaleSetSheafComparison (c.π.app j.left) (D.map j.hom)
        (c.π.app (op i₀)) (c.w j.hom) G
    ∀ (j : Over (op i₀)) (n : ℕ) (V : Fin n → (D.obj j.left).Etale)
      (a : ∀ q, V q ⟶ Y j) (s : ∀ q, (H j).obj.obj (op (V q))),
      Sieve.ofArrows V a ∈ (D.obj j.left).smallEtaleTopology (Y j) →
      (∀ q, IsAffine (V q).left) →
      (∀ q, (β j).hom.app (op (V q)) (s q) =
        L.obj.map ((B j).map (a q) ≫ (e j).inv).op t) →
    ∃ (j' : Over (op i₀)) (r : j' ⟶ j),
      let b := MorphismProperty.Over.pullback @Etale ⊤ (D.map r.left)
      let hr := (D.map_comp r.left j.hom).symm.trans
        (congrArg (fun z : j'.left ⟶ op i₀ ↦ D.map z) r.w)
      let d := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        (D.map r.left) (D.map j.hom) (D.map j'.hom) hr.symm).app W.obj
      let V' := fun q ↦ b.obj (V q)
      let a' := fun q ↦ b.map (a q) ≫ d.inv
      let s' := fun q ↦ (etaleSetSheafComparison (D.map r.left) (D.map j.hom)
        (D.map j'.hom) hr G).hom.app (op (V q)) (s q)
      Sieve.ofArrows V' a' ∈ (D.obj j'.left).smallEtaleTopology (Y j') ∧
      (∀ q, (β j').hom.app (op (V' q)) (s' q) =
        L.obj.map ((B j').map (a' q) ≫ (e j').inv).op t) ∧
      Presieve.Arrows.Compatible (H j').obj a' s' := by
  dsimp only
  intro j n V a s ha hV hs
  obtain ⟨j', r, hcompat⟩ :=
    etaleSet_eventualLocalStageCompatibility D c hc i₀ G W t j n V a s hV hs
  refine ⟨j', r, ?_, ?_, hcompat⟩
  · let b := MorphismProperty.Over.pullback @Etale ⊤ (D.map r.left)
    let hr := (D.map_comp r.left j.hom).symm.trans
      (congrArg (fun z : j'.left ⟶ op i₀ ↦ D.map z) r.w)
    let d := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      (D.map r.left) (D.map j.hom) (D.map j'.hom) hr.symm).app W.obj
    have hb := (Scheme.coverPreserving_overPullback
      (P := @Etale) (Q := @Etale) (le_refl _) (D.map r.left)).cover_preserve ha
    rw [Sieve.functorPushforward_ofArrows] at hb
    have hd := (D.obj j'.left).smallEtaleTopology.pullback_stable d.hom hb
    rwa [Sieve.pullback_ofArrows_of_iso] at hd
  · exact etaleSet_localStageImageEquations D c i₀ G W.obj t j n V a s hs j' r

end AlgebraicGeometry
