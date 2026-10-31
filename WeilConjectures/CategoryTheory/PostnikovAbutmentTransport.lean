/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.PostnikovAdditiveExactCoupleData
import all WeilConjectures.CategoryTheory.Abelian.Filtration

/-! # Transport of the canonical Postnikov filtration

Source: Stacks Project, Homology, Tag 0121.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w uB vB

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]

private noncomputable def imageStepIso {X Y : B} (J : DecreasingFiltration X)
    (b : X ≅ Y) (p : ℤ) : (J.F p : B) ≅ ((J.image b.hom).F p : B) :=
  (imageMonoIsoSource (J.F p).arrow).symm ≪≫ (imageSubobjectIso _).symm ≪≫
    (imageSubobjectCompIso (J.F p).arrow b.hom).symm

private theorem imageStepIso_arrow {X Y : B} (J : DecreasingFiltration X)
    (b : X ≅ Y) (p : ℤ) :
    (imageStepIso J b p).hom ≫ ((J.image b.hom).F p).arrow =
      (J.F p).arrow ≫ b.hom := by
  dsimp only [imageStepIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  change (imageMonoIsoSource (J.F p).arrow).inv ≫
    (imageSubobjectIso (J.F p).arrow).inv ≫
      (imageSubobjectCompIso (J.F p).arrow b.hom).inv ≫
        (imageSubobject ((J.F p).arrow ≫ b.hom)).arrow = _
  rw [imageSubobjectCompIso_inv_arrow, imageSubobject_arrow'_assoc,
    imageMonoIsoSource_inv_ι_assoc]

private theorem imageStepIso_comm {X Y : B} (J : DecreasingFiltration X)
    (b : X ≅ Y) (p : ℤ) :
    Subobject.ofLE _ _ (J.F_succ_le p) ≫ (imageStepIso J b p).hom =
      (imageStepIso J b (p + 1)).hom ≫
        Subobject.ofLE _ _ ((J.image b.hom).F_succ_le p) := by
  apply (cancel_mono ((J.image b.hom).F p).arrow).mp
  simp only [Category.assoc, imageStepIso_arrow, Subobject.ofLE_arrow_assoc,
    Subobject.ofLE_arrow]

/-- Transporting the abutment along a natural isomorphism preserves its additive step
and graded functors and the quotient squares.

Source: Stacks Project, Homology, Tag 0121
(blueprint: lem-per-postnikov-abutment-transport).

Proof: Image each step of the canonical image filtration under the composite of the
abutment comparison and the given isomorphism. The image of a monomorphism is its
source, so every original step has a canonical isomorphism to the transported step.
The adjacent-step squares commute after composing with the target step inclusion;
monicity proves the squares themselves. Cokernel functoriality gives the graded
isomorphisms and their quotient squares. Postcompose the existing natural inclusions
with the natural isomorphism. Their naturality proves the required map squares.
Addition is the existing additivity of the three functors. -/
theorem postnikov_abutment_transport {T : DerivedCategory A ⥤ B}
    {C : PostnikovCoupleData T} {P : PostnikovPageData C}
    (H : PostnikovAbutmentData P) : H.Transport := by
  classical
  intro ρ n F hF η
  let ι (p : ℤ) : H.step ρ n p ⟶ F := H.inclusion ρ n p ≫ η.hom
  let J (L : (postnikovHalfPlane C ρ).FullSubcategory) :
      DecreasingFiltration (H.colimit ρ L n).obj :=
    { F := ((C.couple ρ L.obj).imageFiltration n (H.colimit ρ L n)).step
      F_succ_le := fun p ↦
        ((C.couple ρ L.obj).imageFiltration n (H.colimit ρ L n)).antitone_step
          (by omega : p ≤ p + 1) }
  let b (L : (postnikovHalfPlane C ρ).FullSubcategory) :=
    H.abutmentIso ρ L n ≪≫ η.app L
  let G (L : (postnikovHalfPlane C ρ).FullSubcategory) := (J L).image (b L).hom
  let z (L : (postnikovHalfPlane C ρ).FullSubcategory) (p : ℤ) :
      (H.step ρ n p).obj L ≅ ((G L).F p : B) :=
    H.stepIso ρ n p L ≪≫ imageStepIso (J L) (b L) p
  have hz (L : (postnikovHalfPlane C ρ).FullSubcategory) (p : ℤ) :
      (z L p).hom ≫ ((G L).F p).arrow = (ι p).app L := by
    dsimp only [z, Iso.trans_hom, G]
    rw [Category.assoc, imageStepIso_arrow]
    simp only [ι, NatTrans.comp_app, H.inclusion_eq, b, Iso.trans_hom,
      Iso.app_hom, Category.assoc, J]
  let e (L : (postnikovHalfPlane C ρ).FullSubcategory) (p : ℤ) :
      (H.graded ρ n p).obj L ≅ (G L).gr p :=
    H.gradedIso ρ n p L ≪≫
      cokernel.mapIso (Subobject.ofLE _ _ ((J L).F_succ_le p))
        (Subobject.ofLE _ _ ((G L).F_succ_le p))
        (imageStepIso (J L) (b L) (p + 1)) (imageStepIso (J L) (b L) p)
        (imageStepIso_comm (J L) (b L) p)
  refine ⟨ι, G, e, ?_, ?_, ?_, ?_, ?_⟩
  · intro p L
    rfl
  · intro p L
    calc
      (G L).F p = imageSubobject ((z L p).hom ≫ ((G L).F p).arrow) := by
        rw [imageSubobject_mono]
        exact (Subobject.mk_eq_of_comm _ (z L p) rfl).symm
      _ = imageSubobject ((ι p).app L) :=
        congrArg (fun f ↦ imageSubobject f) (hz L p)
  · intro L p
    refine ⟨z L p, hz L p, ?_⟩
    dsimp only [e, Iso.trans_hom, z]
    rw [← Category.assoc, H.quotient_eq]
    simp only [Category.assoc, cokernel.mapIso_hom, cokernel.map]
    change _ ≫ (cokernel.π (Subobject.ofLE _ _ ((J L).F_succ_le p)) ≫
      cokernel.desc _ _ _) = _
    rw [cokernel.π_desc]
  · intro L M u p
    exact (ι p).naturality u
  · intro L M u v p
    have := H.step_additive ρ n p
    have := H.graded_additive ρ n p
    exact ⟨F.map_add, (H.step ρ n p).map_add, (H.graded ρ n p).map_add⟩

end DerivedCategory
