/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.AlgebraicGeometry.ReesConeNormalization
import Sheaf.RingTheory.ReesAssociatedGradedChart
import Sheaf.AlgebraicGeometry.ConormalConeHomExt
import Sheaf.AlgebraicGeometry.ConormalConeZeroSectionPullback

/-! # Normalized Rees cone existence
Source: Stacks 0630, 0632; sk-thm-dnc, Local construction.
(blueprint: lem-pur-rees-cone-normalized-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

private def affineReesAlgebraIso {V S : Scheme.{u}} (s : S ⟶ V)
    [IsClosedImmersion s] (U : V.AffineZariskiSite) :
    (ConormalGradedAlgebra.presentation s).algebra.right.obj.obj
      (Opposite.op (s ⁻¹ᵁ U.1)) ≅ s.ker.normalConePresheaf.obj (Opposite.op U) :=
  ((ConormalGradedAlgebra.presentation s).affineChart ⟨U.1, U.2⟩).choose ≪≫
    (Ideal.rees_associatedGraded_chart (s.ker.siteIdeal U)).choose.toCommRingCatIso

private theorem affineReesAlgebraIso_class {V S : Scheme.{u}} (s : S ⟶ V)
    [IsClosedImmersion s] (U : V.AffineZariskiSite) (n : ℕ)
    (b : (ConormalGradedAlgebra.power s n).val.obj (Opposite.op U.1)) :
    ∃ _hb : (ConormalGradedAlgebra.powerInclusion s n).val.app (Opposite.op U.1) b ∈
        s.ker.siteIdeal U ^ n,
      ∃ ha : LaurentPolynomial.C (R := Γ(V, U.1))
          ((ConormalGradedAlgebra.powerInclusion s n).val.app (Opposite.op U.1) b) *
            LaurentPolynomial.T (-(n : ℤ)) ∈ (s.ker.siteIdeal U).extendedReesAlgebra,
        (affineReesAlgebraIso s U).hom
          (ConormalGradedAlgebra.homogeneousClass s
            (ConormalGradedAlgebra.presentation s).algebra
            (ConormalGradedAlgebra.presentation s).inclusion n U.1 b) =
          Ideal.Quotient.mk _ ⟨LaurentPolynomial.C (R := Γ(V, U.1))
            ((ConormalGradedAlgebra.powerInclusion s n).val.app (Opposite.op U.1) b) *
              LaurentPolynomial.T (-(n : ℤ)), ha⟩ := by
  obtain ⟨hb, he⟩ := ((ConormalGradedAlgebra.presentation s).affineChart
    ⟨U.1, U.2⟩).choose_spec n b
  have hb' : (ConormalGradedAlgebra.powerInclusion s n).val.app
      (Opposite.op U.1) b ∈ s.ker.siteIdeal U ^ n := hb
  obtain ⟨ha, hclass⟩ := (Ideal.rees_associatedGraded_chart
    (s.ker.siteIdeal U)).choose_spec n ⟨_, hb'⟩
  refine ⟨hb', ha, ?_⟩
  change (Ideal.rees_associatedGraded_chart (s.ker.siteIdeal U)).choose
    (((ConormalGradedAlgebra.presentation s).affineChart ⟨U.1, U.2⟩).choose.hom _) = _
  rw [he]
  exact hclass

set_option backward.isDefEq.respectTransparency false in
private theorem homogeneousClass_restrict {V S : Scheme.{u}} (s : S ⟶ V)
    [IsClosedImmersion s] (n : ℕ) {U W : V.Opens} (h : U ≤ W)
    (b : (ConormalGradedAlgebra.power s n).val.obj (Opposite.op W)) :
    (ConormalGradedAlgebra.presentation s).algebra.right.obj.map
      (homOfLE (s.preimage_mono h)).op
      (ConormalGradedAlgebra.homogeneousClass s
        (ConormalGradedAlgebra.presentation s).algebra
        (ConormalGradedAlgebra.presentation s).inclusion n W b) =
    ConormalGradedAlgebra.homogeneousClass s
      (ConormalGradedAlgebra.presentation s).algebra
      (ConormalGradedAlgebra.presentation s).inclusion n U
        ((ConormalGradedAlgebra.power s n).val.map (homOfLE h).op b) := by
  dsimp only [ConormalGradedAlgebra.homogeneousClass, ConormalGradedAlgebra.representative]
  have hi := PresheafOfModules.naturality_apply
    ((ConormalGradedAlgebra.presentation s).inclusion n).val
    (homOfLE (s.preimage_mono h)).op
      (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction s)).unit.app
        (ConormalGradedAlgebra.power s n)).val.app (Opposite.op W) b)
  refine hi.symm.trans ?_
  congr 1
  exact (PresheafOfModules.naturality_apply
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction s)).unit.app
      (ConormalGradedAlgebra.power s n)).val (homOfLE h).op b).symm

set_option backward.isDefEq.respectTransparency false in
private theorem affineReesAlgebraIso_naturality {V S : Scheme.{u}} (s : S ⟶ V)
    [IsClosedImmersion s] {U W : V.AffineZariskiSite} (f : U ⟶ W) :
    (ConormalGradedAlgebra.presentation s).algebra.right.obj.map
        (homOfLE (s.preimage_mono
          (Scheme.AffineZariskiSite.toOpens_mono f.le))).op ≫
      (affineReesAlgebraIso s U).hom =
      (affineReesAlgebraIso s W).hom ≫ s.ker.normalConePresheaf.map f.op := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨e, he⟩ := (ConormalGradedAlgebra.presentation s).affineChart ⟨W.1, W.2⟩
  have hx : ∃ y, x = e.inv y := ⟨e.hom x, by simp⟩
  obtain ⟨x, rfl⟩ := hx
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y ihx ihy => simp only [map_add, ihx, ihy]
  | of n a =>
    induction a using Submodule.Quotient.induction_on with
    | _ a =>
      obtain ⟨p, hp⟩ := (ConormalGradedAlgebra.presentation s).powerIdentification n
      have hm : a.val ∈ (s.ker ^ n).ideal ⟨W.1, W.2⟩ := by simpa using a.property
      have hm' : a.val ∈ Set.range ((s.ker ^ n).toModulesι.app W.1) := by
        rw [(s.ker ^ n).range_toModulesι_app ⟨W.1, W.2⟩]
        exact hm
      obtain ⟨c, hc⟩ := hm'
      let b := p.inv.val.app (Opposite.op W.1) c
      have hb : (ConormalGradedAlgebra.powerInclusion s n).val.app
          (Opposite.op W.1) b = a.val := by
        have hh : p.inv ≫ ConormalGradedAlgebra.powerInclusion s n =
            (s.ker ^ n).toModulesι := by rw [← hp, Iso.inv_hom_id_assoc]
        exact (congrArg (fun k ↦ k.val.app (Opposite.op W.1) c) hh).trans hc
      have heq : e.inv (DirectSum.of (Ideal.associatedGradedPiece (s.ker.ideal
          ⟨W.1, W.2⟩)) n (Submodule.Quotient.mk a)) =
          ConormalGradedAlgebra.homogeneousClass s
            (ConormalGradedAlgebra.presentation s).algebra
            (ConormalGradedAlgebra.presentation s).inclusion n W.1 b := by
        apply (ConcreteCategory.bijective_of_isIso e.hom).1
        obtain ⟨hb', he'⟩ := he n b
        simp [he', hb]
      change (affineReesAlgebraIso s U).hom
        ((ConormalGradedAlgebra.presentation s).algebra.right.obj.map
          (homOfLE (s.preimage_mono
            (Scheme.AffineZariskiSite.toOpens_mono f.le))).op (e.inv _)) =
        s.ker.normalConePresheaf.map f.op ((affineReesAlgebraIso s W).hom (e.inv _))
      rw [heq, homogeneousClass_restrict s n
        (Scheme.AffineZariskiSite.toOpens_mono f.le)]
      obtain ⟨_, haW, hW⟩ := affineReesAlgebraIso_class s W n b
      obtain ⟨_, haU, hU⟩ := affineReesAlgebraIso_class s U n
        ((ConormalGradedAlgebra.power s n).val.map
          (homOfLE (Scheme.AffineZariskiSite.toOpens_mono f.le)).op b)
      rw [hU, hW]
      change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
      congr 1
      apply Subtype.ext
      change LaurentPolynomial.C
          (@id Γ(V, U.1) ((ConormalGradedAlgebra.powerInclusion s n).val.app (Opposite.op U.1)
            ((ConormalGradedAlgebra.power s n).val.map
              (homOfLE (Scheme.AffineZariskiSite.toOpens_mono f.le)).op b))) *
          LaurentPolynomial.T (-(n : ℤ)) =
        LaurentPolynomial.mapRingHom
          (V.presheaf.map (homOfLE (Scheme.AffineZariskiSite.toOpens_mono f.le)).op).hom
          (LaurentPolynomial.C
            (@id Γ(V, W.1) ((ConormalGradedAlgebra.powerInclusion s n).val.app
              (Opposite.op W.1) b)) *
            LaurentPolynomial.T (-(n : ℤ)))
      rw [map_mul, LaurentPolynomial.mapRingHom_C, LaurentPolynomial.mapRingHom_T]
      congr 2
      exact PresheafOfModules.naturality_apply
        (ConormalGradedAlgebra.powerInclusion s n).val
        (homOfLE (Scheme.AffineZariskiSite.toOpens_mono f.le)).op b

private def ambientBasis {V S : Scheme.{u}} (s : S ⟶ V) :
    V.AffineZariskiSite ⥤ TopologicalSpace.Opens S :=
  Scheme.AffineZariskiSite.toOpensFunctor V ⋙ TopologicalSpace.Opens.map s.base

private theorem ambientBasis_dense {V S : Scheme.{u}} (s : S ⟶ V)
    [IsClosedImmersion s] :
    (ambientBasis s).IsCoverDense (Opens.grothendieckTopology S) := by
  apply (TopCat.Opens.coverDense_iff_isBasis _).2
  change TopologicalSpace.Opens.IsBasis
    (Set.range (fun U : V.AffineZariskiSite ↦ s ⁻¹ᵁ U.1))
  convert! V.isBasis_affineOpens.of_isInducing s.isClosedEmbedding.isInducing using 1
  ext W
  constructor
  · rintro ⟨U, rfl⟩
    exact ⟨U.1, U.2, rfl⟩
  · rintro ⟨U, hU, rfl⟩
    exact ⟨⟨U, hU⟩, rfl⟩

private theorem ambientBasis_locallyFull {V S : Scheme.{u}} (s : S ⟶ V) :
    (ambientBasis s).IsLocallyFull (Opens.grothendieckTopology S) := by
  constructor
  intro U W f x hx
  have hxW : s x ∈ W.1 := f.le hx
  obtain ⟨a, b, hab, hxa⟩ := exists_basicOpen_le_affine_inter U.2 W.2
    (s x) ⟨hx, hxW⟩
  let A' : V.AffineZariskiSite := U.basicOpen a
  let j : A' ⟶ U := homOfLE ⟨a, rfl⟩
  let k : A' ⟶ W := homOfLE ⟨b, hab.symm⟩
  refine ⟨(ambientBasis s).obj A', (ambientBasis s).map j, ?_, hxa⟩
  exact ⟨A', j, 𝟙 _, ⟨k, Subsingleton.elim _ _⟩, (Category.id_comp _).symm⟩

private theorem reesProjection_fac {V S : Scheme.{u}} (s : S ⟶ V)
    [IsClosedImmersion s] :
    Scheme.Hom.purityNormalProjection s ≫ s =
      (Scheme.AffineZariskiSite.relativeGluingData
        s.ker.coequifibered_toNormalConePresheaf).toBase :=
  IsClosedImmersion.lift_fac _ _ _

private theorem reesProjection_preimage {V S : Scheme.{u}} (s : S ⟶ V)
    [IsClosedImmersion s] (U : V.AffineZariskiSite) :
    Scheme.Hom.purityNormalProjection s ⁻¹ᵁ (s ⁻¹ᵁ U.1) =
      (Scheme.AffineZariskiSite.relativeGluingData
        s.ker.coequifibered_toNormalConePresheaf).toBase ⁻¹ᵁ U.1 := by
  rw [← Scheme.Hom.comp_preimage, reesProjection_fac]

private def reesSectionsIso {V S : Scheme.{u}} (s : S ⟶ V)
    [IsClosedImmersion s] (U : V.AffineZariskiSite) :
    Γ(s.ker.normalCone, Scheme.Hom.purityNormalProjection s ⁻¹ᵁ (s ⁻¹ᵁ U.1)) ≅
      s.ker.normalConePresheaf.obj (Opposite.op U) :=
  s.ker.normalCone.presheaf.mapIso (eqToIso (reesProjection_preimage s U).symm).op ≪≫
    Scheme.AffineZariskiSite.sectionsIso s.ker.coequifibered_toNormalConePresheaf U

private theorem reesChart_preimage {V S : Scheme.{u}} (s : S ⟶ V)
    [IsClosedImmersion s] (U : V.AffineZariskiSite) :
    ⊤ ≤ reesConeChart s U ⁻¹ᵁ
      (Scheme.Hom.purityNormalProjection s ⁻¹ᵁ (s ⁻¹ᵁ U.1)) := by
  rw [reesProjection_preimage]
  exact Scheme.AffineZariskiSite.top_le_preimage_toBase
    s.ker.coequifibered_toNormalConePresheaf U

private theorem reesSectionsIso_hom {V S : Scheme.{u}} (s : S ⟶ V)
    [IsClosedImmersion s] (U : V.AffineZariskiSite) :
    (reesSectionsIso s U).hom =
      (reesConeChart s U).appLE
        (Scheme.Hom.purityNormalProjection s ⁻¹ᵁ (s ⁻¹ᵁ U.1)) ⊤
        (reesChart_preimage s U) ≫ (Scheme.ΓSpecIso _).hom := by
  dsimp only [reesSectionsIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Scheme.AffineZariskiSite.sectionsIso_hom, ← Category.assoc,
    Scheme.Hom.map_appLE]
  rfl

private theorem reesSectionsIso_naturality {V S : Scheme.{u}} (s : S ⟶ V)
    [IsClosedImmersion s] {U W : V.AffineZariskiSite} (f : U ⟶ W) :
    s.ker.normalCone.presheaf.map
        (homOfLE ((Scheme.Hom.purityNormalProjection s).preimage_mono
          (s.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono f.le)))).op ≫
      (reesSectionsIso s U).hom =
    (reesSectionsIso s W).hom ≫ s.ker.normalConePresheaf.map f.op := by
  dsimp only [reesSectionsIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc, ← Functor.map_comp_assoc]
  rw [show (homOfLE ((Scheme.Hom.purityNormalProjection s).preimage_mono
      (s.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono f.le)))).op ≫
      (eqToIso (reesProjection_preimage s U).symm).op.hom =
      (eqToIso (reesProjection_preimage s W).symm).op.hom ≫
        (homOfLE ((Scheme.AffineZariskiSite.relativeGluingData
          s.ker.coequifibered_toNormalConePresheaf).toBase.preimage_mono
            (Scheme.AffineZariskiSite.toOpens_mono f.le))).op from Subsingleton.elim _ _]
  rw [Functor.map_comp, Category.assoc,
    Scheme.AffineZariskiSite.sectionsIso_hom_naturality]

private def reesSheafIso {V S : Scheme.{u}} (s : S ⟶ V)
    [IsClosedImmersion s] :
    (ConormalGradedAlgebra.presentation s).algebra.right ≅
      (TopCat.Sheaf.pushforward CommRingCat.{u}
        (Scheme.Hom.purityNormalProjection s).base).obj s.ker.normalCone.sheaf := by
  have := ambientBasis_dense s
  have := ambientBasis_locallyFull s
  apply Functor.IsCoverDense.sheafIso (G := ambientBasis s)
  refine NatIso.ofComponents (fun U ↦
    affineReesAlgebraIso s U.unop ≪≫ (reesSectionsIso s U.unop).symm) ?_
  intro U W f
  change _ ≫ ((affineReesAlgebraIso s W.unop).hom ≫
      (reesSectionsIso s W.unop).inv) =
    ((affineReesAlgebraIso s U.unop).hom ≫
      (reesSectionsIso s U.unop).inv) ≫ _
  apply (cancel_mono (reesSectionsIso s W.unop).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change _ = (affineReesAlgebraIso s U.unop).hom ≫
    (reesSectionsIso s U.unop).inv ≫
      s.ker.normalCone.presheaf.map
        (homOfLE ((Scheme.Hom.purityNormalProjection s).preimage_mono
          (s.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono f.unop.le)))).op ≫
            (reesSectionsIso s W.unop).hom
  rw [reesSectionsIso_naturality]
  · simp only [Iso.inv_hom_id_assoc]
    exact affineReesAlgebraIso_naturality s f.unop

private theorem reesSheafIso_hom_app {V S : Scheme.{u}} (s : S ⟶ V)
    [IsClosedImmersion s] (U : V.AffineZariskiSite) :
    (reesSheafIso s).hom.hom.app (Opposite.op (s ⁻¹ᵁ U.1)) =
      (affineReesAlgebraIso s U).hom ≫ (reesSectionsIso s U).inv := by
  have := ambientBasis_dense s
  have := ambientBasis_locallyFull s
  exact NatTrans.congr_app
    (Functor.IsCoverDense.sheafHom_restrict_eq
      (G := ambientBasis s) (K := Opens.grothendieckTopology S) _) (Opposite.op U)

private theorem reesSheafIso_structure {V S : Scheme.{u}} (s : S ⟶ V)
    [IsClosedImmersion s] :
    (ConormalGradedAlgebra.presentation s).algebra.hom ≫ (reesSheafIso s).hom =
      ⟨(Scheme.Hom.purityNormalProjection s).c⟩ := by
  apply CategoryTheory.Sheaf.hom_ext
  apply TopCat.Sheaf.hom_ext _ _ (B := fun U : V.affineOpens ↦ s ⁻¹ᵁ U.1)
    (by
      convert! V.isBasis_affineOpens.of_isInducing s.isClosedEmbedding.isInducing using 1
      ext W
      constructor
      · rintro ⟨U, rfl⟩
        exact ⟨U.1, U.2, rfl⟩
      · rintro ⟨U, hU, rfl⟩
        exact ⟨⟨U, hU⟩, rfl⟩)
  intro U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  obtain ⟨a, rfl⟩ := s.app_surjective U.1 U.2 a
  change (reesSheafIso s).hom.hom.app (Opposite.op (s ⁻¹ᵁ U.1))
    ((ConormalGradedAlgebra.presentation s).algebra.hom.hom.app
      (Opposite.op (s ⁻¹ᵁ U.1)) (s.app U.1 a)) = _
  rw [← (ConormalGradedAlgebra.presentation s).constants U.1 a,
    reesSheafIso_hom_app s ⟨U.1, U.2⟩]
  obtain ⟨hb, ha, he⟩ := affineReesAlgebraIso_class s ⟨U.1, U.2⟩ 0 a
  change (reesSectionsIso s ⟨U.1, U.2⟩).inv
    ((affineReesAlgebraIso s ⟨U.1, U.2⟩).hom _) = _
  rw [he]
  apply (ConcreteCategory.bijective_of_isIso
    (reesSectionsIso s ⟨U.1, U.2⟩).hom).1
  simp only [Iso.inv_hom_id_apply]
  have hh := Scheme.AffineZariskiSite.toBase_appLE_sectionsIso_hom
    s.ker.coequifibered_toNormalConePresheaf ⟨U.1, U.2⟩
  have hp : s.app U.1 ≫ (Scheme.Hom.purityNormalProjection s).app (s ⁻¹ᵁ U.1) ≫
      (reesSectionsIso s ⟨U.1, U.2⟩).hom =
      (s.ker.toReesPresheaf ≫ Scheme.toQuotientPresheaf s.ker.tIdeal
        s.ker.map_tIdeal).app (Opposite.op ⟨U.1, U.2⟩) := by
    dsimp only [reesSectionsIso, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← Category.assoc, ← Scheme.Hom.comp_app]
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
    rw [Scheme.Hom.appLE_congr_hom (reesProjection_fac s)]
    exact hh
  change _ = ((s.app U.1 ≫ (Scheme.Hom.purityNormalProjection s).app (s ⁻¹ᵁ U.1)) ≫
    (reesSectionsIso s ⟨U.1, U.2⟩).hom) a
  rw [Category.assoc, hp]
  apply congrArg (Ideal.Quotient.mk _)
  apply Subtype.ext
  simp only [ConormalGradedAlgebra.powerInclusion, Scheme.idealSheafPower,
    Nat.cast_zero, neg_zero, LaurentPolynomial.T_zero, mul_one]
  rfl

private def reesAlgebraIso {V S : Scheme.{u}} (s : S ⟶ V) [IsClosedImmersion s] :
    (ConormalGradedAlgebra.presentation s).algebra ≅
      Under.mk (⟨(Scheme.Hom.purityNormalProjection s).c⟩ : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u}
          (Scheme.Hom.purityNormalProjection s).base).obj s.ker.normalCone.sheaf) :=
  Under.isoMk (reesSheafIso s) (reesSheafIso_structure s)

open Opposite in
private theorem sheaf_eqToHom_app {T : TopCat.{u}}
    {A B : TopCat.Sheaf CommRingCat.{u} T} (e : A = B) (W : TopologicalSpace.Opens T) :
    (eqToHom e).hom.app (op W) = eqToHom (by cases e; rfl) := by
  cases e
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem isoOfAlgebraIso {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsAffineHom f] [IsAffineHom g]
    (α : (Under.mk (⟨g.c⟩ : S.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj Y.sheaf) : S.CommAlgebraSheaf) ≅
      Under.mk (⟨f.c⟩ : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf)) :
    ∃ (q : X ≅ Y) (w : q.hom ≫ g = f), ∀ U : S.Opens,
      q.hom.appLE (g ⁻¹ᵁ U) (f ⁻¹ᵁ U)
        (by rw [← Scheme.Hom.comp_preimage, w]) = α.hom.right.hom.app (op U) := by
  obtain ⟨_, E, hobj, ρ, hmap, _⟩ := affine_morphism_relative_spec S
  let X' : ObjectProperty.FullSubcategory (fun T : Over S ↦ IsAffineHom T.hom) :=
    ⟨Over.mk f, (show IsAffineHom f from inferInstance)⟩
  let Y' : ObjectProperty.FullSubcategory (fun T : Over S ↦ IsAffineHom T.hom) :=
    ⟨Over.mk g, (show IsAffineHom g from inferInstance)⟩
  let β := eqToIso (hobj Y') ≪≫ α ≪≫ (eqToIso (hobj X')).symm
  let β' : E.functor.obj (op Y') ≅ E.functor.obj (op X') := ObjectProperty.isoMk _ β
  let q' := (E.functor.preimageIso β').unop
  let q : X ≅ Y := (Over.forget S).mapIso ((ObjectProperty.ι _).mapIso q')
  have w : q.hom ≫ g = f := Over.w q'.hom.hom
  refine ⟨q, w, ?_⟩
  intro U
  have hm := hmap X' Y' q'.hom U
  have hβ : E.functor.map q'.hom.op = β'.hom := by
    exact E.functor.map_preimage _
  rw [hβ] at hm
  change _ = eqToHom _ ≫ q.hom.appLE _ _ _ ≫ eqToHom _ at hm
  change (eqToHom (hobj Y') ≫ α.hom ≫ eqToHom (hobj X').symm).right.hom.app
    (op U) = eqToHom _ ≫ q.hom.appLE _ _ _ ≫ eqToHom _ at hm
  simp only [Under.comp_right, Under.eqToHom_right, TopCat.Sheaf.comp_app,
    sheaf_eqToHom_app] at hm
  dsimp only [X', Y', Over.mk_hom] at hm
  simpa only [Category.assoc, cancel_epi, cancel_mono] using hm.symm


set_option backward.isDefEq.respectTransparency false in
private theorem reesZeroSection_class {V S : Scheme.{u}} (s : S ⟶ V)
    [IsClosedImmersion s] (U : V.AffineZariskiSite)
    (b : (ConormalGradedAlgebra.power s 1).val.obj (op U.1)) :
    (s.normalConeZeroSection.appLE
      (Scheme.Hom.purityNormalProjection s ⁻¹ᵁ (s ⁻¹ᵁ U.1)) (s ⁻¹ᵁ U.1)
      (by
        rw [← Scheme.Hom.comp_preimage]
        have hsec : s.normalConeZeroSection ≫ Scheme.Hom.purityNormalProjection s = 𝟙 S := by
          apply (cancel_mono s).mp
          rw [Category.assoc, reesProjection_fac,
            Scheme.Hom.normalConeZeroSection_toBase, Category.id_comp]
        rw [hsec]; simp))
      ((reesSheafIso s).hom.hom.app (op (s ⁻¹ᵁ U.1))
        (ConormalGradedAlgebra.homogeneousClass s
          (ConormalGradedAlgebra.presentation s).algebra
          (ConormalGradedAlgebra.presentation s).inclusion 1 U.1 b)) = 0 := by
  rw [reesSheafIso_hom_app, CommRingCat.comp_apply]
  obtain ⟨hb, ha, he⟩ := affineReesAlgebraIso_class s U 1 b
  have hb' : (ConormalGradedAlgebra.powerInclusion s 1).val.app (op U.1) b ∈
      s.ker.siteIdeal U := by simpa using hb
  rw [he]
  let z := Scheme.AffineZariskiSite.relativeGluingMap
    s.ker.coequifibered_toNormalConePresheaf
    s.ker.coequifibered_toQuotientAlgebra s.ker.normalConeToQuotient
  let π := (Scheme.AffineZariskiSite.relativeGluingData
    s.ker.coequifibered_toQuotientAlgebra).toBase
  have hz : π ⁻¹ᵁ U.1 ≤ z ⁻¹ᵁ
      (Scheme.Hom.purityNormalProjection s ⁻¹ᵁ (s ⁻¹ᵁ U.1)) := by
    rw [reesProjection_preimage]
    exact (Scheme.AffineZariskiSite.relativeGluingMap_preimage
      s.ker.coequifibered_toNormalConePresheaf
      s.ker.coequifibered_toQuotientAlgebra s.ker.normalConeToQuotient
      s.ker.toNormalConePresheaf_comp_normalConeToQuotient U).ge
  have ht : s ⁻¹ᵁ U.1 ≤ s.toQuotientSpec ⁻¹ᵁ (π ⁻¹ᵁ U.1) := by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toQuotientSpec_toBase]
  change ((s.toQuotientSpec ≫ z).appLE
    (Scheme.Hom.purityNormalProjection s ⁻¹ᵁ (s ⁻¹ᵁ U.1)) (s ⁻¹ᵁ U.1) _)
      ((reesSectionsIso s U).inv _) = 0
  rw [← Scheme.Hom.appLE_comp_appLE _ _ _ _ _ hz ht, CommRingCat.comp_apply]
  suffices hh : z.appLE _ _ hz ((reesSectionsIso s U).inv
      (Ideal.Quotient.mk _ ⟨_, ha⟩)) = 0 by rw [hh, map_zero]
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.AffineZariskiSite.sectionsIso s.ker.coequifibered_toQuotientAlgebra U).hom).1
  rw [map_zero]
  change ((reesSectionsIso s U).inv ≫ z.appLE _ _ hz ≫
    (Scheme.AffineZariskiSite.sectionsIso
      s.ker.coequifibered_toQuotientAlgebra U).hom) _ = 0
  have hglue := Scheme.AffineZariskiSite.relativeGluingMap_appLE_sectionsIso_hom
    s.ker.coequifibered_toNormalConePresheaf
    s.ker.coequifibered_toQuotientAlgebra s.ker.normalConeToQuotient
    s.ker.toNormalConePresheaf_comp_normalConeToQuotient U
  dsimp only [reesSectionsIso, Iso.trans_inv, Functor.mapIso_inv]
  rw [Category.assoc, Scheme.Hom.map_appLE_assoc, hglue,
    Iso.inv_hom_id_assoc]
  change Polynomial.eval 0 ((s.ker.siteIdeal U).extendedReesAlgebraToPolynomial
    (Ideal.Quotient.mk _) Ideal.mk_ker.ge ⟨_, ha⟩) = 0
  have hh := Ideal.extendedReesAlgebraToPolynomial_C_mul_T_neg_one
    (I := s.ker.siteIdeal U) (R := Γ(V, U.1))
    (Ideal.Quotient.mk (s.ker.siteIdeal U)) Ideal.mk_ker.ge hb'
  exact (congrArg (Polynomial.eval 0) hh).trans Polynomial.eval_zero

set_option backward.isDefEq.respectTransparency false in
/-- Existence with the homogeneous representative normalization.
Source: Stacks 0630, 0632; sk-thm-dnc, Local construction
(blueprint: lem-pur-rees-cone-normalized-existence).
Proof: on each affine chart send a homogeneous class of a in I^n/I^(n+1) to
 a/t^n modulo t in the extended Rees algebra. Changing a by I^(n+1) multiplies
 the corresponding Rees representative by t, so this is well defined. Products
 and constants have the same formulas, and the inverse sends each Laurent term
 back to its homogeneous class. Localization commutes with these formulas;
 relative Spec therefore glues the inverse ring maps. They preserve projection
 and augmentation. The sheaf coproduct presentation and generation of I^n by
 products of n ideal sections show that the displayed degree-one identities,
 together with the structural map, determine every homogeneous class. Affine
 charts cover the cone, so they determine a unique scheme isomorphism. -/
theorem reesConeComparison_exists {V S : Scheme.{u}} (s : S ⟶ V)
    [IsClosedImmersion s] :
    ∃ q : s.ker.normalCone ≅ PurityNormalBundle.normalCone s,
      ReesConeNormalized s q := by
  have : IsAffineHom ((Scheme.AffineZariskiSite.relativeGluingData
      s.ker.coequifibered_toNormalConePresheaf).toBase) :=
    Scheme.AffineZariskiSite.toBase_of_forall _ _ fun _ ↦ inferInstance
  have : IsAffineHom (Scheme.Hom.purityNormalProjection s ≫ s) := by
    rw [reesProjection_fac]
    infer_instance
  have : IsAffineHom (Scheme.Hom.purityNormalProjection s) := IsAffineHom.of_comp _ s
  have : IsAffineHom (PurityNormalBundle.projection s) :=
    (PurityNormalBundle.over s).property
  obtain ⟨q, hq, hqapp⟩ := isoOfAlgebraIso
    (Scheme.Hom.purityNormalProjection s) (PurityNormalBundle.projection s)
    ((coneAlgebraIso s).symm ≪≫ reesAlgebraIso s)
  have hqa (W : S.Opens) :
      (coneAlgebraIso s).hom.right.hom.app (op W) ≫
        q.hom.appLE (PurityNormalBundle.projection s ⁻¹ᵁ W)
          (Scheme.Hom.purityNormalProjection s ⁻¹ᵁ W)
          (by rw [← Scheme.Hom.comp_preimage, hq]) =
        (reesSheafIso s).hom.hom.app (op W) := by
    rw [hqapp]
    change ((coneAlgebraIso s).hom ≫
      ((coneAlgebraIso s).inv ≫ (reesAlgebraIso s).hom)).right.hom.app _ = _
    rw [Iso.hom_inv_id_assoc]
    rfl
  have hs : s.normalConeZeroSection ≫ Scheme.Hom.purityNormalProjection s = 𝟙 S := by
    apply (cancel_mono s).mp
    rw [Category.assoc, reesProjection_fac,
      Scheme.Hom.normalConeZeroSection_toBase, Category.id_comp]
  refine ⟨q, hq, ?_, ?_⟩
  · apply conormalCone_hom_ext s (PurityNormalBundle.projection s) (coneAlgebraIso s)
      (𝟙 S) (s.normalConeZeroSection ≫ q.hom) (PurityNormalBundle.zeroSection s)
      (by rw [Category.assoc, hq, hs]) (PurityNormalBundle.zeroSection_spec s).1
    intro U b
    simp only [Scheme.Hom.id_preimage]
    have hc := Scheme.Hom.appLE_comp_appLE s.normalConeZeroSection q.hom
      (PurityNormalBundle.projection s ⁻¹ᵁ (s ⁻¹ᵁ U.1))
      (Scheme.Hom.purityNormalProjection s ⁻¹ᵁ (s ⁻¹ᵁ U.1)) (s ⁻¹ᵁ U.1)
      (by rw [← Scheme.Hom.comp_preimage q.hom (PurityNormalBundle.projection s), hq])
      (by rw [← Scheme.Hom.comp_preimage, hs]; simp)
    rw [← hc]
    change (((coneAlgebraIso s).hom.right.hom.app (op (s ⁻¹ᵁ U.1)) ≫
      q.hom.appLE _ _ _) ≫ s.normalConeZeroSection.appLE _ _ _) _ =
      ((coneAlgebraIso s).hom.right.hom.app (op (s ⁻¹ᵁ U.1)) ≫
        (PurityNormalBundle.zeroSection s).appLE _ _ _) _
    rw [hqa, coneZeroSection_app]
    change s.normalConeZeroSection.appLE _ _ _
      ((reesSheafIso s).hom.hom.app _ _) =
        (ConormalGradedAlgebra.augmentation s).right.hom.app _ _
    rw [reesZeroSection_class s ⟨U.1, U.2⟩ b]
    symm
    exact (ConormalGradedAlgebra.presentation s).augmentation.exists.choose_spec 1 U.1 b
  · intro U b hb hU
    have hcomp := Scheme.Hom.appLE_comp_appLE (reesConeChart s U) q.hom
      (PurityNormalBundle.projection s ⁻¹ᵁ (s ⁻¹ᵁ U.1))
      (Scheme.Hom.purityNormalProjection s ⁻¹ᵁ (s ⁻¹ᵁ U.1)) ⊤
      (by rw [← Scheme.Hom.comp_preimage q.hom (PurityNormalBundle.projection s), hq])
      (reesChart_preimage s U)
    rw [← hcomp, CommRingCat.comp_apply, hqapp]
    have he : (coneAlgebraIso s).hom.right.hom.app (op (s ⁻¹ᵁ U.1)) ≫
        (((coneAlgebraIso s).symm ≪≫ reesAlgebraIso s).hom.right.hom.app
          (op (s ⁻¹ᵁ U.1))) = (reesSheafIso s).hom.hom.app (op (s ⁻¹ᵁ U.1)) := by
      change ((coneAlgebraIso s).hom ≫
        ((coneAlgebraIso s).inv ≫ (reesAlgebraIso s).hom)).right.hom.app _ = _
      rw [Iso.hom_inv_id_assoc]
      rfl
    change (((coneAlgebraIso s).hom.right.hom.app (op (s ⁻¹ᵁ U.1)) ≫
      (((coneAlgebraIso s).symm ≪≫ reesAlgebraIso s).hom.right.hom.app
        (op (s ⁻¹ᵁ U.1)))) ≫
      (reesConeChart s U).appLE _ ⊤ (reesChart_preimage s U)) _ = _
    rw [he, reesSheafIso_hom_app]
    change ((affineReesAlgebraIso s U).hom ≫ (reesSectionsIso s U).inv ≫
      (reesConeChart s U).appLE _ ⊤ (reesChart_preimage s U)) _ = _
    have hc : (reesSectionsIso s U).inv ≫
        (reesConeChart s U).appLE _ ⊤ (reesChart_preimage s U) =
          (Scheme.ΓSpecIso _).inv := by
      apply (cancel_mono (Scheme.ΓSpecIso _).hom).mp
      rw [Category.assoc, ← reesSectionsIso_hom, Iso.inv_hom_id, Iso.inv_hom_id]
    rw [hc]
    obtain ⟨_, ha, heq⟩ := affineReesAlgebraIso_class s U 1 b
    rw [CommRingCat.comp_apply, heq]
    rfl

end AlgebraicGeometry.Etale.FiniteSmoothPurity
