/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.DerivedScalarExtensionCounitShift

/-! # Computation and exactness of a universal scalar-extension counit
Source: Stacks Project, Tags 06YT, 06YY, 06XN and 05SU.
(blueprint: lem-sbc-scalar-extension-counit-properties)
-/

@[expose] public section
set_option autoImplicit false
universe u v r wR wS u' v' w w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem kan_of_precomp_quotient
    {A : Type u} [Category.{v} A] [Abelian A]
    {D : Type u'} [Category.{v'} D] {H : Type w} [Category.{w'} H]
    (L : HomotopyCategory A (.up ℤ) ⥤ D)
    (G : HomotopyCategory A (.up ℤ) ⥤ H) (F : D ⥤ H)
    (α : L ⋙ F ⟶ G)
    (h : F.IsRightKanExtension
      ((associator (HomotopyCategory.quotient A (.up ℤ)) L F).hom ≫
        whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) α)) :
    F.IsRightKanExtension α := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  have : ((whiskeringLeft _ _ H).obj q).Full := by
    exact inferInstanceAs (((whiskeringLeft _ _ H).obj
      (HomotopyCategory.quotient A (.up ℤ))).Full)
  have : ((whiskeringLeft _ _ H).obj q).Faithful := by
    exact inferInstanceAs (((whiskeringLeft _ _ H).obj
      (HomotopyCategory.quotient A (.up ℤ))).Faithful)
  let P := RightExtension.precomp L G q
  have : P.Full := by
    dsimp only [P, RightExtension.precomp]
    apply CostructuredArrow.full_map₂
  have : P.Faithful := by
    dsimp [P, RightExtension.precomp]
    infer_instance
  let β := (associator q L F).hom ≫ whiskerLeft q α
  let e : P.obj (RightExtension.mk F α) ≅ RightExtension.mk F β :=
    CostructuredArrow.isoMk (Iso.refl _)
  let := h
  exact ⟨⟨IsTerminal.isTerminalOfObj P _
    (IsTerminal.ofIso (F.isUniversalOfIsRightKanExtension β) e.symm)⟩⟩


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem kan_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {G G' : C ⥤ H} (F : D ⥤ H)
    (i : Q ≅ Q') (j : G ≅ G') (α : Q ⋙ F ⟶ G)
    [F.IsRightKanExtension α] :
    F.IsRightKanExtension (whiskerRight i.inv F ≫ α ≫ j.hom) := by
  let P := (rightExtensionEquivalenceOfIso₁ i G).functor ⋙
    (rightExtensionEquivalenceOfIso₂ Q' j).functor
  constructor
  refine ⟨IsTerminal.ofIso
    (IsTerminal.isTerminalObj P _ (F.isUniversalOfIsRightKanExtension α)) ?_⟩
  exact CostructuredArrow.isoMk (Iso.refl _) (by
    ext X
    simp [P, rightExtensionEquivalenceOfIso₁, rightExtensionEquivalenceOfIso₂])



namespace SheafOfModules
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The given universal pair computes tensor on K-flat complexes and is triangulated
for its counit-compatible shift.
Source: Stacks Project, Tags 06YT, 06YY, 06XN, 05SU and 05SE.
(blueprint: lem-sbc-scalar-extension-counit-properties).

Proof: Use the existing derived-change-of-rings cochain model. The identifications
of the ordinary functor on objects and maps give a natural isomorphism with E.
Transport its universal pair along this isomorphism. Uniqueness of right Kan
extensions gives a counit-compatible isomorphism with the given pair F, epsilon.
The model counit is invertible at every K-flat complex, hence so is epsilon.
Pass the given pair to the homotopy category along the full, essentially surjective
homotopy quotient. Apply the counit-shift theorem for derived scalar extension.
Its unique degree-one shift comparison equals the given comparison because
NatTrans.CommShift epsilon is exactly its characterizing equation. Therefore its
preservation of distinguished triangles applies to the given shift of F, proving
F.IsTriangulated. No flatness of the new coefficient ring is used. -/
theorem scalarExtension_counit_properties
    (φ : R ⟶ S)
    [HasDerivedCategory.{wR} (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S))]
    (E : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R) ⥤
      ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S))
    (h : ∀ M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R),
      E.obj M = changeOfRings.{v, u, r} φ M)
    (hmap : ∀ {M N : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)}
      (f : M ⟶ N),
      E.map f = eqToHom (h M) ≫ changeOfRingsHom.{v, u, r} φ M f ≫ eqToHom (h N).symm)
    [E.Additive]
    (F : DerivedCategory (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) ⥤
      DerivedCategory (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S)))
    (ε : DerivedCategory.Q ⋙ F ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor ε
      (HomologicalComplex.quasiIso
        (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) (.up ℤ))]
    [F.CommShift ℤ] [NatTrans.CommShift ε ℤ] :
    F.IsTriangulated ∧
      ∀ P : CochainComplex
        (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
          IsIso (ε.app P) := by
  classical
  let A := ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)
  let B := ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S)
  obtain ⟨m⟩ := nonempty_derivedChangeOfRingsCochainModel φ
  let e : m.E ≅ E := NatIso.ofComponents
    (fun M ↦ eqToIso ((m.obj_eq M).trans (h M).symm)) (by
      intro M N f
      simp only [m.map_eq, hmap, eqToIso.hom, Category.assoc, eqToHom_trans]
      simp)
  let t : m.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)) _
  let := m.universal
  let c := Functor.leftDerivedNatIso m.T F m.ε ε
    (HomologicalComplex.quasiIso A (.up ℤ)) t
  have hcomp (P : CochainComplex A ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P) :
      IsIso (ε.app P) := by
    have := m.computes P hP
    have he := Functor.leftDerivedNatTrans_app m.T F m.ε ε
      (HomologicalComplex.quasiIso A (.up ℤ)) t.hom P
    change c.hom.app (DerivedCategory.Q.obj P) ≫ ε.app P = m.ε.app P ≫ t.hom.app P at he
    rw [← isIso_comp_left_iff (c.hom.app (DerivedCategory.Q.obj P)), he]
    infer_instance
  let q := HomotopyCategory.quotient A (.up ℤ)
  let H := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := B)
  let i := DerivedCategory.quotientCompQhIso A
  let j : q ⋙ H ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let α₀ := Functor.whiskerRight i.hom F ≫ ε ≫ j.inv
  let αpre : q ⋙ (DerivedCategory.Qh ⋙ F) ⟶ q ⋙ H :=
    (Functor.associator _ _ _).inv ≫ α₀
  let α : DerivedCategory.Qh ⋙ F ⟶ H :=
    ((Functor.whiskeringLeft _ _ _).obj q).preimage αpre
  have hαpre : Functor.whiskerLeft q α = αpre :=
    ((Functor.whiskeringLeft _ _ _).obj q).map_preimage αpre
  have hα : F.IsRightKanExtension α := by
    apply kan_of_precomp_quotient _ _ _ α
    have := Functor.IsLeftDerivedFunctor.isRightKanExtension F ε
      (HomologicalComplex.quasiIso A (.up ℤ))
    have hh := kan_change_iso F i.symm j.symm ε
    have he : (Functor.associator q DerivedCategory.Qh F).hom ≫
        Functor.whiskerLeft q α = α₀ := by
      rw [hαpre]
      simp [αpre]
    rw [he]
    exact hh
  have : F.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (.up ℤ)) := ⟨hα⟩
  have hpreShift : NatTrans.CommShift (Functor.whiskerLeft q α) ℤ := by
    rw [hαpre]
    dsimp [αpre, α₀, j, i]
    infer_instance
  have hαshift : NatTrans.CommShift α ℤ := by
    constructor
    intro n
    ext X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    apply (cancel_epi ((DerivedCategory.Qh ⋙ F).map
      ((q.commShiftIso n).hom.app K))).mp
    have hh := NatTrans.shift_app_comm (Functor.whiskerLeft q α) n K
    simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
      Functor.comp_map, Category.assoc] at hh
    have hn := α.naturality ((q.commShiftIso n).hom.app K)
    dsimp at hn
    rw [← reassoc_of% hn] at hh
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Functor.comp_map,
      Category.assoc] using hh
  let := hαshift
  obtain ⟨σ, hσ, huniq, hadd, htri⟩ :=
    derivedScalarExtension_counitShift φ E h hmap F α
  have heq : F.commShiftIso (1 : ℤ) = σ := huniq _ (by
    intro P
    simpa only [H, Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm α (1 : ℤ) P)
  refine ⟨⟨?_⟩, hcomp⟩
  intro T hT
  have ht := htri T hT
  rw [← heq] at ht
  exact ht

end SheafOfModules
