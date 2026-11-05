/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.Adjunction.MateOfNatIsoLeft

/-! # Invertibility of a mate is independent of the choices of right adjoints -/

@[expose] public section

namespace CategoryTheory

open TwoSquare

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {L : A ⥤ B} {R S : B ⥤ A} {L' : C ⥤ D} {R' S' : D ⥤ C}
  {U : A ⥤ C} {V : B ⥤ D}

/-- Changing the right adjoints conjugates a mate by the canonical isomorphisms between
right adjoints, so preserves its invertibility. -/
theorem isIso_mateEquiv_of_same_left
    (adj : L ⊣ R) (adj' : L' ⊣ R') (b : L ⊣ S) (b' : L' ⊣ S')
    (α : TwoSquare U L L' V) [IsIso (mateEquiv adj adj' α).natTrans] :
    IsIso (mateEquiv b b' α).natTrans := by
  let e := conjugateIsoEquiv adj b (Iso.refl L)
  let e' := conjugateIsoEquiv adj' b' (Iso.refl L')
  have h := mateEquiv_whiskerTop_conjugateEquiv adj b adj' b'
    (𝟙 L) (𝟙 L') α α (by ext X; simp [TwoSquare.whiskerLeft, TwoSquare.whiskerRight])
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have hm : U.map (e.hom.app M) ≫ (mateEquiv b b' α).app M =
      (mateEquiv adj adj' α).app M ≫ e'.hom.app (V.obj M) := by
    simpa only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, e, e', conjugateIsoEquiv_apply_hom,
      Iso.refl_hom] using congrArg (fun s ↦ s.app M) h
  have : IsIso (U.map (e.hom.app M) ≫ (mateEquiv b b' α).app M) := by
    rw [hm]
    infer_instance
  exact IsIso.of_isIso_comp_left (U.map (e.hom.app M)) _

/-- Replacing the geometric left adjoint by an isomorphic one preserves an invertible mate
when the comparison square is transported by that isomorphism. -/
theorem isIso_mateEquiv_whiskerLeftIso
    (adj : L ⊣ R) (adj' : L' ⊣ R') {L'' : C ⥤ D} {R'' : D ⥤ C}
    (b' : L'' ⊣ R'') (e : L'' ≅ L') (α : U ⋙ L' ≅ L ⋙ V)
    [IsIso (mateEquiv adj adj' α.hom).natTrans] :
    IsIso (mateEquiv adj b' (Functor.isoWhiskerLeft U e ≪≫ α).hom).natTrans := by
  have he : (mateEquiv adj (adj'.ofNatIsoLeft e.symm)
      (Functor.isoWhiskerLeft U e ≪≫ α).hom).natTrans =
      (mateEquiv adj adj' α.hom).natTrans := by
    ext M
    simp [mateEquiv_apply, Adjunction.ofNatIsoLeft_unit, ← Functor.map_comp]
  have : IsIso (mateEquiv adj (adj'.ofNatIsoLeft e.symm)
      (Functor.isoWhiskerLeft U e ≪≫ α).hom).natTrans := by
    rw [he]
    infer_instance
  exact isIso_mateEquiv_of_same_left adj (adj'.ofNatIsoLeft e.symm) adj b' _

end CategoryTheory
