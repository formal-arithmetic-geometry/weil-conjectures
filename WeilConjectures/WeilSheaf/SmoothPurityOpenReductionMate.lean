module

public import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate

/-! # Changing the right-adjoint coordinates of a coefficient square -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

namespace CategoryTheory.Adjunction

variable {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
  {L : A ⥤ B} {R P : B ⥤ A} {L' : A' ⥤ B'} {R' P' : B' ⥤ A'}
  (a : L ⊣ R) (a' : L' ⊣ R') (T : A ⥤ A') (U : B ⥤ B')
  (e : R ≅ P) (e' : R' ≅ P') (cL : L ⋙ U ≅ T ⋙ L') (cP : P ⋙ T ≅ U ⋙ P')

/-- A mated coefficient square remains mated after replacing both right adjoints by
their pullback coordinates. The cancellation is checked over abstract categories. -/
theorem isMateSquare_ofNatIsoRight_of_conjugate
    (h : a.IsMateSquare a' cL
      (Functor.isoWhiskerRight e T ≪≫ cP ≪≫ Functor.isoWhiskerLeft U e'.symm)) :
    (a.ofNatIsoRight e).IsMateSquare (a'.ofNatIsoRight e') cL cP := by
  rw [isMateSquare_iff] at h ⊢
  rw [mateEquiv_ofNatIsoRight, h]
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, Category.assoc, ← T.map_comp_assoc, Iso.inv_hom_id_app,
    T.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]

end CategoryTheory.Adjunction
