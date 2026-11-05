module

public import WeilConjectures.WeilSheaf.SmoothPurityOpenReductionMate

/-! # Transporting the open exchange along the compact-support identification -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

namespace CategoryTheory.Adjunction

variable {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']

/-- Transporting by a conjugate right-adjoint isomorphism is the same adjunction as
transporting the other adjunction by the original left-adjoint isomorphism. -/
theorem purity_ofNatIsoRight_conjugate
    {L J : A ⥤ B} {R P : B ⥤ A} (a : L ⊣ R) (b : J ⊣ P) (e : L ≅ J) :
    a.ofNatIsoRight (conjugateIsoEquiv a b e.symm) = b.ofNatIsoLeft e.symm := by
  ext K
  simp only [ofNatIsoRight_unit, ofNatIsoLeft_unit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, conjugateIsoEquiv_apply_hom,
    Iso.symm_hom]
  exact unit_conjugateEquiv a b e.inv K

/-- The left exchange respects isomorphisms of its two left adjoints. -/
theorem purity_exchangeLeft_ofNatIsoLeft
    {L J : A ⥤ B} {P : B ⥤ A} {L' J' : A' ⥤ B'} {P' : B' ⥤ A'}
    {H : A ⥤ A'} {H' : B ⥤ B'} (b : J ⊣ P) (b' : J' ⊣ P')
    (e : L ≅ J) (e' : L' ≅ J') (θ : P ⋙ H ≅ H' ⋙ P') :
    exchangeLeft (b.ofNatIsoLeft e.symm) (b'.ofNatIsoLeft e'.symm) θ ≫
        Functor.whiskerRight e.hom H' =
      Functor.whiskerLeft H e'.hom ≫ exchangeLeft b b' θ := by
  ext K
  have hθ := θ.hom.naturality (e.inv.app K)
  have hε := b'.counit.naturality (H'.map (e.inv.app K))
  have hn₁ := e'.hom.naturality (θ.hom.app (L.obj K))
  have hn₂ := e'.hom.naturality (H.map (P.map (e.inv.app K)))
  have hn₃ := e'.hom.naturality (H.map (b.unit.app K))
  simp only [Functor.comp_map, Functor.id_map] at hθ hε
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    exchangeLeft_app, ofNatIsoLeft_unit, ofNatIsoLeft_counit, Iso.symm_hom, Iso.symm_inv,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn₁, reassoc_of% hn₂, reassoc_of% hn₃,
    ← J'.map_comp_assoc (H.map (P.map (e.inv.app K))) (θ.hom.app (L.obj K)),
    hθ, J'.map_comp_assoc, reassoc_of% hε,
    ← H'.map_comp, Iso.inv_hom_id_app, H'.map_id, Category.comp_id]

end CategoryTheory.Adjunction
