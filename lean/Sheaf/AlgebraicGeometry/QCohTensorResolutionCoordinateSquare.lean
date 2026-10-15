module
public import Mathlib.CategoryTheory.Iso

@[expose] public section
open CategoryTheory
namespace AlgebraicGeometry

/-- Compose the affine-model, resolution, and target-restriction squares. -/
theorem tensorResolution_coordinate_square
    {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {A B E Q : C} {A' B' E' Q' : D}
    (f : A ≅ B) (g : B ≅ E) (h : Q ≅ E)
    (f' : A' ≅ B') (g' : B' ≅ E') (h' : Q' ≅ E')
    (a : R.obj A ⟶ A') (b : R.obj B ⟶ B')
    (e : R.obj E ⟶ E') (q : R.obj Q ⟶ Q')
    (hf : R.map f.hom ≫ b = a ≫ f'.hom)
    (hg : R.map g.hom ≫ e = b ≫ g'.hom)
    (hh : R.map h.hom ≫ e = q ≫ h'.hom) :
    R.map (f ≪≫ g ≪≫ h.symm).hom ≫ q = a ≫ (f' ≪≫ g' ≪≫ h'.symm).hom := by
  have hh' : R.map h.inv ≫ q = e ≫ h'.inv := by
    apply (cancel_mono h'.hom).1
    rw [Category.assoc, ← hh, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp]
  calc
    (R.map f.hom ≫ R.map g.hom ≫ R.map h.inv) ≫ q =
        R.map f.hom ≫ R.map g.hom ≫ e ≫ h'.inv := by
      simp only [Category.assoc]
      rw [hh']
    _ = (R.map f.hom ≫ R.map g.hom) ≫ e ≫ h'.inv := by simp only [Category.assoc]
    _ = (R.map f.hom ≫ b ≫ g'.hom) ≫ h'.inv := by
      simp only [Category.assoc]
      rw [← Category.assoc (R.map g.hom), hg]
      simp only [Category.assoc]
    _ = a ≫ f'.hom ≫ g'.hom ≫ h'.inv := by
      simp only [Category.assoc]
      rw [← Category.assoc (R.map f.hom), hf]
      simp only [Category.assoc]


end AlgebraicGeometry
