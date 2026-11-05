/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Proper

/-!
# The smooth proper trace after extending the base field

The trace chosen over the base field remains a universal arrow after a field extension.
This uses invertibility of the canonical dualizing base-change morphism, so no agreement
between the independently chosen orientations over the two fields is needed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Adjunction

/-- Transposing a pulled-back trace gives the pulled-back orientation followed by
exceptional base change. -/
lemma homEquiv_baseChangedTrace
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    {a : C ⥤ D} {a' : D ⥤ C} (adj : a ⊣ a')
    {b : C' ⥤ D'} {b' : D' ⥤ C'} (adj' : b ⊣ b')
    {G : C ⥤ C'} {H : D ⥤ D'} (bc : a ⋙ H ≅ G ⋙ b)
    {U : D} {U' : D'} (e : H.obj U ⟶ U') {T : C} (γ : T ⟶ a'.obj U) :
    adj'.homEquiv _ _
        (bc.inv.app T ≫ H.map (a.map γ ≫ adj.counit.app U) ≫ e) =
      G.map γ ≫ unitBaseChange adj adj' bc.hom e := by
  apply (adj'.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, homEquiv_counit, Functor.map_comp, Category.assoc,
    ← cancel_epi (bc.hom.app T), Iso.hom_inv_id_app_assoc]
  have hn := bc.hom.naturality γ
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn, app_comp_map_unitBaseChange_comp_counit]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

universe u

open Scheme

variable (l : ℕ) [Fact l.Prime] {F L : Type u} [Field F] [Field L] [Algebra F L]
  [Fact (ringChar F).Prime] [Fact (ringChar F ≠ l)] [Fact (ringChar L).Prime]
  [Fact (ringChar L ≠ l)]
  {X : Over (Spec (.of F))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [IsProper (toPoint X).left]
  {X' : Over (Spec (.of L))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [IsProper (toPoint X').left]
  {π : X'.left ⟶ X.left}
  (e : (boundedConstructibleUpperStarOfMap l (X := point F) (Y := point L)
    (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj (𝟙_ _) ⟶ 𝟙_ _)
  (sq : IsPullback π (toPoint X').left (toPoint X).left
    (Spec.map (CommRingCat.ofHom (algebraMap F L))))
  (d : ℕ)

end AlgebraicGeometry.ProEtale.CondensedRing
