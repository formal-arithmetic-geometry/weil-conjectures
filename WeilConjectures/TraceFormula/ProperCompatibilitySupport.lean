/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ConjugateComp
public import WeilConjectures.TraceFormula.ProperCompatibilityExchange
public import WeilConjectures.TraceFormula.ShriekTrace

/-!

# Exchange of the support isomorphisms along a proper pushforward diagram

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

lemma NatTrans.naturality_comp_assoc {C D E : Type*} [Category C] [Category D] [Category E]
    {F₁ F₂ : C ⥤ D} {G₁ G₂ : D ⥤ E} (α : F₁ ⋙ G₁ ⟶ F₂ ⋙ G₂) {X Y : C} (x : X ⟶ Y) {Z : E}
    (h : G₂.obj (F₂.obj Y) ⟶ Z) :
    G₁.map (F₁.map x) ≫ α.app Y ≫ h = α.app X ≫ G₂.map (F₂.map x) ≫ h := by
  simpa using α.naturality_assoc x h

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence.FixedLocus

variable {c : Correspondence ℓ K} (F : c.FixedLocus)

/-- The inclusion of the fixed locus is a closed immersion: it is the base change of the
diagonal. -/
instance isClosedImmersion_ι : IsClosedImmersion F.ι.left :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (F.isPullback.map (Over.forget _)).flip (inferInstanceAs (IsClosedImmersion (diag X).left))

set_option maxHeartbeats 1000000 in
-- the pullbacks and shrieks of bounded constructible complexes are unfolded in defeq checks
/-- **The exceptional adjoint of the support isomorphism** (blueprint
`def-trf-kernel-pushforward-maps`, item 8, last assertion): the `Rc_! ⊣ Rc^!`-adjoint of
`ζ_c : Rι_* ω_Fix(c) ⟶ Rc^! RΔ_* ω_X` is
`Rc_! Rι_* ω ≅ Rc_! Rι_! ω ≅ RΔ_! Rd_! ω ⟶ RΔ_! ω_X ≅ RΔ_* ω_X`, the composition law of the
fixed square followed by the trace `t_d`. -/
theorem homEquiv_symm_supportIso_hom :
    ((boundedConstructibleUpperShriekAdjunction _ ℓ c.support).homEquiv _ _).symm
        F.supportIso.hom =
      (boundedConstructibleLowerShriek _ ℓ c.support).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ F.ι).inv.app
            (dualizingComplex' ℓ F.F)) ≫
        (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ F.ι_support).hom.app
          (dualizingComplex' ℓ F.F) ≫
        (boundedConstructibleLowerShriek _ ℓ (diag X)).map
          (lowerShriekDualizingComplexTrace ℓ F.d) ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (diag X)).hom.app
          (dualizingComplex' ℓ X) := by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ F.isPullback
  have hK := Adjunction.homEquiv_symm_conjugateIsoEquiv_inv_app
    (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ F.ι)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ F.ι)
    (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ (diag X))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (diag X))
    (boundedConstructibleUpperShriekAdjunction _ ℓ c.support)
    (boundedConstructibleUpperShriekAdjunction _ ℓ F.d)
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ F.ι_support)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ F.isPullback)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv ℓ F.isPullback)
    (dualizingComplex' ℓ X)
  have n₁ := (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ F.ι).inv.naturality
    (dualizingComplexComp ℓ F.d).inv
  have n₂ := (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ F.ι_support).hom.naturality
    (dualizingComplexComp ℓ F.d).inv
  simp only [Functor.comp_map] at n₂
  simp only [supportIso, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
    Adjunction.homEquiv_naturality_left_symm, upperShriekLowerStarIso,
    lowerShriekBaseChangeIso, hK, lowerShriekDualizingComplexTrace,
    Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, n₁, Functor.map_comp_assoc]
  congr 1
  rw [← Category.assoc, n₂, Category.assoc]

end Correspondence.FixedLocus

end AlgebraicGeometry.ProEtale.CondensedRing
