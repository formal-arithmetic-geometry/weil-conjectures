/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ConjugateComp
public import WeilConjectures.TraceFormula.PointNormalizationKunneth
public import WeilConjectures.TraceFormula.PointNormalizationTau

/-!

# Point normalization of the trace class: the base change part

Over the base point, the comparison `ζ : LΔ^* ⟶ Rp₁_!` of `CategoryTheory.Verdier.transportζ`
at `Lp₁^* y` is `LΔ^* Lp₁^* y ≅ y` followed by the unit of `Lp₁^* ⊣ Rp₁_!`
(`ProEtale.CondensedRing.Correspondence.transportζ_upperStar_fst`). This rests on the
compatibility of the units of the adjunctions `Lf^* ⊣ Rf_!` of proper morphisms with the
composition isomorphisms (`ProEtale.CondensedRing.upperStarLowerShriekAdjunction_comp_unit_app`),
which is the compatibility of `Rf_! ≅ Rf_*` with composition (blueprint
`prop-functor-package`, clause (3)).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section General

variable {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- **The units of `Lf^* ⊣ Rf_!` are compatible with composition**: for proper `f` and `g`,
the unit of `L(f ≫ g)^* ⊣ R(f ≫ g)_!` read through the composition isomorphisms is the unit of
the composite adjunction `Lg^* ⋙ Lf^* ⊣ Rf_! ⋙ Rg_!`. -/
lemma upperStarLowerShriekAdjunction_comp_unit_app (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f.left]
    [IsProper g.left] [IsProper (f ≫ g).left] (c : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ (f ≫ g)).unit.app c ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom.app
          ((boundedConstructibleUpperStar _ ℓ (f ≫ g)).obj c) ≫
        (boundedConstructibleLowerShriek _ ℓ g).map ((boundedConstructibleLowerShriek _ ℓ f).map
          ((boundedConstructibleUpperStarComp _ ℓ f g).hom.app c)) =
      (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ g).unit.app c ≫
        (boundedConstructibleLowerShriek _ ℓ g).map
          ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f).unit.app
            ((boundedConstructibleUpperStar _ ℓ g).obj c)) :=
  Adjunction.ofNatIsoRight_comp_unit_app
    (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ f)
    (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ g)
    (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ (f ≫ g))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (f ≫ g))
    (boundedConstructibleUpperStarComp _ ℓ f g)
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g)
    (fun K ↦ boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp ℓ f g K) c

variable (X) in
/-- The counit of `R(𝟙)_! ⊣ R(𝟙)^!` is `R(𝟙)_! R(𝟙)^! ≅ R(𝟙)^! ≅ 𝟭`. -/
lemma upperShriekAdjunction_id_counit_app (d : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperShriekAdjunction _ ℓ (𝟙 X)).counit.app d =
      (boundedConstructibleLowerShriekId ℓ X).hom.app
          ((boundedConstructibleUpperShriek _ ℓ (𝟙 X)).obj d) ≫
        (boundedConstructibleUpperShriekId ℓ X).hom.app d := by
  have h := conjugateEquiv_counit (boundedConstructibleUpperShriekAdjunction _ ℓ (𝟙 X))
    Adjunction.id (boundedConstructibleLowerShriekId ℓ X).inv d
  simp only [Functor.id_map, Adjunction.id_counit, NatTrans.id_app] at h
  erw [Category.comp_id] at h
  change (boundedConstructibleUpperShriekId ℓ X).hom.app d = _ at h
  rw [h, Iso.hom_inv_id_app_assoc]

/-- The unit of `Lr^* ⊣ Rr_!` for a morphism `r` equal to the identity, read through an
isomorphism `c : Lr^* y ≅ X'`: it is `X' ≅ R(𝟙)_! X' = Rr_! X'`. -/
lemma unit_map_comp_of_eq_id {r : X ⟶ X} (hr : r = 𝟙 X) [IsProper r.left]
    {y X' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (c : (boundedConstructibleUpperStar _ ℓ r).obj y ≅ X') :
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ r).unit.app X' ≫
        (boundedConstructibleLowerShriek _ ℓ r).map ((boundedConstructibleUpperStar _ ℓ r).map
          (c.inv ≫ eqToHom (congrArg (fun r : X ⟶ X ↦
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj y) hr) ≫
            (boundedConstructibleUpperStarId _ ℓ X).hom.app y) ≫ c.hom) =
      (boundedConstructibleLowerShriekId ℓ X).inv.app X' ≫
        eqToHom (congrArg (fun r : X ⟶ X ↦
          (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ r).obj X')
            hr.symm) := by
  subst hr
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  have hn := (boundedConstructibleUpperStarId _ ℓ X).hom.naturality
    (c.inv ≫ (boundedConstructibleUpperStarId _ ℓ X).hom.app y)
  simp only [Functor.id_map] at hn
  have key : (boundedConstructibleUpperStar _ ℓ (𝟙 X)).map
      (c.inv ≫ (boundedConstructibleUpperStarId _ ℓ X).hom.app y) ≫ c.hom =
      (boundedConstructibleUpperStarId _ ℓ X).hom.app X' := by
    rw [← cancel_mono c.inv, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      ← cancel_mono ((boundedConstructibleUpperStarId _ ℓ X).hom.app y)]
    erw [hn]
    rw [Category.assoc]
  have h₁ := upperStarLowerShriekAdjunction_id_unit_app ℓ X X'
  have hn' := (boundedConstructibleLowerShriekId ℓ X).hom.naturality
    ((boundedConstructibleUpperStarId _ ℓ X).hom.app X')
  simp only [Functor.id_map] at hn'
  rw [key, ← cancel_mono ((boundedConstructibleLowerShriekId ℓ X).hom.app X'), Category.assoc]
  erw [hn', reassoc_of% h₁]
  simp

end General

namespace Correspondence

instance : IsProper (diag (point k) ≫ (prod.fst : point k ⨯ point k ⟶ point k)).left := by
  rw [Over.comp_left]
  infer_instance

/-- **`ζ` on a pullback along `p₁`** over the base point: `ζ_{Lp₁^* y}` is
`LΔ^* Lp₁^* y ≅ y` followed by the unit of `Lp₁^* ⊣ Rp₁_!`. -/
lemma transportζ_upperStar_fst (y : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Verdier.transportζ (pointDiagAdj ℓ k) (pointLowerShriekιΦ ℓ k)
        ((boundedConstructibleUpperStar _ ℓ (prod.fst : point k ⨯ point k ⟶ point k)).obj y) =
      (diagUpperStarProjIso ℓ prod.fst (by simp) y).hom ≫
        (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ
          (prod.fst : point k ⨯ point k ⟶ point k)).unit.app y := by
  have hCF := upperStarLowerShriekAdjunction_comp_unit_app ℓ (diag (point k))
    (prod.fst : point k ⨯ point k ⟶ point k) y
  have hn := (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (diag (point k))
    (prod.fst : point k ⨯ point k ⟶ point k)).hom.naturality
      ((boundedConstructibleUpperStarComp _ ℓ (diag (point k)) prod.fst).hom.app y)
  have hu := (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ
    (diag (point k) ≫ (prod.fst : point k ⨯ point k ⟶ point k))).unit.naturality
      (diagUpperStarProjIso ℓ prod.fst (by simp) y).hom
  have hG := unit_map_comp_of_eq_id ℓ diag_point_fst
    ((boundedConstructibleUpperStarComp _ ℓ (diag (point k)) prod.fst).app y)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn hu
  have key : (pointLowerShriekιΦ ℓ k).inv.app ((boundedConstructibleUpperStar _ ℓ
      (diag (point k))).obj ((boundedConstructibleUpperStar _ ℓ
        (prod.fst : point k ⨯ point k ⟶ point k)).obj y)) =
      (diagUpperStarProjIso ℓ prod.fst (by simp) y).hom ≫
        (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ
          (prod.fst : point k ⨯ point k ⟶ point k)).unit.app y ≫
        (boundedConstructibleLowerShriek _ ℓ (prod.fst : point k ⨯ point k ⟶ point k)).map
          ((pointDiagAdj ℓ k).unit.app ((boundedConstructibleUpperStar _ ℓ
            (prod.fst : point k ⨯ point k ⟶ point k)).obj y)) := by
    erw [← hCF]
    erw [← hn, reassoc_of% hu, ← Functor.map_comp_assoc]
    simp only [diagUpperStarProjIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      eqToIso.hom] at hG ⊢
    rw [reassoc_of% hG]
    simp only [pointLowerShriekιΦ, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, eqToIso.inv,
      eqToHom_app, Category.assoc]
  rw [Verdier.transportζ, key]
  simp only [Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
