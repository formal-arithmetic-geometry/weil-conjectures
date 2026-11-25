/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.FieldTheory.IsSepClosed

import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-!
# Colimits of pointed étale residue triples

The ring diagram of pointed étale residue triples has a colimit, with compatible maps from `R`
and to `K`.

## Implementation details

Triples embed fully faithfully into arrows `B → K` from the opposite of the affine étale site
over `Spec R`. Essential smallness of that site (`Scheme.AffineEtale.instEssentiallySmall`)
makes the category of triples essentially small, so `CommRingCat` has the required colimit.
The map `ρ` comes from the identity triple on `R`, and `ψ` is the descent of the cocone of
residue maps with vertex `K`. Filteredness is not needed for existence.

## References

* Stacks Project, Tag 04GW
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Forget the étale structure morphism, retaining its ring. -/
private noncomputable def affineEtaleRings (R : CommRingCat.{u}) :
    (Spec R).AffineEtaleᵒᵖ ⥤ CommRingCat.{u} where
  obj t := t.unop.left.unop
  map f := f.unop.left.unop

/-- Regard a pointed ring as an arrow from an affine étale ring to `K`. -/
private noncomputable def triplesToPointedRings (R : CommRingCat.{u}) (p : Spec R)
    (K : Type u) [Field K] (χ : (Spec R).residueField p ⟶ CommRingCat.of K) :
    EtaleResidueTriples R p K χ ⥤ CostructuredArrow (affineEtaleRings R) (.of K) where
  obj t := CostructuredArrow.mk (Y := Opposite.op
    (MorphismProperty.CostructuredArrow.mk ⊤ (Spec.map t.α) t.etale))
    ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ)
  map {t s} f := CostructuredArrow.homMk
    (Quiver.Hom.op (MorphismProperty.CostructuredArrow.homMk
      f.hom.right.left.op trivial (by
        have h := congrArg Over.Hom.left (Under.w f.hom)
        simp only [EtaleResidueTriple.factorization, Under.mk_hom, Over.homMk_left,
          Over.comp_left] at h
        change Spec.map f.hom.right.left ≫ Spec.map t.α = Spec.map s.α
        rw [← Spec.map_comp, h]))) (by
      change f.hom.right.left ≫
        ((ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ) =
        (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ
      simpa only [EtaleResidueTriple.factorization,
        Under.mk_right, Over.mk_hom, Category.assoc] using Over.w f.hom.right)
  map_id t := by ext; rfl
  map_comp f g := by ext; rfl

/-- Every map of pointed étale rings comes from a map of triples. -/
private noncomputable def triplesToPointedRingsFullyFaithful
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K) :
    (triplesToPointedRings R p K χ).FullyFaithful where
  preimage {t s} f := InducedCategory.homMk
    (Under.homMk (Over.homMk f.left.unop.left.unop (by
      have h := CostructuredArrow.w f
      change f.left.unop.left.unop ≫
        ((ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ) =
        (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ at h
      simpa only [EtaleResidueTriple.factorization, Under.mk_right, Over.mk_hom,
        Category.assoc] using h)) (by
      apply Over.OverMorphism.ext
      change t.α ≫ f.left.unop.left.unop = s.α
      apply Spec.map_injective
      rw [Spec.map_comp]
      exact f.left.unop.w))
  map_preimage f := by ext; rfl
  preimage_map f := by ext; rfl

/-- A compatible cocone and its colimit exist for pointed étale residue triples. -/
theorem etaleResidueTriples_exists_colimit_part
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    [Algebra ((Spec R).residueField p) K] [IsSepClosure ((Spec R).residueField p) K] :
    ∃ c : Cocone (etaleResidueTriplesRingDiagram R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))),
      Nonempty (IsColimit c) ∧ ∃ (ρ : R ⟶ c.pt) (ψ : c.pt →+* K),
        (∀ t, t.α ≫ c.ι.app t = ρ) ∧
        (∀ t, ψ.comp (c.ι.app t).hom =
          ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom) := by
  classical
  let χ := CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K)
  let D := etaleResidueTriplesRingDiagram R p K χ
  have : (triplesToPointedRings R p K χ).Full :=
    (triplesToPointedRingsFullyFaithful R p K χ).full
  have : (triplesToPointedRings R p K χ).Faithful :=
    (triplesToPointedRingsFullyFaithful R p K χ).faithful
  have : EssentiallySmall.{u} (EtaleResidueTriples R p K χ) :=
    essentiallySmall_of_fully_faithful (triplesToPointedRings R p K χ)
  have : HasColimitsOfShape (EtaleResidueTriples R p K χ) CommRingCat.{u} :=
    HasColimitsOfShape.of_essentiallySmall _ _
  let c := colimit.cocone D
  let hc := colimit.isColimit D
  let t0 : EtaleResidueTriples R p K χ :=
    ⟨R, 𝟙 R, inferInstance, p, by simp, χ, by simp⟩
  let k : Cocone D :=
    { pt := CommRingCat.of K
      ι :=
        { app := fun t => (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ
          naturality := fun t s f => by
            change f.hom.right.left ≫ _ = _ ≫ 𝟙 _
            simpa only [Category.comp_id, EtaleResidueTriple.factorization,
              Under.mk_right, Over.mk_hom, Category.assoc] using Over.w f.hom.right } }
  refine ⟨c, ⟨hc⟩, c.ι.app t0, (hc.desc k).hom, ?_, ?_⟩
  · intro t
    let f : t0 ⟶ t := InducedCategory.homMk
      (Under.homMk (Over.homMk t.α t.compatible) (by
        apply Over.OverMorphism.ext
        change (𝟙 R) ≫ t.α = t.α
        simp))
    exact c.w f
  · intro t
    exact congrArg CommRingCat.Hom.hom (hc.fac k t)

end AlgebraicGeometry.Scheme
