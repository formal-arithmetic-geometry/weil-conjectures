/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B9
-/
module

public import Sheaf.Paper.AdicNormalizedFibreData
import WeilConjectures.CategoryTheory.Triangulated.TStructure.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Faithfulness of degree-zero realization on the rational heart

Source: Bhatt--Scholze, Proposition 6.8.14(2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.Scheme.ContinuousRational.NormalizedFibre
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem homology_map_injective_on_singles
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {K L : DerivedCategory C} {M N : C}
    (e : K ≅ (DerivedCategory.singleFunctor C 0).obj M)
    (d : L ≅ (DerivedCategory.singleFunctor C 0).obj N)
    (f g : K ⟶ L)
    (h : (DerivedCategory.homologyFunctor C 0).map f =
      (DerivedCategory.homologyFunctor C 0).map g) : f = g := by
  let T := DerivedCategory.singleFunctor C 0
  let H := DerivedCategory.homologyFunctor C 0
  obtain ⟨a, ha⟩ := T.map_surjective (e.inv ≫ f ≫ d.hom)
  obtain ⟨b, hb⟩ := T.map_surjective (e.inv ≫ g ≫ d.hom)
  have hab : H.map (T.map a) = H.map (T.map b) := by
    rw [ha, hb, H.map_comp, H.map_comp, H.map_comp, H.map_comp, h]
  have he := NatIso.naturality_1 (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0) a
  have hd := NatIso.naturality_1 (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0) b
  have hab' : a = b := he.symm.trans ((congrArg (fun k ↦
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app M ≫ k ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app N) hab).trans hd)
  have hh := (ha.symm.trans ((congrArg T.map hab').trans hb))
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using congrArg (fun k ↦ e.hom ≫ k ≫ d.inv) hh

/-- The H⁰ realization of the rational heart is faithful.
Source: Bhatt--Scholze, Proposition 6.8.14(2).
(blueprint: lem-per-normalized-heart-realization).

Proof: each heart object has realization isomorphic to a sheaf in degree zero.
Conjugate two derived maps by those isomorphisms. Full faithfulness of the single
embedding and its H⁰ comparison show equality of the conjugated maps from equality
on H⁰. The given fully faithful rational realization then reflects equality. -/
theorem realize_faithful (X : Base.{u} l) (a : At l E X) :
    (realize l E X a).Faithful := by
  constructor
  intro F G f g h
  obtain ⟨M, _, ⟨e⟩⟩ := (a.heart F.obj).mp F.property
  obtain ⟨N, _, ⟨d⟩⟩ := (a.heart G.obj).mp G.property
  apply ObjectProperty.hom_ext
  apply (a.fully_faithful F.obj G.obj).injective
  exact homology_map_injective_on_singles e d _ _ h

/-- Short exact heart sequences realize as ambient short exact module sequences.
Source: Bhatt--Scholze, Proposition 6.8.14(2).
(blueprint: lem-per-normalized-heart-realization).

Proof: extend the heart sequence to its distinguished triangle. Realization is triangulated
and respects both t-bounds. Its homology sequence in degrees -1, 0 and 1 is therefore the
specified sheaf sequence with zero outside terms, proving injectivity and surjectivity. -/
theorem realize_short_exact (X : Base.{u} l) (a : At l E X)
    (S : ShortComplex (Heart l E X)) (hS : S.ShortExact) :
    (S.map (realize l E X a)).ShortExact := by
  let t := localizedT l E X
  let : t.Heart (Heart l E X) := t.hasHeartFullSubcategory
  let : a.J.IsTriangulated := a.triangulated
  obtain ⟨δ, hδ⟩ := (t.shortExact_iff_exists_distTriang S).mp hS
  let T := a.J.mapTriangle.obj (Triangle.mk (t.ιHeart.map S.f) (t.ιHeart.map S.g) δ)
  have hT : T ∈ distTriang _ := a.J.map_distinguished _ hδ
  have : (a.J.obj S.X₃.obj).IsGE 0 := (a.t_bounds S.X₃.obj 0).2.mp S.X₃.property.2
  have : (a.J.obj S.X₁.obj).IsLE 0 := (a.t_bounds S.X₁.obj 0).1.mp S.X₁.property.1
  have hz₃ := DerivedCategory.isZero_of_isGE (a.J.obj S.X₃.obj) 0 (-1) (by omega)
  have hz₁ := DerivedCategory.isZero_of_isLE (a.J.obj S.X₁.obj) 0 1 (by omega)
  have hm : Mono ((DerivedCategory.homologyFunctor _ 0).map T.mor₁) := by
    apply (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (-1) 0).mpr
    exact hz₃.eq_of_src _ _
  have he : Epi ((DerivedCategory.homologyFunctor _ 0).map T.mor₂) := by
    apply (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT 0 1).mpr
    exact hz₁.eq_of_tgt _ _
  let : Mono (S.map (realize l E X a)).f := hm
  let : Epi (S.map (realize l E X a)).g := he
  exact ⟨DerivedCategory.HomologySequence.exact₂ T hT 0⟩

end AlgebraicGeometry.Scheme.ContinuousRational.NormalizedFibre
