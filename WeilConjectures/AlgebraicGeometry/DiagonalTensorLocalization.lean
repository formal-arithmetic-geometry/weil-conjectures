/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarRestrictionTensor
import WeilConjectures.Mathlib.CategoryTheory.Conj

/-! # Transport of a diagonal tensor retract through localization

This is the localization step in the termwise diagonal-summand argument of the
finite-ring Kunneth proof. The tensorator is the given normalized tensorator.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u r
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

variable {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
  [Abelian C] [Abelian D] [IsGrothendieckAbelian.{u + 1} C]
  [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [SymmetricCategory C] [SymmetricCategory D]
  [MonoidalClosed C] [MonoidalClosed D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [HasDerivedCategory.{u + 1} C] [HasDerivedCategory.{u + 1} D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (ordinary : G.LaxMonoidal) (t : RestrictionTensorData G ordinary)
  (K L : CochainComplex C ℤ)

/-- A normalized tensorator transports a diagonal retract on tensor complexes to the
localized tensor objects.
Source: finite-ring Kunneth proof, first paragraph, termwise then K-flat comparison.

Proof. Let i be the tensor of the exact-restriction localization factors followed by the
F-tensor comparison, and let j be restriction of the B-tensor comparison followed by its
localization factor. Both are isomorphisms by the two assumptions. The normalization square
says t.map followed by j equals i followed by Q(t.chain). Define the section by j, Q(s),
and inverse i. Define the action by Q(a) conjugated by inverse i. Cancelling i and j and
applying Q to the two chain identities proves both composites. The final equation records
the action explicitly and makes every coefficient normalization transportable.
(blueprint: lem-pur-diagonal-tensor-localization). -/
theorem diagonalTensorLocalization
    [IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q K L)]
    [IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
      ((G.mapHomologicalComplex (.up ℤ)).obj K)
      ((G.mapHomologicalComplex (.up ℤ)).obj L))]
    {A : Type r} [Semiring A]
    (a : A →+* End ((G.mapHomologicalComplex (.up ℤ)).obj K ⊗
      (G.mapHomologicalComplex (.up ℤ)).obj L))
    (s : (G.mapHomologicalComplex (.up ℤ)).obj (K ⊗ L) ⟶
      (G.mapHomologicalComplex (.up ℤ)).obj K ⊗
        (G.mapHomologicalComplex (.up ℤ)).obj L)
    (e : A) (hs : s ≫ t.chain K L = 𝟙 _)
    (hp : t.chain K L ≫ s = a e) :
    ∃ (ad : A →+* End
        (G.mapDerivedCategory.obj (DerivedCategory.Q.obj K) ⊗
          G.mapDerivedCategory.obj (DerivedCategory.Q.obj L)))
      (sd : G.mapDerivedCategory.obj (DerivedCategory.Q.obj K ⊗ DerivedCategory.Q.obj L) ⟶
        G.mapDerivedCategory.obj (DerivedCategory.Q.obj K) ⊗
          G.mapDerivedCategory.obj (DerivedCategory.Q.obj L)),
      sd ≫ t.map (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) = 𝟙 _ ∧
      t.map (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫ sd = ad e ∧
      ∀ x : A, ad x =
        (G.mapDerivedCategoryFactors.hom.app K ⊗ₘ G.mapDerivedCategoryFactors.hom.app L) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q _ _ ≫ DerivedCategory.Q.map (a x) ≫
        inv (Functor.LaxMonoidal.μ DerivedCategory.Q _ _) ≫
        (G.mapDerivedCategoryFactors.inv.app K ⊗ₘ G.mapDerivedCategoryFactors.inv.app L) := by
  let i := tensorIso (G.mapDerivedCategoryFactors.app K)
      (G.mapDerivedCategoryFactors.app L) ≪≫
    asIso (Functor.LaxMonoidal.μ DerivedCategory.Q
      ((G.mapHomologicalComplex (.up ℤ)).obj K)
      ((G.mapHomologicalComplex (.up ℤ)).obj L))
  let j := G.mapDerivedCategory.mapIso
      (asIso (Functor.LaxMonoidal.μ DerivedCategory.Q K L)) ≪≫
    G.mapDerivedCategoryFactors.app (K ⊗ L)
  let ad := i.symm.conjRingEquiv.toRingHom.comp
    ((Functor.mapEndRingHom DerivedCategory.Q _).comp a)
  let sd := j.hom ≫ DerivedCategory.Q.map s ≫ i.inv
  have ht : t.map (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) =
      i.hom ≫ DerivedCategory.Q.map (t.chain K L) ≫ j.inv := by
    apply (cancel_mono j.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simpa only [i, j, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
      Iso.app_hom, tensorIso_hom, Category.assoc] using t.normalization K L
  refine ⟨ad, sd, ?_, ?_, ?_⟩
  · rw [ht]
    simp only [sd, Category.assoc, Iso.inv_hom_id_assoc,
      ← DerivedCategory.Q.map_comp_assoc, hs, DerivedCategory.Q.map_id, Category.id_comp,
      Iso.hom_inv_id]
  · rw [ht]
    simp only [sd, Category.assoc, Iso.inv_hom_id_assoc,
      ← DerivedCategory.Q.map_comp_assoc, hp]
    rfl
  · intro x
    change i.hom ≫ DerivedCategory.Q.map (a x) ≫ i.inv = _
    simp only [i, Iso.trans_hom, Iso.trans_inv, tensorIso_hom, tensorIso_inv,
      Iso.app_hom, Iso.app_inv, asIso_hom, asIso_inv, Category.assoc]

#print axioms diagonalTensorLocalization

end AlgebraicGeometry.Etale
