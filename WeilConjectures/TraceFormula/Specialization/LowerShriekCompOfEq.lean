/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.CompactSupportExchange

/-!

# Associativity of the transported composition isomorphisms of the lower shriek

For `j : B ⟶ F`, `d : F ⟶ X` and `a : X ⟶ P`, with `d ≫ a = a_F` and `(j ≫ d) ≫ a = a_B`, the
identifications `Ra_{F!} Rj_! ≅ Ra_! Rd_! Rj_! ≅ Ra_! R(j ≫ d)_! ≅ Ra_{B!}` and
`Ra_{F!} Rj_! ≅ Ra_{B!}` of `lowerShriekCompOfEq` agree
(`ProEtale.CondensedRing.lowerShriekCompOfEq_hom_app_comp_map_comp_inv_app`), by the associativity
of the composition isomorphisms (`boundedConstructibleLowerShriekComp_padicAlgCl_assoc`).
For an equality `f = g` of proper morphisms, `Ra_! Rf_* ≅ Ra_! Rf_! ≅ Ra_{B!}` is the transport of
`Ra_! Rg_* ≅ Ra_! Rg_! ≅ Ra_{B!}`
(`ProEtale.CondensedRing.map_isoLowerStar_eqToHom_comp_lowerShriekCompOfEq_inv`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {B F X P : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType F.hom] [QuasiCompact F.hom] [IsSeparated F.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

/-- **Associativity of `lowerShriekCompOfEq`**: `Ra_{F!} Rj_! ≅ Ra_! Rd_! Rj_! ≅ Ra_! R(j ≫ d)_!
≅ Ra_{B!}` is the inverse of `Ra_{B!} ≅ Ra_{F!} Rj_!`. -/
theorem lowerShriekCompOfEq_hom_app_comp_map_comp_inv_app (j : B ⟶ F) (d : F ⟶ X) (a : X ⟶ P)
    {aF : F ⟶ P} {aB : B ⟶ P} (wF : d ≫ a = aF) (wB : (j ≫ d) ≫ a = aB)
    (N : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (lowerShriekCompOfEq ℓ d a wF).hom.app ((boundedConstructibleLowerShriek ℓ j).obj N) ≫
        (boundedConstructibleLowerShriek ℓ a).map
          ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ j d).inv.app N) ≫
        (lowerShriekCompOfEq ℓ (j ≫ d) a wB).inv.app N =
      (lowerShriekCompOfEq ℓ j aF (by rw [← wF, ← wB, Category.assoc])).inv.app N := by
  subst wF wB
  have h := boundedConstructibleLowerShriekComp_padicAlgCl_assoc ℓ j d a N
  simp only [lowerShriekCompOfEq, eqToIso_refl, Iso.refl_trans]
  rw [← cancel_epi ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ j (d ≫ a)).hom.app N),
    Iso.hom_inv_id_app]
  have h2 : (boundedConstructibleLowerShriekComp_padicAlgCl ℓ j (d ≫ a)).hom.app N ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ d a).hom.app
        ((boundedConstructibleLowerShriek ℓ j).obj N) =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (j ≫ d) a).hom.app N ≫
        (boundedConstructibleLowerShriek ℓ a).map
          ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ j d).hom.app N) := by
    rw [h, eqToHom_refl, Category.id_comp]
  rw [reassoc_of% h2, ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.hom_inv_id_app]
  rfl

/-- Transport of `Ra_! Rf_* ≅ Ra_! Rf_! ≅ Ra_{B!}` along an equality `f = g` of proper morphisms. -/
theorem map_isoLowerStar_eqToHom_comp_lowerShriekCompOfEq_inv {f g : B ⟶ X} (h : f = g)
    (a : X ⟶ P) [IsProper f.left] [IsProper g.left] {aB : B ⟶ P} (wf : f ≫ a = aB)
    (wg : g ≫ a = aB) (Q : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ a).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app Q ≫
          eqToHom (by rw [h]) ≫
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app Q) ≫
        (lowerShriekCompOfEq ℓ g a wg).inv.app Q =
      (lowerShriekCompOfEq ℓ f a wf).inv.app Q := by
  subst h
  simp

end AlgebraicGeometry.ProEtale.CondensedRing
