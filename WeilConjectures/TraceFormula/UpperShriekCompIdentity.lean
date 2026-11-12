/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.TraceFormula.PointNormalizationBaseChange

/-!
# Unit laws of the composition isomorphisms of the exceptional inverse image

For bounded constructible `ℚ̄_ℓ`-sheaves, the composition isomorphisms
`R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!`
(`ProEtale.CondensedRing.boundedConstructibleUpperShriekComp_padicAlgCl`) are compatible with
the identity isomorphisms `R(𝟙 X)^! ≅ 𝟭`
(`ProEtale.CondensedRing.boundedConstructibleUpperShriekId`): both unit laws hold. The left unit
law is `ProEtale.CondensedRing.Correspondence.upperShriekComp_id_left_hom_app`; this file
proves the right unit law by conjugating the right unit law of the lower shriek (using
`CategoryTheory.conjugateIsoEquiv_comp_right_hom_app`), and packages
both (blueprint `proposition-composition-open-restriction-compactifications-f--3`).

## Main statements

- `ProEtale.CondensedRing.boundedConstructibleUpperShriekComp_padicAlgCl_id_right_hom_app`
- `ProEtale.CondensedRing.boundedConstructibleUpperShriekComp_padicAlgCl_unitality`
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CategoryTheory Scheme

open scoped CategoryTheory.Obj

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **Right unit law of the composition isomorphisms of the exceptional inverse image**:
`R(f ≫ 𝟙)^! ≅ R(𝟙)^! ⋙ Rf^! ≅ Rf^!` is the identity. This is conjugate to the right unit law
of the composition isomorphisms of the lower shriek
(`boundedConstructibleLowerShriekComp_padicAlgCl_id_right`). -/
lemma boundedConstructibleUpperShriekComp_padicAlgCl_id_right_hom_app (f : X ⟶ Y)
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperShriekComp_padicAlgCl ℓ f (𝟙 Y)).hom.app K ≫
        (boundedConstructibleUpperShriek ℓ f).map
          ((boundedConstructibleUpperShriekId ℓ Y).hom.app K) =
      eqToHom (congrArg (fun p : X ⟶ Y ↦ (boundedConstructibleUpperShriek ℓ p).obj K)
        (Category.comp_id f)) := by
  rw [← Correspondence.conjugateIsoEquiv_eqToIso_hom_app ℓ (Category.comp_id f) K]
  exact conjugateIsoEquiv_comp_right_hom_app
    (boundedConstructibleUpperShriekAdjunction ℓ (f ≫ 𝟙 Y))
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 Y))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (𝟙 Y))
    (boundedConstructibleLowerShriekId ℓ Y)
    (eqToIso (congrArg (fun p : X ⟶ Y ↦ boundedConstructibleLowerShriek ℓ p)
      (Category.comp_id f)))
    (fun K ↦ by
      rw [boundedConstructibleLowerShriekId, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
        eqToHom_app]
      exact boundedConstructibleLowerShriekComp_padicAlgCl_id_right ℓ f K) K

/-- Blueprint `proposition-composition-open-restriction-compactifications-f--3`: **the
composition comparisons are compatible with the identity morphism**. For bounded constructible
`ℚ̄_ℓ`-sheaves and `f : X ⟶ Y`, both unit laws hold for the composition isomorphisms
`R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` (`boundedConstructibleUpperShriekComp_padicAlgCl`) and the identity
isomorphisms `R(𝟙)^! ≅ 𝟭` (`boundedConstructibleUpperShriekId`):
`R(𝟙 ≫ f)^! ≅ Rf^! ⋙ R(𝟙)^! ≅ Rf^!` and `R(f ≫ 𝟙)^! ≅ R(𝟙)^! ⋙ Rf^! ≅ Rf^!` are the
identifications coming from `𝟙 ≫ f = f` and `f ≫ 𝟙 = f`. -/
theorem boundedConstructibleUpperShriekComp_padicAlgCl_unitality (f : X ⟶ Y)
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperShriekComp_padicAlgCl ℓ (𝟙 X) f).hom.app K ≫
        (boundedConstructibleUpperShriekId ℓ X).hom.app
          ((boundedConstructibleUpperShriek ℓ f).obj K) =
      eqToHom (congrArg (fun p : X ⟶ Y ↦ (boundedConstructibleUpperShriek ℓ p).obj K)
        (Category.id_comp f)) ∧
    (boundedConstructibleUpperShriekComp_padicAlgCl ℓ f (𝟙 Y)).hom.app K ≫
        (boundedConstructibleUpperShriek ℓ f).map
          ((boundedConstructibleUpperShriekId ℓ Y).hom.app K) =
      eqToHom (congrArg (fun p : X ⟶ Y ↦ (boundedConstructibleUpperShriek ℓ p).obj K)
        (Category.comp_id f)) :=
  ⟨Correspondence.upperShriekComp_id_left_hom_app ℓ f K,
    boundedConstructibleUpperShriekComp_padicAlgCl_id_right_hom_app ℓ f K⟩

end AlgebraicGeometry.ProEtale.CondensedRing
