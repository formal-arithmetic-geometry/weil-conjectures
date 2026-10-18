/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek

/-!

# The lower shriek of an open and closed immersion

For an open immersion `j : U ⟶ X` which is also proper, the derived lower shriek `Rj_!` on
bounded constructible `ℚ̄_ℓ`-sheaves has two identifications: with the extension by zero `j_!`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl`,
through the compactification `U ⟶[j] X ⟶[𝟙] X`) and with the derived pushforward `Rj_*`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl`, through the
compactification `U ⟶[𝟙] U ⟶[j] X`). This file expresses the composite `j_! ≅ Rj_! ≅ Rj_*`
through the single refinement `j` of the first compactification by the second
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_inv_comp`).

## Sorried input

The clauses of blueprint `prop-compactification-coherence-detailed` (subsection
`sk-prop-sf-cbc` of the six-functor chapter) used here, for the lower shriek of bounded
constructible complexes attached to compactifications:

- the comparison of two compactifications through a common refinement does not depend on the
  refinement, so it is the comparison along any given refinement
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_eq`);
- the comparisons satisfy the cocycle condition
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_trans`);
- the comparisons along refinements are transitive under composition
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekRefinementIso_trans`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Compactification coherence -/

section Coherence

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Z Z₁ Z₂ Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom] [LocallyOfFiniteType Z₂.hom] [QuasiCompact Z₂.hom] [IsSeparated Z₂.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- Blueprint `prop-compactification-coherence-detailed`, transitivity clause ("these
transformations are identities for identity refinements and are transitive under
composition"): for refinements `h : Z ⟶ Z₁` and `h₁ : Z₁ ⟶ Z₂` of factorizations
`X ⟶[i] Z ⟶[p] Y`, `X ⟶[i₁] Z₁ ⟶[p₁] Y` and `X ⟶[i₂] Z₂ ⟶[p₂] Y`, the comparison along the
composite `h ≫ h₁` is the composite of the comparisons. -/
theorem boundedConstructibleLowerShriekRefinementIso_trans {i : X ⟶ Z} {i₁ : X ⟶ Z₁}
    {i₂ : X ⟶ Z₂} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left] [IsOpenImmersion i₂.left]
    {h : Z ⟶ Z₁} {h₁ : Z₁ ⟶ Z₂} {h₂ : Z ⟶ Z₂} (sq : IsPullback (𝟙 X) i i₁ h)
    (sq₁ : IsPullback (𝟙 X) i₁ i₂ h₁) (sq₂ : IsPullback (𝟙 X) i i₂ h₂) (_hh : h ≫ h₁ = h₂)
    {p : Z ⟶ Y} {p₁ : Z₁ ⟶ Y} {p₂ : Z₂ ⟶ Y} (wp : h ≫ p₁ = p) (wp₁ : h₁ ≫ p₂ = p₁)
    (wp₂ : h₂ ≫ p₂ = p)
    [IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange Λ ℓ sq)]
    [IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange Λ ℓ sq₁)]
    [IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange Λ ℓ sq₂)] :
    boundedConstructibleLowerShriekRefinementIso Λ ℓ sq₁ wp₁ ≪≫
        boundedConstructibleLowerShriekRefinementIso Λ ℓ sq wp =
      boundedConstructibleLowerShriekRefinementIso Λ ℓ sq₂ wp₂ :=
  sorry

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {f : X ⟶ Y}

/-- Blueprint `prop-compactification-coherence-detailed`, cocycle clause ("the resulting
comparison is independent of that choice and satisfies the cocycle condition for triples of
compactifications"), for bounded constructible `ℚ̄_ℓ`-sheaves. -/
theorem boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_trans
    (c₁ c₂ c₃ : Compactification f.left) :
    boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ c₁ c₂ ≪≫
        boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ c₂ c₃ =
      boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ c₁ c₃ :=
  sorry

/-- Blueprint `prop-compactification-coherence-detailed`, refinement clause ("for a refinement
`u : c₁ → c₂`, the canonical transformation between the compact-support candidates is the
composite of the proper-composition isomorphism with the isomorphism `Ru_* j_{1!} ≅ j_{2!}`";
"comparison through a common refinement gives a natural isomorphism", independent of the choice
of the refinement): the comparison of `c₁` with a refinement `c` of `c₁` is the comparison along
the refinement. -/
theorem boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_eq
    {c c₁ : Compactification f.left} (r : Compactification.OverRefinement c c₁) :
    haveI := r.isProper
    haveI := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl ℓ
      r.isPullback
    boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ c₁ c =
      boundedConstructibleLowerShriekRefinementIso _ ℓ r.isPullback r.hom_overG :=
  sorry

end Coherence

/-! ### The refinement of an open and proper immersion -/

section Clopen

variable {k : Type u} [Field k] {U X : Over (Spec (.of k))} (j : U ⟶ X) [IsOpenImmersion j.left]
  [IsProper j.left]

/-- The open immersion of the trivial compactification `U ⟶[𝟙] U ⟶[j] X` of the proper `j` is an
isomorphism. -/
instance isIso_ofIsProper_overI : IsIso (Compactification.ofIsProper j.left).overI := by
  have : IsIso ((Over.forget _).map (Compactification.ofIsProper j.left).overI) :=
    inferInstanceAs (IsIso (𝟙 U.left))
  exact isIso_of_reflects_iso _ (Over.forget _)

/-- The morphism `j` from the middle object of the compactification `U ⟶[𝟙] U ⟶[j] X` to `X`. -/
noncomputable def openImmersionProperRefinementHom :
    (Compactification.ofIsProper j.left).overObj ⟶ X :=
  Over.homMk j.left (by
    change j.left ≫ X.hom = j.left ≫ X.hom
    rfl)

instance : IsProper (openImmersionProperRefinementHom j).left :=
  inferInstanceAs (IsProper j.left)

omit [IsOpenImmersion j.left] in
lemma openImmersionProperRefinementHom_comp_id :
    openImmersionProperRefinementHom j ≫ 𝟙 X = (Compactification.ofIsProper j.left).overG := by
  ext
  simp [openImmersionProperRefinementHom, Compactification.overG]
  rfl

lemma isPullback_openImmersionProperRefinementHom :
    IsPullback (𝟙 U) (Compactification.ofIsProper j.left).overI j
      (openImmersionProperRefinementHom j) := by
  have : Mono j := Over.mono_of_mono_left j
  refine (IsKernelPair.id_of_mono j).of_iso (Iso.refl _) (Iso.refl _)
    (asIso (Compactification.ofIsProper j.left).overI) (Iso.refl _) (by simp) (by simp)
    (by simp) ?_
  ext
  simp [openImmersionProperRefinementHom, Compactification.overI]
  rfl

/-- The refinement `j` of the compactification `U ⟶[j] X ⟶[𝟙] X` of `j` by the compactification
`U ⟶[𝟙] U ⟶[j] X`. -/
noncomputable def openImmersionProperRefinement :
    Compactification.OverRefinement (Compactification.ofIsProper j.left)
      (Compactification.ofIsOpenImmersion j.left) where
  hom := openImmersionProperRefinementHom j ≫ openImmersionCompactificationHom j
  hom_overG := by
    rw [Category.assoc, openImmersionCompactificationHom_comp_overG,
      openImmersionProperRefinementHom_comp_id]
  isPullback := by
    simpa using (isPullback_openImmersionProperRefinementHom j).paste_horiz
      (isPullback_openImmersionCompactificationHom j)
  isProper := by
    rw [Over.comp_left]
    infer_instance

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- For an open and proper immersion `j`, the composite `j_! ≅ Rj_! ≅ Rj_*` of the two
identifications of the lower shriek is the comparison along the refinement `j` of the
compactification `U ⟶[j] X ⟶[𝟙] X` by `U ⟶[𝟙] U ⟶[j] X`, up to the identifications
`R(𝟙 X)_* ≅ 𝟭` and `(𝟙 U)_! ≅ 𝟭`. -/
lemma boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_inv_comp :
    haveI := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl ℓ
      (isPullback_openImmersionProperRefinementHom j)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).hom =
      (Functor.rightUnitor _).inv ≫
        Functor.whiskerLeft _ (boundedConstructibleLowerStarId _ ℓ X).inv ≫
        (boundedConstructibleLowerShriekRefinementIso _ ℓ
          (isPullback_openImmersionProperRefinementHom j)
          (openImmersionProperRefinementHom_comp_id j)).hom ≫
        Functor.whiskerRight
          (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso _ ℓ j).hom _ ≫
        (Functor.leftUnitor _).hom := by
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl ℓ
    (isPullback_openImmersionProperRefinementHom j)
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl ℓ
    (isPullback_openImmersionCompactificationHom j)
  have := (openImmersionProperRefinement j).isProper
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl ℓ
    (openImmersionProperRefinement j).isPullback
  have hc := congrArg Iso.hom (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_trans
    ℓ (compactificationOverField j) (Compactification.ofIsOpenImmersion j.left)
    (Compactification.ofIsProper j.left))
  have hr := congrArg Iso.hom (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_eq
    ℓ (openImmersionProperRefinement j))
  have ht := congrArg Iso.hom (boundedConstructibleLowerShriekRefinementIso_trans
    (Profinite.padicAlgClRingObj ℓ) ℓ
    (isPullback_openImmersionProperRefinementHom j) (isPullback_openImmersionCompactificationHom j)
    (openImmersionProperRefinement j).isPullback rfl (openImmersionProperRefinementHom_comp_id j)
    (openImmersionCompactificationHom_comp_overG j) (openImmersionProperRefinement j).hom_overG)
  rw [Iso.trans_hom] at hc ht
  rw [boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_eq,
    boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl,
    boundedConstructibleLowerShriekOfCompactificationOfIsProperIso]
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom]
  simp only [← hc, Category.assoc, Iso.inv_hom_id_assoc, hr]
  have ht' := (Iso.inv_comp_eq _).2 ht.symm
  simp only [reassoc_of% ht']

end Clopen

end AlgebraicGeometry.ProEtale.CondensedRing
