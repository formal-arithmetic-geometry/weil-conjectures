/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
public import WeilConjectures.CategoryTheory.DerivedCategory.NotPreservesCoproducts
public import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSiteColimits
public import WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtPullbackHom

/-!
# The pushforward of an elliptic curve does not preserve countable coproducts

For the structure morphism `a_E : E ⟶ Spec k` of an elliptic curve (more generally an abelian
variety of positive dimension) over an algebraically closed field `k`, `Ra_{E*}` does not preserve
countable coproducts on `D(E_proét, Λ)`, so `Ra_{E!} ≅ Ra_{E*}` has no right adjoint.

## Main statements

- `AlgebraicGeometry.ProEtale.exists_forall_hom_ne_zero_rightDerivedLowerStar`.
- `not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety`: `Ra_{E*}` does not
  preserve countable coproducts.
- `AlgebraicGeometry.ProEtale.not_isLeftAdjoint_rightDerivedLowerShriek_of_isAbelianVariety`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace ProEtale

variable (Λ : Type (u + 1)) [Field Λ] {k : Type u} [Field k] [IsAlgClosed k]
  (E : Over (Spec (.of k))) [GrpObj E] [IsAbelianVariety E]

/-- For an elliptic curve (more generally an abelian variety of positive dimension) `E` over an
algebraically closed field `k` and a field `Λ`, there is a pro-étale sheaf `F` of `Λ`-modules on
`E` such that for every `n ≥ 1` there is a nonzero morphism `Λ[0] ⟶ (Ra_{E*} F)[n]` in
`D((Spec k)_proét, Λ)`.
-/
theorem exists_forall_hom_ne_zero_rightDerivedLowerStar (hE : 0 < IsAbelianVariety.dim E) :
    ∃ F : Sheaf (Scheme.ProEt.topology E.left) (ModuleCat.{u + 1} Λ), ∀ n : ℕ,
      ∃ φ : (DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Scheme.ProEt.topology (Spec (.of k))) (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ Λ)) ⟶
        ((R((E.hom)_*[ModuleCat.{u + 1} Λ])).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))⟦((n + 1 : ℕ) : ℤ)⟧, φ ≠ 0 := by
  obtain ⟨U, V, adj, _, _, _, _, _, _, ⟨eU⟩⟩ := exists_exact_evaluation Λ E hE
  let H := Multiplicative (ULift.{u + 1} ℕ →₀ ℤ)
  let triv := Rep.trivial Λ H Λ
  let Λk := (constantSheaf (Scheme.ProEt.topology (Spec (.of k))) (ModuleCat.{u + 1} Λ)).obj
    (ModuleCat.of Λ Λ)
  have : LocallySmall.{u + 1} (Rep.{u + 1} Λ H) := locallySmall_self _
  have : EnoughProjectives (Rep.{u + 1} Λ H) :=
    Rep.equivalenceModuleMonoidAlgebra.enoughProjectives_iff.2 ModuleCat.enoughProjectives.{u + 1}
  let : HasExt.{u + 1} (Rep.{u + 1} Λ H) := hasExt_of_enoughProjectives _
  have : EnoughInjectives (Rep.{u + 1} Λ H) :=
    Rep.equivalenceModuleMonoidAlgebra.enoughInjectives_iff.2
      (ModuleCat.enoughInjectives.{u + 1} (MonoidAlgebra Λ H))
  refine ⟨V.obj triv, fun m ↦ ?_⟩
  obtain ⟨x, hx⟩ := groupCohomology.exists_ext_ne_zero_finsupp (k := Λ) (ULift.{u + 1} ℕ) m
  -- transport `x` along `U Λ_E ≅ Λ`
  let y : Abelian.Ext (U.obj ((E.hom)^*[ModuleCat.{u + 1} Λ].obj Λk)) triv (m + 1) :=
    (Abelian.Ext.mk₀ eU.hom).comp x (zero_add _)
  have hy : y ≠ 0 := fun h ↦ hx (by
    have := congrArg (fun z ↦ (Abelian.Ext.mk₀ eU.inv).comp z (zero_add _)) h
    simp only [y, Abelian.Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id, Abelian.Ext.mk₀_id_comp,
      Abelian.Ext.comp_zero] at this
    exact this)
  obtain ⟨z, hz⟩ := (adj.mapExtCounit_bijective _ triv (m + 1)).2 y
  refine hom_ne_zero_of_ext_ne_zero (ModuleCat.{u + 1} Λ) E.hom Λk (V.obj triv) (m + 1) z
    fun h ↦ hy ?_
  rw [← hz, h, map_zero]

-- the instances `HasSheafCompose` and `PreservesSheafification` on the small pro-étale site
-- take long to synthesize
/-- For the structure morphism `a_E` of an elliptic curve (more generally an abelian variety of
positive dimension) over an algebraically closed field, `Ra_{E*}` does not preserve countable
coproducts on `D(E_proét, Λ)`. -/
theorem not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety
    (hE : 0 < IsAbelianVariety.dim E) :
    ¬ PreservesColimitsOfShape (Discrete ℕ) (R((E.hom)_*[ModuleCat.{u + 1} Λ])) := by
  have := projective_constantSheaf_spec Λ k
  have := preservesColimitsOfShape_sheafSections_of_iso (A := ModuleCat.{u + 1} Λ)
    (Iso.refl (Spec (.of k))) (Discrete ℕ)
  have : PreservesColimitsOfShape (Discrete ℕ)
      (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of k))) (ModuleCat.{u + 1} Λ)) :=
    preservesColimitsOfShape_of_natIso
      (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId _)).symm
  -- exactness of countable coproducts of sheaves on `Spec k`, obtained from `AB5` by shrinking
  -- universes (instance search cannot guess the intermediate universe)
  have : HasExactColimitsOfShape (Discrete ℕ)
      (Sheaf (Scheme.ProEt.topology (Spec (.of k))) (ModuleCat.{u + 1} Λ)) :=
    have : HasFiniteBiproducts
        (Sheaf (Scheme.ProEt.topology (Spec (.of k))) (ModuleCat.{u + 1} Λ)) :=
      HasFiniteBiproducts.of_hasFiniteProducts
    have := AB5OfSize_of_univLE.{0, 0, u + 1, u + 1}
      (Sheaf (Scheme.ProEt.topology (Spec (.of k))) (ModuleCat.{u + 1} Λ))
    (AB4.of_AB5.{0} _).ofShape ℕ
  have := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) E.hom).isRightAdjoint
  obtain ⟨F, hF⟩ := exists_forall_hom_ne_zero_rightDerivedLowerStar Λ E hE
  refine DerivedCategory.not_preservesColimitsOfShape_of_forall_hom_ne_zero
    (R((E.hom)_*[ModuleCat.{u + 1} Λ])) ((DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf (Scheme.ProEt.topology (Spec (.of k))) (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ Λ))) (fun hc π hπ φ ↦ ?_) F fun n ↦ ?_
  · exact DerivedCategory.exists_finset_forall_comp_eq_zero (constantSheafΓAdj _ _) hc π hπ φ
  obtain ⟨φ, hφ⟩ := hF n
  refine ⟨φ ≫ ((R((E.hom)_*[ModuleCat.{u + 1} Λ])).commShiftIso ((n + 1 : ℕ) : ℤ)).inv.app _,
    fun h ↦ hφ ?_⟩
  exact (cancel_mono _).1 (h.trans zero_comp.symm)

/-- For the structure morphism `a_E` of an elliptic curve (more generally an abelian variety of
positive dimension) over an algebraically closed field, `Ra_{E!}` has no right adjoint on
`D(E_proét, Λ)`. -/
theorem not_isLeftAdjoint_rightDerivedLowerShriek_of_isAbelianVariety
    (hE : 0 < IsAbelianVariety.dim E) :
    ¬ (R(E.hom)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint := fun _ ↦
  not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety Λ E hE
    (preservesColimitsOfShape_of_natIso
      (rightDerivedLowerShriekIsoOfIsProper (ModuleCat.{u + 1} Λ) E.hom))

end ProEtale

end AlgebraicGeometry
