/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuityDefs
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyModules
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived

/-!
# Étale cohomology of sheaves of modules and of their underlying abelian sheaves

For a finite ring `Λ` and an étale sheaf `M` of `Λ`-modules on a scheme `X`, the cohomology
`Hᵠ(X, M)` computed with sheaves of `Λ`-modules vanishes if and only if the cohomology of the
underlying abelian sheaf of `M` vanishes
(`AlgebraicGeometry.Etale.isZero_rightDerived_sectionsFunctor_iff_forget₂`): the underlying
abelian sheaves of an injective resolution of `M` form an acyclic resolution of the underlying
abelian sheaf (`CategoryTheory.Sheaf.subsingleton_H_forget₂_of_injective`), and forgetting the
module structure is exact and faithful.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The forgetful functor from `Λ`-modules to abelian groups is a left adjoint: restriction of
scalars along `ℤ → Λ` is left adjoint to coextension of scalars. -/
lemma isLeftAdjoint_forget₂_moduleCat :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).IsLeftAdjoint := by
  let V := ModuleCat.restrictScalars.{u + 1} (algebraMap ℤ Λ) ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let e : V ≅ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by rfl)
  have : (ModuleCat.restrictScalars.{u + 1} (algebraMap ℤ Λ)).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} (algebraMap ℤ Λ)).isLeftAdjoint
  exact Functor.isLeftAdjoint_of_iso e

/-- Taking underlying abelian sheaves is additive. -/
instance additive_sheafCompose_forget₂' {X : Scheme.{u}} :
    (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).Additive where
  map_add := by
    intros
    rfl

/-- Taking underlying abelian sheaves preserves finite limits. -/
instance preservesFiniteLimits_sheafCompose_forget₂' {X : Scheme.{u}} :
    PreservesFiniteLimits (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) := by
  have : PreservesFiniteLimits (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

/-- Taking underlying abelian sheaves preserves finite colimits. -/
instance preservesFiniteColimits_sheafCompose_forget₂ {X : Scheme.{u}} :
    PreservesFiniteColimits (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) := by
  have := isLeftAdjoint_forget₂_moduleCat (Λ := Λ)
  let hadj := Adjunction.ofIsLeftAdjoint (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have : PreservesLimitsOfSize.{u, u + 1}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).rightAdjoint :=
    hadj.rightAdjoint_preservesLimits
  have : X.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).rightAdjoint :=
    hasSheafCompose_of_preservesLimitsOfSize _
  have := (Sheaf.adjunction X.smallEtaleTopology hadj).isLeftAdjoint
  exact preservesFiniteColimits_of_natIso
    (sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso _ _)

variable [Finite Λ]

/-- The cohomology of an étale sheaf of `Λ`-modules vanishes if and only if the cohomology of its
underlying abelian sheaf vanishes. -/
lemma isZero_rightDerived_sectionsFunctor_iff_forget₂ {X : Scheme.{u}}
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    IsZero (((sectionsFunctor (ModuleCat.{u + 1} Λ) X).rightDerived q).obj M) ↔
      IsZero (((sectionsFunctor AddCommGrpCat.{u + 1} X).rightDerived q).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj M)) := by
  let G := sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let J := injectiveResolution M
  have hacyc (n : ℕ) : (sectionsFunctor AddCommGrpCat.{u + 1} X).rightAcyclic
      (G.obj (J.cocomplex.X n)) := fun m ↦
    (Sheaf.subsingleton_H_iff_isZero_rightDerived _
      (MorphismProperty.Over.mkIdTerminal _ X) (m + 1) _).1
      (Sheaf.subsingleton_H_forget₂_of_injective Λ (J.cocomplex.X n) m)
  let ι' : (CochainComplex.single₀ _).obj (G.obj M) ⟶
      (G.mapHomologicalComplex _).obj J.cocomplex :=
    (G.singleMapHomologicalComplex (ComplexShape.up ℕ) 0).inv.app M ≫
      (G.mapHomologicalComplex _).map J.ι
  have : QuasiIso ι' := by
    dsimp only [ι']
    infer_instance
  rw [(J.isoRightDerivedObj _ q).isZero_iff,
    ((sectionsFunctor AddCommGrpCat.{u + 1} X).rightDerivedObjIsoOfResolution ι' hacyc q).isZero_iff,
    ← HomologicalComplex.exactAt_iff_isZero_homology,
    ← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((((sectionsFunctor (ModuleCat.{u + 1} Λ) X).mapHomologicalComplex _).obj
    J.cocomplex).sc q |>.exact_map_iff_of_faithful
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).symm

end AlgebraicGeometry.Etale
