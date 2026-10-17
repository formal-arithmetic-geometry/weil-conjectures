/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.HypercoverCohomologyColimit
public import WeilConjectures.AlgebraicGeometry.HypercoverCohomologyProof
public import WeilConjectures.AlgebraicGeometry.HypercoverColimitCriterion
public import WeilConjectures.AlgebraicGeometry.HypercoverFreeResolution
public import WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverRefinement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Étale cohomology is computed by finite split hypercovers

Blueprint `thm-weil-pbc-hypercover-cohomology`: for a quasi-compact quasi-separated scheme `X`,
the étale cohomology `H^q(X, F)` is the colimit of the cohomology groups `H^q(C(U, F))` over the
finite split étale hypercovers `U` of `X` and their refinements modulo homotopy, both for
abelian sheaves and for sheaves of modules over a ring.
-/

@[expose] public section

universe u₁

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

namespace FiniteSplitEtaleHypercover

variable {X : Scheme.{u₁}} [CompactSpace X] [QuasiSeparatedSpace X]

lemma IsCohomologyColimit.ofIso {A : Type*} [Category* A] [Abelian A] {q : ℕ}
    {H H' : Sheaf X.smallEtaleTopology A ⥤ A} (h : IsCohomologyColimit A q H) (e : H ≅ H') :
    IsCohomologyColimit A q H' := by
  obtain ⟨hhom, c, hc, hu⟩ := h
  refine ⟨hhom, fun U ↦ c U ≫ e.hom, fun U V f ↦ by rw [← Category.assoc, hc], ?_⟩
  intro F B d hd
  obtain ⟨g, hg, hgu⟩ := hu F B d hd
  refine ⟨e.inv.app F ≫ g, fun U ↦ ?_, fun g' hg' ↦ ?_⟩
  · simp [hg]
  · rw [← hgu (e.hom.app F ≫ g') (fun U ↦ by rw [← Category.assoc, ← NatTrans.comp_app, hg'])]
    simp

/-- A natural isomorphism of additive functors induces isomorphisms of right derived
functors. -/
noncomputable def rightDerivedIsoOfIso {C D : Type*} [Category* C] [Category* D] [Abelian C]
    [Abelian D] [HasInjectiveResolutions C] {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived e.hom n
  inv := NatTrans.rightDerived e.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

lemma elementwiseAbelian_ab : ElementwiseAbelian AddCommGrpCat.{u₁ + 1} where
  sub_apply _ _ _ := rfl
  exact_of_elem S h := (ShortComplex.ab_exact_iff S).2 h
  elem_of_exact S hS := (ShortComplex.ab_exact_iff S).1 hS
  injective_of_mono f _ := (AddCommGrpCat.mono_iff_injective f).1 inferInstance
  surjective_of_epi f _ := (AddCommGrpCat.epi_iff_surjective f).1 inferInstance
  isIso_of_bijective f hf := by
    have : IsIso ((CategoryTheory.forget AddCommGrpCat).map f) := (isIso_iff_bijective _).2 hf
    exact isIso_of_reflects_iso f (CategoryTheory.forget _)

lemma elementwiseAbelian_moduleCat (R : Type (u₁ + 1)) [Ring R] :
    ElementwiseAbelian (ModuleCat.{u₁ + 1} R) where
  sub_apply _ _ _ := rfl
  exact_of_elem S h := (ShortComplex.moduleCat_exact_iff S).2 h
  elem_of_exact S hS := (ShortComplex.moduleCat_exact_iff S).1 hS
  injective_of_mono f _ := (ModuleCat.mono_iff_injective f).1 inferInstance
  surjective_of_epi f _ := (ModuleCat.epi_iff_surjective f).1 inferInstance
  isIso_of_bijective f hf := by
    have : IsIso ((CategoryTheory.forget (ModuleCat R)).map f) := (isIso_iff_bijective _).2 hf
    exact isIso_of_reflects_iso f (CategoryTheory.forget _)

lemma hasLocalMk_ab : HasLocalMk AddCommGrpCat.{u₁ + 1} := by
  intro Y B φ hφ
  have hadd : ∀ y₁ y₂, φ (y₁ + y₂) = φ y₁ + φ y₂ := by
    intro y₁ y₂
    obtain ⟨Z, a, b, z₁, z₂, rfl, rfl, h⟩ := hφ y₁ y₂
    rw [← map_add, h, h, h, map_add]
  exact ⟨AddCommGrpCat.ofHom (AddMonoidHom.mk' φ hadd), fun _ ↦ rfl⟩

lemma hasLocalMk_moduleCat (R : Type (u₁ + 1)) [Ring R] : HasLocalMk (ModuleCat.{u₁ + 1} R) := by
  intro Y B φ hφ
  have hadd : ∀ y₁ y₂, φ (y₁ + y₂) = φ y₁ + φ y₂ := by
    intro y₁ y₂
    obtain ⟨Z, a, b, z₁, z₂, rfl, rfl, h⟩ := hφ y₁ y₂
    rw [← map_add, h, h, h, map_add]
  have hsmul : ∀ (r : R) y, φ (r • y) = r • φ y := by
    intro r y
    obtain ⟨Z, a, b, z₁, z₂, rfl, -, h⟩ := hφ y y
    rw [← map_smul, h, h, map_smul]
  exact ⟨ModuleCat.ofHom { toFun := φ, map_add' := hadd, map_smul' := hsmul }, fun _ ↦ rfl⟩

end FiniteSplitEtaleHypercover

open FiniteSplitEtaleHypercover SplitEtaleHypercover

/-- Blueprint `thm-weil-pbc-hypercover-cohomology`: étale cohomology of a quasi-compact
quasi-separated scheme is the colimit over finite split étale hypercovers of their cohomology,
for abelian sheaves and for sheaves of modules. -/
theorem hypercover_cohomology (X : Scheme.{u₁}) [CompactSpace X] [QuasiSeparatedSpace X]
    (q : ℕ) :
    FiniteSplitEtaleHypercover.IsCohomologyColimit AddCommGrpCat.{u₁ + 1} q
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u₁ + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u₁ + 1} X (q : ℤ)) ∧
    ∀ (R : Type (u₁ + 1)) [Ring R],
      FiniteSplitEtaleHypercover.IsCohomologyColimit (ModuleCat.{u₁ + 1} R) q
        (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u₁ + 1} R)) 0 ⋙
          Etale.cohomology (ModuleCat.{u₁ + 1} R) X (q : ℤ)) := by
  constructor
  · have hA : ElementwiseAbelian AddCommGrpCat.{u₁ + 1} := elementwiseAbelian_ab
    let Free := AddCommGrpCat.free.{u₁ + 1}
    have hfin : ∀ (S : Type (u₁ + 1)) (x : ToType (Free.obj S)), ∃ F : Set S, F.Finite ∧
        x ∈ Set.range (Free.map (↾(Subtype.val : F → S))) :=
      fun _ x ↦ freeAbelianGroup_exists_finite x
    have h := isCohomologyColimit_of hasLocalMk_ab q _
      (fun U V f g h ↦ cohomologyRefinement_eq_of_isRefinementHomotopic _ h q)
      (cnat hA Free AddCommGrpCat.adj hfin q)
      (fun U V f ↦ cnat_refinement hA Free AddCommGrpCat.adj hfin q f)
      (fun F y ↦ cmap_surjective hA Free AddCommGrpCat.adj hfin q F y)
      (fun U F x hx ↦ cmap_injective hA Free AddCommGrpCat.adj hfin q U F x hx)
      (exists_common_refinement (X := X))
    refine h.ofIso (Iso.trans
      (Y := (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u₁ + 1}).rightDerived q)
      ?_ (Iso.symm ?_))
    · exact rightDerivedIsoOfIso
        (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u₁ + 1}
          terminalIsTerminal).symm q
    · exact Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
          (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u₁ + 1}).rightDerivedFunctorPlusCompatibility.symm)
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u₁ + 1} (q : ℤ)) ≪≫
          (Sheaf.Γ X.smallEtaleTopology
            AddCommGrpCat.{u₁ + 1}).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q
  · intro R _
    have hA := elementwiseAbelian_moduleCat R
    let Free := ModuleCat.free.{u₁ + 1} R
    have hfin : ∀ (S : Type (u₁ + 1)) (x : ToType (Free.obj S)), ∃ F : Set S, F.Finite ∧
        x ∈ Set.range (Free.map (↾(Subtype.val : F → S))) :=
      fun _ x ↦ finsupp_exists_finite x
    have h := isCohomologyColimit_of (hasLocalMk_moduleCat R) q _
      (fun U V f g h ↦ cohomologyRefinement_eq_of_isRefinementHomotopic _ h q)
      (cnat hA Free (ModuleCat.adj R) hfin q)
      (fun U V f ↦ cnat_refinement hA Free (ModuleCat.adj R) hfin q f)
      (fun F y ↦ cmap_surjective hA Free (ModuleCat.adj R) hfin q F y)
      (fun U F x hx ↦ cmap_injective hA Free (ModuleCat.adj R) hfin q U F x hx)
      (exists_common_refinement (X := X))
    refine h.ofIso (Iso.trans
      (Y := (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u₁ + 1} R)).rightDerived q) ?_ (Iso.symm ?_))
    · exact rightDerivedIsoOfIso
        (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u₁ + 1} R)
          terminalIsTerminal).symm q
    · exact Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
          (Sheaf.Γ X.smallEtaleTopology
            (ModuleCat.{u₁ + 1} R)).rightDerivedFunctorPlusCompatibility.symm)
        (DerivedCategory.homologyFunctor (ModuleCat.{u₁ + 1} R) (q : ℤ)) ≪≫
          (Sheaf.Γ X.smallEtaleTopology
            (ModuleCat.{u₁ + 1} R)).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q

end AlgebraicGeometry
