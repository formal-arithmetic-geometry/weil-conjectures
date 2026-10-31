/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingMappingTower
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import all WeilConjectures.AlgebraicGeometry.PurSequenceConstantRingFactorization
import all WeilConjectures.CategoryTheory.TowerRightDerivedEvaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.SixFunctors.CoefCompletedTowerSectionsAcyclic

/-! # Natural scalar comparison on the entire input derived category -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] Functor.leftAdjoint limit

universe a b c d va vb vc vd

private def scalarHomTransport
    {A : Type a} [Category.{va} A] {B : Type b} [Category.{vb} B]
    {C : Type c} [Category.{vc} C] {D : Type d} [Category.{vd} D]
    (F : A ⥤ B) (L : B ⥤ C) (R : C ⥤ B) (V : A ⥤ C)
    (H : Bᵒᵖ × B ⥤ B) (J : Cᵒᵖ × C ⥤ C)
    (G : B ⥤ D) (T : C ⥤ D) (N : C) (N' : B)
    (r : R.obj N ≅ N') (v : F ⋙ L ≅ V)
    (s : (L.op.prod (𝟭 C)) ⋙ J ⋙ R ≅ ((𝟭 Bᵒᵖ).prod R) ⋙ H)
    (t : R ⋙ G ≅ T) :
    F.op ⋙ (Functor.curry.obj H).flip.obj N' ⋙ G ≅
      V.op ⋙ Prod.sectL _ N ⋙ J ⋙ T := by
  let h := (Functor.curry.obj H).flip.mapIso r.symm
  let first : F.op ⋙ (Functor.curry.obj H).flip.obj N' ⋙ G ≅
      F.op ⋙ (Functor.curry.obj H).flip.obj (R.obj N) ⋙ G :=
    Functor.isoWhiskerLeft F.op (Functor.isoWhiskerRight h G)
  let sh : F.op ⋙ (Functor.curry.obj H).flip.obj (R.obj N) ⋙ G ≅
      ((F.op ⋙ Prod.sectL _ N) ⋙ ((𝟭 Bᵒᵖ).prod R) ⋙ H) ⋙ G :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro K K' f
      change G.map (H.map (Prod.mkHom (F.map f.unop).op (𝟙 _))) ≫ 𝟙 _ =
        𝟙 _ ≫ G.map (H.map (Prod.mkHom (F.map f.unop).op (R.map (𝟙 N))))
      simp only [Category.id_comp, Category.comp_id]
      exact congrArg (fun g ↦ G.map (H.map (Prod.mkHom (F.map f.unop).op g)))
        (R.map_id N).symm)
  let middle := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (F.op ⋙ Prod.sectL _ N) s.symm) G
  let last := Functor.isoWhiskerLeft (V.op ⋙ Prod.sectL _ N ⋙ J) t
  let changeInput := Functor.isoWhiskerRight
    (NatIso.op v.symm) (Prod.sectL _ N ⋙ J ⋙ R ⋙ G)
  exact first ≪≫ sh ≪≫ middle ≪≫ changeInput ≪≫ last

private def derivedUnit
    {A : Type a} [Category.{va} A] {B : Type b} [Category.{vb} B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions A] (T : A ⥤ B) [T.Additive] :
    T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ T.rightDerivedFunctor :=
  { app := T.rightDerivedFunctorUnitQ
    naturality := by
      intro K L f
      exact T.rightDerivedFunctorUnitQ_naturality f }

private def derivedComposite
    {A : Type a} [Category.{va} A] {B : Type b} [Category.{vb} B]
    {C : Type c} [Category.{vc} C] [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (h : ∀ (I : CochainComplex A ℤ), I.IsKInjective →
      IsIso (G.rightDerivedFunctorUnitQ ((F.mapHomologicalComplex (.up ℤ)).obj I))) :
    (F ⋙ G).rightDerivedFunctor ≅ F.mapDerivedCategory ⋙ G.rightDerivedFunctor := by
  let b : (F ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.mapDerivedCategory ⋙ G.rightDerivedFunctor :=
    Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ)) (derivedUnit G) ≫
      Functor.whiskerRight F.mapDerivedCategoryFactors.inv G.rightDerivedFunctor
  let hβ := TowerRightDerivedEvaluation.descend_comparison
    (fun K ↦ by
      obtain ⟨I, hI, f, _, hf⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
      exact ⟨I, f, hI, hf⟩)
    (F ⋙ G).rightDerivedFunctor (F.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    _ (derivedUnit (F ⋙ G)) b
    (fun I hI ↦ by
      have := hI
      dsimp only [derivedUnit]
      change IsIso ((F ⋙ G).rightDerivedFunctorUnitQ I)
      rw [Functor.rightDerivedFunctorUnitQ_eq]
      infer_instance)
    (fun I hI ↦ by
      have := h I hI
      dsimp only [b, derivedUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app]
      change IsIso (G.rightDerivedFunctorUnitQ _ ≫
        G.rightDerivedFunctor.map (F.mapDerivedCategoryFactors.inv.app I))
      infer_instance)
  exact hβ.choose

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

private theorem ordinaryRestriction :
    coefHomOrdinaryRestriction l E X ⋙ (coefHomEquivalence l E X).functor =
      coefficientSequenceRestriction l E X := by
  exact firstFactor_restriction l E X

private def restrictionComparison :
    coefHomDerivedRestriction l E X ≅
      coefficientSequenceDerivedRestriction l E X ⋙
        (coefHomEquivalence l E X).inverse.mapDerivedCategory := by
  let e := (coefHomEquivalence l E X).mapDerivedCategory
  let r : coefHomDerivedRestriction l E X ⋙ e.functor ≅
      coefficientSequenceDerivedRestriction l E X :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (eqToIso (ordinaryRestriction l E X))
  exact (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ e.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight r e.inverse

private def reductionComparison
    (M : ScalarHomModels.{u + 1, u, u, u + 2}
      (coefficientSequenceTopology (ProEt.topology X)))
    (S : CoefficientDerivedSystemCalculus l E X) :
    coefHomDerivedConstant l E X ⋙ (M.scalar (coefHomScalarMap l E X)).derived ≅
      S.reduction := by
  let e := (coefHomEquivalence l E X).mapDerivedCategory
  let Δ : scalarReductionSource l E X ⥤ (ℕᵒᵖ ⥤ scalarReductionSource l E X) :=
    Functor.const ℕᵒᵖ
  let ac := (constLimAdj : Δ ⊣ lim).mapDerivedCategoryRightDerivedAdjunction
  let ad := ((ac.comp e.symm.toAdjunction).ofNatIsoLeft
    (Functor.mapDerivedCategoryCompIso Δ (coefHomEquivalence l E X).inverse).symm).comp
      (M.scalar (coefHomScalarMap l E X)).adjunction
  let r : coefHomDerivedRestriction l E X ⋙ e.functor ≅
      coefficientSequenceDerivedRestriction l E X :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (eqToIso (ordinaryRestriction l E X))
  exact (ad.ofNatIsoRight
    (Functor.isoWhiskerRight r (coefficientConstantTowerLimit l E X))).leftAdjointUniq
      S.adjunction

private def levelSectionsComparison :
    coefHomSections l E X ≅ coefTraceConstantScalars l E X ⋙
      (sheafSections (ProEt.topology X) (ModuleCat.{u + 1} (coefTraceRing l E))).obj
        (op (ProEt.mk (𝟙 X))) := by
  let T := op (ProEt.mk (𝟙 X))
  let ht : IsInitial T := (MorphismProperty.Over.mkIdTerminal _ _).op
  have hi : ht.to T = 𝟙 T := ht.hom_ext _ _
  let F := coefHomSections l E X
  let G := coefTraceConstantScalars l E X ⋙
    (sheafSections (ProEt.topology X) (ModuleCat.{u + 1} (coefTraceRing l E))).obj T
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine LinearEquiv.toModuleIso
      (show F.obj M ≃ₗ[coefTraceRing l E] G.obj M from
        { toFun := fun x ↦ x
          invFun := fun x ↦ x
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := ?_ })
    intro r x
    let : Module ((completedIntegralCoefficientSheafUnrestricted l E X).obj.obj T)
        (F.obj M) := (M.val.obj T).isModule
    change (coefTraceScalar l E X r) • x =
      ((completedIntegralCoefficientSheafUnrestricted l E X).obj.map (ht.to T)).hom
        (coefTraceScalar l E X r) • x
    rw [hi, (completedIntegralCoefficientSheafUnrestricted l E X).obj.map_id T]
    rfl
  · intro M N f
    ext x
    rfl

private def sectionsComparison :
    coefHomDerivedRestriction l E X ⋙ coefHomConstantDerivedSections l E X ≅
      coefPairingSections l E X := by
  let r := coefHomOrdinaryRestriction l E X
  let e := (coefHomEquivalence l E X).functor
  let f := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (coefTraceConstantScalars l E X)
  let g := coefTraceSections l E X
  let σ : coefHomTowerSections l E X ≅ f ⋙ g :=
    (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (levelSectionsComparison l E X)
  let k : (coefHomTowerSections l E X).rightDerivedFunctor ≅
      f.mapDerivedCategory ⋙ g.rightDerivedFunctor :=
    Functor.rightDerivedFunctorNatIso σ ≪≫ derivedComposite f g (fun I hI ↦ by
      have := hI
      exact coefCompletedTowerSections_acyclic l E X I)
  let c : coefHomConstantDerivedSections l E X ≅
      e.mapDerivedCategory ⋙ f.mapDerivedCategory ⋙ g.rightDerivedFunctor :=
    Functor.mapDerivedCategoryCompRightDerivedFunctorIso e (coefHomTowerSections l E X) ≪≫
      Functor.isoWhiskerLeft e.mapDerivedCategory k
  let o : (r ⋙ e) ⋙ f ≅ coefTraceSystemRestriction l E X :=
    Functor.isoWhiskerRight (eqToIso (ordinaryRestriction l E X)) f
  let q : r.mapDerivedCategory ⋙ e.mapDerivedCategory ⋙ f.mapDerivedCategory ≅
      (coefTraceSystemRestriction l E X).mapDerivedCategory :=
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso r e).symm
        f.mapDerivedCategory ≪≫
      (Functor.mapDerivedCategoryCompIso (r ⋙ e) f).symm ≪≫
      Functor.mapDerivedCategoryNatIso o
  exact Functor.isoWhiskerLeft r.mapDerivedCategory c ≪≫
    Functor.isoWhiskerRight q g.rightDerivedFunctor

/-- The scalar Hom comparison for a prescribed quotient-system complex is natural
on the entire completed-coefficient derived category, before constructible restriction.

Source: blueprint prop-coef-integral-dualizing, second paragraph, first mapping
comparison; Stacks 07A6, 08J9 and 0941.
(blueprint: lem-coef-hom-scalar-naturality).

Proof: apply the sequence-site derived extension--restriction internal-Hom
adjunction to the constant completed input and Q. The constant-sequence
section-preserving equivalence identifies restriction on the sequence site with
the inverse realization of coefficientSequenceDerivedRestriction. The normalized
reduction adjunction identifies derived extension of the constant input with
S.reduction: both are left adjoint to the same total derived limit, and the
unique adjunction comparison carries their units to one another. Substitute this
natural comparison in the contravariant argument of internal Hom. The ordinary
scalar-section square and its derived comparison identify constant-ring sections
of restricted quotient Hom with coefPairingSections of quotient Hom, retaining
the actual R action and the full tower index. Compose these natural isomorphisms.
Naturality is inherited from the bifunctorial scalar internal-Hom comparison,
the adjunction comparison, and the derived section square; it is not inferred
from finite evaluations or from unrelated objectwise isomorphisms. No inverse
limit of Hom towers or exceptional adjunction is used. All comparisons apply to
zero complexes and to the empty scheme. -/
theorem coefHom_scalar_naturality
    (Q : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (S : CoefficientDerivedSystemCalculus l E X) :
    Nonempty (
      (coefHomDerivedConstant l E X).op ⋙
        (Functor.curry.obj (coefHomConstantInternalHom l E X)).flip.obj
          ((coefHomEquivalence l E X).inverse.mapDerivedCategory.obj
            ((coefficientSequenceDerivedRestriction l E X).obj (coefTraceInput l E X Q))) ⋙
        coefHomConstantDerivedSections l E X ≅ coefPairingHom l E X S Q) := by
  obtain ⟨M, μ, ⟨A⟩⟩ := scalarInternalHomAdjunction_exists.{u + 1, u, u, u + 2}
    (J := coefficientSequenceTopology (ProEt.topology X))
  exact ⟨scalarHomTransport (coefHomDerivedConstant l E X)
    (M.scalar (coefHomScalarMap l E X)).derived (coefHomDerivedRestriction l E X)
    S.reduction (coefHomConstantInternalHom l E X) (coefficientSequenceInternalHom l E X)
    (coefHomConstantDerivedSections l E X) (coefPairingSections l E X)
    (coefTraceInput l E X Q) _ ((restrictionComparison l E X).app _)
    (reductionComparison l E X M S) (A.iso (coefHomScalarMap l E X)) (sectionsComparison l E X)⟩

end WeilConjectures
