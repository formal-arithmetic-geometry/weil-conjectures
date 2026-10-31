/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingMappingTower
public import WeilConjectures.SixFunctors.IntegralDualizingResolvedGlobalHom
public import WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv

/-! # Natural strict Hom tower comparison

Source: Stacks Project, Tags 04TT, 0A8X, 08JA and 0941.
(blueprint: lem-coef-integral-dualizing-strict-hom-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u c v r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

attribute [local irreducible] homComplexFunctor

private theorem mappingHom_precomp
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (R : Sheaf J CommRingCat.{r})
    (P P' T : CochainComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (f : P' ⟶ P) (i p q : ℤ) (hpq : p + i = q) (U : Cᵒᵖ)
    (x : ((homComplex (R := R) P T).X i).val.obj U)
    (V : (Over U.unop)ᵒᵖ) (z : (P'.X p).val.obj (op V.unop.left)) :
    ((homComplexπ (R := R) P' T i p q hpq).val.app U
      ((((homComplexFunctor (R := R)).map f.op).app T).f i |>.val.app U |>.hom <| x)).app
        V z =
      ((homComplexπ (R := R) P T i p q hpq).val.app U x).app V
        ((f.f p).val.app (op V.unop.left) z) := by
  have hn := homComplexFunctor_map_f_π (R := R) f (𝟙 T) i p q hpq
  rw [((homComplexFunctor (R := R)).obj (op P')).map_id T, Category.comp_id,
    HomologicalComplex.id_f] at hn
  have h := congrArg
    (fun k ↦ ((k.val.app U x).app V).hom z) hn
  exact h

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

private def mappingScalarSectionsEquiv
    (N : scalarReductionSource l E X) :
    (RingedSiteGlobalRHom.sections.{u + 1, u, u + 1, u + 1}
      (completedIntegralCommRingSheafUnrestricted l E X)
      (integralDualizingCoefficients l E) (integralDualizingScalarSections l E X)).obj N ≃ₗ[
        integralDualizingCoefficients l E] (integralDualizingSections l E X).obj N where
  toFun f := f.val.app (op (Scheme.ProEt.mk (𝟙 X)))
    (1 : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
      (op (Scheme.ProEt.mk (𝟙 X))))
  invFun x := N.unitHomEquiv.symm (N.val.sectionsMk
    (fun U ↦ N.val.map ((Scheme.ProEt.isTerminalMkId X).op.to U) x)
    (by
      intro U V f
      rw [← PresheafOfModules.map_comp_apply]
      exact N.val.congr_map_apply
        ((Scheme.ProEt.isTerminalMkId X).op.hom_ext _ _) x))
  left_inv f := by
    apply N.unitHomEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply PresheafOfModules.sections_ext
    intro U
    change N.val.map _ (f.val.app _ (1 :
      (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
        (op (Scheme.ProEt.mk (𝟙 X))))) = f.val.app U
        (1 : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
    have hf := PresheafOfModules.naturality_apply f.val
      ((Scheme.ProEt.isTerminalMkId X).op.to U)
      (1 : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
        (op (Scheme.ProEt.mk (𝟙 X))))
    change f.val.app U
        ((completedIntegralCoefficientSheafUnrestricted l E X).obj.map
          ((Scheme.ProEt.isTerminalMkId X).op.to U) 1) =
      N.val.map _ (f.val.app _
        (1 : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
          (op (Scheme.ProEt.mk (𝟙 X))))) at hf
    rw [map_one] at hf
    exact hf.symm
  right_inv x := by
    change (N.unitHomEquiv (N.unitHomEquiv.symm _)).val _ = x
    rw [Equiv.apply_symm_apply]
    change N.val.map _ x = x
    have h : (Scheme.ProEt.isTerminalMkId X).op.to
        (op (Scheme.ProEt.mk (𝟙 X))) = 𝟙 _ :=
      (Scheme.ProEt.isTerminalMkId X).op.hom_ext _ _
    rw [h]
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def mappingScalarSectionsIso :
    RingedSiteGlobalRHom.sections.{u + 1, u, u + 1, u + 1}
      (completedIntegralCommRingSheafUnrestricted l E X)
      (integralDualizingCoefficients l E) (integralDualizingScalarSections l E X) ≅
        integralDualizingSections l E X :=
  NatIso.ofComponents (fun N ↦ (mappingScalarSectionsEquiv l E X N).toModuleIso)
    (by intro M N f; ext x; rfl)

private theorem mappingHomSection_ext
    (P T : CochainComplex (scalarReductionSource l E X) ℤ) (i : ℤ)
    (U : X.ProEtᵒᵖ) (x y : ((homComplex
      (R := completedIntegralCommRingSheafUnrestricted l E X) P T).X i).val.obj U)
    (h : ∀ p : ℤ,
      (homComplexπ.{u + 1, u, u + 1, u + 1}
          (R := completedIntegralCommRingSheafUnrestricted l E X)
        P T i p (p + i) rfl).val.app U x =
        (homComplexπ.{u + 1, u, u + 1, u + 1}
          (R := completedIntegralCommRingSheafUnrestricted l E X)
        P T i p (p + i) rfl).val.app U y) : x = y := by
  let V : scalarReductionSource l E X ⥤
      ModuleCat.{u + 1} ((completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U) :=
    SheafOfModules.evaluation
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (completedIntegralCommRingSheafUnrestricted l E X)) U
  apply Concrete.isLimit_ext _ (isLimitOfPreserves V (homComplexIsLimit.{u + 1, u, u + 1, u + 1}
    (R := completedIntegralCommRingSheafUnrestricted l E X) P T i)) x y
  rintro ⟨p⟩
  exact h p

private theorem mappingSlice_naturality
    (P P' : CochainComplex (scalarReductionSource l E X) ℤ) (f : P' ⟶ P)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ) :
    ((coefHomConstantSections l E X).mapHomologicalComplex (.up ℤ)).map
      (((homComplexFunctor (R := coefHomConstantRing l E X)).map
        (((coefHomConstant l E X).mapHomologicalComplex (.up ℤ)).map f).op).app
          (coefHomSequenceComplex l E X I)) ≫
      (coefHomSequenceSectionsIso l E X P' I).hom =
    (coefHomSequenceSectionsIso l E X P I).hom ≫
      (HomologicalComplex.functorEquivalence.inverse _ (.up ℤ) ℕᵒᵖ).map
        (Functor.whiskerLeft I.asFunctor
          (Functor.whiskerRight
            ((homComplexFunctor.{u + 1, u, u + 1, u + 1}
              (R := completedIntegralCommRingSheafUnrestricted l E X)).map f.op)
            ((coefHomSections l E X).mapHomologicalComplex (.up ℤ)))) := by
  apply HomologicalComplex.hom_ext
  intro i
  apply NatTrans.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply mappingHomSection_ext l E X P' (I.asFunctor.obj n) i
    (op (Scheme.ProEt.mk (𝟙 X)))
  intro p
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have hP := (coefHomSequenceSections_iso l E X P I).choose_spec.1
  have hP' := (coefHomSequenceSections_iso l E X P' I).choose_spec.1
  have h₁ := eq_of_heq (hP' i p n.unop U.unop.left U.unop.hom
    (((((coefHomConstantSections l E X).mapHomologicalComplex (.up ℤ)).map
      (((homComplexFunctor (R := coefHomConstantRing l E X)).map
        (((coefHomConstant l E X).mapHomologicalComplex (.up ℤ)).map f).op).app
          (coefHomSequenceComplex l E X I))).f i).app n x))
  have h₂ := eq_of_heq (hP i p n.unop U.unop.left U.unop.hom x)
  have h₃ := mappingHom_precomp (coefHomConstantRing l E X)
    (((coefHomConstant l E X).mapHomologicalComplex (.up ℤ)).obj P)
    (((coefHomConstant l E X).mapHomologicalComplex (.up ℤ)).obj P')
    (coefHomSequenceComplex l E X I)
    (((coefHomConstant l E X).mapHomologicalComplex (.up ℤ)).map f)
    i p (p + i) rfl (op (n.unop, Scheme.ProEt.mk (𝟙 X))) x
    (op (Over.mk (Prod.mkHom (𝟙 n.unop) U.unop.hom))) z
  have h₄ := mappingHom_precomp (completedIntegralCommRingSheafUnrestricted l E X)
    P P' (I.asFunctor.obj n) f i p (p + i) rfl
    (op (Scheme.ProEt.mk (𝟙 X)))
    (((coefHomSequenceSectionsIso l E X P I).hom.f i).app n x) U z
  exact (congrArg (fun k ↦ k z) h₁).trans (h₃.trans
    ((congrArg (fun k ↦ k ((f.f p).val.app (op U.unop.left) z)) h₂).symm.trans h₄.symm))

attribute [local irreducible] coefHomSequenceSectionsIso mappingScalarSectionsIso

/-- Ordinary sequence-site Hom sections from a constant complex form the strict
tower of signed global Hom complexes, naturally in the source.

Source: Stacks Project, Tags 04TT, 0A8X, 08JA and 0941.
(blueprint: lem-coef-integral-dualizing-strict-hom-comparison).

Proof: use the existing uniquely slice-normalized complex isomorphism. Project its
naturality square to every Hom factor, then evaluate at every slice object and
section. The normalization formula identifies both paths with restriction to the
sequence index followed by precomposition by the source chain map. The Hom product
projections detect equality because evaluation preserves limits. Next identify
compatible scalar sections with evaluation at the terminal pro-etale object: a
unit morphism is evaluated on 1, and the inverse takes compatible restrictions of
the terminal section. These operations are inverse and linear for the specified
integral scalar action. Whisker this scalar comparison with Hom and the target
tower, transpose complexes and towers, and compose with the natural slice
comparison. All maps retain the signed differentials and postcomposition
transitions. No injectivity, boundedness, derived limit, or nonzero hypothesis is
needed. -/
theorem integralDualizing_strict_hom_comparison
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ) :
    Nonempty (((coefHomConstant l E X).mapHomologicalComplex (.up ℤ)).op ⋙
      (homComplexFunctor (R := coefHomConstantRing l E X)).flip.obj
        (coefHomSequenceComplex l E X I) ⋙
      (coefHomConstantSections l E X).mapHomologicalComplex (.up ℤ) ≅
      (integralDualizingResolvedHom l E X ⋙
        (Functor.whiskeringLeft _ _ _).obj I.asFunctor ⋙
          HomologicalComplex.functorEquivalence.inverse _ (.up ℤ) ℕᵒᵖ)) := by
  let C := (coefHomConstant l E X).mapHomologicalComplex (.up ℤ)
  let H := (homComplexFunctor (R := coefHomConstantRing l E X)).flip.obj
    (coefHomSequenceComplex l E X I)
  let F := coefHomConstantSections l E X
  let S := homComplexFunctor.{u + 1, u, u + 1, u + 1}
      (R := completedIntegralCommRingSheafUnrestricted l E X) ⋙
    (Functor.whiskeringRight _ _ _).obj
      ((coefHomSections l E X).mapHomologicalComplex (.up ℤ)) ⋙
    (Functor.whiskeringLeft _ _ _).obj I.asFunctor ⋙
    HomologicalComplex.functorEquivalence.inverse _ (.up ℤ) ℕᵒᵖ
  have b : C.op ⋙ H ⋙ F.mapHomologicalComplex (.up ℤ) ≅ S :=
    NatIso.ofComponents (fun P ↦ coefHomSequenceSectionsIso l E X P.unop I)
      (by intro P P' f; exact mappingSlice_naturality l E X P.unop P'.unop f.unop I)
  have ε : RingedSiteGlobalRHom.sections.{u + 1, u, u + 1, u + 1}
      (completedIntegralCommRingSheafUnrestricted l E X)
      (integralDualizingCoefficients l E) (integralDualizingScalarSections l E X) ≅
        coefHomSections l E X := mappingScalarSectionsIso l E X
  have β := Functor.isoWhiskerLeft
    (homComplexFunctor.{u + 1, u, u + 1, u + 1}
      (R := completedIntegralCommRingSheafUnrestricted l E X))
    ((Functor.whiskeringRight _ _ _).mapIso (NatIso.mapHomologicalComplex ε (.up ℤ)))
  have c : (integralDualizingResolvedHom l E X ⋙
        (Functor.whiskeringLeft _ _ _).obj I.asFunctor ⋙
          HomologicalComplex.functorEquivalence.inverse _ (.up ℤ) ℕᵒᵖ) ≅ S :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight β ((Functor.whiskeringLeft _ _ _).obj I.asFunctor))
      (HomologicalComplex.functorEquivalence.inverse _ (.up ℤ) ℕᵒᵖ)
  exact ⟨b ≪≫ c.symm⟩

end WeilConjectures
