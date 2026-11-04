/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerClassSupportedScalarLevelCokernel
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerClassSupportedScalarLevelGeneration
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFiniteDiagonal

/-! # The supported scalar comparison is invertible

The level cokernel description on the projective line is carried to the diagonal surface by
the exact closed direct image, which identifies both sides of the ordinary scalar adjunct of
the supported quotient system level by level.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [local implicit_reducible] spCoefficientCommRings SpTowerShriek.tau lineModule

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The supported finite quotient is the closed direct image of the finite quotient on the
projective line, read through the push evaluation. -/
private theorem finiteSupportedQuotient_eq {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    (g : SpTowerShriek.Geometry l E b (diagonalImmersion S)) (n : ℕ) :
    finiteSupportedQuotient l E g n =
      (lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion S)).map
          (finiteQuotient l E (ProjectiveLine S) n) ≫
        (pushEvaluationUnderlying l E g
          (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S))) n).inv := by
  let e := pushEvaluationUnderlying l E g
    (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S))) n
  apply (finiteSupportedQuotient_existsUnique l E g n).unique
    (finiteSupportedQuotient_existsUnique l E g n).exists.choose_spec
  intro U k
  have he : ((lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion S)).map
      (finiteQuotient l E (ProjectiveLine S) n) ≫ e.inv) ≫ e.hom =
      (lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion S)).map
        (finiteQuotient l E (ProjectiveLine S) n) := by
    simp
  have h := congrArg (fun a ↦ a.hom.app U
    ((toSheafify (Scheme.ProEt.topology (ProjectiveLine S))
      ((Functor.const (ProjectiveLine S).ProEtᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (chart (diagonalImmersion S) U) k)) he
  exact ((pushEvaluationUnderlying_apply l E g _ n U _).symm).trans
    (h.heq.trans ((finiteQuotient_existsUnique l E (ProjectiveLine S) n).exists.choose_spec
      (chart (diagonalImmersion S) U) k))

/-- The coefficient ring map of the constant-ring direct image is the constant direct-image
map. -/
theorem proEtaleRingDirectImageMap_constant {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u)
    [CommRing A] :
    proEtaleRingDirectImageMap f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
        (proEtaleConstantRingComparison f A) =
      proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} A)) := by
  unfold proEtaleRingDirectImageMap proEtaleConstantRingComparison
  rw [asIso_hom, proEtaleCoefficientInverseImageMap, proEtaleConstantInverseImageMap,
    ← Adjunction.homEquiv_counit, ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]

/-- The constant direct-image ring map sends a constant section to the same constant
section on the base-changed chart. -/
theorem proEtaleConstantDirectImageMap_ring_toSheafify {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : CommRingCat.{u + 1}) (U : Y.ProEtᵒᵖ) (a : A) :
    (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A).hom.app U
        ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app U a) =
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
        ((proEtaleBaseChange f).op.obj U) a := by
  have h := Equiv.apply_symm_apply ((sheafificationAdjunction (ProEt.topology Y)
    CommRingCat.{u + 1}).homEquiv _ ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A)))
    (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun a' ↦ (a'.app U).hom a) h

/-- Multiplication by constant sections commutes with the closed push evaluation. -/
private theorem pushEvaluationUnderlying_smul {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    (g : SpTowerShriek.Geometry l E b (diagonalImmersion S)) (n : ℕ)
    (r : SpTowerShriek.R l E n) :
    (pushEvaluationUnderlying l E g
        (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S))) n).hom ≫
      (lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion S)).map
        (levelSmul l E (ProjectiveLine S) n r
          (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))) =
    levelSmul l E (diagonalSurface S) n r
        (g.push.obj (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))) ≫
      (pushEvaluationUnderlying l E g
        (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S))) n).hom := by
  let Y := (SpTowerShriek.ev l E (ProjectiveLine S) n).obj
    (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
  have h : sectionSmul (constSection l E (diagonalSurface S) n r)
      (constSection_map l E (diagonalSurface S) n r)
      ((proEtaleConstantRingPushforward (SpTowerShriek.R l E n) (diagonalImmersion S)).obj Y) ≫
        (directImageUnderlying (SpTowerShriek.R l E n) (diagonalImmersion S) Y).hom =
      (directImageUnderlying (SpTowerShriek.R l E n) (diagonalImmersion S) Y).hom ≫
        (lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion S)).map
          (sectionSmul (constSection l E (ProjectiveLine S) n r)
            (constSection_map l E (ProjectiveLine S) n r) Y) := by
    unfold directImageUnderlying
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    have hc := proEtaleConstantDirectImageMap_ring_toSheafify (diagonalImmersion S)
      (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n))) U (ULift.up r)
    rw [← proEtaleRingDirectImageMap_constant] at hc
    exact congrArg (fun c ↦ DistribSMul.toAddMonoidHom
      (Y.val.obj ((proEtaleBaseChange (diagonalImmersion S)).op.obj U)) c x) hc
  unfold pushEvaluationUnderlying
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  refine (congrArg (_ ≫ ·) h.symm).trans ?_
  rw [← Category.assoc]
  exact (congrArg (· ≫ _) (sectionSmul_naturality _ _ _).symm).trans (Category.assoc _ _ _)

/-- The basis multiples of the supported finite quotient present the level-`n` supported
coefficient sheaf as the cokernel of multiplication by `l ^ (n + 1)` on copies of the
supported integer sheaf: the closed direct image of `levelQuotient_cokernel`. -/
theorem supportedQuotient_level_cokernel {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    (g : SpTowerShriek.Geometry l E b (diagonalImmersion S)) (n d : ℕ)
    (e : letI := coefficientZModAlgebra l E n
      Module.Basis (Fin d) (ZMod (l ^ (n + 1))) (SpTowerShriek.R l E n)) :
    ∃ hz : (l ^ (n + 1) • 𝟙 (⨁ fun _ : Fin d ↦ diagonalIntegralSource S)) ≫
        biproduct.desc (fun i : Fin d ↦ finiteSupportedQuotient l E g n ≫
          levelSmul l E (diagonalSurface S) n (e i)
            (g.push.obj (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S))))) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ hz)) := by
  let i := diagonalImmersion S
  let F := lowerStar AddCommGrpCat.{u + 1} i
  let C := coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S))
  have := SmoothOfRelativeDimension.smooth 1 (ProjectiveLine S ↘ S)
  have : LocallyOfFinitePresentation (ProjectiveLine S ↘ S) := inferInstance
  have : LocallyOfFinitePresentation (diagonalImmersion S) := by
    change LocallyOfFinitePresentation (pullback.diagonal (ProjectiveLine S ↘ S))
    infer_instance
  have := preservesFiniteColimits_lowerStar_of_isFinite_ab (diagonalImmersion S)
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  obtain ⟨hz, ⟨h⟩⟩ := levelQuotient_cokernel l E (ProjectiveLine S) n d e
  have hF := isColimitCoforkMapOfIsColimit' F hz h
  let ε := pushEvaluationUnderlying l E g C n
  have key : ∀ (π : (⨁ fun _ : Fin d ↦ diagonalIntegralSource S) ⟶
      (finiteForget l E (diagonalSurface S) n).obj
        ((SpTowerShriek.ev l E (diagonalSurface S) n).obj (g.push.obj C))),
      π = (F.mapBiproduct fun _ : Fin d ↦
          (abEvaluation (ProjectiveLine S) n).obj (integers (ProjectiveLine S))).symm.hom ≫
        F.map (biproduct.desc (fun j : Fin d ↦ finiteQuotient l E (ProjectiveLine S) n ≫
          levelSmul l E (ProjectiveLine S) n (e j) C)) ≫ ε.symm.hom →
      ∃ hz : (l ^ (n + 1) • 𝟙 _) ≫ π = 0, Nonempty (IsColimit (CokernelCofork.ofπ π hz)) := by
    rintro _ rfl
    refine cokernel_of_isos _ _ _ ?_ _ _ hF _
    simp
  refine key _ ?_
  rw [Iso.symm_hom, Iso.symm_hom, ← Category.assoc, biproduct.mapBiproduct_inv_map_desc]
  apply biproduct.hom_ext'
  intro j
  rw [biproduct.ι_desc, biproduct.ι_desc_assoc, finiteSupportedQuotient_eq, Functor.map_comp,
    Category.assoc]
  have h2 : ε.inv ≫ levelSmul l E (diagonalSurface S) n (e j) (g.push.obj C) =
      F.map (levelSmul l E (ProjectiveLine S) n (e j) C) ≫ ε.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc]
    exact (Iso.eq_comp_inv ε).2 (pushEvaluationUnderlying_smul l E g n (e j)).symm
  exact congrArg (F.map (finiteQuotient l E (ProjectiveLine S) n) ≫ ·) h2

/-- A system map is invertible once its forgotten evaluation is invertible at every level. -/
theorem isIso_of_forget_evaluation {T : Scheme.{u}} {Y Y' : Systems T (Arings l E T)}
    (f : Y ⟶ Y')
    (h : ∀ n, IsIso ((finiteForget l E T n).map ((SpTowerShriek.ev l E T n).map f))) :
    IsIso f := by
  have hfaith : JointlyFaithful (SpTowerShriek.ev l E T) := by
    constructor
    intro M N f h hfh
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    rintro ⟨n, V⟩
    ext x
    exact congrArg (fun k ↦ k.val.app (op V) x) (hfh n)
  have (n : ℕ) : IsIso ((SpTowerShriek.ev l E T n).map f) :=
    isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)
  exact hfaith.jointlyReflectsIsomorphisms.isIso f

/-- The ordinary scalar extension of the reduced supported integral source is the
supported coefficient system: the scalar adjunct of a system map which is the canonical
supported finite quotient at every level is invertible.

Source: latest blueprint classes proof (3), steps 11--12 of
`lem-sp-prescribed-projective-class-package`
(blueprint: lem-sp-tower-class-supported-scalar-push-comparison).

Proof plan: invertibility is checked level by level, since the evaluations jointly
reflect isomorphisms; level n of ordinary scalar extension is the level scalar extension
along `ZMod (l^(n+1)) → O_E/l^(n+1)` (`scalarEvaluationMate_isIso`). By
`powerSystem_ordinary_cokernel` the reduction unit at level n is a cokernel of
multiplication by `l^(n+1)` on the supported integer sheaf `Z`, and the target at level n
is the closed direct image of the constant sheaf `O_E/l^(n+1)`. Choose a basis `b_i` of
`O_E/l^(n+1)` over `ZMod (l^(n+1))` (`levelRing_free`). Then
`(k_i) ↦ Σ b_i · finiteSupportedQuotient n (k_i)` from `Z^d` is a cokernel of `l^(n+1)`:
it is the closed direct image (exact, `preservesFiniteColimits_lowerStar_of_isFinite_ab`)
of the constant-sheaf image of `ℤ^d → O_E/l^(n+1)`. The pure tensors `b_i ⊗ k` generate
the extended module locally, so this cokernel description yields an inverse, checked on
these generators. -/
theorem supportedQuotient_scalarAdjunct_isIso {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    (c : Chern l E (diagonalSurface S))
    (g : SpTowerShriek.Geometry l E b (diagonalImmersion S))
    (q : c.reduction.ordinary.obj
        ((constant (diagonalSurface S)).obj (diagonalIntegralSource S)) ⟶
        (WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E (diagonalSurface S))).obj
          (g.push.obj (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))))
    (hq : ∀ n : ℕ,
        (abEvaluation (diagonalSurface S) n).map
            (c.reduction.model.adjunction.unit.app
              ((constant (diagonalSurface S)).obj (diagonalIntegralSource S))) ≫
          (c.reduction.forget.F ⋙ abEvaluation (diagonalSurface S) n).map q ≫
          (finiteScalarForgetIso l E c n).hom.app
            (g.push.obj (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))) =
        finiteSupportedQuotient l E g n) :
    IsIso ((c.scalar.ordinaryAdjunction.homEquiv _ _).symm q) := by
  have : ∀ n, Finite (SpTowerShriek.R l E n) := b.finite
  obtain ⟨hz, ⟨hcol⟩⟩ := powerSystem_ordinary_cokernel l (diagonalSurface S) c.reduction
    ((constant (diagonalSurface S)).obj (diagonalIntegralSource S))
  have hu : c.scalar.ordinaryAdjunction.unit.app _ ≫
      (WeilConjectures.SemilinearSections.res
        (coefficientSystemMap l E (diagonalSurface S))).map
        ((c.scalar.ordinaryAdjunction.homEquiv _ _).symm q) = q :=
    (c.scalar.ordinaryAdjunction.homEquiv_unit _ _ _).symm.trans
      ((c.scalar.ordinaryAdjunction.homEquiv _ _).apply_symm_apply q)
  apply isIso_of_forget_evaluation
  intro n
  let := coefficientZModAlgebra l E n
  have := coefficient_zmod_free l E n
  have : Module.Finite (ZMod (l ^ (n + 1))) (SpTowerShriek.R l E n) := Module.Finite.of_finite
  let e := (Module.Free.chooseBasis (ZMod (l ^ (n + 1))) (SpTowerShriek.R l E n)).reindex
    (Fintype.equivFin _)
  have := levelExtension_basis_epi l E c
    (c.reduction.ordinary.obj ((constant (diagonalSurface S)).obj (diagonalIntegralSource S)))
    n _ e
  obtain ⟨hΨ, ⟨hΨc⟩⟩ := supportedQuotient_level_cokernel l E g n _ e
  refine isIso_of_biproduct_cokernels (l ^ (n + 1)) _ rfl _ _
    (isColimitCoforkMapOfIsColimit' (abEvaluation (diagonalSurface S) n) hz hcol) _
    (biproduct.desc (f := fun _ ↦ (abEvaluation (diagonalSurface S) n).obj
      (c.reduction.forget.F.obj (c.reduction.ordinary.obj
        ((constant (diagonalSurface S)).obj (diagonalIntegralSource S))))) fun i ↦
      (abEvaluation (diagonalSurface S) n).map (c.reduction.forget.F.map
          (c.scalar.ordinaryAdjunction.unit.app _)) ≫
        (finiteScalarForgetIso l E c n).hom.app (c.scalar.model.E.obj _) ≫
        levelSmul l E (diagonalSurface S) n (e i) (c.scalar.model.E.obj _))
    ((finiteForget l E (diagonalSurface S) n).map ((SpTowerShriek.ev l E (diagonalSurface S) n).map
      ((c.scalar.ordinaryAdjunction.homEquiv _ _).symm q))) _ hΨ hΨc ?_
  apply biproduct.hom_ext'
  intro i
  have hn := (finiteScalarForgetIso l E c n).hom.naturality
    ((c.scalar.ordinaryAdjunction.homEquiv _ _).symm q)
  have hqn := hq n
  simp only [Functor.comp_map] at hn hqn
  have hu' : (abEvaluation (diagonalSurface S) n).map (c.reduction.forget.F.map
      (c.scalar.ordinaryAdjunction.unit.app _)) ≫ (abEvaluation (diagonalSurface S) n).map
      (c.reduction.forget.F.map ((WeilConjectures.SemilinearSections.res
        (coefficientSystemMap l E (diagonalSurface S))).map
        ((c.scalar.ordinaryAdjunction.homEquiv _ _).symm q))) =
      (abEvaluation (diagonalSurface S) n).map (c.reduction.forget.F.map q) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hu]
  rw [biproduct.ι_map_assoc, biproduct.ι_desc_assoc, biproduct.ι_desc, Category.assoc,
    Category.assoc, sectionSmul_naturality, ← reassoc_of% hn, reassoc_of% hu', reassoc_of% hqn]

end AlgebraicGeometry.ProEtale.SpTowerClasses
