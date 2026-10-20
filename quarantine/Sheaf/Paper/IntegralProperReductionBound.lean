/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F5
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.Paper.IntegralProperReductionModel
import all Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import Sheaf.CategoryTheory.RightDerivedFunctorUpperBound


/-! # Finite reduction bounds for proper integral direct image -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.Etale

private theorem algClosurePoint_eq (Y : Scheme.{u}) (t : Y) :
    Y.algClosurePoint t = Spec.map (CommRingCat.ofHom
      (algebraMap (Y.residueField t) (AlgebraicClosure (Y.residueField t)))) ≫
        Y.fromSpecResidueField t := by
  rfl

private theorem torsion_geometric_bound
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Scheme.IsTorsionAbelianSheaf F) (q : ℤ) (hq : 2 * (d : ℤ) < q) :
    IsZero
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) := by
  lift q to ℕ using (by omega)
  have hqNat : 2 * d < q := by exact_mod_cast hq
  have ht : F.IsTorsion := (Scheme.isTorsionAbelianSheaf_characterizations F).1.mp hF
  let K := (DerivedCategory.Plus.singleFunctor
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F
  let R := (rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj K
  let M := (DerivedCategory.Plus.homologyFunctor
    (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj R
  have hpoints (t : Y) :
      IsZero ((upperStar AddCommGrpCat.{u + 1} (Y.algClosurePoint t)).obj M) := by
    let y := Y.algClosurePoint t
    let a := pullback.snd f y
    let i := pullback.fst f y
    have : IsProper a := IsProper.pullback_snd f y
    have hd' : topologicalKrullDim (pullback f y : Scheme.{u}) ≤
        (d : WithBot ℕ∞) := by
      let e := pullback.congrHom (rfl : f = f) (algClosurePoint_eq Y t)
      exact e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.le.trans (hd t)
    have hvan := isZero_higherDirectImage_over_algClosed
      (AlgebraicClosure (Y.residueField t)) a d hd'
      ((upperStar AddCommGrpCat.{u + 1} i).obj F) (isTorsion_upperStar i ht) q hqNat
    have hbc := isIso_baseChange_of_isProper (IsPullback.of_hasPullback f y) K
      (torsionHomology_single F ht)
    rw [baseChange_eq_derivedBaseChangeMapPlus] at hbc
    have := hbc
    exact hvan.of_iso
      (((upperStar AddCommGrpCat.{u + 1} y).mapDerivedCategoryPlusHomologyFunctorIso q).app
          R ≪≫
        (DerivedCategory.Plus.homologyFunctor _ q).mapIso
          (asIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
            (IsPullback.of_hasPullback f y).toCommSq).app K)) ≪≫
        (DerivedCategory.Plus.homologyFunctor _ q).mapIso
          ((lowerStar AddCommGrpCat.{u + 1} a).rightDerivedFunctorPlus.mapIso
            (((upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlusSingleFunctor 0).app F)))
  have hz := isZero_zero (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
  have : IsIso (hz.from_ M) := by
    refine isIso_of_isIso_upperStar_map_of_jointlySurjective AddCommGrpCat.{u + 1}
      (fun t ↦ Y.algClosurePoint t)
      (fun t ↦ ⟨t, IsLocalRing.closedPoint _, Scheme.algClosurePoint_base _ _ _⟩) _
      fun t ↦ ?_
    have hz' := Functor.map_isZero (upperStar AddCommGrpCat.{u + 1} (Y.algClosurePoint t)) hz
    exact ⟨⟨hz'.to_ _, (hpoints t).eq_of_src _ _, hz'.eq_of_src _ _⟩⟩
  exact hz.of_iso (asIso (hz.from_ M))

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

private theorem integralLevel_isLE (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (b : ℤ) (hb : K.IsLE b) (n : ℕ) :
    (AdicCompletion.integralLevel l E X K n).IsLE b := by
  let q := AdicCompletion.quotient l E X n
  let F := AdicCompletion.derivedReduction l E X n
  let G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.finiteRing l E X n) ⥤ AdicCompletion.Modules l E X := Mod.comap q
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction q
  have : (Mod.extendScalars q).leftDerivedFunctor.Additive := adj.left_adjoint_additive
  have hred : (F.obj K).IsLE b := by
    change DerivedCategory.TStructure.t.IsLE (F.obj K) b
    rw [DerivedCategory.TStructure.t.isLE_iff_orthogonal b (b + 1) rfl]
    intro Z f hZ
    have : Z.IsGE (b + 1) := hZ
    have : (G.mapDerivedCategory.obj Z).IsGE (b + 1) :=
      G.isGE_mapDerivedCategory_obj Z (b + 1)
    have hz : adj.homEquiv K Z f = 0 :=
      DerivedCategory.TStructure.t.zero _ b (b + 1) (by omega)
    exact (adj.homEquiv K Z).injective
      (hz.trans (adj.homAddEquiv_zero K Z).symm)
  exact G.isLE_mapDerivedCategory_obj (F.obj K) b

/-- The positive finite reductions of a proper integral image have the torsion bound.
Source: blueprint main-20261015, det-prop-int-compactness-direct-sums, proof (1),
finite reduction and torsion comparison steps
(blueprint: lem-sfb-integral-proper-reduction-bound).

Proof: Derived extension to O_E/pi^(n+1) is right t-exact, so it preserves the
upper bound b. Its constructible cohomology has classical finite-coefficient etale
models, by the integral constructibility criterion and finite comparison. On these
models proper torsion direct image has upper bound b+2d, by the finite
cohomological-dimension theorem.
Apply the proper base-change theorem at each algebraically closed geometric
stalk; the assumed bound is already the bound of that geometric fibre. The perfect
two-term quotient resolution and the projection
formula identify reduction of ordinary integral direct image with direct image of
the reduction. Exact coefficient restriction reflects the upper bound. The quotient
is indexed by n+1, hence is always a positive finite quotient, including n=0. -/
theorem integralProperReductionBound
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K)
    (b : ℤ) (hb : K.IsLE b) (n : ℕ) :
    (AdicCompletion.integralLevel l E Y
      ((CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) p).obj K)
      n).IsLE (b + 2 * (d : ℤ)) := by
  let R := ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let : Finite R := inferInstance
  obtain ⟨L, ⟨eIn⟩, ⟨e⟩⟩ := integralProperReductionModel l E k p K hK n
  let UX := Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (AdicCompletion.ring l E X)
  let WX := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1}) ⋙ comparisonUpperStar Ab.{u + 1} X
  have hred := integralLevel_isLE l E X K b hb n
  have hUX := UX.isLE_mapDerivedCategory_obj (AdicCompletion.integralLevel l E X K n) b
  have hWX := DerivedCategory.TStructure.t.isLE_of_iso eIn b
  have hL : L.IsLE b := by
    rw [DerivedCategory.isLE_iff]
    intro q hq
    exact WX.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      (DerivedCategory.isZero_of_isLE _ b q hq (hX := hWX))
  have hdim (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (q : ℕ)
      (hq : 2 * d < q) :
      IsZero (((Etale.lowerStar (ModuleCat.{u + 1} R) p).rightDerived q).obj M) := by
    let V := (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1})).obj M
    have hV : Scheme.IsTorsionAbelianSheaf V := by
      apply (Scheme.isTorsionAbelianSheaf_characterizations V).1.mpr
      apply Sheaf.IsTorsion.of_forall_isAddTorsion
      intro U
      exact IsAddTorsion.module_of_finite R (M.obj.obj U)
    have hz := Etale.torsion_geometric_bound p d hd V hV (q : ℤ)
      (by exact_mod_cast hq)
    obtain ⟨j⟩ := Etale.nonempty_higherDirectImage_forget_iso R p (q : ℤ) M
    have hz' := hz.of_iso j
    have hmodule : IsZero (Etale.higherDirectImage R p (q : ℤ) M) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply (sheafCompose Y.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1})).map_injective
      exact hz'.eq_of_src _ _
    exact hmodule.of_iso
      (Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso
        (Etale.lowerStar (ModuleCat.{u + 1} R) p) M q).symm
  have : L.IsLE b := hL
  have hpush := Functor.isLE_rightDerivedFunctor_obj_of_dimension
    (Etale.lowerStar (ModuleCat.{u + 1} R) p) (2 * d) hdim L b hL
  have : ((Etale.lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor.obj L).IsLE
      (b + 2 * (d : ℤ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hpush
  let W := sheafCompose Y.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1}) ⋙ comparisonUpperStar Ab.{u + 1} Y
  have hW := W.isLE_mapDerivedCategory_obj
    ((Etale.lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor.obj L)
    (b + 2 * (d : ℤ))
  have hf := DerivedCategory.TStructure.t.isLE_of_iso e.symm (b + 2 * (d : ℤ))
  let U := Mod.forget (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (AdicCompletion.ring l E Y)
  rw [DerivedCategory.isLE_iff]
  intro q hq
  have hz := DerivedCategory.isZero_of_isLE _ (b + 2 * (d : ℤ)) q hq (hX := hf)
  have hz' := hz.of_iso ((U.mapDerivedCategoryHomologyFunctorIso q).app _)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply U.map_injective
  exact hz'.eq_of_src _ _

end AlgebraicGeometry.ProEtale
