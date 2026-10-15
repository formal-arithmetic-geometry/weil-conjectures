/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Sheaf.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal
import Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Higher direct image stalks over a field

Source: Stacks Project, Tags 03Q9 and 03SI, and blueprint
`lem-sc-cd-ground-field`, proof steps 2--4.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

private lemma isUniversalHomeomorphism_field_strictHenselizationEval
    {K : Type u} [Field K] (L : Type u) [Field L] [Algebra K L]
    [IsAlgClosure K L] [IsAlgClosed L] :
    IsUniversalHomeomorphism
      (Spec.map (strictHenselizationEval
        (Spec.map (CommRingCat.ofHom (algebraMap K L))))) := by
  classical
  let s := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let C := strictHenselization s
  have hc := strictHenselization_chart_maximalIdeal (.of K) (𝟙 _) s
  rw [show s ≫ 𝟙 _ = s from Category.comp_id s] at hc
  obtain ⟨hl, ρ, hρ, hm⟩ := hc
  rw [Category.comp_id] at hρ
  have hzero : IsLocalRing.maximalIdeal C = ⊥ := by
    rw [hm]
    have hp : (s (IsLocalRing.closedPoint L)).asIdeal = ⊥ :=
      Ideal.eq_bot_of_prime (s (IsLocalRing.closedPoint L)).asIdeal
    rw [hp, Ideal.map_bot]
  let : Field C := (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hzero).toField
  let : Algebra K C := ρ.hom.toAlgebra
  let : Algebra C L := (strictHenselizationEval s).hom.toAlgebra
  have ht : (strictHenselizationEval s).hom.comp ρ.hom = algebraMap K L := by
    suffices he : ρ ≫ strictHenselizationEval s =
        CommRingCat.ofHom (algebraMap K L) from congrArg CommRingCat.Hom.hom he
    apply Spec.map_injective
    change Spec.map (ρ ≫ strictHenselizationEval s) = s
    rw [Spec.map_comp, hρ]
    exact spec_map_strictHenselizationEval_comp_strictLocalizationToBase s
  have : IsScalarTower K C L := IsScalarTower.of_algebraMap_eq fun x ↦
    (DFunLike.congr_fun ht x).symm
  have : Algebra.IsAlgebraic C L := Algebra.IsAlgebraic.tower_top (K := K) C
  let e : C ≃+* IsLocalRing.ResidueField C := RingEquiv.ofBijective (IsLocalRing.residue C)
    ⟨RingHom.injective _, IsLocalRing.residue_surjective⟩
  have : IsSepClosed C := IsSepClosed.of_ringEquiv e.symm
  have : IsPurelyInseparable C L := inferInstance
  exact inferInstanceAs (IsUniversalHomeomorphism
    (Spec.map (CommRingCat.ofHom (algebraMap C L))))

set_option backward.isDefEq.respectTransparency false in
private lemma nonempty_addEquiv_strictLocalization
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (L : Type u) [Field L] [IsAlgClosed L] (s : Spec (.of L) ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ) :
    Nonempty ((((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
        (((lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj F)) ≃+
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
        (pullback.fst f (strictHenselizationStructuralMap s))).obj F) q) := by
  let A := AddCommGrpCat.{u + 1}
  let Y := pullback f (strictHenselizationStructuralMap s)
  let G := (upperStar A (pullback.fst f (strictHenselizationStructuralMap s))).obj F
  let e₁ := ((pointSmallEtale s).sheafFiber (A := A)).mapIso
    (((lowerStar A f).homologyRightDerivedFunctorPlusObjSingleFunctorIso F q).symm)
  obtain ⟨r, _, hr⟩ := (strictHenselizationStalkFormula f s F hF q).1
  have := hr
  let e₂ := asIso (r ≫ strictHenselizationCohomologyComparison s f F q)
  let e₃ := (Sheaf.Γ Y.smallEtaleTopology A).homologyRightDerivedFunctorObjSingleFunctorIso G q
  have : ((sheafSections Y.smallEtaleTopology A).obj
      (Opposite.op (⊤_ Y.Etale))).Additive :=
    inferInstanceAs (sheafToPresheaf _ _ ⋙ (evaluation _ A).obj _).Additive
  let e₄ := (NatIso.rightDerived
    (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology A terminalIsTerminal) q).app G
  obtain ⟨e₅⟩ := Sheaf.nonempty_rightDerived_sections_obj_iso_functorH Y.smallEtaleTopology
    terminalIsTerminal q G
  exact ⟨(e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅).addCommGroupIsoToAddEquiv⟩

/-- Over a field, the geometric stalk of a higher direct image is the cohomology
of the base change to the chosen algebraic closure.

Source: Stacks Project, Tag 03Q9 (higher direct images), Tag 03SI (topological
invariance), and blueprint `lem-sc-cd-ground-field`, proof steps 2--4.
(blueprint: lem-sc-field-higher-direct-image-stalk)

Proof: finite type over a field makes the source locally Noetherian, so the morphism
is quasi-separated. In the identity affine chart the maximal ideal of the strict
henselization C is the extension of the zero prime of K, hence zero. Thus C is a
field; its separably closed residue field identifies with C. The evaluation C → L
is compatible with K → L, making L algebraic over C. An algebraic extension of a
separably closed field is purely inseparable, so Spec L → Spec C and its base change
are universal homeomorphisms. Apply the strict-henselization stalk formula, convert
between ordinary and bounded-below right derived functors and Ext cohomology, and
compose with topological invariance and the composition isomorphism for pullback.
The explicit algebraically-closed instance is redundant with IsAlgClosure and
keeps instance search in the statement independent of the choice of ground field. -/
theorem nonempty_addEquiv_sheafFiber_rightDerived_lowerStar_of_isAlgClosure
    {K : Type u} [Field K] (L : Type u) [Field L] [Algebra K L]
    [IsAlgClosure K L] [IsAlgClosed L] {X : Scheme.{u}} (a : X ⟶ Spec (.of K))
    [LocallyOfFiniteType a] [QuasiCompact a]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion)
    (q : ℕ) :
    Nonempty
      ((((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K L)))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj
          (((lowerStar AddCommGrpCat.{u + 1} a).rightDerived q).obj F)) ≃+
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
          (pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap K L))))).obj F) q) := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let g := strictHenselizationStructuralMap s
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian a
  have : QuasiSeparated a := (quasiSeparated_iff_quasiSeparatedSpace a).2 inferInstance
  obtain ⟨d⟩ := nonempty_addEquiv_strictLocalization a L s F hF q
  let k := Spec.map (strictHenselizationEval s)
  have hk : k ≫ g = s := spec_map_strictHenselizationEval_comp_strictLocalizationToBase s
  have : IsUniversalHomeomorphism k :=
    isUniversalHomeomorphism_field_strictHenselizationEval L
  let p := pullback.fst a g
  let pL := pullback.fst a s
  let u : pullback a s ⟶ pullback a g :=
    pullback.lift pL (pullback.snd a s ≫ k) (by
      rw [Category.assoc, hk]
      exact pullback.condition)
  have hp : u ≫ p = pL := pullback.lift_fst _ _ _
  have hu : IsPullback u (pullback.snd a s) (pullback.snd a g) k := by
    have outer : IsPullback (u ≫ p) (pullback.snd a s) a (k ≫ g) := by
      rw [hp, hk]
      exact IsPullback.of_hasPullback a s
    exact outer.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback a g)
  have : IsUniversalHomeomorphism u :=
    MorphismProperty.of_isPullback (P := @IsUniversalHomeomorphism) hu.flip inferInstance
  let G := (upperStar AddCommGrpCat.{u + 1} p).obj F
  let ec := (upperStarComp AddCommGrpCat.{u + 1} u p pL hp.symm).symm.app F
  exact ⟨d.trans ((cohomologyEquiv u G q).trans
    (((Sheaf.functorH _ q).mapIso ec).addCommGroupIsoToAddEquiv))⟩

end AlgebraicGeometry.Etale
