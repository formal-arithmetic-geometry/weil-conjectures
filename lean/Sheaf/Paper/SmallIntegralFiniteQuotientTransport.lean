/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion
public import Sheaf.AlgebraicGeometry.IntegralConstantModelRealization
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import all Sheaf.Paper.DerivedNakayamaResolution
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Sheaf.NumberTheory.Padics.IntegersCosetBasis

/-! # Finite quotient modules under an integral coefficient isomorphism

Source: the integral-heart local-model completeness argument, Stacks Tags 099L and 099M.
(blueprint: lem-sfb-small-integral-finite-quotient-transport)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.IntegralConstantModel.pointComparison
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesMonoidal AdicCompletion.modulesSymmetric AdicCompletion.modulesClosed
  AdicCompletion.modulesMonoidalPreadditive AdicCompletion.modulesDerived
  AdicCompletion.modulesProducts AdicCompletion.complexProducts

/-- The pro-etale site is essentially small in its own object universe.
Source: essentiallySmallSelf (blueprint: def-sfb-small-coefficient-derived-completion). -/
local instance smallIntegralSiteEssentiallySmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _


/-- The canonical tensor structure on pro-etale abelian sheaves, with fixed universes.
Source: the sheaf tensor construction
(blueprint: def-sfb-small-coefficient-derived-completion). -/
local instance smallIntegralSheafMonoidal (X : Scheme.{u}) :
    MonoidalCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall.{u + 2, u} _ _

/-- Closedness of the same canonical sheaf tensor structure.
Source: the sheaf tensor construction
(blueprint: def-sfb-small-coefficient-derived-completion). -/
local instance smallIntegralSheafClosed (X : Scheme.{u}) :
    MonoidalClosed (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  GrothendieckTopology.monoidalClosed_sheaf_of_essentiallySmall.{u + 2, u} _ _

/-- The canonical monoidal structure on the small coefficient module category.
Source: the relative tensor product of internal modules
(blueprint: def-sfb-small-coefficient-derived-completion). -/
local instance smallIntegralModulesMonoidal
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] (X : Scheme.{u}) :
    MonoidalCategory (SmallAdicCompletion.Modules ℓ E X) := inferInstance

open MonoidalCategory MonObj Opposite

private theorem ringPresheafMon_eq
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}) :
    (sheafToPresheaf _ Ab.{u + 1}).monObjObj
      ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R) =
        R.obj.monObjCompForget₂ := by
  apply MonObj.ext
  let A := (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  let : MonObj A.obj := R.obj.monObjCompForget₂
  exact Sheaf.μ_comp_map_mul A

private def ringSheafHom
    {R S : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}}
    (f : (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R ⟶
      (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj S)
    [IsMonHom f] : R ⟶ S := by
  let F := sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  have hR := ringPresheafMon_eq R
  have hS := ringPresheafMon_eq S
  have hf : @IsMonHom (Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) _ _ _ _
      R.obj.monObjCompForget₂ S.obj.monObjCompForget₂ f.hom := by
    rw [← hR, ← hS]
    exact Functor.map.instIsMonHom (F := F) _ _ f
  refine ⟨{ app := fun U ↦ ?_, naturality := ?_ }⟩
  · refine RingCat.ofHom
      { toFun := fun a ↦ (f.hom.app U) a
        map_zero' := map_zero _
        map_add' := map_add _
        map_one' := ?_
        map_mul' := ?_ }
    · have h := @IsMonHom.one_hom _ _ _ _ _
        R.obj.monObjCompForget₂ S.obj.monObjCompForget₂ f.hom hf
      have he := ConcreteCategory.congr_hom (congr_app h U) (ULift.up 1)
      change (f.hom.app U) ((1 : ℤ) : R.obj.obj U) = ((1 : ℤ) : S.obj.obj U) at he
      simpa only [Int.cast_one] using he
    · intro a b
      have h := @IsMonHom.mul_hom _ _ _ _ _
        R.obj.monObjCompForget₂ S.obj.monObjCompForget₂ f.hom hf
      exact ConcreteCategory.congr_hom (congr_app h U) (a ⊗ₜ[ℤ] b)
  · intro U V g
    ext a
    exact ConcreteCategory.congr_hom (f.hom.naturality g) a

private def ringSheafIso
    {R S : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}}
    (e : Mon.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R) ≅
      Mon.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj S)) : R ≅ S where
  hom := ringSheafHom e.hom.hom
  inv := ringSheafHom e.inv.hom
  hom_inv_id := by
    ext U a
    have h := congr_app (congrArg (fun f ↦ f.hom.hom) e.hom_inv_id) U
    exact ConcreteCategory.congr_hom h a
  inv_hom_id := by
    ext U a
    have h := congr_app (congrArg (fun f ↦ f.hom.hom) e.inv_hom_id) U
    exact ConcreteCategory.congr_hom h a

private def singletonRingEquiv (R : Type*) [TopologicalSpace R] [Ring R]
    [IsTopologicalRing R] :
    R ≃+* ULift.{u + 1} C(Profinite.of PUnit.{u + 1}, R) where
  toFun r := ULift.up (ContinuousMap.const _ r)
  invFun f := f.down PUnit.unit
  left_inv _ := rfl
  right_inv f := by
    apply ULift.ext
    ext x
    exact congrArg f.down (Subsingleton.elim _ _)
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private theorem mapCoefficientIdeal
    (l : ℕ) [Fact l.Prime] (E : Type*) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (F : Type*) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (a : Padic.coefficientExtensionIntegers l E ≃+*
      Padic.coefficientExtensionIntegers l F) (n : ℕ) :
    Ideal.map a (Padic.coefficientExtensionIdeal l E n) =
      Padic.coefficientExtensionIdeal l F n := by
  have hE := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hF := (Padic.extension_integers_dvr l F (Padic.coefficientExtensionAbsoluteValue l F)
    (spectralNorm_extends (K := Padic l) (L := F))).choose_spec.choose_spec
  let : IsLocalRing (Padic.coefficientExtensionIntegers l E) := hE.2.2.2.1
  let : IsLocalRing (Padic.coefficientExtensionIntegers l F) := hF.2.2.2.1
  have hmaxE : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := hE.2.2.2.2.1
  have hmaxF : (Padic.coefficientExtensionMaximalIdeal l F).IsMaximal := hF.2.2.2.2.1
  have hmE : IsLocalRing.maximalIdeal (Padic.coefficientExtensionIntegers l E) =
      Padic.coefficientExtensionMaximalIdeal l E := (IsLocalRing.eq_maximalIdeal hmaxE).symm
  have hmF : IsLocalRing.maximalIdeal (Padic.coefficientExtensionIntegers l F) =
      Padic.coefficientExtensionMaximalIdeal l F := (IsLocalRing.eq_maximalIdeal hmaxF).symm
  have hgenE : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    hE.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hgenF : Ideal.span {Padic.coefficientExtensionUniformizer l F} =
      Padic.coefficientExtensionMaximalIdeal l F :=
    hF.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  change Ideal.map a (Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ n) =
    Ideal.span {Padic.coefficientExtensionUniformizer l F} ^ n
  rw [hgenE, hgenF, Ideal.map_pow, ← hmE, ← hmF,
    IsLocalRing.map_ringEquiv_maximalIdeal]

private def integerIso
    (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (c : Mon.mk (SmallAdicCompletion.Coefficients.integerRing.{u} l E) ≅
      Mon.mk (DerivedNakayama.integerRing l F)) :
    SmallAdicCompletion.Coefficients.integers l E ≃+*
      Padic.coefficientExtensionIntegers l F := by
  letI := (Padic.coefficientExtensionAbsoluteValue l F).toNormedField
  let d : Profinite.continuousMapRingSheaf.{u}
      (SmallAdicCompletion.Coefficients.integers l E) ≅
      DerivedNakayama.integerRingSheaf l F := ringSheafIso c
  exact (singletonRingEquiv _).trans
    ((Iso.ringCatIsoToRingEquiv ((sheafToPresheaf _ _).mapIso d |>.app
      (op (Profinite.of PUnit.{u + 1})))).trans (singletonRingEquiv _).symm)

private theorem integerIso_apply
    (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (c : Mon.mk (SmallAdicCompletion.Coefficients.integerRing.{u} l E) ≅
      Mon.mk (DerivedNakayama.integerRing l F))
    (S : Profinite.{u})
    (f : (SmallAdicCompletion.Coefficients.integerRing.{u} l E).obj.obj (op S))
    (x : S) :
    ((c.hom.hom.hom.app (op S)) f).down x = integerIso l E F c (f.down x) := by
  let i : Profinite.of PUnit.{u + 1} ⟶ S :=
    ConcreteCategory.ofHom (ContinuousMap.const _ x)
  have h := ConcreteCategory.congr_hom (c.hom.hom.hom.naturality i.op) f
  have hf :
      (SmallAdicCompletion.Coefficients.integerRing.{u} l E).obj.map i.op f =
        (singletonRingEquiv _ : SmallAdicCompletion.Coefficients.integers l E ≃+* _)
          (f.down x) := by
    apply ULift.ext
    ext t
    rfl
  change (c.hom.hom.hom.app (op (Profinite.of PUnit.{u + 1})))
      ((SmallAdicCompletion.Coefficients.integerRing.{u} l E).obj.map i.op f) =
    (DerivedNakayama.integerRing l F).obj.map i.op ((c.hom.hom.hom.app (op S)) f) at h
  rw [hf] at h
  exact (congrArg (fun z ↦ z.down PUnit.unit) h).symm

private theorem spectralQuotientDiscrete
    (l : ℕ) [Fact l.Prime] (E : Type*) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    letI := spectralNorm.normedField (Padic l) E
    DiscreteTopology (Padic.coefficientExtensionRing l E n) := by
  let := spectralNorm.normedField (Padic l) E
  cases n with
  | zero =>
    have : Subsingleton (Padic.coefficientExtensionRing l E 0) := by
      apply Ideal.Quotient.subsingleton_iff.mpr
      simp [Padic.coefficientExtensionIdeal]
    exact Subsingleton.discreteTopology
  | succ n =>
    have hb := Padic.coefficientExtension_integers_coset_basis l E
    have hq : IsLocallyConstant
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) := by
      apply (IsLocallyConstant.iff_eventually_eq _).mpr
      intro x
      exact (hb x).mem_of_mem (i := n) trivial
    apply discreteTopology_iff_isOpen_singleton.mpr
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← isQuotientMap_quot_mk.isOpen_preimage]
    exact hq.isOpen_fiber _

private def quotientRingSheafIso
    (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (c : Mon.mk (SmallAdicCompletion.Coefficients.integerRing.{u} l E) ≅
      Mon.mk (DerivedNakayama.integerRing l F)) (n : ℕ) :
    SmallAdicCompletion.Coefficients.quotientRingSheaf.{u} l E n ≅
      DerivedNakayama.quotientRingSheaf l F n := by
  letI := (Padic.coefficientExtensionAbsoluteValue l F).toNormedField
  let a := integerIso l E F c
  let q := Ideal.quotientEquiv
    (Padic.coefficientExtensionIdeal l (SmallAdicCompletion.Coefficients.field l E) n)
    (Padic.coefficientExtensionIdeal l F n) a
    (mapCoefficientIdeal l _ F a n).symm
  letI := spectralQuotientDiscrete l (SmallAdicCompletion.Coefficients.field l E) n
  letI := DerivedNakayama.quotientDiscrete l F n
  exact
    { hom := ⟨{
        app := fun _ ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((q.toRingHom.compLeftContinuous _ continuous_of_discreteTopology).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun _ ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((q.symm.toRingHom.compLeftContinuous _ continuous_of_discreteTopology).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        ext x
        exact q.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        ext x
        exact q.apply_symm_apply _ }

private def quotientIso
    (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (c : Mon.mk (SmallAdicCompletion.Coefficients.integerRing.{u} l E) ≅
      Mon.mk (DerivedNakayama.integerRing l F)) (n : ℕ) :
    SmallAdicCompletion.Coefficients.quotientRing.{u} l E n ≅
      DerivedNakayama.quotientRing l F n :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso
    (quotientRingSheafIso l E F c n)

private instance quotientIso_isMonHom
    (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (c : Mon.mk (SmallAdicCompletion.Coefficients.integerRing.{u} l E) ≅
      Mon.mk (DerivedNakayama.integerRing l F)) (n : ℕ) :
    IsMonHom (quotientIso l E F c n).hom := by
  exact Sheaf.isMonHom_sheafCompose_map _ (quotientRingSheafIso l E F c n).hom

private theorem quotientIso_unit
    (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (c : Mon.mk (SmallAdicCompletion.Coefficients.integerRing.{u} l E) ≅
      Mon.mk (DerivedNakayama.integerRing l F)) (n : ℕ) :
    SmallAdicCompletion.Coefficients.reductionRing.{u} l E n ≫
      (quotientIso l E F c n).hom = c.hom.hom ≫ DerivedNakayama.reductionRing l F n := by
  let := (Padic.coefficientExtensionAbsoluteValue l F).toNormedField
  ext S f
  apply ULift.ext
  ext x
  change Ideal.quotientEquiv _ _ (integerIso l E F c)
    (mapCoefficientIdeal l _ F (integerIso l E F c) n).symm
    (Ideal.Quotient.mk _ (f.down x)) =
      Ideal.Quotient.mk _ (((c.hom.hom.hom.app S) f).down x)
  rw [Ideal.quotientEquiv_mk, integerIso_apply]

private theorem quotientIso_step
    (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (c : Mon.mk (SmallAdicCompletion.Coefficients.integerRing.{u} l E) ≅
      Mon.mk (DerivedNakayama.integerRing l F)) (n : ℕ) :
    SmallAdicCompletion.transitionRing.{u} l E n ≫ (quotientIso l E F c (n + 1)).hom =
      (quotientIso l E F c (n + 2)).hom ≫ AdicCompletion.transitionRing l F n := by
  let := (Padic.coefficientExtensionAbsoluteValue l F).toNormedField
  ext S f
  apply ULift.ext
  ext x
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (f.down x)
  change Ideal.quotientEquiv _ _ (integerIso l E F c)
      (mapCoefficientIdeal l _ F (integerIso l E F c) (n + 1)).symm
      (Padic.coefficientExtensionTransition l _ (n + 1) (f.down x)) =
    Padic.coefficientExtensionTransition l F (n + 1)
      (Ideal.quotientEquiv _ _ (integerIso l E F c)
        (mapCoefficientIdeal l _ F (integerIso l E F c) (n + 2)).symm (f.down x))
  rw [← hr]
  simp only [Padic.coefficientExtensionTransition, Ideal.Quotient.factor_mk,
    Ideal.quotientEquiv_mk]

private theorem pulledQuotientAction
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
    {R B : C} [MonObj R] [MonObj B] (q : R ⟶ B) [IsMonHom q] :
    Mod.act ((F.mapMod R).obj ((Mod.comap q).obj (Mod.regular B))).X =
      F.map q ▷ F.obj B ≫ μ[F.obj B] := by
  change Functor.LaxMonoidal.μ F R B ≫ F.map (q ▷ B ≫ μ[B]) = _
  rw [Functor.map_comp, ← Functor.LaxMonoidal.μ_natural_left_assoc]
  rfl

private theorem restrictedLinear
    {C : Type*} [Category C] [MonoidalCategory C]
    {R S T : C} [MonObj S] [MonObj T] (q : R ⟶ S) (r : R ⟶ T)
    (f : S ⟶ T) [IsMonHom f] (h : q ≫ f = r) :
    (q ▷ S ≫ μ[S]) ≫ f = R ◁ f ≫ (r ▷ T ≫ μ[T]) := by
  simp only [Category.assoc, IsMonHom.mul_hom, tensorHom_def']
  rw [← whisker_exchange_assoc, ← comp_whiskerRight_assoc, h]

/-- A condensed integral ring isomorphism identifies the positive finite quotient
modules, their quotient units and their consecutive transition maps. This is a
statement about ordinary modules; it assumes no completeness or bound on a complex.

Source: integral-heart-local-model, clause (2), Completeness; Stacks Tags 099L and
099M, and the positive quotient construction of the coefficient DVR.
(blueprint: lem-sfb-small-integral-finite-quotient-transport)

Proof: evaluate the condensed ring isomorphism on the one-point profinite space.
Evaluation on points and naturality show that its action on continuous functions is
postcomposition by the resulting ring isomorphism. A ring isomorphism between the
coefficient DVRs carries the unique maximal ideal to the unique maximal ideal, and
therefore carries its (n+1)st power to the same power. The universal property of the
quotient gives the finite quotient isomorphism. Positive quotients are finite discrete
topological rings, so these maps and their inverses are continuous. The quotient
isomorphisms commute with the quotient units and consecutive quotient maps, as can
be checked after their surjective quotient maps. Apply the continuous-function
construction and pull back to X. Restriction along the inverse coefficient map turns
these ring maps into the displayed module isomorphisms. The regular-module unit of
the monoidal scalar restriction is the coefficient isomorphism itself; hence the
first equality includes exactly its inverse, as displayed. Both equalities can be
checked before pullback and are preserved by it. The spectral/absolute coefficient
identification is pointComparison, so its use changes no quotient or unit. -/
theorem smallIntegralFiniteQuotientTransport
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (F : Type u) [Field F] [Algebra (Padic ℓ) F] [FiniteDimensional (Padic ℓ) F]
    (e : Mon.mk (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E) ≅
      sfbCondensedIntegers ℓ F) (X : Scheme.{u}) :
    let G := Mod.comap (coefficientMap (IntegralConstantModel.pointComparison ℓ F).hom.hom X ≫
      coefficientMap e.inv.hom X)
    ∃ b : ∀ n : ℕ, G.obj (SmallAdicCompletion.finiteModule ℓ E X n) ≅
        AdicCompletion.finiteModule ℓ F X n,
      (∀ n : ℕ, G.map (SmallAdicCompletion.finiteUnit ℓ E X n) ≫ (b n).hom =
        (Functor.Monoidal.εIso G).inv ≫ AdicCompletion.finiteUnit ℓ F X n) ∧
      ∀ n : ℕ,
        G.map ((SmallAdicCompletion.Coefficients.pullback.{u, v} ℓ E X).map
            (SmallAdicCompletion.quotientStep.{u, v} ℓ E n)) ≫ (b n).hom =
          (b (n + 1)).hom ≫ (DerivedNakayama.pullback ℓ F X).map
            (AdicCompletion.quotientStep.{u} ℓ F n) := by
  let c : Mon.mk (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E) ≅
      Mon.mk (DerivedNakayama.integerRing ℓ F) :=
    e ≪≫ (IntegralConstantModel.pointComparison ℓ F).symm
  let H := upperStarFromPoint X
  let ψ := coefficientMap (IntegralConstantModel.pointComparison ℓ F).hom.hom X ≫
    coefficientMap e.inv.hom X
  let G : SmallAdicCompletion.Modules ℓ E X ⥤ AdicCompletion.Modules ℓ F X :=
    Mod.comap ψ
  have hψ : ψ = H.map c.inv.hom := by
    simp only [ψ, c, Iso.trans_inv, Iso.symm_inv, ← coefficientMap_comp]
    rfl
  have hci : c.inv.hom ≫ c.hom.hom = 𝟙 _ :=
    congrArg (fun f ↦ f.hom) c.inv_hom_id
  have hch : c.hom.hom ≫ c.inv.hom = 𝟙 _ :=
    congrArg (fun f ↦ f.hom) c.hom_inv_id
  let b (n : ℕ) : G.obj (SmallAdicCompletion.finiteModule ℓ E X n) ≅
      AdicCompletion.finiteModule ℓ F X n :=
    Mod.isoMk (H.mapIso (quotientIso ℓ E F c (n + 1))) (by
      rw [Mod.act_comap_obj, pulledQuotientAction, pulledQuotientAction]
      change (ψ ▷ H.obj (SmallAdicCompletion.Coefficients.quotientRing ℓ E (n + 1)) ≫
        H.map (SmallAdicCompletion.Coefficients.reductionRing ℓ E (n + 1)) ▷ _ ≫
        μ[H.obj (SmallAdicCompletion.Coefficients.quotientRing ℓ E (n + 1))]) ≫
          H.map (quotientIso ℓ E F c (n + 1)).hom = _
      rw [← comp_whiskerRight_assoc]
      apply restrictedLinear
      rw [hψ, ← H.map_comp, ← H.map_comp, Category.assoc, quotientIso_unit,
        ← Category.assoc, hci, Category.id_comp])
  refine ⟨b, ?_, ?_⟩
  · intro n
    apply Mod.hom_ext
    change H.map (SmallAdicCompletion.Coefficients.reductionRing ℓ E (n + 1)) ≫
        H.map (quotientIso ℓ E F c (n + 1)).hom =
      inv ψ ≫ H.map (DerivedNakayama.reductionRing ℓ F (n + 1))
    rw [← H.map_comp, quotientIso_unit, H.map_comp]
    congr 1
    apply (cancel_mono ψ).mp
    rw [IsIso.inv_hom_id, hψ, ← H.map_comp, hch, H.map_id]
  · intro n
    apply Mod.hom_ext
    change H.map (SmallAdicCompletion.transitionRing ℓ E n) ≫
        H.map (quotientIso ℓ E F c (n + 1)).hom =
      H.map (quotientIso ℓ E F c (n + 2)).hom ≫
        H.map (AdicCompletion.transitionRing ℓ F n)
    rw [← H.map_comp, quotientIso_step, H.map_comp]

end AlgebraicGeometry.ProEtale
