/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J9
-/
module

public import Mathlib.Algebra.Field.ULift
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.IntegralDerivedCoefficientData
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Comparing the two integral coefficient presentations

Source: the coefficient conventions of sk-def-sf-setting and det-lem-int-ext-bound;
Mathlib spectralNorm_unique_field_norm_ext and the definition of finite constant models.
(blueprint: lem-integral-coefficient-ext-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

section

private theorem spectral_embedded_norm
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)] (x : ULift.{u} E.val) :
    Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.val) x =
      ‖(x.down : PadicAlgCl ℓ)‖ := by
  let f : ULift.{u} E.val →+* PadicAlgCl ℓ :=
    E.val.val.toRingHom.comp ULift.ringEquiv.toRingHom
  let a : AbsoluteValue (ULift.{u} E.val) ℝ :=
    { toFun := fun x ↦ ‖f x‖
      map_mul' := fun x y ↦ by rw [map_mul, norm_mul]
      nonneg' := fun x ↦ norm_nonneg _
      eq_zero' := fun x ↦ by simp only [norm_eq_zero, map_eq_zero_iff f f.injective]
      add_le' := fun x y ↦ by rw [map_add]; exact norm_add_le _ _ }
  have ha : ∀ y : ℚ_[ℓ], a (algebraMap ℚ_[ℓ] (ULift.{u} E.val) y) = ‖y‖ := by
    intro y
    change ‖algebraMap ℚ_[ℓ] (PadicAlgCl ℓ) y‖ = ‖y‖
    exact PadicAlgCl.norm_extends ℓ y
  exact (spectralNorm_unique_field_norm_ext ha x).symm
open CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
private theorem mem_lift_integers
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)] (x : ULift.{u} E.val) :
    x ∈ Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val) ↔
      x.down ∈ PadicAlgCl.integers ℓ E.val := by
  have h := (Padic.extension_integers_dvr ℓ (ULift.{u} E.val)
    (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.val))
    (spectralNorm_extends (K := ℚ_[ℓ]) (L := ULift.{u} E.val))).choose_spec.choose_spec.1 x
  rw [spectral_embedded_norm ℓ E x] at h
  exact h.trans (by
    rw [PadicAlgCl.mem_integers_iff, ← NNReal.coe_le_coe]
    rfl)
private noncomputable def integerLiftEquiv
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)] :
    PadicAlgCl.integers ℓ E.val ≃+*
      Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val) where
  toFun x := ⟨ULift.up x.val, (mem_lift_integers ℓ E _).2 x.property⟩
  invFun x := ⟨x.val.down, (mem_lift_integers ℓ E _).1 x.property⟩
  left_inv _x := rfl
  right_inv _x := rfl
  map_mul' _x _y := rfl
  map_add' _x _y := rfl
private noncomputable def integerLiftHomeo
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)] :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.val
    letI nf := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.val)).toNormedField
    letI : TopologicalSpace (ULift.{u} E.val) :=
      nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    PadicAlgCl.integers ℓ E.val ≃ₜ
      Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val) := by
  letI src := PadicAlgCl.normedFieldOfAlgebra ℓ E.val
  letI tgt := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.val)).toNormedField
  letI : TopologicalSpace (ULift.{u} E.val) :=
    tgt.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let e := integerLiftEquiv ℓ E
  let sm : MetricSpace (PadicAlgCl.integers ℓ E.val) :=
    @Subtype.metricSpace E.val _ src.toMetricSpace
  let tm : MetricSpace (Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val)) :=
    @Subtype.metricSpace (ULift.{u} E.val) _ tgt.toMetricSpace
  letI : PseudoEMetricSpace (PadicAlgCl.integers ℓ E.val) :=
    sm.toPseudoMetricSpace.toPseudoEMetricSpace
  letI : PseudoEMetricSpace
      (Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val)) :=
    tm.toPseudoMetricSpace.toPseudoEMetricSpace
  have hi : @Isometry _ _ sm.toPseudoMetricSpace.toPseudoEMetricSpace
      tm.toPseudoMetricSpace.toPseudoEMetricSpace e := by
    apply @Isometry.of_dist_eq _ _ sm.toPseudoMetricSpace tm.toPseudoMetricSpace
    intro x y
    change Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.val)
      (-ULift.up x.val + ULift.up y.val) = dist
        (algebraMap E.val (PadicAlgCl ℓ) x.val)
        (algebraMap E.val (PadicAlgCl ℓ) y.val)
    rw [spectral_embedded_norm ℓ E]
    change ‖-(x.val : PadicAlgCl ℓ) + (y.val : PadicAlgCl ℓ)‖ =
      dist (x.val : PadicAlgCl ℓ) (y.val : PadicAlgCl ℓ)
    exact (dist_eq_norm_neg_add _ _).symm
  exact { e.toEquiv with
    continuous_toFun := hi.continuous
    continuous_invFun := (hi.right_inv e.right_inv).continuous }

open CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
private noncomputable def integerRingSheafIso
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)] :
    Profinite.padicIntegersCondensedRing.{u} ℓ E.val ≅
      DerivedNakayama.integerRingSheaf ℓ (ULift.{u} E.val) := by
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.val
  letI nf := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.val)).toNormedField
  letI : Norm (ULift.{u} E.val) := nf.toNorm
  letI : MetricSpace (ULift.{u} E.val) := nf.toMetricSpace
  letI : TopologicalSpace (ULift.{u} E.val) :=
    nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let e := integerLiftEquiv ℓ E
  let h := integerLiftHomeo ℓ E
  let forward (S : Profinite.{u}ᵒᵖ) :
      ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E.val) →+*
        ULift.{u + 1} C(S.unop, Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val)) :=
    ULift.ringEquiv.symm.toRingHom.comp
      ((e.toRingHom.compLeftContinuous _ h.continuous_toFun).comp ULift.ringEquiv.toRingHom)
  let backward (S : Profinite.{u}ᵒᵖ) :
      ULift.{u + 1} C(S.unop, Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val)) →+*
        ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E.val) :=
    ULift.ringEquiv.symm.toRingHom.comp
      ((e.symm.toRingHom.compLeftContinuous _ h.continuous_invFun).comp
        ULift.ringEquiv.toRingHom)
  refine
    { hom := ⟨{ app := fun S ↦ RingCat.ofHom (forward S)
                naturality := by intros; ext x; rfl }⟩
      inv := ⟨{ app := fun S ↦ RingCat.ofHom (backward S)
                naturality := by intros; ext x; rfl }⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · ext S x
    apply ULift.ext
    ext t
    rfl
  · ext S x
    apply ULift.ext
    ext t
    rfl

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (e : Λ ≅ Λ') [IsMonHom e.hom]
private noncomputable def coeffTransport (X : Scheme.{u}) :=
  Mod.comapEquivalenceOfIsIso ((upperStarFromPoint X).map e.inv)
omit [IsCommMonObj Λ] [IsCommMonObj Λ'] in
private theorem coeffTransport_additive (X : Scheme.{u}) :
    (coeffTransport e X).functor.Additive := by
  change (Mod.comap ((upperStarFromPoint X).map e.inv)).Additive
  infer_instance

open CategoryTheory.Limits
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (e : Λ ≅ Λ') [IsMonHom e.hom]
private noncomputable def pointTransport := Mod.comapEquivalenceOfIsIso e.inv
private instance pointTransport_additive : (pointTransport e).functor.Additive := by
  change (Mod.comap e.inv).Additive
  infer_instance
private noncomputable def freeTransport (n : ℕ) :
    (pointTransport e).functor.obj (Mod.finiteFree Λ n) ≅ Mod.finiteFree Λ' n :=
  (pointTransport e).functor.mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫
    biproduct.mapIso (fun _ ↦ (Mod.comapUnitIso e.inv).symm)
private theorem fpTransport (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (hP : Mod.IsFinitelyPresented Λ P) :
    Mod.IsFinitelyPresented Λ' ((pointTransport e).functor.obj P) := by
  let : PreservesFiniteColimits (tensorLeft Λ') := inferInstance
  obtain ⟨n, m, f, ⟨i⟩⟩ := hP
  let T := (pointTransport e).functor
  let g : Mod.finiteFree Λ' m ⟶ Mod.finiteFree Λ' n :=
    (freeTransport e m).inv ≫ T.map f ≫ (freeTransport e n).hom
  refine ⟨n, m, g, ⟨T.mapIso i ≪≫ PreservesCokernel.iso T f ≪≫ ?_⟩⟩
  exact cokernel.mapIso _ _ (freeTransport e m) (freeTransport e n) (by
    dsimp [g]
    simp)
private noncomputable def transportPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (coeffTransport e Y).functor ⋙ CondensedRing.upperStar Λ' f ≅
      CondensedRing.upperStar Λ f ⋙ (coeffTransport e X).functor :=
  (CondensedRing.comapUpperStarIso e.inv f).symm
private theorem localTransport (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ' X ((coeffTransport e X).functor.obj M) := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨j⟩⟩ := hU i
  refine ⟨(pointTransport e).functor.obj P, fpTransport e P hP, ⟨?_⟩⟩
  exact (transportPullback e (U.f i)).app M ≪≫
    (coeffTransport e (U.X i)).functor.mapIso j ≪≫
    ((upperStarFromPoint (U.X i)).mapModComapIso e.inv).symm.app P

private theorem localModelIso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (j : M ≅ N) (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨k⟩⟩ := hU i
  exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (U.f i)).mapIso j.symm ≪≫ k⟩⟩

private theorem stratifiedTransport (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsFiniteConstantStratified Λ X M) :
    IsFiniteConstantStratified Λ' X ((coeffTransport e X).functor.obj M) := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  exact localModelIso ((transportPullback e (S.immersion a)).app M).symm
    (localTransport e _ _ (hS a))

private theorem stratifiedIso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (j : M ≅ N) (hM : IsFiniteConstantStratified Λ X M) :
    IsFiniteConstantStratified Λ X N := by
  obtain ⟨S, hS⟩ := hM
  exact ⟨S, fun a ↦ localModelIso
    ((CondensedRing.upperStar Λ (S.immersion a)).mapIso j) (hS a)⟩

private theorem constructibleTransport (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ' X ((coeffTransport e X).functor.obj M) := by
  classical
  unfold IsConstantModelConstructible at *
  split_ifs at * with h
  · exact stratifiedTransport e X M hM
  · intro U hU
    exact stratifiedIso ((transportPullback e U.ι).app M).symm
      (stratifiedTransport e _ _ (hM U hU))

end


/-- Changing from the embedded valuation ring to the spectral valuation ring in a larger
universe preserves finite constant models.

Source: det-lem-int-ext-bound, integral coefficient convention; Mathlib's
spectralNorm_unique_field_norm_ext; the definitions in sk-def-sfb-constructible
(blueprint: lem-integral-coefficient-ext-comparison).

Proof: Identify ULift E with E by its algebra equivalence. The spectral absolute value
on the lift equals the pullback of the absolute value induced from PadicAlgCl: both
extend the p-adic absolute value, so spectralNorm_unique_field_norm_ext applies. The
membership characterizations of the two integer rings therefore give a ring equivalence.
The same equality of norms makes that equivalence and its inverse continuous. Apply
continuous postcomposition sectionwise to obtain inverse morphisms of condensed rings;
they preserve addition, multiplication and one pointwise. Pull them back to X. Restriction
of scalars along this ring isomorphism is an additive exact equivalence F of module
categories. It commutes with pullback to every pro-etale cover and stratum, preserves
finite sums of the regular module and cokernels, and hence preserves finite presentations
on the point. Transport the cover, finite presentation and local isomorphism in each
finite constant local model, then the finite stratification, to show constructibility
is preserved. The argument also works on every affine open when X is not qcqs.
No boundedness, completeness,
finite-type or nonempty-scheme hypothesis is needed. -/
theorem integralCoefficientExtComparison
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)] (X : Scheme.{u}) :
    ∃ F :
      CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) ≌
        CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (CondensedRing.integralCoefficientRing ℓ (ULift.{u} E.val)) X),
      F.functor.Additive ∧
      (∀ C, IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X C →
        IsConstantModelConstructible
          (CondensedRing.integralCoefficientRing ℓ (ULift.{u} E.val)) X (F.functor.obj C)) := by
  let e := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso (integerRingSheafIso ℓ E)
  have : IsMonHom e.hom := by
    dsimp [e]
    infer_instance
  exact ⟨coeffTransport e X, coeffTransport_additive e X, constructibleTransport e X⟩

end AlgebraicGeometry.ProEtale
