/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierUnit
import all WeilConjectures.SixFunctors.Coef.CoefVerdierScalarUnitNormalization

/-! Unit component of normalized finite Verdier coherence.

Source: thm-coef-qbar-verdier, identity-extension clause.
(blueprint: lem-coef-qbar-verdier-finite-unit-equation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w z
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage unitor)
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private theorem identity_comparison
    (A : Type u) [Field A] [Algebra (Padic l) A] [FiniteDimensional (Padic l) A]
    (w : IntegralFiniteExtension.DualizingDatum l X D hl A)
    (d : RationalVerdier.Datum D l hl X A w)
    (e : RationalVerdier.Extension D l hl X A A (AlgHom.id (Padic l) A) w w d d)
    (he : RationalVerdier.ExtensionProperties D l hl X A A
      (AlgHom.id (Padic l) A) w w d d e)
    (K : sfRationalConstructibleCategory l A X) :
    e.comparison.hom.app (op K) =
      (sfRationalScalarUnit l A X 0 (Fact.out : l.Prime).ne_zero).hom.app
        (d.dual.obj (op K)) ≫
      d.dual.map ((sfRationalScalarUnit l A X 0
        (Fact.out : l.Prime).ne_zero).hom.app K).op := by
  obtain ⟨j, hj, heq⟩ := RationalVerdier.extension_unit D l hl X A w d e he
  have hunit : j = sfRationalScalarUnit l A X 0 (Fact.out : l.Prime).ne_zero := by
    apply (sfRationalScalarUnit_existsUnique l A X 0 (Fact.out : l.Prime).ne_zero).unique
    · intro M
      have hu := integral_unit_normalization l A X M.obj
      have hu' : ObjectProperty.homMk
          (X := (RationalVerdier.integralScalar l X A A (AlgHom.id (Padic l) A)).obj M.obj)
          (Y := M.obj) (IntegralFiniteExtension.unit l A X M.obj.obj M.obj.property.1).hom =
          (sfIntegralScalarUnit l A X 0 (Fact.out : l.Prime).ne_zero).hom.app M.obj := by
        apply ObjectProperty.hom_ext
        exact hu.symm
      have hm := congrArg (sfRationalConstructibleLocalization l A X).map hu'
      exact (hj M.obj).trans (heq_of_eq hm)
    · exact (sfRationalScalarUnit_existsUnique l A X 0
        (Fact.out : l.Prime).ne_zero).exists.choose_spec
  have h₁ := congrArg (fun z ↦ z.hom.app (d.dual.obj (op K))) hunit
  have h₂ := congrArg (fun z ↦ d.dual.map (z.hom.app K).op) hunit
  exact (heq K).trans (congrArg₂ (fun f g ↦ f ≫ g) h₁ h₂)

private theorem path_reduce {α : Sort*} {b : α}
    (P : (a : α) → a = b → Prop) (p : P b rfl) (a : α) (h : a = b) : P a h := by
  cases h
  exact p

private theorem normalized_identity_comparison
    (A : Type u) [Field A] [Algebra (Padic l) A] [FiniteDimensional (Padic l) A]
    (i : A →ₐ[Padic l] A) (hi : i = AlgHom.id (Padic l) A)
    (w : IntegralFiniteExtension.DualizingDatum l X D hl A)
    (d : RationalVerdier.Datum D l hl X A w)
    : ∀ (e : RationalVerdier.Extension D l hl X A A i w w d d)
    (_he : RationalVerdier.ExtensionProperties D l hl X A A i w w d d e)
    (K : sfRationalConstructibleCategory l A X),
    e.comparison.hom.app (op K) =
      (eqToIso (congrArg (sfRationalScalarExtension l A X 0 (Fact.out : l.Prime).ne_zero A) hi) ≪≫
        sfRationalScalarUnit l A X 0 (Fact.out : l.Prime).ne_zero).hom.app
          (d.dual.obj (op K)) ≫
      d.dual.map ((eqToIso (congrArg
        (sfRationalScalarExtension l A X 0 (Fact.out : l.Prime).ne_zero A) hi) ≪≫
        sfRationalScalarUnit l A X 0 (Fact.out : l.Prime).ne_zero).hom.app K).op := by
  exact path_reduce (fun i hi ↦ ∀ (e : RationalVerdier.Extension D l hl X A A i w w d d)
    (_he : RationalVerdier.ExtensionProperties D l hl X A A i w w d d e)
    (K : sfRationalConstructibleCategory l A X),
    e.comparison.hom.app (op K) =
      (eqToIso (congrArg (sfRationalScalarExtension l A X 0 (Fact.out : l.Prime).ne_zero A) hi) ≪≫
        sfRationalScalarUnit l A X 0 (Fact.out : l.Prime).ne_zero).hom.app
          (d.dual.obj (op K)) ≫
      d.dual.map ((eqToIso (congrArg
        (sfRationalScalarExtension l A X 0 (Fact.out : l.Prime).ne_zero A) hi) ≪≫
        sfRationalScalarUnit l A X 0 (Fact.out : l.Prime).ne_zero).hom.app K).op)
    (by
      intro e he K
      simpa only [eqToIso_refl, Iso.refl_trans] using
        identity_comparison D l hl X A w d e he K) i hi

private theorem stage_unitor_def (E : Index l Ω) :
    unitor l Ω X E =
      eqToIso (congrArg (sfRationalScalarExtension l (Coefficient.{u} l Ω E) X 0
        (Fact.out : l.Prime).ne_zero (Coefficient.{u} l Ω E))
        ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).1 E)) ≪≫
        sfRationalScalarUnit l (Coefficient.{u} l Ω E) X 0
          (Fact.out : l.Prime).ne_zero := by
  unfold GeneralAlgebraicallyClosedCoefficients.unitor
  rfl

private theorem stage_unitor_normalized (E : Index l Ω) :
    HEq (eqToIso (congrArg (sfRationalScalarExtension l (Coefficient.{u} l Ω E) X 0
        (Fact.out : l.Prime).ne_zero (Coefficient.{u} l Ω E))
        ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).1 E)) ≪≫
        sfRationalScalarUnit l (Coefficient.{u} l Ω E) X 0
          (Fact.out : l.Prime).ne_zero) (unitor l Ω X E) := by
  exact heq_of_eq (stage_unitor_def l Ω X E).symm

omit [IsAlgClosure (Padic l) Ω] in
private theorem stage_beta_normalized (F : Finite D l hl Ω X) (E : Index l Ω)
    (K : Stage l Ω X E) :
    HEq ((F.scalar E E le_rfl).comparison.hom.app (op K))
      ((F.beta E E le_rfl).hom.app (op K)) := by
  apply iso_app_hom_heq rfl rfl
  all_goals first | exact (F.betaNormalized E E le_rfl).symm | rfl

private theorem conjugate_unit_transfer
    {C C' : Type w} [cC : Category.{z} C] [cC' : Category.{z} C']
    {F : C ⥤ C} {F' : C' ⥤ C'} {T : Cᵒᵖ ⥤ C} {T' : C'ᵒᵖ ⥤ C'}
    {j : F ≅ 𝟭 C} {j' : F' ≅ 𝟭 C'} {K : C} {K' : C'}
    {b : F.obj (T.obj (op K)) ⟶ T.obj (op (F.obj K))}
    {b' : F'.obj (T'.obj (op K')) ⟶ T'.obj (op (F'.obj K'))}
    (h : b = j.hom.app (T.obj (op K)) ≫ T.map (j.hom.app K).op)
    (hC : C = C') (hc : HEq cC cC') (hF : HEq F F') (hT : HEq T T')
    (hj : HEq j j') (hK : HEq K K') (hb : HEq b b') :
    b' = j'.hom.app (T'.obj (op K')) ≫ T'.map (j'.hom.app K').op := by
  subst C'
  have hc' : cC = cC' := eq_of_heq hc
  subst cC'
  have hF' : F = F' := eq_of_heq hF
  have hT' : T = T' := eq_of_heq hT
  subst F' T'
  have hj' : j = j' := eq_of_heq hj
  have hK' : K = K' := eq_of_heq hK
  subst j' K'
  have hb' : b = b' := eq_of_heq hb
  subst b'
  exact h

private theorem eq_from_heqs {α β : Sort w} {a b : α} {c d : β}
    (h : c = d) (ha : HEq a c) (hb : HEq b d) : a = b :=
  eq_of_heq (ha.trans ((heq_of_eq h).trans hb.symm))

private theorem comp_heq_context
    {C C' : Type w} [cC : Category.{z} C] [cC' : Category.{z} C']
    {A B Z : C} {A' B' Z' : C'}
    {f : A ⟶ B} {g : B ⟶ Z} {f' : A' ⟶ B'} {g' : B' ⟶ Z'}
    (hC : C = C') (hc : HEq cC cC')
    (hA : HEq A A') (hB : HEq B B') (hZ : HEq Z Z')
    (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  subst C'
  have hc' : cC = cC' := eq_of_heq hc
  subst cC'
  have hA' : A = A' := eq_of_heq hA
  have hB' : B = B' := eq_of_heq hB
  have hZ' : Z = Z' := eq_of_heq hZ
  subst A' B' Z'
  have hf' : f = f' := eq_of_heq hf
  have hg' : g = g' := eq_of_heq hg
  subst f' g'
  rfl

private theorem functor_obj_heq_context
    {C C' D D' : Type w} [cC : Category.{z} C] [cC' : Category.{z} C']
    [cD : Category.{z} D] [cD' : Category.{z} D']
    {Q : C ⥤ D} {Q' : C' ⥤ D'} {P : C} {P' : C'}
    (hC : C = C') (hD : D = D') (hc : HEq cC cC') (hd : HEq cD cD')
    (hQ : HEq Q Q') (hP : HEq P P') : HEq (Q.obj P) (Q'.obj P') := by
  subst C' D'
  have hc' : cC = cC' := eq_of_heq hc
  have hd' : cD = cD' := eq_of_heq hd
  subst cC' cD'
  have hQ' : Q = Q' := eq_of_heq hQ
  have hP' : P = P' := eq_of_heq hP
  subst Q' P'
  rfl

private theorem functor_map_heq_context
    {C C' D D' : Type w} [cC : Category.{z} C] [cC' : Category.{z} C']
    [cD : Category.{z} D] [cD' : Category.{z} D']
    {Q : C ⥤ D} {Q' : C' ⥤ D'} {A B : C} {A' B' : C'}
    {f : A ⟶ B} {f' : A' ⟶ B'}
    (hC : C = C') (hD : D = D') (hc : HEq cC cC') (hd : HEq cD cD')
    (hQ : HEq Q Q') (hA : HEq A A') (hB : HEq B B') (hf : HEq f f') :
    HEq (Q.map f) (Q'.map f') := by
  subst C' D'
  have hc' : cC = cC' := eq_of_heq hc
  have hd' : cD = cD' := eq_of_heq hd
  subst cC' cD'
  have hQ' : Q = Q' := eq_of_heq hQ
  have hA' : A = A' := eq_of_heq hA
  have hB' : B = B' := eq_of_heq hB
  subst Q' A' B'
  have hf' : f = f' := eq_of_heq hf
  subst f'
  rfl

private theorem hom_op_heq_context
    {C C' : Type w} [cC : Category.{z} C] [cC' : Category.{z} C']
    {A B : C} {A' B' : C'} {f : A ⟶ B} {f' : A' ⟶ B'}
    (hC : C = C') (hc : HEq cC cC')
    (hA : HEq A A') (hB : HEq B B') (hf : HEq f f') : HEq f.op f'.op := by
  subst C'
  have hc' : cC = cC' := eq_of_heq hc
  subst cC'
  have hA' : A = A' := eq_of_heq hA
  have hB' : B = B' := eq_of_heq hB
  subst A' B'
  have hf' : f = f' := eq_of_heq hf
  subst f'
  rfl

/-- The identity-stage component equation for a finite Verdier datum.
Source: thm-coef-qbar-verdier, final coefficient-transport paragraph;
(blueprint: lem-coef-qbar-verdier-finite-unit-equation).

Proof: identify the identity coefficient inclusion with the identity field map. Apply
RationalVerdier.extension_unit to the normalized rational extension. Its normalized
integral component is exactly the prescribed stage unitor, by the uniqueness theorem
for the canonical scalar unit and the coefficient-inclusion identity law. Transport
along the resulting equality and evaluate at the given stage object. This argument
also covers repeated fields, zero objects, and the empty scheme. -/
theorem finite_unit_equation (F : Finite D l hl Ω X) :
    ∀ (E : Index l Ω) (K : Stage l Ω X E),
    (F.beta E E le_rfl).hom.app (op K) =
      (unitor l Ω X E).hom.app ((F.datum E).dual.obj (op K)) ≫
        (F.datum E).dual.map ((unitor l Ω X E).hom.app K).op := by
  intro E K
  have assembled :=
    conjugate_unit_transfer (C' := Stage l Ω X E)
      (cC' := GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω X E)
      (T' := (F.datum E).dual) (j' := unitor l Ω X E) (K' := K)
      (b' := (F.beta E E le_rfl).hom.app (op K))
      (normalized_identity_comparison D l hl X (Coefficient.{u} l Ω E)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E E le_rfl)
        ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).1 E)
        (F.omega E) (F.datum E) (F.scalar E E le_rfl) (F.normalized E E le_rfl) K) rfl
      HEq.rfl HEq.rfl HEq.rfl (stage_unitor_normalized l Ω X E)
      HEq.rfl (stage_beta_normalized D l hl Ω X F E K)
  refine eq_from_heqs assembled HEq.rfl ?_
  apply comp_heq_context rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · apply iso_app_hom_heq rfl rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · apply functor_obj_heq_context rfl rfl
      all_goals rfl
  · apply functor_map_heq_context rfl rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · apply hom_op_heq_context rfl
      · rfl
      · rfl
      · rfl
      · apply iso_app_hom_heq rfl rfl
        all_goals rfl

end WeilConjectures.CoefQbarVerdier
