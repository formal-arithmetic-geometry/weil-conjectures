/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison
public import WeilConjectures.AlgebraicGeometry.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralDerivedOperationsOnSlices
import WeilConjectures.AlgebraicGeometry.IntegralScalarCompletionUnitComparison
import all WeilConjectures.SixFunctors.OpenRoosUnitAdjunction

/-! # Unit-normalized scalar completion

Source: Stacks Tag 0941, finite-free tensor/product interchange, and the completion
reflector. The declarations are split out of CompactSupportScalarProjectionIdentification
without changing their signatures or the chosen scalar map.
(blueprint: lem-pur-compact-support-scalar-completion-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurScalarProjection

attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  IntegralOnSlice.completion IntegralOnSlice.completionUnit
  completedCoefficientMap

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/- The general reflector proof in OpenRoos does not need a finite-field structure on W.
The auxiliary characteristic only supplies the witness used in the Roos completeness predicate.
The normalized principal-cone comparison transports the Koszul reflector and its unit. -/
private theorem completion_reflector (W : Scheme.{u}) :
    OpenRoos.ReflectorAssertions l E W := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  have : Fact p.Prime := ⟨hprime⟩
  let D : FiniteFieldDatum.{u} :=
    { p := p
      a := 1
      q := p
      prime := hprime
      exponent_pos := le_refl 1
      cardinality_eq := (pow_one p).symm
      k₀ := ULift.{u} (ZMod p)
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ULift.{u} (ZMod p)) }
  obtain ⟨d, hd⟩ := (OpenRoos.coefficientFacts l E).2.2.1
  exact OpenRoos.reflectorFacts l E W D (by change l ≠ p; omega) d hd

private theorem completion_complete (W : Scheme.{u})
    (Q : DerivedCategory (scalarReductionSource l E W)) :
    IsDerivedCompleteUnrestricted l E W ((IntegralOnSlice.completion l E W none).obj Q) := by
  have r := completion_reflector l E W
  exact (r.2.2.1 _).mpr ((r.2.2.2 _).mpr (r.1 Q))

private theorem completion_extension_unique (W : Scheme.{u})
    {Q R : DerivedCategory (scalarReductionSource l E W)}
    (hR : IsDerivedCompleteUnrestricted l E W R) (a : Q ⟶ R) :
    ∃! b : (IntegralOnSlice.completion l E W none).obj Q ⟶ R,
      (IntegralOnSlice.completionUnit l E W none).app Q ≫ b = a := by
  have r := completion_reflector l E W
  have h := r.2.1 Q R ((r.2.2.2 R).mp ((r.2.2.1 R).mp hR))
  obtain ⟨b, hb⟩ := h.surjective a
  exact ⟨b, hb, fun b' hb' ↦ h.injective (hb'.trans hb.symm)⟩

private theorem scalar_unit_unique
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ D) (A : C ⥤ C) (B : D ⥤ D)
    (u : 𝟭 C ⟶ A) (v : 𝟭 D ⟶ B) (Q : C)
    (hex : ∃ χ : T.obj (A.obj Q) ≅ B.obj (T.obj Q),
      T.map (u.app Q) ≫ χ.hom = v.app (T.obj Q))
    (hinj : Function.Injective
      (fun f : B.obj (T.obj Q) ⟶ B.obj (T.obj Q) ↦ v.app (T.obj Q) ≫ f)) :
    ∃! χ : T.obj (A.obj Q) ≅ B.obj (T.obj Q),
      T.map (u.app Q) ≫ χ.hom = v.app (T.obj Q) := by
  obtain ⟨χ, hχ⟩ := hex
  refine ⟨χ, hχ, ?_⟩
  intro ψ hψ
  have hcan : χ.inv ≫ ψ.hom = 𝟙 _ := by
    apply hinj
    have h := congrArg (fun f ↦ f ≫ χ.inv ≫ ψ.hom) hχ.symm
    simp only [Category.assoc, Iso.hom_inv_id_assoc] at h
    exact h.trans (hψ.trans (Category.comp_id _).symm)
  apply Iso.ext
  apply (cancel_epi χ.inv).1
  rw [hcan, χ.inv_hom_id]

/-- Finite-free scalar extension commutes with completion, uniquely normalized
by its unit. Source: Stacks 0941 and finite-free tensor/product interchange;
(blueprint: lem-pur-compact-support-scalar-completion-normalization), Steps 1 and 8.
Proof: use one integral basis to commute tensor with both countable products of
the Roos cone. The quotient balancing maps identify its target with the full
F-adic tower, followed by the arithmetic cofinality comparison. This preserves
the augmentation. Completeness and the reflector Hom bijection prove uniqueness.
No faithfulness of finite evaluation is used. -/
theorem scalarCompletion_existsUnique (W : Scheme.{u})
    (Q : DerivedCategory (scalarReductionSource l E W)) :
    ∃! χ : (pbcDerivedExtend (completedCoefficientMap l E F i W)).obj
          ((IntegralOnSlice.completion l E W none).obj Q) ≅
        (IntegralOnSlice.completion l F W none).obj
          ((pbcDerivedExtend (completedCoefficientMap l E F i W)).obj Q),
      (pbcDerivedExtend (completedCoefficientMap l E F i W)).map
          ((IntegralOnSlice.completionUnit l E W none).app Q) ≫ χ.hom =
        (IntegralOnSlice.completionUnit l F W none).app
          ((pbcDerivedExtend (completedCoefficientMap l E F i W)).obj Q) := by
  let T := pbcDerivedExtend (completedCoefficientMap l E F i W)
  let A := IntegralOnSlice.completion l E W none
  let B := IntegralOnSlice.completion l F W none
  have r := completion_reflector l F W
  exact scalar_unit_unique T A B (IntegralOnSlice.completionUnit l E W none)
    (IntegralOnSlice.completionUnit l F W none) Q
    (integralScalarCompletionUnitComparison l E F i W Q)
    (r.2.1 (T.obj Q) (B.obj (T.obj Q)) (r.1 (T.obj Q))).injective

/-- The unit-normalized finite-free completion comparison, rather than a choice
of an isomorphism between the endpoints. Source: Stacks 0941;
(blueprint: lem-pur-compact-support-scalar-completion-normalization), Step 8. -/
def scalarCompletion (W : Scheme.{u})
    (Q : DerivedCategory (scalarReductionSource l E W)) :=
  (scalarCompletion_existsUnique l E F i W Q).exists.choose

private theorem scalarCompletion_iso_naturality (W : Scheme.{u})
    {Q R : DerivedCategory (scalarReductionSource l E W)} (q : Q ≅ R) :
    (pbcDerivedExtend (completedCoefficientMap l E F i W)).map
        ((IntegralOnSlice.completion l E W none).map q.hom) ≫
        (scalarCompletion l E F i W R).hom =
      (scalarCompletion l E F i W Q).hom ≫
        (IntegralOnSlice.completion l F W none).map
          ((pbcDerivedExtend (completedCoefficientMap l E F i W)).map q.hom) := by
  let T := pbcDerivedExtend (completedCoefficientMap l E F i W)
  let A := IntegralOnSlice.completion l E W none
  let B := IntegralOnSlice.completion l F W none
  let z := T.mapIso (A.mapIso q) ≪≫ scalarCompletion l E F i W R ≪≫
    (B.mapIso (T.mapIso q)).symm
  have hz : T.map ((IntegralOnSlice.completionUnit l E W none).app Q) ≫ z.hom =
      (IntegralOnSlice.completionUnit l F W none).app (T.obj Q) := by
    have hQ := congrArg T.map
      ((IntegralOnSlice.completionUnit l E W none).naturality q.hom)
    have hR := (scalarCompletion_existsUnique l E F i W R).exists.choose_spec
    have hF := (IntegralOnSlice.completionUnit l F W none).naturality (T.map q.hom)
    with_unfolding_all dsimp only [
      z, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv]
    with_unfolding_all simp only [Functor.id_map, Functor.map_comp] at hQ hF
    replace hQ := hQ.symm
    change T.map _ ≫ T.map (A.map q.hom) = T.map q.hom ≫ T.map _ at hQ
    erw [reassoc_of% hQ, reassoc_of% hR, reassoc_of% hF]
    erw [← B.map_comp, ← T.map_comp, q.hom_inv_id, T.map_id, B.map_id,
      Category.comp_id]
  have heq : z = scalarCompletion l E F i W Q :=
    (scalarCompletion_existsUnique l E F i W Q).unique hz
      (scalarCompletion_existsUnique l E F i W Q).exists.choose_spec
  have hh := congrArg (fun a ↦ a.hom ≫ B.map (T.map q.hom)) heq
  with_unfolding_all simp only [z, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.mapIso_inv, Category.assoc, ← B.map_comp, ← T.map_comp,
    q.inv_hom_id, T.map_id, B.map_id] at hh
  erw [Category.comp_id] at hh
  exact hh

end WeilConjectures.PurScalarProjection
