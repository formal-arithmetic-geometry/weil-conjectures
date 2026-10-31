/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalOperations.RationalOperationsData
import WeilConjectures.SixFunctors.RationalOperations.RationalHomAdjunction
import WeilConjectures.SixFunctors.RationalOperations.RationalHomScalarEvaluation
import WeilConjectures.SixFunctors.Integral.IntegralConstructibleInternalHom
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-! # The full rational Hom adjunction and its scalar evaluation square

Source: lem-coef-rational-operations, steps 2--9, 12 and 20
(blueprint: lem-sf-rational-hom-identifications).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open scoped TensorProduct
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalOperations
open ConstructibleExceptionalCoefficients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]

variable (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

private theorem chosen_spec {T : Sort*} {p : T → Prop} (h : ∃! a, p a)
    (a : T) (ha : a = h.exists.choose) : p a :=
  ha.symm ▸ h.exists.choose_spec

private abbrev rationalHom_spec :=
  chosen_spec (rationalDerivedInternalHom_existsUnique l E X)
    (rationalDerivedInternalHom l E X) rfl

attribute [local irreducible] rationalDerivedInternalHom

include D hl in
private theorem integralHom_permitted
    (K M : sfIntegralConstructibleCategory l E X) :
    constructibleIntegralHomPairs l E X (op K, M) := by
  have legacy (N : sfIntegralConstructibleCategory l E X) :
      boundedConstructibleDerivedCompleteIntegral D l hl E X N.obj := by
    obtain ⟨hc, a, b, hab, h⟩ := N.property
    exact ⟨(sfDerivedComplete_iff_legacy l E X D hl N.obj).mp hc,
      a, b, hab, h⟩
  have h := (integral_constructible_internalHom D l hl E X K.obj M.obj
    (legacy K) (legacy M)).1
  exact ⟨(sfDerivedComplete_iff_legacy l E X D hl _).mpr h.1, h.2⟩

include D hl in
private theorem hom_permitted
    (K M : sfRationalConstructibleCategory l E X) :
    constructibleRationalHomPairs l E X (op K, M) :=
  integralHom_permitted D l hl X E K.obj M.obj

private theorem homDual_obj
    (h : ∀ K M : sfRationalConstructibleCategory l E X,
      constructibleRationalHomPairs l E X (op K, M))
    (w : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (A : RationalVerdier.Datum D l hl X E w)
    (K : sfRationalConstructibleCategory l E X) :
    (homDual l E X h ((sfRationalConstructibleLocalization l E X).obj w.omega)).obj
        (op K) = A.dual.obj (op K) := by
  rw [A.objects K]
  exact (rationalHom_spec l X E).1 _

private theorem homDual_additive
    (h : ∀ K M : sfRationalConstructibleCategory l E X,
      constructibleRationalHomPairs l E X (op K, M))
    (ω : sfRationalConstructibleCategory l E X) :
    (homDual l E X h ω).Additive := by
  constructor
  intro K M f g
  obtain ⟨b, hb, _⟩ := (rationalHom_spec l X E).2
    ⟨(K, ω), h K.unop ω⟩ ⟨(M, ω), h M.unop ω⟩
  have hf : (homDual l E X h ω).map f = b f.unop (𝟙 ω) := hb f.unop (𝟙 ω)
  have hg : (homDual l E X h ω).map g = b g.unop (𝟙 ω) := hb g.unop (𝟙 ω)
  rw [hf, hg]
  apply Eq.trans (show (homDual l E X h ω).map (f + g) =
    b (f + g).unop (𝟙 ω) from hb _ _)
  change b (f.unop + g.unop) (𝟙 ω) = _
  rw [map_add, LinearMap.add_apply]
  rfl

private theorem homDual_pure
    (h : ∀ K M : sfRationalConstructibleCategory l E X,
      constructibleRationalHomPairs l E X (op K, M))
    (w : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (A : RationalVerdier.Datum D l hl X E w)
    (K M : sfIntegralConstructibleCategory l E X) (f : K ⟶ M)
    (c : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
    HEq ((homDual l E X h ((sfRationalConstructibleLocalization l E X).obj w.omega)).map
      (Quiver.Hom.op (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
        (sfRationalConstructibleLocalization l E X).obj K ⟶
        (sfRationalConstructibleLocalization l E X).obj M)))
      (c ⊗ₜ[Padic.coefficientExtensionIntegers l E]
        (IntegralVerdier.restrictedDual l E X w.omega.obj A.preserves).map f.op) := by
  let Q := sfRationalConstructibleLocalization l E X
  obtain ⟨b, hb, hp⟩ := (rationalHom_spec l X E).2
    ⟨(op (Q.obj M), Q.obj w.omega), h _ _⟩
    ⟨(op (Q.obj K), Q.obj w.omega), h _ _⟩
  have hf : (homDual l E X h (Q.obj w.omega)).map
      (Quiver.Hom.op (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
        Q.obj K ⟶ Q.obj M)) = b (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] f)
          (𝟙 (Q.obj w.omega)) := hb _ _
  exact (heq_of_eq hf).trans ((hp f (𝟙 w.omega) c 1).trans (by
    simp only [mul_one]
    rfl))

private theorem duality_eq
    (h : ∀ K M : sfRationalConstructibleCategory l E X,
      constructibleRationalHomPairs l E X (op K, M))
    (w : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (A : RationalVerdier.Datum D l hl X E w) :
    A.dual = homDual l E X h ((sfRationalConstructibleLocalization l E X).obj w.omega) := by
  let H := homDual l E X h ((sfRationalConstructibleLocalization l E X).obj w.omega)
  have : A.dual.Additive := A.additive
  have : H.Additive := homDual_additive l X E h _
  have ho (K : (sfRationalConstructibleCategory l E X)ᵒᵖ) :
      A.dual.obj K = H.obj K := (homDual_obj D l hl X E h w A K.unop).symm
  apply Functor.hext ho
  intro K M f
  have hm (g : M.unop ⟶ K.unop) : HEq (A.dual.map g.op) (H.map g.op) := by
    apply (conj_eqToHom_iff_heq _ _ (ho K) (ho M)).mp
    induction g using TensorProduct.induction_on with
    | zero =>
      change A.dual.map (0 : K ⟶ M) = eqToHom (ho K) ≫
        H.map (0 : K ⟶ M) ≫ eqToHom (ho M).symm
      simp only [Functor.map_zero, CategoryTheory.Limits.comp_zero,
        CategoryTheory.Limits.zero_comp]
    | tmul c g =>
      exact (conj_eqToHom_iff_heq _ _ (ho K) (ho M)).mpr
        ((A.pure _ _ g c).trans (homDual_pure D l hl X E h w A _ _ g c).symm)
    | add g g' hg hg' =>
      change A.dual.map (Quiver.Hom.op (g : M.unop ⟶ K.unop) +
          Quiver.Hom.op (g' : M.unop ⟶ K.unop)) =
        eqToHom (ho K) ≫ H.map (Quiver.Hom.op (g : M.unop ⟶ K.unop) +
          Quiver.Hom.op (g' : M.unop ⟶ K.unop)) ≫ eqToHom (ho M).symm
      simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp, hg, hg']
  exact hm f.unop

private theorem tensor_transport_heq {C : Type*} [Category* C]
    (T : C × C ⥤ C) (K : C) {M N P : C} (e : M = N)
    (f : T.obj (K, N) ⟶ P) :
    HEq (T.map (Prod.mkHom (𝟙 K) (eqToHom e)) ≫ f) f := by
  cases e
  change HEq (T.map (𝟙 (K, M)) ≫ f) f
  exact heq_of_eq (by rw [CategoryTheory.Functor.map_id, Category.id_comp])

private theorem homIdentification_nonempty
    (w : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (A : RationalVerdier.Datum D l hl X E w) :
    Nonempty (HomIdentification l E X D hl w A) := by
  let permitted := hom_permitted D l hl X E
  obtain ⟨adj, norm⟩ := rationalHom_adjunction D l hl X E permitted A.ordinary A.completion
  let d := duality_eq D l hl X E permitted w A
  refine ⟨{
    permitted := permitted
    adjunction := adj
    integral_evaluation := norm
    duality := eqToIso d
    evaluation := ?_ }⟩
  intro K
  cases K with
  | mk K =>
    change (RationalVerdier.tensor D l hl X E).map
        (Prod.mkHom (𝟙 ((sfRationalConstructibleLocalization l E X).obj K))
          ((eqToIso d).hom.app (op ((sfRationalConstructibleLocalization l E X).obj K)))) ≫
      (adj ((sfRationalConstructibleLocalization l E X).obj K)).counit.app
        ((sfRationalConstructibleLocalization l E X).obj w.omega) = _
    change (RationalVerdier.tensor D l hl X E).map
        (Prod.mkHom (𝟙 ((sfRationalConstructibleLocalization l E X).obj K))
          ((eqToHom d).app (op ((sfRationalConstructibleLocalization l E X).obj K)))) ≫ _ = _
    rw [eqToHom_app]
    apply eq_of_heq
    exact (tensor_transport_heq _ _ _ _).trans
      ((norm K w.omega).trans (A.evaluation_integral K).symm)

/-- The full rational tensor-Hom adjunction, with its normalized integral evaluation,
identifies Verdier duality with Hom into the dualizing object and respects finite scalars.
Source: lem-coef-rational-operations, DAG proof steps 2--9, 12 and 20
(blueprint: lem-sf-rational-hom-identifications).

Proof: integral internal-Hom constructibility and the intrinsic/legacy completeness
comparison supply every permitted rational Hom pair. Restrict each supplied ordinary
adjunction along the invertible completion map and extend its linear Hom equivalence
to the raw rational category, retaining the normalized counit. These constructions
are carried out in rationalHom_adjunction. With second Hom input omega, the recorded
object equations identify the Hom objects with the supplied Verdier duality objects.
The bilinear Hom action proves additivity, and its pure-map formula agrees with that
of the supplied duality. Tensor induction and functor extensionality give equality
of the functors. The normalized counit at omega agrees with evaluation_integral;
equality transport through tensor therefore gives the required evaluation field.
Apply this construction separately to E and L. The finite-scalar evaluation square
is the strictly separate remaining obligation rationalHom_scalar_evaluation.
Combining it with the two constructed records gives the stated existential witnesses. -/
theorem rationalHom_identifications
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wL : IntegralFiniteExtension.DualizingDatum l X D hl L)
    (A : RationalVerdier.Datum D l hl X E wE)
    (B : RationalVerdier.Datum D l hl X L wL) :
    ∃ (hE : HomIdentification l E X D hl wE A)
      (hL : HomIdentification l L X D hl wL B),
      HomScalarCompatibility l E X D hl L ι wE wL A B hE hL := by
  obtain ⟨hE⟩ := homIdentification_nonempty D l hl X E wE A
  obtain ⟨hL⟩ := homIdentification_nonempty D l hl X L wL B
  exact ⟨hE, hL, rationalHom_scalar_evaluation D l hl X E L ι wE wL A B hE hL⟩

end WeilConjectures.RationalOperations
