/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalOperations.RationalOperationsData
import WeilConjectures.SmoothPurity.Integral.IntegralDerivedHomBilinear
import WeilConjectures.CategoryTheory.ScalarLocalization.PbcRationalTransport
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Rationalization of the normalized completed tensor-Hom adjunction

Source: the restriction and scalar-localization argument of
lem-sf-rational-hom-identifications, steps 6--7
(blueprint: lem-sf-rational-hom-adjunction).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe r u v
open scoped TensorProduct
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
private noncomputable def adjHomLinearEquiv
    (R : Type r) [CommRing R] {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear R C] {F G : C ⥤ C}
    (adj : F ⊣ G) [G.Additive] [G.Linear R] (X Y : C) :
    (F.obj X ⟶ Y) ≃ₗ[R] (X ⟶ G.obj Y) where
  toEquiv := adj.homEquiv X Y
  map_add' f g := by simp [Adjunction.homEquiv_unit]
  map_smul' a f := by simp [Adjunction.homEquiv_unit]

private noncomputable def rawAdjunction
    (R : Type r) [CommRing R] {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R) {F G : C ⥤ C}
    (adj : F ⊣ G) [F.Additive] [F.Linear R] [G.Additive] [G.Linear R] :
    ScalarLocalization.transport R p F ⊣ ScalarLocalization.transport R p G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y ↦
        ((adjHomLinearEquiv R adj X.obj Y.obj).baseChange R (Localization.Away p)).toEquiv
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        change ((adjHomLinearEquiv R adj X'.obj Y.obj).baseChange R
            (Localization.Away p)).symm (ScalarLocalization.composition R C p _ _ _ g f) =
          ScalarLocalization.composition R C p _ _ _
            (((adjHomLinearEquiv R adj X.obj Y.obj).baseChange R
              (Localization.Away p)).symm g)
            ((ScalarLocalization.transportHom R p F _ _) f)
        induction g using TensorProduct.induction_on with
        | zero => simp
        | tmul b g =>
          induction f using TensorProduct.induction_on with
          | zero => simp
          | tmul a f =>
            simp [ScalarLocalization.composition_tmul, ScalarLocalization.transportHom,
              adjHomLinearEquiv, adj.homEquiv_naturality_left_symm]
          | add f f' hf hf' => simp [map_add, hf, hf']
        | add g g' hg hg' => simp [map_add, hg, hg']
      homEquiv_naturality_right := by
        intro X Y Y' f g
        change ((adjHomLinearEquiv R adj X.obj Y'.obj).baseChange R (Localization.Away p))
            (ScalarLocalization.composition R C p _ _ _ g f) =
          ScalarLocalization.composition R C p _ _ _
            ((ScalarLocalization.transportHom R p G _ _) g)
            (((adjHomLinearEquiv R adj X.obj Y.obj).baseChange R
              (Localization.Away p)) f)
        induction g using TensorProduct.induction_on with
        | zero => simp
        | tmul b g =>
          induction f using TensorProduct.induction_on with
          | zero => simp
          | tmul a f =>
            simp [ScalarLocalization.composition_tmul, ScalarLocalization.transportHom,
              adjHomLinearEquiv, adj.homEquiv_naturality_right]
          | add f f' hf hf' => simp [map_add, hf, hf']
        | add g g' hg hg' => simp [map_add, hg, hg'] }

private theorem rawAdjunction_counit
    (R : Type r) [CommRing R] {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R) {F G : C ⥤ C}
    (adj : F ⊣ G) [F.Additive] [F.Linear R] [G.Additive] [G.Linear R] (Y : C) :
    (rawAdjunction R p adj).counit.app (ScalarLocalization.mk Y) =
      (1 : Localization.Away p) ⊗ₜ[R] adj.counit.app Y := by
  change ((adjHomLinearEquiv R adj (G.obj Y) Y).baseChange R
    (Localization.Away p)).symm (1 ⊗ₜ[R] 𝟙 (G.obj Y)) = _
  rw [LinearEquiv.baseChange_symm_tmul]
  change 1 ⊗ₜ[R] (adj.homEquiv _ _).symm (𝟙 _) = _
  rw [adj.homEquiv_symm_id]

private theorem scalarAdjunction_exists
    (R : Type r) [CommRing R] {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R) {F G : C ⥤ C}
    (adj : F ⊣ G) [F.Additive] [F.Linear R] [G.Additive] [G.Linear R]
    (F' G' : ScalarLocalization R C p ⥤ ScalarLocalization R C p)
    (hF : F' = ScalarLocalization.transport R p F)
    (hG : G' = ScalarLocalization.transport R p G) :
    ∃ a : F' ⊣ G', ∀ Y : C,
      HEq (a.counit.app (ScalarLocalization.mk Y))
        ((1 : Localization.Away p) ⊗ₜ[R] adj.counit.app Y) := by
  subst F'
  subst G'
  exact ⟨rawAdjunction R p adj, fun Y ↦ heq_of_eq (rawAdjunction_counit R p adj Y)⟩

namespace WeilConjectures.RationalOperations
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
private noncomputable def intLeft (K : sfIntegralConstructibleCategory l E X) :
    sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E X :=
  (((Functor.const _).obj K).prod' (𝟭 _)) ⋙
    @constructibleIntegralTensor l _ E _ _ _ X (RationalVerdier.units D l hl X)
private noncomputable def intRight
    (h : ∀ K M : sfRationalConstructibleCategory l E X,
      constructibleRationalHomPairs l E X (op K, M))
    (K : sfIntegralConstructibleCategory l E X) :
    sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E X :=
  (constructibleIntegralHomPairs l E X).lift
    (((Functor.const _).obj (op K)).prod' (𝟭 _))
      (fun M ↦ h ((sfRationalConstructibleLocalization l E X).obj K)
        ((sfRationalConstructibleLocalization l E X).obj M)) ⋙ constructibleIntegralHom l E X
private noncomputable def intCompletion
    (ordinary : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (completion : RationalVerdier.Completion D l hl X E ordinary)
    (K : sfIntegralConstructibleCategory l E X) :
    (sfIntegralConstructible l E X).ι ⋙ (Functor.curry.obj ordinary.tensor).obj K.obj ≅
      intLeft D l hl X E K ⋙ (sfIntegralConstructible l E X).ι :=
  NatIso.ofComponents (fun M ↦ @asIso _ _ _ _
    (completion.map.app (K.obj, M.obj)) (completion.invertible K M))
    (fun {_M _N} f ↦ completion.map.naturality (Prod.mkHom (𝟙 K.obj) f.hom))
private noncomputable def intAdjunction
    (h : ∀ K M : sfRationalConstructibleCategory l E X,
      constructibleRationalHomPairs l E X (op K, M))
    (ordinary : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (completion : RationalVerdier.Completion D l hl X E ordinary)
    (K : sfIntegralConstructibleCategory l E X) :
    intLeft D l hl X E K ⊣ intRight l X E h K :=
  (ordinary.adjunction K.obj).restrictFullyFaithful
    (sfIntegralConstructible l E X).fullyFaithfulι
    (sfIntegralConstructible l E X).fullyFaithfulι
    (intCompletion D l hl X E ordinary completion K) (Iso.refl _)
private theorem intRight_additive
    (h : ∀ K M : sfRationalConstructibleCategory l E X,
      constructibleRationalHomPairs l E X (op K, M))
    (K : sfIntegralConstructibleCategory l E X) :
    (intRight l X E h K).Additive := by
  constructor
  intro M N f g
  obtain ⟨b, hb⟩ := integralDerivedHom_bilinear l E X K.obj K.obj M.obj N.obj
  apply ObjectProperty.hom_ext
  change (integralDerivedInternalHom l E X).map
      (Prod.mkHom (Quiver.Hom.op (𝟙 K.obj)) (f.hom + g.hom)) =
    (integralDerivedInternalHom l E X).map (Prod.mkHom (Quiver.Hom.op (𝟙 K.obj)) f.hom) +
      (integralDerivedInternalHom l E X).map (Prod.mkHom (Quiver.Hom.op (𝟙 K.obj)) g.hom)
  simpa only [hb] using (b (𝟙 K.obj)).map_add f.hom g.hom
private theorem intRight_linear
    (h : ∀ K M : sfRationalConstructibleCategory l E X,
      constructibleRationalHomPairs l E X (op K, M))
    (K : sfIntegralConstructibleCategory l E X) :
    (intRight l X E h K).Linear (Padic.coefficientExtensionIntegers l E) := by
  constructor
  intro M N f c
  obtain ⟨b, hb⟩ := integralDerivedHom_bilinear l E X K.obj K.obj M.obj N.obj
  apply ObjectProperty.hom_ext
  change (integralDerivedInternalHom l E X).map
      (Prod.mkHom (Quiver.Hom.op (𝟙 K.obj)) (c • f.hom)) =
    c • (integralDerivedInternalHom l E X).map
      (Prod.mkHom (Quiver.Hom.op (𝟙 K.obj)) f.hom)
  simpa only [hb] using (b (𝟙 K.obj)).map_smul c f.hom

private theorem chosen_spec {T : Sort*} {p : T → Prop} (h : ∃! a, p a)
    (a : T) (ha : a = h.exists.choose) : p a := ha.symm ▸ h.exists.choose_spec
private abbrev rationalHom_spec :=
  chosen_spec (rationalDerivedInternalHom_existsUnique l E X)
    (rationalDerivedInternalHom l E X) rfl
private abbrev rationalTensor_spec :=
  chosen_spec (@rationalDerivedTensor_existsUnique l _ E _ _ _ X
    (RationalVerdier.units D l hl X))
    (@rationalDerivedTensor l _ E _ _ _ X (RationalVerdier.units D l hl X)) rfl
attribute [local irreducible] rationalDerivedInternalHom rationalDerivedTensor

private theorem linear_from_maps
    {S : Type*} [Semiring S] {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [Linear S C] [Linear S D]
    (F : C ⥤ D)
    (h : ∀ X Y : C, ∃ b : (X ⟶ Y) →ₗ[S] (F.obj X ⟶ F.obj Y),
      ∀ f, F.map f = b f) : F.Additive ∧ F.Linear S := by
  constructor
  · constructor
    intro X Y f g
    obtain ⟨b, hb⟩ := h X Y
    rw [hb, hb, hb, map_add]
  · constructor
    intro X Y f c
    obtain ⟨b, hb⟩ := h X Y
    rw [hb, hb, map_smul]

private theorem homRight_linear
    (h : ∀ K M : sfRationalConstructibleCategory l E X,
      constructibleRationalHomPairs l E X (op K, M))
    (K : sfRationalConstructibleCategory l E X) :
    (homRight l E X h K).Additive ∧
      (homRight l E X h K).Linear
        (Localization.Away (Padic.coefficientExtensionUniformizer l E)) := by
  apply linear_from_maps
  intro M N
  obtain ⟨b, hb, _⟩ := (rationalHom_spec l X E).2
    ⟨(op K, M), h K M⟩ ⟨(op K, N), h K N⟩
  exact ⟨b (𝟙 K), fun f ↦ hb _ _⟩

omit [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] in
private theorem tensorLeft_linear
    (K : sfRationalConstructibleCategory l E X) :
    (@tensorLeft l _ E _ _ _ X (RationalVerdier.units D l hl X) K).Additive ∧
      (@tensorLeft l _ E _ _ _ X (RationalVerdier.units D l hl X) K).Linear
        (Localization.Away (Padic.coefficientExtensionUniformizer l E)) := by
  apply linear_from_maps
  intro M N
  obtain ⟨b, hb, _⟩ := (rationalTensor_spec D l hl X E).2 K K M N
  exact ⟨b (𝟙 K), fun f ↦ hb _ _⟩

private theorem homRight_transport
    (h : ∀ K M : sfRationalConstructibleCategory l E X,
      constructibleRationalHomPairs l E X (op K, M))
    (K : sfIntegralConstructibleCategory l E X) :
    let := intRight_additive l X E h K
    let := intRight_linear l X E h K
    homRight l E X h ((sfRationalConstructibleLocalization l E X).obj K) =
      ScalarLocalization.transport (Padic.coefficientExtensionIntegers l E)
        (Padic.coefficientExtensionUniformizer l E) (intRight l X E h K) := by
  let := intRight_additive l X E h K
  let := intRight_linear l X E h K
  let Q := sfRationalConstructibleLocalization l E X
  have := (homRight_linear l X E h (Q.obj K)).1
  have := (homRight_linear l X E h (Q.obj K)).2
  apply ScalarLocalization.transport_unique
  · intro M
    exact (rationalHom_spec l X E).1 _
  · intro M N f
    obtain ⟨b, hb, hp⟩ := (rationalHom_spec l X E).2
      ⟨(op (Q.obj K), Q.obj M), h _ _⟩ ⟨(op (Q.obj K), Q.obj N), h _ _⟩
    have hf : (homRight l E X h (Q.obj K)).map
        (1 ⊗ₜ[Padic.coefficientExtensionIntegers l E] f : Q.obj M ⟶ Q.obj N) =
        b (𝟙 (Q.obj K)) (1 ⊗ₜ[Padic.coefficientExtensionIntegers l E] f) := hb _ _
    exact (heq_of_eq hf).trans ((hp (𝟙 K) f 1 1).trans (by simp only [one_mul]; rfl))

omit [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] in
private theorem tensorLeft_transport
    (K : sfIntegralConstructibleCategory l E X)
    [(intLeft D l hl X E K).Additive]
    [(intLeft D l hl X E K).Linear (Padic.coefficientExtensionIntegers l E)] :
    @tensorLeft l _ E _ _ _ X (RationalVerdier.units D l hl X)
        ((sfRationalConstructibleLocalization l E X).obj K) =
      ScalarLocalization.transport (Padic.coefficientExtensionIntegers l E)
        (Padic.coefficientExtensionUniformizer l E) (intLeft D l hl X E K) := by
  let Q := sfRationalConstructibleLocalization l E X
  have := (tensorLeft_linear D l hl X E (Q.obj K)).1
  have := (tensorLeft_linear D l hl X E (Q.obj K)).2
  apply ScalarLocalization.transport_unique
  · intro M
    exact (rationalTensor_spec D l hl X E).1 _
  · intro M N f
    obtain ⟨b, hb, hp⟩ := (rationalTensor_spec D l hl X E).2 (Q.obj K) (Q.obj K)
      (Q.obj M) (Q.obj N)
    have hf : (@tensorLeft l _ E _ _ _ X (RationalVerdier.units D l hl X) (Q.obj K)).map
        (1 ⊗ₜ[Padic.coefficientExtensionIntegers l E] f : Q.obj M ⟶ Q.obj N) =
        b (𝟙 (Q.obj K)) (1 ⊗ₜ[Padic.coefficientExtensionIntegers l E] f) := hb _ _
    exact (heq_of_eq hf).trans ((hp (𝟙 K) f 1 1).trans (by simp only [one_mul]; rfl))

omit [LocallyOfFiniteType (X ↘ Spec (.of D.k))] in
private theorem intAdjunction_counit
    (h : ∀ K M : sfRationalConstructibleCategory l E X,
      constructibleRationalHomPairs l E X (op K, M))
    (ordinary : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (completion : RationalVerdier.Completion D l hl X E ordinary)
    (K M : sfIntegralConstructibleCategory l E X) :
    (intAdjunction D l hl X E h ordinary completion K).counit.app M =
      ObjectProperty.homMk
        ((@asIso _ _ _ _ (completion.map.app
          (K.obj, ((intRight l X E h K).obj M).obj))
          (completion.invertible K ((intRight l X E h K).obj M))).inv ≫
          (ordinary.adjunction K.obj).counit.app M.obj) := by
  apply ObjectProperty.hom_ext
  change (sfIntegralConstructible l E X).ι.map
    ((intAdjunction D l hl X E h ordinary completion K).counit.app M) = _
  dsimp only [intAdjunction]
  rw [Adjunction.map_restrictFullyFaithful_counit_app]
  change (@asIso _ _ _ _ (completion.map.app
      (K.obj, ((intRight l X E h K).obj M).obj))
      (completion.invertible K ((intRight l X E h K).obj M))).inv ≫
      ((Functor.curry.obj ordinary.tensor).obj K.obj).map (𝟙 _) ≫
        (ordinary.adjunction K.obj).counit.app M.obj = _
  rw [CategoryTheory.Functor.map_id]
  exact congrArg (fun f ↦ (@asIso _ _ _ _ (completion.map.app
      (K.obj, ((intRight l X E h K).obj M).obj))
      (completion.invertible K ((intRight l X E h K).obj M))).inv ≫ f)
    (Category.id_comp ((ordinary.adjunction K.obj).counit.app M.obj))

omit [LocallyOfFiniteType (X ↘ Spec (.of D.k))] in
/-- The ordinary tensor-Hom adjunction and a normalized invertible completion map
induce a rational adjunction, with exactly the prescribed integral counit.
Source: lem-sf-rational-hom-identifications, steps 6--7; Stacks Tags 08J9 and 07K0
(blueprint: lem-sf-rational-hom-adjunction).

Proof: use fullness to restrict ordinary tensor-Hom currying to integral constructible
objects. Transport its left side along the given completion isomorphism. The resulting
counit is the inverse completion map followed by ordinary evaluation. Both sides of the
Hom bijection are linear over the valuation ring: currying commutes with constant
scalars, as is checked on local homogeneous tensors; the completion map does too by its
quotient-map normalization on K-flat representatives. Extend this linear isomorphism
and its inverse by tensoring with the localized coefficient ring. The two resulting
maps remain inverse. The object and pure-map specifications of rational tensor and
internal Hom identify them with these extended operations. Naturality on pure tensors
is integral naturality multiplied by the product of their scalar coefficients;
additivity extends it to all maps. The natural Hom bijection constructs the adjunction.
Its counit is the inverse Hom bijection applied to the identity, hence the integral
counit tensored with one, giving the displayed normalization. This argument includes
zero objects, zero categories, torsion objects and the identity coefficient field. -/
theorem rationalHom_adjunction
    (permitted : ∀ K M : sfRationalConstructibleCategory l E X,
      constructibleRationalHomPairs l E X (op K, M))
    (ordinary : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (completion : RationalVerdier.Completion D l hl X E ordinary) :
    ∃ adj : ∀ K : sfRationalConstructibleCategory l E X,
      @tensorLeft l _ E _ _ _ X (RationalVerdier.units D l hl X) K ⊣
        homRight l E X permitted K,
    ∀ (K M : sfIntegralConstructibleCategory l E X),
    HEq ((adj ((sfRationalConstructibleLocalization l E X).obj K)).counit.app
      ((sfRationalConstructibleLocalization l E X).obj M))
      ((sfRationalConstructibleLocalization l E X).map
        (ObjectProperty.homMk
          (X := (@constructibleIntegralTensor l _ E _ _ _ X
            (RationalVerdier.units D l hl X)).obj
              (K, (constructibleIntegralHom l E X).obj
                (integralPairOfRationalHomPair l E X
                  ⟨(op ((sfRationalConstructibleLocalization l E X).obj K),
                    (sfRationalConstructibleLocalization l E X).obj M), permitted _ _⟩)))
          (Y := M)
          ((@asIso _ _ _ _ (completion.map.app
            (K.obj, ((integralDerivedInternalHom l E X).obj (op K.obj, M.obj))))
            (completion.invertible K
              ((constructibleIntegralHom l E X).obj
                (integralPairOfRationalHomPair l E X
                  ⟨(op ((sfRationalConstructibleLocalization l E X).obj K),
                    (sfRationalConstructibleLocalization l E X).obj M), permitted _ _⟩)))).inv ≫
            (ordinary.adjunction K.obj).counit.app M.obj))) := by
  classical
  let a K := intAdjunction D l hl X E permitted ordinary completion K
  let (K : sfIntegralConstructibleCategory l E X) : (intRight l X E permitted K).Additive :=
    intRight_additive l X E permitted K
  let (K : sfIntegralConstructibleCategory l E X) :
      (intRight l X E permitted K).Linear (Padic.coefficientExtensionIntegers l E) :=
    intRight_linear l X E permitted K
  let (K : sfIntegralConstructibleCategory l E X) : (intLeft D l hl X E K).Additive :=
    (a K).left_adjoint_additive
  let (K : sfIntegralConstructibleCategory l E X) :
      (intLeft D l hl X E K).Linear (Padic.coefficientExtensionIntegers l E) :=
    (a K).left_adjoint_linear
  have h (K : sfIntegralConstructibleCategory l E X) :=
    scalarAdjunction_exists (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionUniformizer l E) (a K)
      (@tensorLeft l _ E _ _ _ X (RationalVerdier.units D l hl X)
        ((sfRationalConstructibleLocalization l E X).obj K))
      (homRight l E X permitted ((sfRationalConstructibleLocalization l E X).obj K))
      (tensorLeft_transport D l hl X E K) (homRight_transport l X E permitted K)
  choose adj norm using h
  refine ⟨fun K ↦ adj K.obj, ?_⟩
  intro K M
  refine (norm K M).trans ?_
  change HEq ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l E))
    ⊗ₜ[Padic.coefficientExtensionIntegers l E]
      (intAdjunction D l hl X E permitted ordinary completion K).counit.app M) _
  rw [intAdjunction_counit]
  rfl

end WeilConjectures.RationalOperations
