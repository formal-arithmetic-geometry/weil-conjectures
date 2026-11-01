/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import all WeilConjectures.SmoothPurity.OperationsScalarLocalization.DerivedScalarLocalizationBilinearComparison
import all WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierEvaluationDetection

/-! # Rational evaluation and signed transposition

Source: blueprint thm-coef-rational-verdier, evaluation and transposition paragraphs.
(blueprint: lem-coef-rational-verdier-pairing-calculus). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped TensorProduct

namespace WeilConjectures.RationalVerdier

attribute [local irreducible] rationalDerivedTensor
  integralCompletedTensor integralCompletedTensorComparison
  integralOperationsTensorComplexFunctor IntegralHom.totalTensor IntegralHom.homModelMap
  IntegralHom.projection IntegralHom.evaluate
attribute [local implicit_reducible] constructibleIntegralTensor
  IntegralVerdier.restrictedDual IntegralVerdier.dual

private theorem conjugate_natural {C : Type*} [Category* C]
    {A B D E A' B' D' E' : C}
    (a : A ≅ A') (b : B ≅ B') (d : D ≅ D') (e : E ≅ E')
    (f : A ⟶ B) (g : D ⟶ E) (f' : A' ⟶ B') (g' : D' ⟶ E')
    (s : A ⟶ D) (t : B ⟶ E)
    (hf : f ≫ b.hom = a.hom ≫ f')
    (hg : g ≫ e.hom = d.hom ≫ g') (hs : f ≫ t = s ≫ g) :
    f' ≫ b.inv ≫ t ≫ e.hom = a.inv ≫ s ≫ d.hom ≫ g' := by
  apply (cancel_epi a.hom).1
  simp only [← Category.assoc]
  rw [← hf]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc f t, hs]
  simp only [Category.assoc]
  rw [hg]

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

variable (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (w : IntegralFiniteExtension.DualizingDatum l X D hl E)

/-- Completed integral interchange is the ordinary signed swap conjugated by completion.
This is an actual construction, independent of any rational transposition theorem.
Source: blueprint thm-coef-rational-verdier, ordinary-to-completed evaluation comparison.
(blueprint: lem-coef-rational-verdier-pairing-calculus). -/
def completedInterchange (A : Datum D l hl X E w)
    (K M : sfIntegralConstructibleCategory l E X) :
    (integralTensor D l hl X E).obj (K, M) ⟶
      (integralTensor D l hl X E).obj (M, K) :=
  ObjectProperty.homMk
    ((@asIso _ _ _ _ (A.completion.map.app (K.obj, M.obj))
        (A.completion.invertible K M)).inv ≫
      (A.symmetry.swap K.obj M.obj).hom ≫ A.completion.map.app (M.obj, K.obj))

/-- The normalized rational signed interchange, with the two properties of evaluation
used in transposition. The integral formula fixes interchange on every raw rational object.
Source: blueprint thm-coef-rational-verdier, paragraph 1, evaluation and transposition;
IntegralVerdier.delta and the quotient-normalized completion comparison.
(blueprint: lem-coef-rational-verdier-pairing-calculus). -/
structure PairingCalculus (A : Datum D l hl X E w) where
  swap : ∀ K M : sfRationalConstructibleCategory l E X,
    (tensor D l hl X E).obj (K, M) ⟶ (tensor D l hl X E).obj (M, K)
  integral : ∀ K M : sfIntegralConstructibleCategory l E X,
    HEq (swap ((sfRationalConstructibleLocalization l E X).obj K)
      ((sfRationalConstructibleLocalization l E X).obj M))
      ((sfRationalConstructibleLocalization l E X).map
        (completedInterchange D l hl X E w A K M))
  natural : ∀ (K M K' M' : sfRationalConstructibleCategory l E X)
    (f : K ⟶ K') (g : M ⟶ M'),
    (tensor D l hl X E).map (Prod.mkHom f g) ≫ swap K' M' =
      swap K M ≫ (tensor D l hl X E).map (Prod.mkHom g f)
  bidual : ∀ K : sfRationalConstructibleCategory l E X,
    (tensor D l hl X E).map
        (Prod.mkHom (𝟙 (A.dual.obj (op K))) (A.bidual.hom.app K)) ≫
      A.evaluation (A.dual.obj (op K)) = swap (A.dual.obj (op K)) K ≫ A.evaluation K
  detect : ∀ (K V : sfRationalConstructibleCategory l E X)
    (f g : V ⟶ A.dual.obj (op K)),
    (tensor D l hl X E).map (Prod.mkHom (𝟙 K) f) ≫ A.evaluation K =
      (tensor D l hl X E).map (Prod.mkHom (𝟙 K) g) ≫ A.evaluation K → f = g

private abbrev integralDual (A : Datum D l hl X E w) :=
  IntegralVerdier.restrictedDual l E X w.omega.obj A.preserves

private def integralEvaluation (A : Datum D l hl X E w)
    (K : sfIntegralConstructibleCategory l E X) :
    (integralTensor D l hl X E).obj (K, (integralDual D l hl X E w A).obj (op K)) ⟶
      w.omega :=
  ObjectProperty.homMk
    ((@asIso _ _ _ _ (A.completion.map.app
      (K.obj, ((integralDual D l hl X E w A).obj (op K)).obj))
      (A.completion.invertible K ((integralDual D l hl X E w A).obj (op K)))).inv ≫
      (A.ordinary.adjunction K.obj).counit.app w.omega.obj)

private def integralDelta (A : Datum D l hl X E w)
    (K : sfIntegralConstructibleCategory l E X) :
    K ⟶ (integralDual D l hl X E w A).obj
      (op ((integralDual D l hl X E w A).obj (op K))) :=
  ObjectProperty.homMk (IntegralVerdier.delta X A.ordinary A.symmetry w.omega.obj K.obj)

private theorem inverse_square {C : Type*} [Category* C] {U V U' V' : C}
    (a : U ≅ U') (b : V ≅ V') (f : U ⟶ V) (g : U' ⟶ V')
    (h : f ≫ b.hom = a.hom ≫ g) : g ≫ b.inv = a.inv ≫ f := by
  apply (cancel_epi a.hom).1
  calc
    a.hom ≫ g ≫ b.inv = (f ≫ b.hom) ≫ b.inv := by rw [h, Category.assoc]
    _ = f := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = a.hom ≫ a.inv ≫ f := by rw [Iso.hom_inv_id_assoc]

private theorem integral_delta_evaluation (A : Datum D l hl X E w)
    (K : sfIntegralConstructibleCategory l E X) :
    (integralTensor D l hl X E).map
        (Prod.mkHom (𝟙 ((integralDual D l hl X E w A).obj (op K)))
          (integralDelta D l hl X E w A K)) ≫
      integralEvaluation D l hl X E w A ((integralDual D l hl X E w A).obj (op K)) =
    completedInterchange D l hl X E w A ((integralDual D l hl X E w A).obj (op K)) K ≫
      integralEvaluation D l hl X E w A K := by
  let DK := (integralDual D l hl X E w A).obj (op K)
  let DDK := (integralDual D l hl X E w A).obj (op DK)
  let d := IntegralVerdier.delta X A.ordinary A.symmetry w.omega.obj K.obj
  let c (P Q : sfIntegralConstructibleCategory l E X) :=
    @asIso _ _ _ _ (A.completion.map.app (P.obj, Q.obj)) (A.completion.invertible P Q)
  have hn := inverse_square (c DK K) (c DK DDK) _ _
    (A.completion.map.naturality (Prod.mkHom (𝟙 DK.obj) d))
  have hd := ((A.ordinary.adjunction DK.obj).homEquiv K.obj w.omega.obj).symm_apply_apply
    ((A.symmetry.swap DK.obj K.obj).hom ≫
      (A.ordinary.adjunction K.obj).counit.app w.omega.obj)
  rw [Adjunction.homEquiv_counit] at hd
  change A.ordinary.tensor.map (Prod.mkHom (𝟙 DK.obj) d) ≫
    (A.ordinary.adjunction DK.obj).counit.app w.omega.obj = _ at hd
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  dsimp only [integralEvaluation, completedInterchange,
    ObjectProperty.homMk_hom]
  simp only [Category.assoc]
  change (integralCompletedTensor l E X).map (Prod.mkHom (𝟙 DK.obj) d) ≫
      (c DK DDK).inv ≫ (A.ordinary.adjunction DK.obj).counit.app w.omega.obj =
    (c DK K).inv ≫ (A.symmetry.swap DK.obj K.obj).hom ≫
      (c K DK).hom ≫ (c K DK).inv ≫ (A.ordinary.adjunction K.obj).counit.app w.omega.obj
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, hn, Category.assoc, hd]

omit [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))] in
private theorem rationalTensor_integral
    (K K' M M' : sfIntegralConstructibleCategory l E X) (f : K ⟶ K') (g : M ⟶ M') :
    HEq ((tensor D l hl X E).map (Prod.mkHom
      ((sfRationalConstructibleLocalization l E X).map f)
      ((sfRationalConstructibleLocalization l E X).map g)))
      ((sfRationalConstructibleLocalization l E X).map
        ((integralTensor D l hl X E).map (Prod.mkHom f g))) := by
  let : ∀ x : X, Invertible (l : X.residueField x) := units D l hl X
  obtain ⟨b, hb, hgen⟩ := (rationalTensor_spec l E X).2
    ((sfRationalConstructibleLocalization l E X).obj K)
    ((sfRationalConstructibleLocalization l E X).obj K')
    ((sfRationalConstructibleLocalization l E X).obj M)
    ((sfRationalConstructibleLocalization l E X).obj M')
  have hm : (tensor D l hl X E).map (Prod.mkHom
      ((sfRationalConstructibleLocalization l E X).map f)
      ((sfRationalConstructibleLocalization l E X).map g)) = _ := hb _ _
  have h := hgen f g 1 1
  simp only [one_mul] at h
  exact (heq_of_eq hm).trans h

private theorem id_heq {C : Type*} [Category* C] {K M : C} (h : K = M) :
    HEq (𝟙 K) (𝟙 M) := by cases h; rfl

private theorem rational_delta_evaluation (A : Datum D l hl X E w)
    (swap : ∀ K M : sfRationalConstructibleCategory l E X,
      (tensor D l hl X E).obj (K, M) ⟶ (tensor D l hl X E).obj (M, K))
    (hswap : ∀ K M : sfIntegralConstructibleCategory l E X,
      HEq (swap ((sfRationalConstructibleLocalization l E X).obj K)
        ((sfRationalConstructibleLocalization l E X).obj M))
        ((sfRationalConstructibleLocalization l E X).map
          (completedInterchange D l hl X E w A K M)))
    (K : sfRationalConstructibleCategory l E X) :
    (tensor D l hl X E).map
        (Prod.mkHom (𝟙 (A.dual.obj (op K))) (A.bidual.hom.app K)) ≫
      A.evaluation (A.dual.obj (op K)) = swap (A.dual.obj (op K)) K ≫ A.evaluation K := by
  let J := sfRationalConstructibleLocalization l E X
  let T := integralTensor D l hl X E
  let RT := tensor D l hl X E
  let k := K.obj
  let dk := (integralDual D l hl X E w A).obj (op k)
  let ddk := (integralDual D l hl X E w A).obj (op dk)
  have hD : A.dual.obj (op K) = J.obj dk := A.objects K
  have hDD : A.dual.obj (op (A.dual.obj (op K))) = J.obj ddk := by
    rw [hD]
    exact A.objects (J.obj dk)
  have hobj (P Q : sfRationalConstructibleCategory l E X) :
      RT.obj (P, Q) = J.obj (T.obj (P.obj, Q.obj)) :=
    (@rationalTensor_spec l _ E _ _ _ X
      (units D l hl X)).1 (P, Q)
  have hdom : RT.obj (A.dual.obj (op K), K) = J.obj (T.obj (dk, k)) := by
    rw [hD, hobj]
    rfl
  have hmid : RT.obj (A.dual.obj (op K), A.dual.obj (op (A.dual.obj (op K)))) =
      J.obj (T.obj (dk, ddk)) := by
    rw [hDD, hD, hobj]
    rfl
  have hevD : HEq (A.evaluation (A.dual.obj (op K)))
      (J.map (integralEvaluation D l hl X E w A dk)) :=
    (congr_arg_heq A.evaluation hD).trans (A.evaluation_integral dk)
  have hev : HEq (A.evaluation K) (J.map (integralEvaluation D l hl X E w A k)) :=
    A.evaluation_integral k
  have hs : HEq (swap (A.dual.obj (op K)) K)
      (J.map (completedInterchange D l hl X E w A dk k)) := by
    rw [hD]
    exact hswap dk k
  have hp := OperationsScalarLocalization.prod_hom_heq hD hD (rfl : K = J.obj k) hDD
    (id_heq hD) (A.bidual_integral k)
  have hm := OperationsScalarLocalization.map_heq RT
    (congrArg (fun P ↦ (P, K)) hD)
    (congrArg₂ Prod.mk hD hDD) hp
  have hmap : HEq (RT.map
      (Prod.mkHom (𝟙 (A.dual.obj (op K))) (A.bidual.hom.app K)))
      (J.map (T.map (Prod.mkHom (𝟙 dk) (integralDelta D l hl X E w A k)))) := by
    have h := rationalTensor_integral D l hl X E dk dk k ddk
      (𝟙 dk) (integralDelta D l hl X E w A k)
    exact hm.trans h
  have hleft := heq_comp hdom hmid rfl hmap hevD
  have hevmid : RT.obj (K, A.dual.obj (op K)) = J.obj (T.obj (k, dk)) := by
    rw [hD, hobj]
    rfl
  have hright := heq_comp hdom hevmid rfl hs hev
  have hi := congrArg J.map (integral_delta_evaluation D l hl X E w A k)
  simp only [Functor.map_comp] at hi
  exact eq_of_heq (hleft.trans ((heq_of_eq hi).trans hright.symm))

/-- The normalized localized counit detects maps, and the localized integral delta
untransposes to the normalized signed evaluation. Naturality of the swap is not asserted
here; it follows separately from ambient naturality and bilinear localization.
Source: blueprint thm-coef-rational-verdier, paragraph 1, evaluation and transposition;
Stacks 08J9. (blueprint: lem-coef-rational-verdier-pairing-calculus).

Proof: use A.objects to identify the rational dual with the localized restricted
integral dual, and A.evaluation_integral to identify evaluation with the localized
ordinary counit after inverse completion. The ordinary adjunction's inverse Hom
bijection is O_E-linear: the tensor arrow action and composition are O_E-linear.
Restrict it to the full constructible subcategory and base change its linear equivalence
to the localized coefficient ring. The rational tensor pure-tensor formula identifies
this base-changed inverse with evaluation, after conjugating endpoints by the prescribed
object equations and the invertible completion map. It is therefore injective.
For the bidual equation, use A.bidual_integral and A.evaluation_integral, cancel
completion with its inverse, and apply the inverse-adjunction identity to the transpose
defining IntegralVerdier.delta. This gives ordinary evaluation after the signed swap;
the hypothesis on swap is precisely its completion conjugate and localization.
All rational objects have integral representatives, so no essential-surjectivity choice
or restriction on a representative is required. -/
theorem normalized_evaluation_transpose (A : Datum D l hl X E w)
    (swap : ∀ K M : sfRationalConstructibleCategory l E X,
      (tensor D l hl X E).obj (K, M) ⟶ (tensor D l hl X E).obj (M, K))
    (hswap : ∀ K M : sfIntegralConstructibleCategory l E X,
    HEq (swap ((sfRationalConstructibleLocalization l E X).obj K)
      ((sfRationalConstructibleLocalization l E X).obj M))
      ((sfRationalConstructibleLocalization l E X).map
        (completedInterchange D l hl X E w A K M))) :
    (∀ K : sfRationalConstructibleCategory l E X,
    (tensor D l hl X E).map
        (Prod.mkHom (𝟙 (A.dual.obj (op K))) (A.bidual.hom.app K)) ≫
      A.evaluation (A.dual.obj (op K)) = swap (A.dual.obj (op K)) K ≫ A.evaluation K) ∧
    (∀ (K V : sfRationalConstructibleCategory l E X)
    (f g : V ⟶ A.dual.obj (op K)),
    (tensor D l hl X E).map (Prod.mkHom (𝟙 K) f) ≫ A.evaluation K =
      (tensor D l hl X E).map (Prod.mkHom (𝟙 K) g) ≫ A.evaluation K → f = g) := by
  exact ⟨rational_delta_evaluation D l hl X E w A swap hswap,
    rational_evaluation_detect D l hl X E w A⟩

/-- Evaluation retains its universal property after rationalization, and the specified
bidual map untransposes to signed evaluation.
Source: blueprint thm-coef-rational-verdier, first paragraph, evaluation and second
transposition; Stacks 08J9. (blueprint: lem-coef-rational-verdier-pairing-calculus).

Proof: conjugate the ordinary signed swap by the invertible completion maps on
constructible integral pairs, and localize. The rational tensor object equation transports
its endpoints. Naturality of completion and the assumed ambient swap equation give
naturality on integral arrows. Bilinearity of rational tensor and scalar-localized
composition extend it to pure tensors and then sums. For biduality, substitute the
integral normalization equations of A.objects, A.evaluation and A.bidual. Cancel the
completion maps and use the counit identity for the transpose defining IntegralVerdier.delta.
For detection, the ordinary tensor-Hom adjunction is an O_E-linear Hom equivalence.
Restrict it to the full constructible subcategory, tensor this linear equivalence with
the localized coefficient ring, and conjugate by the invertible completion comparison.
The pure-tensor equations identify its inverse with rational evaluation. Hence that
inverse is injective. Every raw rational object is an integral representative, so these
arguments cover all objects, including zero objects and the empty scheme. -/
theorem pairing_calculus (A : Datum D l hl X E w)
    (hA : ∀ (K M K' M' : IntegralHom.Derived.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l E X))
      (f : K ⟶ K') (g : M ⟶ M'),
      A.ordinary.tensor.map (Prod.mkHom f g) ≫ (A.symmetry.swap K' M').hom =
        (A.symmetry.swap K M).hom ≫ A.ordinary.tensor.map (Prod.mkHom g f)) :
    Nonempty (PairingCalculus D l hl X E w A) := by
  let : ∀ x : X, Invertible (l : X.residueField x) := units D l hl X
  let I := sfIntegralConstructibleCategory l E X
  let t := Padic.coefficientExtensionUniformizer l E
  let T := integralTensor D l hl X E
  let RT := tensor D l hl X E
  let e (KM : I × I) : T.obj KM ≅ T.obj (KM.2, KM.1) :=
    (sfIntegralConstructible l E X).isoMk
      ((@asIso _ _ _ _ (A.completion.map.app (KM.1.obj, KM.2.obj))
        (A.completion.invertible KM.1 KM.2)).symm ≪≫
      A.symmetry.swap KM.1.obj KM.2.obj ≪≫
      @asIso _ _ _ _ (A.completion.map.app (KM.2.obj, KM.1.obj))
        (A.completion.invertible KM.2 KM.1))
  have he (KM PQ : I × I) (f : KM ⟶ PQ) :
      T.map f ≫ (e PQ).hom = (e KM).hom ≫ T.map (Prod.mkHom f.2 f.1) := by
    apply ObjectProperty.hom_ext
    simpa only [T, integralTensor, constructibleIntegralTensor, ObjectProperty.lift,
      Functor.comp_map, Functor.prod_map, ObjectProperty.ι_map, e,
      ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.isoMk,
      ObjectProperty.homMk_hom, Iso.trans, Iso.symm, asIso_hom, Category.assoc]
      using conjugate_natural
      (@asIso _ _ _ _ (A.completion.map.app (KM.1.obj, KM.2.obj))
        (A.completion.invertible KM.1 KM.2))
      (@asIso _ _ _ _ (A.completion.map.app (PQ.1.obj, PQ.2.obj))
        (A.completion.invertible PQ.1 PQ.2))
      (@asIso _ _ _ _ (A.completion.map.app (KM.2.obj, KM.1.obj))
        (A.completion.invertible KM.2 KM.1))
      (@asIso _ _ _ _ (A.completion.map.app (PQ.2.obj, PQ.1.obj))
        (A.completion.invertible PQ.2 PQ.1))
      _ _ _ _ _ _
      (A.completion.map.naturality (Prod.mkHom f.1.hom f.2.hom))
      (A.completion.map.naturality (Prod.mkHom f.2.hom f.1.hom))
      (hA _ _ _ _ f.1.hom f.2.hom)
  let ei : T ≅ CategoryTheory.Prod.swap I I ⋙ T :=
    NatIso.ofComponents e (fun {K M} f ↦ he K M f)
  have hRT := rationalTensor_spec l E X
  change (∀ MN, RT.obj MN = ⟨T.obj (MN.1.obj, MN.2.obj)⟩) ∧ _ at hRT
  have mRT (K K' M M' : sfRationalConstructibleCategory l E X) := hRT.2 K K' M M'
  let F : sfRationalConstructibleCategory l E X × sfRationalConstructibleCategory l E X ⥤
      sfRationalConstructibleCategory l E X :=
    CategoryTheory.Prod.swap _ _ ⋙ RT
  obtain ⟨alpha, halpha, _⟩ :=
    OperationsScalarLocalization.rawBilinearIso_existsUnique t t id T
      (CategoryTheory.Prod.swap I I ⋙ T)
      ei RT F hRT.1 (fun KM ↦ hRT.1 (KM.2, KM.1)) (by
        intro K K' M M'
        obtain ⟨b, hb, hgen⟩ := mRT K K' M M'
        exact ⟨LinearMap.toAddMonoidHom'.comp b.toAddMonoidHom, hb, hgen⟩) (by
        intro K K' M M'
        obtain ⟨b, hb, hgen⟩ := mRT M M' K K'
        refine ⟨?_, ?_, ?_⟩
        · exact
            { toFun := fun f ↦ (b.flip f).toAddMonoidHom
              map_zero' := by
                ext g
                change b g 0 = 0
                exact map_zero (b g)
              map_add' := by
                intro f g
                ext a
                change b a (f + g) = b a f + b a g
                exact map_add (b a) f g }
        · intro f g
          exact hb g f
        · intro f g x y
          change HEq (b (y ⊗ₜ g) (x ⊗ₜ f))
            ((x * y) ⊗ₜ T.map (Prod.mkHom g f))
          simpa only [mul_comm] using hgen g f y x)
  let swap K M := alpha.hom.app (K, M)
  have hswap : ∀ K M : sfIntegralConstructibleCategory l E X,
      HEq (swap ((sfRationalConstructibleLocalization l E X).obj K)
        ((sfRationalConstructibleLocalization l E X).obj M))
        ((sfRationalConstructibleLocalization l E X).map
          (completedInterchange D l hl X E w A K M)) := by
    intro K M
    exact halpha (⟨K⟩, ⟨M⟩)
  obtain ⟨hdelta, hdetect⟩ := normalized_evaluation_transpose D l hl X E w A swap hswap
  refine ⟨⟨swap, hswap, ?_, hdelta, hdetect⟩⟩
  intro K M K' M' f g
  exact alpha.hom.naturality (Prod.mkHom f g)

end WeilConjectures.RationalVerdier
