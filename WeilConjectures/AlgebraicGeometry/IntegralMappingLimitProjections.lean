/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.Algebra.Homology.RhomGlobalSectionsOfUniverses
public import WeilConjectures.AlgebraicGeometry.PurReductionLimitShiftAdjunction
public import WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniversesSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.AlgebraicGeometry.SfDerivedCompleteLegacyComparison
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Invertible
public import WeilConjectures.AlgebraicGeometry.CoefficientEnrichedGlobalShift

/-! # Integral mapping limits and their actual finite projections

Source: main-20261015, prop-coef-integral-exceptional-adjoint.proof.md, paragraph 2
(blueprint: lem-coef-integral-mapping-limit-projections).

All finite indices n denote exponent n+1. The maps below are composites of the
recorded unit, enriched adjunction and actual total-limit projections. Composition
is expressed before global sections, by the tensor-Hom composition square; applying
derived global sections gives composition of the global mapping complexes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] CoefficientClosedStructure.tensor
  CoefficientClosedStructure.evaluation CoefficientClosedStructure.transpose
  CoefficientClosedStructure.composition coefficientBaseChangeHom
  coefficientEnrichedAdjunctionMap

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Actual mapping-limit projection, followed by the canonical finite identifications.
Source: the same paragraph, first and last mapping comparisons
(blueprint: lem-coef-integral-mapping-limit-projections). -/
def integralMappingLimitProjection (S : CoefficientDerivedSystemCalculus l E W)
    (P Q : DerivedCategory (scalarReductionSource l E W)) (n : ℕ) :=
  (coefficientMappingProjection.{max u (t+1)} n).app
      ((coefficientSequenceGlobalHom l E W).obj
        (op (S.reduction.obj P), S.reduction.obj Q)) ≫
    (S.globalEvaluation _ _ (S.reduction_normalized P) (S.reduction_normalized Q) n).hom ≫
    (coefficientFiniteGlobalHom l E W n).map
      (Prod.mkHom ((S.reductionEvaluation n).inv.app P).op
        ((S.reductionEvaluation n).hom.app Q))

/-- H-zero of the actual lambda and actual projection, using the recorded RHom-Hom maps.
Source: the same paragraph and Stacks 08JA
(blueprint: lem-coef-integral-mapping-limit-projections). -/
def integralMappingLimitHom (S : CoefficientDerivedSystemCalculus l E W)
    (P Q : DerivedCategory (scalarReductionSource l E W)) (n : ℕ) (h : P ⟶ Q) :=
  coefficientFiniteHomEquiv l E W n _ _
    (((DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t+1)} 0).map
      (integralMappingLimitMap l E W S P Q ≫
        integralMappingLimitProjection l E W S P Q n))
      ((coefficientIntegralHomEquiv l E W P Q).symm h))

/-- The internal enriched comparison underlying lambda, before derived global sections.
Source: the same paragraph, enriched adjunction comparison
(blueprint: lem-coef-integral-mapping-limit-projections). -/
def integralMappingLimitInternal (S : CoefficientDerivedSystemCalculus l E W)
    (P Q : DerivedCategory (scalarReductionSource l E W)) :=
  (coefficientIntegralInternalHom l E W).map
      (Prod.mkHom (𝟙 (op P)) (S.adjunction.unit.app Q)) ≫
    coefficientEnrichedAdjunctionMap S.integralClosed S.systemClosed S.reduction
      S.adjunction S.reductionTensor P (S.reduction.obj Q)

/-- The canonical lax tensor comparison of total limit, the mate of tensoring counits.
Source: the same paragraph, compatibility of the enriched adjunction with composition
(blueprint: lem-coef-integral-mapping-limit-projections). -/
def integralMappingLimitTensor (S : CoefficientDerivedSystemCalculus l E W)
    (M N : coefficientSequenceDerived l E W) :=
  (S.adjunction.homEquiv _ _)
    ((S.reductionTensor).hom.app
        ((coefficientSequenceLimit l E W).obj M, (coefficientSequenceLimit l E W).obj N) ≫
      S.systemClosed.tensor.map
        (Prod.mkHom (S.adjunction.counit.app M) (S.adjunction.counit.app N)))

attribute [local irreducible] HasDerivedCategory.standard

private theorem enriched_target
    {A B : Type*} [Category A] [Category B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) {G : B ⥤ A} (adj : F ⊣ G)
    (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (hc : CoefficientEvaluationCompatible SA SB F μ)
    (P : A) (N N' : B) (b : N ⟶ N') :
    HA.map (Prod.mkHom (𝟙 (op P)) (G.map b)) ≫
        coefficientEnrichedAdjunctionMap SA SB F adj μ P N' =
      coefficientEnrichedAdjunctionMap SA SB F adj μ P N ≫
        G.map (HB.map (Prod.mkHom (𝟙 (op (F.obj P))) b)) := by
  unfold coefficientEnrichedAdjunctionMap
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
  apply congrArg (adj.homEquiv _ _)
  have hn := hc.naturality P (G.obj N) P (G.obj N') (𝟙 P) (G.map b)
  simp only [op_id, CategoryTheory.Functor.map_id] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← HB.map_comp]
  congr 2
  ext
  · simp
  · exact adj.counit.naturality b

private theorem enriched_unit
    {A B : Type*} [Category A] [Category B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) {G : B ⥤ A} (adj : F ⊣ G)
    (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (hc : CoefficientEvaluationCompatible SA SB F μ) (P Q : A) :
    HA.map (Prod.mkHom (𝟙 (op P)) (adj.unit.app Q)) ≫
        coefficientEnrichedAdjunctionMap SA SB F adj μ P (F.obj Q) =
      adj.homEquiv _ _ (coefficientBaseChangeHom SA SB F μ P Q) := by
  unfold coefficientEnrichedAdjunctionMap
  erw [← adj.homEquiv_naturality_left]
  apply congrArg (adj.homEquiv _ _)
  have hn := hc.naturality P Q P (G.obj (F.obj Q)) (𝟙 P) (adj.unit.app Q)
  simp only [op_id, CategoryTheory.Functor.map_id] at hn
  rw [← Category.assoc, hn, Category.assoc, ← HB.map_comp]
  have ht : Prod.mkHom (𝟙 (op (F.obj P))) (F.map (adj.unit.app Q)) ≫
      Prod.mkHom (𝟙 (op (F.obj P))) (adj.counit.app (F.obj Q)) =
      𝟙 (op (F.obj P), F.obj Q) := by
    ext <;> simp [adj.left_triangle_components]
  rw [ht, HB.map_id, Category.comp_id]

private theorem lax_pair
    {A B : Type*} [Category A] [Category B]
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (F : A ⥤ B) {G : B ⥤ A} (adj : F ⊣ G)
    (μ : TA ⋙ F ≅ F.prod F ⋙ TB)
    {X Y : A} {M N : B} (f : F.obj X ⟶ M) (g : F.obj Y ⟶ N) :
    TA.map (Prod.mkHom (adj.homEquiv _ _ f) (adj.homEquiv _ _ g)) ≫
        adj.homEquiv _ _ (μ.hom.app (G.obj M, G.obj N) ≫
          TB.map (Prod.mkHom (adj.counit.app M) (adj.counit.app N))) =
      adj.homEquiv _ _ (μ.hom.app (X, Y) ≫ TB.map (Prod.mkHom f g)) := by
  rw [← adj.homEquiv_naturality_left]
  apply congrArg (adj.homEquiv _ _)
  have hn := μ.hom.naturality
    (Prod.mkHom (adj.homEquiv _ _ f) (adj.homEquiv _ _ g))
  change F.map (TA.map _) ≫ μ.hom.app _ = μ.hom.app _ ≫ TB.map _ at hn
  rw [← Category.assoc, hn, Category.assoc, ← TB.map_comp]
  congr 2
  ext
  · change F.map (adj.homEquiv _ _ f) ≫ adj.counit.app M = f
    simpa only [Adjunction.homEquiv_counit] using
      (adj.homEquiv _ _).symm_apply_apply f
  · change F.map (adj.homEquiv _ _ g) ≫ adj.counit.app N = g
    simpa only [Adjunction.homEquiv_counit] using
      (adj.homEquiv _ _).symm_apply_apply g

private theorem mappingHom_eq (S : CoefficientDerivedSystemCalculus l E W)
    (C : CoefficientDerivedSystemCoherence l E W S)
    (P Q : DerivedCategory (scalarReductionSource l E W)) (h : P ⟶ Q) (n : ℕ) :
    integralMappingLimitHom l E W S P Q n h =
      (coefficientFiniteDerivedExtension l E W n).map h := by
  let H₀ := DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t+1)} 0
  have hi := (coefficientHomZeroEquiv_exists.{u, t+1, t}
    (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)).choose_spec.1.1
  have hf := (coefficientHomZeroEquiv_exists.{u, t+1, t}
    (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W n)).choose_spec.1.1
  have hu : H₀.map ((coefficientIntegralGlobalHom l E W).map
      (Prod.mkHom (𝟙 (op P)) (S.adjunction.unit.app Q)))
        ((coefficientIntegralHomEquiv l E W P Q).symm h) =
      (coefficientIntegralHomEquiv l E W P _).symm (h ≫ S.adjunction.unit.app Q) := by
    apply (coefficientIntegralHomEquiv l E W P _).injective
    simpa [coefficientIntegralHomEquiv, coefficientHomZeroEquiv, H₀,
      coefficientIntegralGlobalHom, coefficientIntegralSections] using
      hi P Q P _ (𝟙 P) (S.adjunction.unit.app Q)
        ((coefficientIntegralHomEquiv l E W P Q).symm h)
  unfold integralMappingLimitHom integralMappingLimitMap integralMappingLimitProjection
  simp only [CategoryTheory.Functor.map_comp, AddCommGrpCat.comp_apply]
  rw [hu]
  have hfin := hf _ _ _ _ ((S.reductionEvaluation n).inv.app P)
    ((S.reductionEvaluation n).hom.app Q)
    ((coefficientGammaZeroMap l E W S P (S.reduction.obj Q)
      (S.reduction_normalized Q) n)
      ((coefficientIntegralHomEquiv l E W P _).symm (h ≫ S.adjunction.unit.app Q)))
  have hp := C.hom_projection P (S.reduction.obj Q) (S.reduction_normalized Q)
    (h ≫ S.adjunction.unit.app Q) n
  simp only [coefficientGammaZeroMap, coefficientGammaZero,
    CategoryTheory.Functor.map_comp, AddCommGrpCat.comp_apply] at hp hfin
  change coefficientFiniteHomEquiv l E W n _ _ _ = _ at hfin
  erw [hfin]
  erw [hp]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_app_assoc]
  have hn := (S.reductionEvaluation n).inv.naturality (S.adjunction.unit.app Q)
  change (coefficientFiniteDerivedExtension l E W n).map (S.adjunction.unit.app Q) ≫
    (S.reductionEvaluation n).inv.app _ =
    (S.reductionEvaluation n).inv.app Q ≫
      (coefficientSequenceDerivedEvaluation l E W n).map
        (S.reduction.map (S.adjunction.unit.app Q)) at hn
  rw [reassoc_of% hn]
  have ht := congrArg (coefficientSequenceDerivedEvaluation l E W n).map
    (S.adjunction.left_triangle_components Q)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at ht
  rw [← Category.assoc
    ((coefficientSequenceDerivedEvaluation l E W n).map
      (S.reduction.map (S.adjunction.unit.app Q))), ht]
  simp

variable (X : Scheme.{u})

/-- The clauses of the integral mapping-limit comparison. Naturality and composition
are equations of derived complexes, before taking finite projections. The internal
composition square is the enriched tensor-Hom form of composition, hence also gives
composition after derived global sections. Source: the same paragraph
(blueprint: lem-coef-integral-mapping-limit-projections). -/
structure IntegralMappingLimitAssertions (S : CoefficientDerivedSystemCalculus l E X)
    (C : CoefficientDerivedSystemCoherence l E X S)
    (sh : PurReductionLimitShiftData l E X S) : Prop where
  /-- The specified composite is an isomorphism on the stated constructible category. -/
  isIso : ∀ (P Q : sfIntegralConstructibleCategory l E X),
    IsIso (integralMappingLimitMap l E X S P.obj Q.obj)
  /-- Naturality in both variables, for arbitrary integral morphisms. -/
  naturality : ∀ (P P' Q Q' : sfIntegralConstructibleCategory l E X)
    (a : P' ⟶ P) (b : Q ⟶ Q'),
    (coefficientIntegralGlobalHom l E X).map (Prod.mkHom a.hom.op b.hom) ≫
        integralMappingLimitMap l E X S P'.obj Q'.obj =
      integralMappingLimitMap l E X S P.obj Q.obj ≫ coefficientMappingLimit.{u+1}.map
        ((coefficientSequenceGlobalHom l E X).map
          (Prod.mkHom (S.reduction.map a.hom).op (S.reduction.map b.hom)))
  /-- The actual projection is reduction in the second variable followed by scalar adjunction. -/
  projection : ∀ (P Q : sfIntegralConstructibleCategory l E X) (n : ℕ),
    integralMappingLimitMap l E X S P.obj Q.obj ≫
        integralMappingLimitProjection l E X S P.obj Q.obj n =
      (coefficientIntegralGlobalHom l E X).map
          (Prod.mkHom (𝟙 (op P.obj)) ((coefficientFiniteAdjunction l E X n).unit.app Q.obj)) ≫
        (coefficientIntegralSections l E X).map
          (coefficientEnrichedAdjunctionMap S.integralClosed (S.finiteClosed n)
            (coefficientFiniteDerivedExtension l E X n) (coefficientFiniteAdjunction l E X n)
            (S.finiteTensor n) P.obj ((coefficientFiniteDerivedExtension l E X n).obj Q.obj)) ≫
        (C.scalarSections n).hom.app ((coefficientFiniteInternalHom l E X n).obj
          (op ((coefficientFiniteDerivedExtension l E X n).obj P.obj),
            (coefficientFiniteDerivedExtension l E X n).obj Q.obj))
  /-- The actual H-zero projection sends a morphism to its reduction. -/
  hom : ∀ (P Q : sfIntegralConstructibleCategory l E X) (h : P ⟶ Q) (n : ℕ),
    integralMappingLimitHom l E X S P.obj Q.obj n h.hom =
      (coefficientFiniteDerivedExtension l E X n).map h.hom
  /-- The evaluated triangle identity is precisely e_n (u_Q)_n h_n = h_n. -/
  triangle : ∀ (P Q : sfIntegralConstructibleCategory l E X) (h : P ⟶ Q) (n : ℕ),
    (coefficientFiniteDerivedExtension l E X n).map h.hom ≫
        (S.reductionEvaluation n).inv.app Q.obj ≫
        (coefficientSequenceDerivedEvaluation l E X n).map
          (S.reduction.map (S.adjunction.unit.app Q.obj)) ≫
        (coefficientSequenceDerivedEvaluation l E X n).map
          (S.adjunction.counit.app (S.reduction.obj Q.obj)) ≫
        (S.reductionEvaluation n).hom.app Q.obj =
      (coefficientFiniteDerivedExtension l E X n).map h.hom
  /-- Every integer shift, including negative shifts, has its actual reduced projection. -/
  shifted_hom : ∀ (P Q : sfIntegralConstructibleCategory l E X) (r : ℤ)
    (h : P.obj ⟶ Q.obj⟦r⟧) (n : ℕ),
    integralMappingLimitHom l E X S P.obj (Q.obj⟦r⟧) n h ≫
        ((sh.finite_reduction_shift n).commShiftIso r).hom.app Q.obj =
      (coefficientFiniteDerivedExtension l E X n).map h ≫
        ((sh.finite_reduction_shift n).commShiftIso r).hom.app Q.obj
  /-- Compatibility with the normalized shifts of the entire mapping complexes. -/
  shift : ∀ (P Q : sfIntegralConstructibleCategory l E X) (r : ℤ),
    integralMappingLimitMap l E X S P.obj (Q.obj⟦r⟧) ≫
        integralMappingLimitTargetShift l E X S sh P.obj Q.obj r =
      integralMappingLimitSourceShift l E X P.obj Q.obj r ≫
        (integralMappingLimitMap l E X S P.obj Q.obj)⟦r⟧'
  /-- Enriched composition square, before global sections or finite projections. -/
  composition : ∀ (P Q T : sfIntegralConstructibleCategory l E X),
    S.integralClosed.tensor.map
        (Prod.mkHom (integralMappingLimitInternal l E X S Q.obj T.obj)
          (integralMappingLimitInternal l E X S P.obj Q.obj)) ≫
        integralMappingLimitTensor l E X S
          ((coefficientSequenceInternalHom l E X).obj
            (op (S.reduction.obj Q.obj), S.reduction.obj T.obj))
          ((coefficientSequenceInternalHom l E X).obj
            (op (S.reduction.obj P.obj), S.reduction.obj Q.obj)) ≫
        (coefficientSequenceLimit l E X).map
          (S.systemClosed.composition (S.reduction.obj P.obj)
            (S.reduction.obj Q.obj) (S.reduction.obj T.obj)) =
      S.integralClosed.composition P.obj Q.obj T.obj ≫
        integralMappingLimitInternal l E X S P.obj T.obj

/-- Integral mapping-limit comparison with its actual projections, shifts and composition.
Source: main-20261015, prop-coef-integral-exceptional-adjoint.proof.md, paragraph 2
(blueprint: lem-coef-integral-mapping-limit-projections).

Proof:
1. Q is Roos-complete by def-weil-derived-complete-integral-detailed. Since l differs
   from the characteristic of k, it is invertible on X. Apply
   lem-pur-normalized-actual-reconstruction-maps: the actual unit u_Q is invertible
   and RQ is normalized. This uses that unit, not uniqueness of a lift of projections.
2. Apply gamma of lem-coef-derived-system-evaluation-calculus to P and RQ. Functorial
   RHom sends u_Q and its inverse to inverses, giving exactly the defined lambda.
   Naturality of u and gamma gives the displayed naturality square. For composition,
   use u_T g = LR(g) u_Q and the calculus's evaluation and transpose compatibility.
   Uncurrying gives the displayed tensor-Hom composition square; apply derived global
   sections and the calculus's global-limit comparison for mapping-complex composition.
3. The calculus's gamma projection formula is limit projection followed by scalar
   adjunction. Composing with RHom(P,u_Q), use unit_projection to obtain the actual
   scalar reduction unit of Q. Its H-zero formula is evaluated counit after reduced
   unit after reduced h. Evaluate the adjunction triangle at n to cancel those maps.
   The canonical reductionEvaluation isomorphisms give the displayed formulas.
4. Shift the augmented Roos triangle to see that Q[r] is complete. Exact reduction
   identifies its reduction with Q_n[r]. Hom-complex target reindexing commutes with
   all the simultaneous adjunction and projection maps, proving the shift square.
   Apply step 3 to Q[r], and use lem-pur-rhom-global-sections to obtain the shifted
   Hom formula for every integer r. At no point tensor an integral internal Hom with
   a quotient, or infer equality of maps to a derived limit from their projections.
-/
theorem integralMappingLimitProjections
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    [X.Over (Spec (CommRingCat.of D.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    (S : CoefficientDerivedSystemCalculus l E X)
    (C : CoefficientDerivedSystemCoherence l E X S)
    (sh : PurReductionLimitShiftData l E X S) :
    IntegralMappingLimitAssertions l E X S C sh := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P Q
    have : Fact D.p.Prime := ⟨D.prime⟩
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
    have hunit : IsUnit (l : D.k₀) :=
      (CharP.cast_ne_zero_of_ne_of_prime D.k₀ (Fact.out : l.Prime) _hl.symm).isUnit
    have hX : IsUnit (l : Γ(X, ⊤)) := by
      simpa only [map_natCast] using hunit.map
        ((Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv ≫
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))).appTop ≫
          (X ↘ Spec (CommRingCat.of D.k)).appTop).hom
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
    let : Fact p.Prime := ⟨hprime⟩
    let D₀ : FiniteFieldDatum.{0} :=
      { p := p, a := 1, q := p, prime := hprime, exponent_pos := le_refl 1,
        cardinality_eq := (pow_one p).symm, k₀ := ZMod p,
        card_base := by simp [Nat.card_eq_fintype_card], k := AlgebraicClosure (ZMod p) }
    have hl₀ : l ≠ D₀.p := by change l ≠ p; omega
    have hc : IntegralOnSlice.IsComplete l E X none Q.obj :=
      ⟨D₀, hl₀, (sfDerivedComplete_iff_legacy l E X D₀ hl₀ Q.obj).mp Q.property.1⟩
    have hu : IsIso (S.adjunction.unit.app Q.obj) :=
      (purNormalizedReconstruction l E X hX S).2 Q.obj hc
    have : IsIso (Prod.mkHom (𝟙 (op P.obj)) (S.adjunction.unit.app Q.obj)) :=
      (inferInstance : IsIso ((Iso.refl (op P.obj)).prod
        (asIso (S.adjunction.unit.app Q.obj))).hom)
    unfold integralMappingLimitMap
    infer_instance
  · intro P P' Q Q' a b
    unfold integralMappingLimitMap
    rw [← Category.assoc, ← Functor.map_comp]
    have hu := S.adjunction.unit.naturality b.hom
    have hf : Prod.mkHom a.hom.op b.hom ≫
        Prod.mkHom (𝟙 (op P'.obj)) (S.adjunction.unit.app Q'.obj) =
      Prod.mkHom (𝟙 (op P.obj)) (S.adjunction.unit.app Q.obj) ≫
        Prod.mkHom a.hom.op ((coefficientSequenceLimit l E X).map
          (S.reduction.map b.hom)) := by
      ext
      · simp
      · simp
    rw [hf, Functor.map_comp, Category.assoc]
    rw [C.gamma_naturality _ _ _ _ (S.reduction_normalized Q.obj)
      (S.reduction_normalized Q'.obj)]
    simp only [Category.assoc]
  · intro P Q n
    unfold integralMappingLimitMap integralMappingLimitProjection
    simp only [Category.assoc]
    rw [reassoc_of% C.gamma_projection P.obj _ (S.reduction_normalized Q.obj) n]
    simp only [← CategoryTheory.Functor.map_comp]
    have hprod : Prod.mkHom ((S.reductionEvaluation n).hom.app P.obj).op
        (𝟙 ((coefficientSequenceDerivedEvaluation l E X n).obj (S.reduction.obj Q.obj))) ≫
      Prod.mkHom ((S.reductionEvaluation n).inv.app P.obj).op
        ((S.reductionEvaluation n).hom.app Q.obj) =
      Prod.mkHom (𝟙 (op ((coefficientFiniteDerivedExtension l E X n).obj P.obj)))
        ((S.reductionEvaluation n).hom.app Q.obj) := by
      ext <;> simp
    rw [hprod]
    have hn := (C.scalarSections n).hom.naturality
      ((coefficientFiniteInternalHom l E X n).map
        (Prod.mkHom (𝟙 (op ((coefficientFiniteDerivedExtension l E X n).obj P.obj)))
          ((S.reductionEvaluation n).hom.app Q.obj)))
    change (coefficientIntegralSections l E X).map
        ((coefficientFiniteDerivedRestriction l E X n).map _) ≫ _ = _ at hn
    erw [← hn]
    rw [← (coefficientIntegralSections l E X).map_comp_assoc]
    have he := enriched_target S.integralClosed (S.finiteClosed n)
      (coefficientFiniteDerivedExtension l E X n) (coefficientFiniteAdjunction l E X n)
      (S.finiteTensor n) (S.finite_compatible n) P.obj _ _
      ((S.reductionEvaluation n).hom.app Q.obj)
    erw [← he]
    rw [CategoryTheory.Functor.map_comp]
    simp only [Category.assoc]
    change (coefficientIntegralGlobalHom l E X).map _ ≫
      (coefficientIntegralGlobalHom l E X).map _ ≫
      (coefficientIntegralGlobalHom l E X).map _ ≫ _ = _
    rw [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc]
    have hu : S.adjunction.unit.app Q.obj ≫
        (coefficientSequenceProjection l E X n).app (S.reduction.obj Q.obj) ≫
        (coefficientFiniteDerivedRestriction l E X n).map
          ((S.reductionEvaluation n).hom.app Q.obj) =
      (coefficientFiniteAdjunction l E X n).unit.app Q.obj := by
      rw [← Category.assoc, S.unit_projection, Category.assoc,
        ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
        CategoryTheory.Functor.map_id]
      exact Category.comp_id _
    congr 2
    ext <;> simp [hu]
  · intro P Q h n
    exact mappingHom_eq l E X S C P.obj Q.obj h.hom n
  · intro P Q h n
    have ht := congrArg (coefficientSequenceDerivedEvaluation l E X n).map
      (S.adjunction.left_triangle_components Q.obj)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at ht
    rw [← Category.assoc
      ((coefficientSequenceDerivedEvaluation l E X n).map
        (S.reduction.map (S.adjunction.unit.app Q.obj))), ht]
    simp
  · intro P Q r h n
    rw [mappingHom_eq l E X S C P.obj (Q.obj⟦r⟧) h n]
  · intro P Q r
    exact coefficientEnrichedGlobalShift l E X S C sh P.obj Q.obj r
  · intro P Q T
    unfold integralMappingLimitInternal integralMappingLimitTensor
    rw [enriched_unit S.integralClosed S.systemClosed S.reduction S.adjunction
      S.reductionTensor S.reduction_compatible,
      enriched_unit S.integralClosed S.systemClosed S.reduction S.adjunction
        S.reductionTensor S.reduction_compatible,
      enriched_unit S.integralClosed S.systemClosed S.reduction S.adjunction
        S.reductionTensor S.reduction_compatible]
    rw [← Category.assoc, lax_pair]
    erw [← S.adjunction.homEquiv_naturality_right]
    simp only [Category.assoc]
    rw [← S.reduction_compatible.composition]
    exact S.adjunction.homEquiv_naturality_left _ _

end WeilConjectures
