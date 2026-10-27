/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.FdCoefficientComparisonSystem
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.GeometricFibreComparisonHypotheses
import Sheaf.CategoryTheory.FixedPairEquivalenceTransport
import Sheaf.CategoryTheory.FixedPairMixedSquareLift

/-! # Frobenius fixed-pair comparison for a supplied comparison system

Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace,
`def-fd-trace-function.md`, final sentence, geometric-fibre and fixed-pair auxiliary
(blueprint: lem-fd-frobenius-fixed-pair-comparison).

The finite/common-stage transports and scalar/inclusion comparisons below use the
specified comparisons of the supplied system, with their recorded reverse orientation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u w u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.Endofunctor

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (S : FdCoefficientComparisonSystem.{u} l Ω)
  (T : Scheme.{u}) [IsNoetherian T]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  (g : T ≅ T)

/-- A square of fixed-pair transports commutes by the specified coefficient comparison.
The component equality ensures that this is the supplied comparison, not an arbitrary
isomorphism of functors.
Source: trace-definition final sentence, auxiliary proof steps 8--10
(blueprint: lem-fd-frobenius-fixed-pair-comparison). -/
def FdFixedPairSquare
    {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
    [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
    {F₁ : C₁ ⥤ C₁} {F₂ : C₂ ⥤ C₂} {F₃ : C₃ ⥤ C₃} {F₄ : C₄ ⥤ C₄}
    {L₁₂ : C₁ ⥤ C₂} {L₂₄ : C₂ ⥤ C₄} {L₁₃ : C₁ ⥤ C₃} {L₃₄ : C₃ ⥤ C₄}
    (e₁₂ : L₁₂ ⋙ F₂ ≅ F₁ ⋙ L₁₂) (e₂₄ : L₂₄ ⋙ F₄ ≅ F₂ ⋙ L₂₄)
    (e₁₃ : L₁₃ ⋙ F₃ ≅ F₁ ⋙ L₁₃) (e₃₄ : L₃₄ ⋙ F₄ ≅ F₃ ⋙ L₃₄)
    (a : L₁₂ ⋙ L₂₄ ≅ L₁₃ ⋙ L₃₄) : Prop :=
  ∃ j : IsoAlgebra.mapOfNatIso e₁₂ ⋙ IsoAlgebra.mapOfNatIso e₂₄ ≅
      IsoAlgebra.mapOfNatIso e₁₃ ⋙ IsoAlgebra.mapOfNatIso e₃₄,
    ∀ K, (j.hom.app K).hom.f = a.hom.app K.carrier

private theorem comp_eq {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    {F F' : C ⥤ D} {G G' : D ⥤ E} (hF : F = F') (hG : G = G') :
    F ⋙ G = F' ⋙ G' := by
  cases hF
  cases hG
  rfl

@[irreducible] private def transportIso {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    {F G F' G' : C ⥤ D} (hF : F = F') (hG : G = G') (e : F' ≅ G') : F ≅ G :=
  eqToIso hF ≪≫ e ≪≫ (eqToIso hG).symm

private theorem transportIso_heq {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    {F G F' G' : C ⥤ D} (hF : F = F') (hG : G = G') (e : F' ≅ G') :
    HEq (transportIso hF hG e) e := by
  subst F'
  subst G'
  simp [transportIso]

private theorem iso_app_heq {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    {F G F' G' : C ⥤ D} {e : F ≅ G} {e' : F' ≅ G'}
    (hF : F = F') (hG : G = G') (h : HEq e e') (X : C) :
    HEq (e.hom.app X) (e'.hom.app X) := by
  subst F'
  subst G'
  cases h
  rfl

@[irreducible] private def transportSquareIso
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {A A' : C ⥤ D} {B B' : C ⥤ C} {P : D ⥤ D}
    (hA : A = A') (hB : B = B') (e : A' ⋙ P ≅ B' ⋙ A') : A ⋙ P ≅ B ⋙ A :=
  transportIso (comp_eq hA rfl) (comp_eq hB hA) e

private theorem transportSquareIso_heq
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {A A' : C ⥤ D} {B B' : C ⥤ C} {P : D ⥤ D}
    (hA : A = A') (hB : B = B') (e : A' ⋙ P ≅ B' ⋙ A') :
    HEq (transportSquareIso hA hB e) e := by
  unfold transportSquareIso
  exact transportIso_heq (comp_eq hA rfl) (comp_eq hB hA) e

private theorem transportSquareIso_app_heq
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {A A' : C ⥤ D} {B B' : C ⥤ C} {P : D ⥤ D}
    (hA : A = A') (hB : B = B') (e : A' ⋙ P ≅ B' ⋙ A') (K : C) :
    HEq ((transportSquareIso hA hB e).hom.app K) (e.hom.app K) :=
  iso_app_heq (comp_eq hA rfl) (comp_eq hB hA) (transportSquareIso_heq hA hB e) K

@[irreducible] private def transportSourceIso
    {C C' : Type u₁} {D : Type u₂}
    [cc : Category.{v₁} C] [cc' : Category.{v₁} C'] [Category.{v₂} D]
    {A : C ⥤ D} {A' : C' ⥤ D} {B : C ⥤ C} {B' : C' ⥤ C'} {P : D ⥤ D}
    (ht : C = C') (hc : HEq cc cc') (hA : HEq A A') (hB : HEq B B')
    (e : A' ⋙ P ≅ B' ⋙ A') : A ⋙ P ≅ B ⋙ A := by
  subst C'
  cases eq_of_heq hc
  cases eq_of_heq hA
  cases eq_of_heq hB
  exact e

private theorem transportSourceIso_heq
    {C C' : Type u₁} {D : Type u₂}
    [cc : Category.{v₁} C] [cc' : Category.{v₁} C'] [Category.{v₂} D]
    {A : C ⥤ D} {A' : C' ⥤ D} {B : C ⥤ C} {B' : C' ⥤ C'} {P : D ⥤ D}
    (ht : C = C') (hc : HEq cc cc') (hA : HEq A A') (hB : HEq B B')
    (e : A' ⋙ P ≅ B' ⋙ A') :
    HEq (transportSourceIso ht hc hA hB e) e ∧
      HEq (transportSourceIso ht hc hA hB e).hom e.hom := by
  subst C'
  cases eq_of_heq hc
  cases eq_of_heq hA
  cases eq_of_heq hB
  unfold transportSourceIso
  exact ⟨HEq.rfl, HEq.rfl⟩

private theorem transportSourceIso_map_app_heq
    {C C' : Type u₁} {D : Type u₂} {E : Type u₃}
    [cc : Category.{v₁} C] [cc' : Category.{v₁} C']
    [Category.{v₂} D] [Category.{v₃} E]
    {A : C ⥤ D} {A' : C' ⥤ D} {B : C ⥤ C} {B' : C' ⥤ C'} {P : D ⥤ D}
    (ht : C = C') (hc : HEq cc cc') (hA : HEq A A') (hB : HEq B B')
    (e : A' ⋙ P ≅ B' ⋙ A') (K : C) (K' : C') (hK : HEq K K') (L : D ⥤ E) :
    HEq (L.map ((transportSourceIso ht hc hA hB e).hom.app K))
      (L.map (e.hom.app K')) := by
  subst C'
  cases eq_of_heq hc
  cases eq_of_heq hA
  cases eq_of_heq hB
  cases eq_of_heq hK
  unfold transportSourceIso
  exact HEq.rfl

private theorem cast_heq {α β : Sort u₁} (h : α = β) (x : α) : HEq x (cast h x) := by
  subst β
  rfl

private theorem rawCategoryHEq
    (l : ℕ) [Fact l.Prime] {A B : Type u}
    [fa : Field A] [fb : Field B]
    [aa : Algebra ℚ_[l] A] [ab : Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (T : Scheme.{u}) (h : A = B) (hf : HEq fa fb) (ha : HEq aa ab) :
    HEq (inferInstance : Category (sfRationalConstructibleCategory l A T))
      (inferInstance : Category (sfRationalConstructibleCategory l B T)) := by
  subst B
  cases eq_of_heq hf
  cases eq_of_heq ha
  rfl

private theorem finiteStageTypeEq (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] (T : Scheme.{u})
    (E : Padic.FiniteCoefficientFields l Ω) :
    GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E =
      sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω E) T := by
  rfl

private theorem finiteStageCategoryHEq (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] (T : Scheme.{u})
    (E : Padic.FiniteCoefficientFields l Ω) :
    HEq (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω T E)
      (inferInstance : Category
        (sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)) := by
  exact rawCategoryHEq l T (by rfl) (by unfold pbcFiniteFieldField; rfl)
    (by unfold pbcFiniteFieldAlgebra; rfl)

private theorem pairTransportIsEquivalence
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {F : C ⥤ C} {G : D ⥤ D} (J : C ≌ D) (b : J.functor ⋙ G ≅ F ⋙ J.functor) :
    (IsoAlgebra.mapOfNatIso b).IsEquivalence :=
  (IsoAlgebra.fixedPair_equivalence_transport F G J b.symm).1

private theorem pairEquivalence {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] {F F' : C ⥤ C} {G : D ⥤ D}
    (hF : F = F') (L : IsoAlgebra F' ⥤ IsoAlgebra G) [L.IsEquivalence] :
    ∃ J : IsoAlgebra F ≌ IsoAlgebra G, HEq J.functor L := by
  subst F'
  exact ⟨L.asEquivalence, HEq.rfl⟩

private theorem reverseSquare
    {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
    [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
    {F₁ : C₁ ⥤ C₁} {F₂ : C₂ ⥤ C₂} {F₃ : C₃ ⥤ C₃} {F₄ : C₄ ⥤ C₄}
    {L₁₂ : C₁ ⥤ C₂} {L₂₄ : C₂ ⥤ C₄} {L₁₃ : C₁ ⥤ C₃} {L₃₄ : C₃ ⥤ C₄}
    (e₁₂ : L₁₂ ⋙ F₂ ≅ F₁ ⋙ L₁₂) (e₂₄ : L₂₄ ⋙ F₄ ≅ F₂ ⋙ L₂₄)
    (e₁₃ : L₁₃ ⋙ F₃ ≅ F₁ ⋙ L₁₃) (e₃₄ : L₃₄ ⋙ F₄ ≅ F₃ ⋙ L₃₄)
    (a : L₁₂ ⋙ L₂₄ ≅ L₁₃ ⋙ L₃₄)
    (h : ∀ K, L₃₄.map (e₁₃.hom.app K) ≫ a.inv.app (F₁.obj K) ≫
        L₂₄.map (e₁₂.inv.app K) =
      e₃₄.inv.app (L₁₃.obj K) ≫ F₄.map (a.inv.app K) ≫ e₂₄.hom.app (L₁₂.obj K)) :
    FdFixedPairSquare e₁₂ e₂₄ e₁₃ e₃₄ a := by
  have hm (K : C₁) :
      a.hom.app (F₁.obj K) ≫ L₃₄.map (e₁₃.inv.app K) ≫
          e₃₄.inv.app (L₁₃.obj K) =
        L₂₄.map (e₁₂.inv.app K) ≫ e₂₄.inv.app (L₁₂.obj K) ≫
          F₄.map (a.hom.app K) := by
    have hh := congrArg (fun f ↦ a.hom.app (F₁.obj K) ≫
      L₃₄.map (e₁₃.inv.app K) ≫ f ≫ e₂₄.inv.app (L₁₂.obj K) ≫
        F₄.map (a.hom.app K)) (h K)
    simpa [Category.assoc, ← Functor.map_comp, ← Functor.map_comp_assoc] using hh.symm
  obtain ⟨j, hj, _, _⟩ :=
    (IsoAlgebra.fixedPair_mixedSquare_lift.{u₁, v₁, u₂, v₂, u₃, v₃, u₄, v₄, 0, 0, 0, 0}
      F₁ F₂ F₃ F₄ L₁₃ L₂₄ L₁₂ L₃₄
      e₁₃.symm e₂₄.symm e₁₂.symm e₃₄.symm a hm).1
  exact ⟨j, hj⟩

set_option allowUnsafeReducibility true in
attribute [local reducible] StageSystem.Morphism.functor
  StageSystem.ι GeneralAlgebraicallyClosedCoefficients.stageCategory

private theorem stageSquares
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u₁} {D : I → Type u₂}
    [∀ i, Category.{v₁} (C i)] [∀ i, Category.{v₂} (D i)]
    {U : StageSystem C} {V : StageSystem D}
    (A : U.Morphism V) (B : U.Morphism U) (P : V.Morphism V)
    (m : StageSystem.Morphism.Hom (A.comp P) (B.comp A))
    (b : ∀ i, A.Φ i ⋙ P.Φ i ≅ B.Φ i ⋙ A.Φ i)
    (c : A.functor ⋙ P.functor ≅ B.functor ⋙ A.functor)
    (hb : ∀ i, (b i).hom = m.τ i)
    (hc : ∀ i (K : C i), c.hom.app ⟨i, K⟩ = (V.ι i).map ((b i).hom.app K)) :
    (∀ (i j : I) (e : i ≤ j),
      FdFixedPairSquare (B.β e).symm (b j) (b i) (P.β e).symm (A.β e).symm) ∧
    (∀ i, FdFixedPairSquare (B.ιCompFunctorIso i) c (b i)
      (P.ιCompFunctorIso i) (A.ιCompFunctorIso i)) := by
  constructor
  · intro i j e
    apply reverseSquare
    intro K
    have h := m.comm e K
    simp only [StageSystem.Morphism.comp_β_hom_app] at h
    simp only [Iso.symm_inv, hb i, hb j]
    exact h.trans (Category.assoc _ _ _)
  · intro i
    apply reverseSquare
    intro K
    change (V.ι i).map ((b i).hom.app K) ≫ 𝟙 _ ≫
        A.functor.map (𝟙 ((U.ι i).obj ((B.Φ i).obj K))) =
      𝟙 _ ≫ P.functor.map (𝟙 ((V.ι i).obj ((A.Φ i).obj K))) ≫
        c.hom.app ((U.ι i).obj K)
    rw [A.functor.map_id, P.functor.map_id]
    simp only [Category.id_comp]
    exact (Category.comp_id ((V.ι i).map ((b i).hom.app K))).trans (hc i K).symm

/-- All fixed-pair clauses of the supplied system. The existential comparisons are
uniquely fixed by HEq to the actual finite and common comparisons in S; this merely
transports their dependent types to the supplied stage-family endpoints. It introduces
no arbitrary coefficient map. The source family is identified with the actual pullback
by S.sfFinite and S.sfPair, and the coefficient functors by S.finite_functor and
S.pair_functor.
Source: trace-definition final sentence, auxiliary proof steps 4--10
(blueprint: lem-fd-frobenius-fixed-pair-comparison). -/
def FdFixedPairComparison : Prop :=
  (IsoAlgebra.mapOfNatIso (S.pullback g).pair).IsEquivalence ∧
  (∀ E, (IsoAlgebra.mapOfNatIso ((S.pullback g).finite E).rational).IsEquivalence) ∧
  ∃ (b : ∀ E : Padic.FiniteCoefficientFields l Ω,
      (S.coefficients T).family.Φ E ⋙ (pbcQbarPullFamily l Ω g.hom).Φ E ≅
        (S.pullback g).sfFamily.Φ E ⋙ (S.coefficients T).family.Φ E)
    (c : (S.coefficients T).family.functor ⋙ (pbcQbarPullFamily l Ω g.hom).functor ≅
      (S.pullback g).sfFamily.functor ⋙ (S.coefficients T).family.functor),
    (∀ E, HEq (b E) ((S.pullback g).finite E).rational) ∧
    HEq c (S.pullback g).pair ∧
    (∀ (E L : Padic.FiniteCoefficientFields l Ω) (e : E ≤ L),
      FdFixedPairSquare ((S.pullback g).sfFamily.β e).symm (b L) (b E)
        ((pbcQbarPullFamily l Ω g.hom).β e).symm
        ((S.coefficients T).family.β e).symm) ∧
    (∀ E : Padic.FiniteCoefficientFields l Ω,
      FdFixedPairSquare ((S.pullback g).sfFamily.ιCompFunctorIso E) c (b E)
        ((pbcQbarPullFamily l Ω g.hom).ιCompFunctorIso E)
        ((S.coefficients T).family.ιCompFunctorIso E))

/-- The comparison on the recorded framework Weil categories, together with all
normalized compatibility squares. HEq only identifies different proof presentations
of the same actual pullback; it fixes the full functor, including its Hom map.
Source: trace-definition final sentence, auxiliary proof steps 4--10
(blueprint: lem-fd-frobenius-fixed-pair-comparison). -/
def FdGeometricFixedPairComparison (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] [IsNoetherian (D.geometricFiber X₀).left]
    [Fact (∃ n : ℕ, topologicalKrullDim (D.geometricFiber X₀).left ≤ n)]
    [Fact (∀ x : (D.geometricFiber X₀).left,
      IsUnit (l : (D.geometricFiber X₀).left.presheaf.stalk x))] : Prop :=
  FdFixedPairComparison l Ω S (D.geometricFiber X₀).left (D.geometricFrobenius X₀) ∧
  (∃ J : sfCommonStageWeilComplex D l hl X₀ Ω ≌
      IsoAlgebra (pbcQbarCompletedPull l Ω (D.geometricFrobenius X₀).hom),
    HEq J.functor (IsoAlgebra.mapOfNatIso (S.pullback (D.geometricFrobenius X₀)).pair)) ∧
  (∀ E : Padic.FiniteCoefficientFields l Ω,
    ∃ J : sfWeilComplex D l hl X₀ (pbcFiniteField.{u} l Ω E) ≌
        IsoAlgebra ((pbcQbarPullFamily l Ω (D.geometricFrobenius X₀).hom).Φ E),
      HEq J.functor
        (IsoAlgebra.mapOfNatIso ((S.pullback (D.geometricFrobenius X₀)).finite E).rational))

set_option allowUnsafeReducibility true in
attribute [local irreducible] ScalarLocalization.category ScalarLocalization.preadditive
  ScalarLocalization.linear sfIntegralConstructible sfIntegralConstructibleLinear
  rationalDerivedPullback commonStageDerivedPullback integralDerivedPullback
  sfRationalScalarExtension Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionAbsoluteValue
  HasDerivedCategory.standard integralCoefficientLinear pbcQbarPullFamily

attribute [local implicit_reducible] GeneralAlgebraicallyClosedCoefficients.Stage
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

private theorem fixedPairComparison : FdFixedPairComparison l Ω S T g := by
  let A := (S.coefficients T).family
  let B := (S.pullback g).sfFamily
  let P := pbcQbarPullFamily l Ω g.hom
  let b (E : Padic.FiniteCoefficientFields l Ω) :=
    transportSourceIso (A := A.Φ E) (B := B.Φ E) (P := P.Φ E)
      (finiteStageTypeEq l Ω T E) (finiteStageCategoryHEq l Ω T E)
      ((S.coefficients T).finite_functor E) ((S.pullback g).sfFinite E)
      ((S.pullback g).finite E).rational
  have hb E : HEq (b E) ((S.pullback g).finite E).rational :=
    (transportSourceIso_heq (finiteStageTypeEq l Ω T E)
      (finiteStageCategoryHEq l Ω T E) ((S.coefficients T).finite_functor E)
      ((S.pullback g).sfFinite E) ((S.pullback g).finite E).rational).1
  have hbτ E : (b E).hom = (S.pullback g).mixed.τ E :=
    eq_of_heq ((transportSourceIso_heq (finiteStageTypeEq l Ω T E)
      (finiteStageCategoryHEq l Ω T E) ((S.coefficients T).finite_functor E)
      ((S.pullback g).sfFinite E) ((S.pullback g).finite E).rational).2.trans
        ((S.pullback g).mixed_components E).symm)
  have hAc : A.functor = (S.coefficients T).equivalence.functor :=
    (S.coefficients T).pair_functor.symm
  have hBc : B.functor = commonStageDerivedPullback l Ω g.hom :=
    (S.pullback g).sfPair
  let c := transportSquareIso (A := A.functor) (B := B.functor) (P := P.functor)
    hAc hBc (S.pullback g).pair
  have hc : HEq c (S.pullback g).pair := transportSquareIso_heq hAc hBc _
  have hcapp (E : Padic.FiniteCoefficientFields l Ω)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E) :
      c.hom.app ⟨E, K⟩ =
        ((pbcScalarSystem l Ω T Fact.out Fact.out).ι E).map ((b E).hom.app K) := by
    have h₁ := transportSquareIso_app_heq hAc hBc (S.pullback g).pair ⟨E, K⟩
    let K' := cast (finiteStageTypeEq l Ω T E) K
    have hK : HEq K K' := cast_heq (finiteStageTypeEq l Ω T E) K
    have h₂ := (S.pullback g).pair_components ⟨E, K⟩ K' hK
    dsimp only at h₂
    have h₃ := transportSourceIso_map_app_heq (finiteStageTypeEq l Ω T E)
      (finiteStageCategoryHEq l Ω T E) ((S.coefficients T).finite_functor E)
      ((S.pullback g).sfFinite E) ((S.pullback g).finite E).rational K K' hK
      ((pbcScalarSystem l Ω T Fact.out Fact.out).ι E)
    exact eq_of_heq (h₁.trans (h₂.trans h₃.symm))
  constructor
  · exact pairTransportIsEquivalence (S.coefficients T).equivalence (S.pullback g).pair
  constructor
  · intro E
    exact pairTransportIsEquivalence ((S.coefficients T).stage E).rational
      ((S.pullback g).finite E).rational
  refine ⟨b, c, hb, hc, ?_, ?_⟩
  · exact (stageSquares A B P (S.pullback g).mixed b c hbτ hcapp).1
  · exact (stageSquares A B P (S.pullback g).mixed b c hbτ hcapp).2

/-- The geometric fibre satisfies all coefficient-comparison hypotheses, and the
specified transport of Weil pairs is an equivalence compatible with scalar extension
and finite-stage inclusions. No k-linearity of geometric Frobenius is required.
Source: blueprint main-20261015, trace-definition final sentence
(blueprint: lem-fd-frobenius-fixed-pair-comparison).

Proof:
1. Base change the separated finite-type structure morphism to k, using
   lem-pod-separated-finite-type-base-change. Finite generation is preserved even
   though the algebraic closure need not be finite over the base field.
2. A field is noetherian; finite type over it gives noetherianity by
   lem-weil-pbc-finite-type-over-noetherian. Apply lem-kun-dimension-finite-type to
   obtain a natural-number dimension bound, also valid for the empty scheme.
3. Since l and p are distinct primes, l is a unit in k, hence in every local ring
   of X. The recorded geometricFrobenius is the scheme automorphism with inverse
   id times Spec of arithmetic Frobenius; no k-linearity is used.
4. At a finite or common stage transport theta using the inverse of the forward
   pullback comparison, then J(theta). Both factors are isomorphisms.
5. Naturality of the comparison identifies the two intertwining conditions.
   Faithfulness reflects their equality. Thus the Hom map is exactly J restricted
   to intertwining arrows and is bijective, including its inverse restriction.
6. Given a target pair, essential surjectivity of J gives an underlying isomorphism
   from JK. Conjugate its structure to JK and lift it and its inverse through the
   Hom bijection. Faithfulness proves the inverse equations upstairs.
7. Apply lem-trf-fully-faithful-ess-surj-equivalence to this very pair functor.
8. The mixed scalar square is the given compatible transformation of stage systems
   in S, with its specified actual scalar and Frobenius comparisons.
9. Naturality of the coefficient scalar comparison at theta, combined with that
   square, says that its inverse component intertwines the transported structures.
   Its inverse intertwines too, giving the stated normalized natural isomorphism.
10. Apply the same calculation to stage inclusions and the common comparison's
    specified finite components. Naturality gives the inclusion isomorphisms.
    Identity and scalar cocycle equations lift because forgetting pairs is faithful. -/
theorem frobeniusFixedPairComparison (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] :
    ∃ (_hN : IsNoetherian (D.geometricFiber X₀).left)
      (_hD : Fact (∃ n : ℕ, topologicalKrullDim (D.geometricFiber X₀).left ≤ n))
      (_hI : Fact (∀ x : (D.geometricFiber X₀).left,
        IsUnit (l : (D.geometricFiber X₀).left.presheaf.stalk x))),
      @FdGeometricFixedPairComparison l _ Ω _ _ _ S D hl X₀ _ _ _ _hN _hD _hI := by
  have h := D.geometric_fibre_comparison_hypotheses l Fact.out hl X₀
  let hN := h.2.2.2.1
  let hD : Fact (∃ n : ℕ, topologicalKrullDim (D.geometricFiber X₀).left ≤ n) :=
    ⟨h.2.2.2.2.1⟩
  let hI : Fact (∀ x : (D.geometricFiber X₀).left,
      IsUnit (l : (D.geometricFiber X₀).left.presheaf.stalk x)) := ⟨fun x ↦ by
    obtain ⟨t, ht, _⟩ := h.2.2.2.2.2.1 x
    exact ⟨t, ht⟩⟩
  have hp := fixedPairComparison l Ω S (D.geometricFiber X₀).left
    (D.geometricFrobenius X₀)
  refine ⟨hN, hD, hI, hp, ?_, ?_⟩
  · have he := hp.1
    let : (IsoAlgebra.mapOfNatIso (S.pullback (D.geometricFrobenius X₀)).pair).IsEquivalence :=
      he
    apply pairEquivalence _ _
    unfold sfCommonStageWeilFrobeniusPullback
    congr 1
  · intro E
    have he := hp.2.1 E
    let : (IsoAlgebra.mapOfNatIso
        ((S.pullback (D.geometricFrobenius X₀)).finite E).rational).IsEquivalence := he
    apply pairEquivalence _ _
    unfold sfWeilFrobeniusPullback
    congr 1

end WeilConjectures
