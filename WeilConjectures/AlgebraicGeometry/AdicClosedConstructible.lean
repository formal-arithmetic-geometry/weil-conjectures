/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionUniverses
public import WeilConjectures.AlgebraicGeometry.IntegralOperationsScalarComparisons
public import WeilConjectures.AlgebraicGeometry.SfScalarExtensionComposition
public import WeilConjectures.AlgebraicGeometry.CompletedPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionConstructibleIntrinsic
public import WeilConjectures.ZetaSeries
import WeilConjectures.AlgebraicGeometry.PodReindexingCompletedEvaluationReflection
import all WeilConjectures.AlgebraicGeometry.IntegralOperationsScalarComparisons
import all WeilConjectures.AlgebraicGeometry.SfScalarExtensionComposition
import all WeilConjectures.AlgebraicGeometry.RationalTensorTowerCoherence
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Closed structure on integral constructible adic complexes

Source: Bhatt--Scholze, Sections 3.4, 6.5 and 6.7, especially Lemmas 3.4.11,
6.7.12 and 6.7.13 (blueprint: lem-per-adic-closed-constructible).
The scalar comparisons are transposes of evaluation through the recorded completed
tensor comparison. Coefficients are modules over the completed ring sheaf.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicClosed

/-- Transport the inverse of ell along the structural residue-field map.
Source: Bhatt--Scholze, the ell-coprime hypothesis in Section 6.7
(blueprint: lem-per-adic-closed-constructible). -/
@[instance_reducible] def residueInvertible (l : ℕ) (k : Type u) [Field k] (hl : IsUnit (l : k))
    (W : Scheme.{u}) [W.Over (Spec (.of k))] (w : W) :
    Invertible (l : W.residueField w) :=
  (map_natCast ((W ↘ Spec (.of k)).residueFieldAlgebraMap w) l) ▸
    (hl.map ((W ↘ Spec (.of k)).residueFieldAlgebraMap w)).invertible

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (k : Type u) [Field k] (hl : IsUnit (l : k))
  (W : Scheme.{u}) [hW : W.Over (Spec (.of k))]
  [hft : LocallyOfFiniteType (W ↘ Spec (.of k))]
  [hqc : QuasiCompact (W ↘ Spec (.of k))]
  [hsep : IsSeparated (W ↘ Spec (.of k))]

include hl hW hft hqc hsep in
/-- Ambient internal Hom preserves the intrinsic integral constructible predicate.
Source: Bhatt--Scholze, Lemma 6.7.13
(blueprint: lem-per-adic-closed-constructible).

Proof: (1) the completed coefficient ring is flat over the DVR, has the specified
finite reductions, and its degree-zero unit is stratified perfect. Finite type over
k makes W Noetherian and finite-dimensional. (2) identify the strict finite-tensor
Roos tower with completion of ordinary tensor on flat-term K-flat representatives.
(3) integral Hom reduction gives completeness and evaluation-defined reduction
isomorphisms. At the residue field, both inputs have finite Tor amplitude.
(4) lem-per-finite-tor-internal-hom-any-field gives bounded constructibility of
that residue Hom. (5) the coefficient exact sequences A_1 -> A_n -> A_(n-1)
give triangles after derived tensor. Induction and the cohomology long exact
sequence keep the same interval; the weak Serre property preserves constructibility.
Affine-local and finite global stratifications agree on the Noetherian W, and
finite-ring derived origin gives the required pro-etale reductions. Together with
completeness these are precisely sfIntegralConstructible. -/
theorem hom_constructible (P Q : sfIntegralConstructibleCategory l E W) :
    sfIntegralConstructible l E W
      ((integralDerivedInternalHom l E W).obj (op P.obj, Q.obj)) := by
  sorry

/-- The full internal-Hom functor is the restriction of the recorded ambient functor.
Only its constructibility proof is postponed; its object and arrow maps are real.
Source: Bhatt--Scholze, Lemma 6.7.13
(blueprint: lem-per-adic-closed-constructible). -/
def hom : (sfIntegralConstructibleCategory l E W)ᵒᵖ ×
    sfIntegralConstructibleCategory l E W ⥤ sfIntegralConstructibleCategory l E W :=
  (sfIntegralConstructible l E W).lift
    (((sfIntegralConstructible l E W).ι.op.prod (sfIntegralConstructible l E W).ι) ⋙
      integralDerivedInternalHom l E W)
    (fun P ↦ hom_constructible l E k hl W P.1.unop P.2)

/-- The recorded completed tensor with residue invertibility derived from the base.
Source: Bhatt--Scholze, Lemma 6.7.12
(blueprint: lem-per-adic-closed-constructible). -/
abbrev tensor := @constructibleIntegralTensor l _ E _ _ _ W (residueInvertible l k hl W)

/-- The completed adjunction is uniquely fixed by the ambient transpose after the
actual reduction/limit unit and the prescribed Roos tensor realization.
Source: Bhatt--Scholze, Lemma 3.4.11; node proof Steps 2 and 6
(blueprint: lem-per-adic-closed-constructible).

Proof: the displayed composite is the ordinary-to-completed tensor map. On good
representatives it is the quotient augmentation into the finite tensor Roos tower.
The Koszul completion reflector identifies precomposition by this map with a
bijection for every complete target Q. Compose with ambient tensor-Hom transposition.
Both bijections are additive, so this is an additive equivalence. Its displayed
value on every arrow determines the equivalence uniquely. -/
theorem transpose_existsUnique (M P Q : sfIntegralConstructibleCategory l E W) :
    ∃! e : ((tensor l E k hl W).obj (M, P) ⟶ Q) ≃+
        (M ⟶ (hom l E k hl W).obj (op P, Q)),
      ∀ f : (tensor l E k hl W).obj (M, P) ⟶ Q,
        HEq ((e f).hom)
          ((pullbackTensorCalculus l E W).integralClosed.transpose M.obj P.obj Q.obj
            ((pullbackTensorCalculus l E W).adjunction.unit.app
                ((pullbackTensorCalculus l E W).integralClosed.tensor.obj (M.obj, P.obj)) ≫
              (coefficientSequenceLimit l E W).map
                ((pullbackTensorCalculus l E W).reductionTensor.hom.app (M.obj, P.obj)) ≫
              (pullbackTensorIntegralTensorModel l E W).inv.app (M.obj, P.obj) ≫ f.hom)) := by
  let S := (pullbackTensorCalculus l E W).integralClosed
  let := S.monoidal
  let H := integralDerivedInternalHom l E W
  have : (Prod.sectR (op P.obj) _ ⋙ H).IsRightAdjoint :=
    (S.adjunction P.obj).isRightAdjoint
  have : (Prod.sectR (op P.obj) _ ⋙ H).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (Prod.sectR (op P.obj) _ ⋙ coefficientIntegralInternalHom l E W).Additive :=
    show (Prod.sectR (op P.obj) _ ⋙ H).Additive from inferInstance
  have : (MonoidalCategory.tensorRight P.obj).Additive :=
    (S.adjunction P.obj).left_adjoint_additive
  let tr : ((tensor l E k hl W).obj (M, P) ⟶ Q) ≃+
      (M ⟶ (hom l E k hl W).obj (op P, Q)) :=
    InducedCategory.homAddEquiv.trans
      ((AddEquiv.ofBijective
        ({ toFun := fun f ↦ PodCompletedReflection.unit l E W M.obj P.obj ≫ f
           map_zero' := by simp
           map_add' := fun f g ↦ by simp only [Preadditive.comp_add] } :
          ((integralCompletedTensor l E W).obj (M.obj, P.obj) ⟶ Q.obj) →+
            (S.tensor.obj (M.obj, P.obj) ⟶ Q.obj))
        (PodCompletedReflection.precompose_bijective l E W M P Q)).trans
          ((S.adjunction P.obj).homAddEquiv M.obj Q.obj |>.trans
            (InducedCategory.homAddEquiv (X := M)
              (Y := (hom l E k hl W).obj (op P, Q))).symm))
  refine ⟨tr, ?_, ?_⟩
  · intro f
    apply heq_of_eq
    change S.transpose M.obj P.obj Q.obj
      (PodCompletedReflection.unit l E W M.obj P.obj ≫ f.hom) = _
    congr 1
    simp only [PodCompletedReflection.unit, Category.assoc]
    rfl
  intro tr' htr'
  apply AddEquiv.ext
  intro f
  apply ObjectProperty.hom_ext
  apply eq_of_heq
  apply (htr' f).trans
  apply heq_of_eq
  change _ = S.transpose M.obj P.obj Q.obj
    (PodCompletedReflection.unit l E W M.obj P.obj ≫ f.hom)
  congr 1
  simp only [PodCompletedReflection.unit, Category.assoc]
  rfl

/-- The full completed transpose with its unique ambient normalization.
Source: Bhatt--Scholze, Lemma 3.4.11; node proof Step 6
(blueprint: lem-per-adic-closed-constructible). -/
def transpose (M P Q : sfIntegralConstructibleCategory l E W) :
    ((tensor l E k hl W).obj (M, P) ⟶ Q) ≃+
      (M ⟶ (hom l E k hl W).obj (op P, Q)) :=
  (transpose_existsUnique l E k hl W M P Q).exists.choose

/-- The restricted ambient evaluation, equivalently the inverse transpose of identity.
Source: Bhatt--Scholze, Lemma 3.4.11, and node proof Step 6
(blueprint: lem-per-adic-closed-constructible). -/
def evaluation (P Q : sfIntegralConstructibleCategory l E W) :
    (tensor l E k hl W).obj ((hom l E k hl W).obj (op P, Q), P) ⟶ Q :=
  (transpose l E k hl W _ P Q).symm (𝟙 _)

/-- The closed symmetric monoidal structure has the recorded completed tensor,
the degree-zero completed coefficient unit, and precisely the ambient transposes.
Source: Bhatt--Scholze, Lemmas 3.4.11 and 6.7.12--13
(blueprint: lem-per-adic-closed-constructible).

Proof: Steps 1--5 give Hom closure and the coefficient unit. Step 6 uses the
completion reflector to identify maps out of completed tensor into a complete
target with maps out of ordinary tensor, then applies ambient tensor-Hom adjunction.
Fullness identifies these with the subcategory Hom groups. Step 7 reflects the
ordinary associator, unitors and symmetry: completion of CA tensor D equals
completion of A tensor D, by testing maps into complete targets and currying.
Both triple bracketings identify with completion of ordinary triple tensor.
Pentagon, triangle and symmetry follow from their ordinary total-tensor identities.
The normalization in transpose_existsUnique fixes exactly these transposes. -/
theorem closed_symmetric_monoidal :
    ∃ S : CoefficientClosedStructure (hom l E k hl W),
      ∃ ht : S.tensor = tensor l E k hl W,
        Nonempty (@SymmetricCategory _ _ S.monoidal) ∧
        S.monoidal.tensorUnit.obj =
          (DerivedCategory.singleFunctor (integralTowerModules l E W) 0).obj
            (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W)) ∧
        ∀ (M P Q : sfIntegralConstructibleCategory l E W)
          (f : (tensor l E k hl W).obj (M, P) ⟶ Q),
          S.transpose M P Q (eqToHom (congrArg (fun T ↦ T.obj (M, P)) ht) ≫ f) =
            transpose l E k hl W M P Q f := by
  sorry

private theorem closedEvaluation_naturality
    {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (P Q P' Q' : D)
    (f : P' ⟶ P) (g : Q ⟶ Q') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 P')) ≫
        S.evaluation P' Q' =
      S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation P Q ≫ g := by
  let := S.monoidal
  have he : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P')) ≫
      S.evaluation P' Q = S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation P Q := by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      S.evaluation_naturality P P' Q f
  have hg : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P')) ≫
      S.evaluation P' Q' = S.evaluation P' Q ≫ g := by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      (S.adjunction P').counit.naturality g
  have hh : H.map (Prod.mkHom f.op g) =
      H.map (Prod.mkHom f.op (𝟙 Q)) ≫ H.map (Prod.mkHom (𝟙 (op P')) g) := by
    rw [← H.map_comp]
    congr 1
    ext <;> simp
  rw [hh]
  have ht : Prod.mkHom
      (H.map (Prod.mkHom f.op (𝟙 Q)) ≫ H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P') =
      Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P') := by
    ext <;> simp
  rw [ht, S.tensor.map_comp, Category.assoc, hg, ← Category.assoc, he]
  exact Category.assoc _ _ _


private theorem normalized_uncurry
    {D : Type a} [Category.{b} D] [Preadditive D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (T : D × D ⥤ D)
    (τ : ∀ M P Q : D, (T.obj (M, P) ⟶ Q) ≃+ (M ⟶ H.obj (op P, Q)))
    (ht : S.tensor = T)
    (hn : ∀ (M P Q : D) (f : T.obj (M, P) ⟶ Q),
      S.transpose M P Q (eqToHom (congrArg (fun T ↦ T.obj (M, P)) ht) ≫ f) =
        τ M P Q f) (M P Q : D) (g : M ⟶ H.obj (op P, Q)) :
    (τ M P Q).symm g = T.map (Prod.mkHom g (𝟙 P)) ≫
      (τ (H.obj (op P, Q)) P Q).symm (𝟙 _) := by
  subst T
  simp only [eqToHom_refl, Category.id_comp] at hn
  have hτ (A B C : D) : (τ A B C).toEquiv = S.transpose A B C := by
    ext f
    exact (hn A B C f).symm
  change ((τ M P Q).toEquiv).symm g = _
  rw [hτ]
  change _ = S.tensor.map (Prod.mkHom g (𝟙 P)) ≫
    ((τ (H.obj (op P, Q)) P Q).toEquiv).symm (𝟙 _)
  rw [hτ]
  let := S.monoidal
  have hu := (S.adjunction P).homEquiv_counit M Q g
  have he := (S.adjunction P).homEquiv_symm_id Q
  change (S.transpose M P Q).symm g = _ at hu
  change (S.transpose (H.obj (op P, Q)) P Q).symm (𝟙 _) = _ at he
  rw [he]
  exact hu.trans (congrArg (fun f ↦ f ≫ (S.adjunction P).counit.app Q)
    (@MonoidalCategory.tensorHom_id D _ S.monoidal _ _ g P).symm)

private theorem normalized_inverse_pre
    {D : Type a} [Category.{b} D] [Preadditive D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (T : D × D ⥤ D)
    (τ : ∀ M P Q : D, (T.obj (M, P) ⟶ Q) ≃+ (M ⟶ H.obj (op P, Q)))
    (ht : S.tensor = T)
    (hn : ∀ (M P Q : D) (f : T.obj (M, P) ⟶ Q),
      S.transpose M P Q (eqToHom (congrArg (fun T ↦ T.obj (M, P)) ht) ≫ f) =
        τ M P Q f) (M M' P Q : D) (f : M' ⟶ M) (g : M ⟶ H.obj (op P, Q)) :
    (τ M' P Q).symm (f ≫ g) = T.map (Prod.mkHom f (𝟙 P)) ≫ (τ M P Q).symm g := by
  rw [normalized_uncurry S T τ ht hn M' P Q (f ≫ g),
    normalized_uncurry S T τ ht hn M P Q g]
  rw [← Category.assoc, ← T.map_comp]
  congr 2
  ext <;> simp

private theorem normalized_evaluation_naturality
    {D : Type a} [Category.{b} D] [Preadditive D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (T : D × D ⥤ D)
    (τ : ∀ M P Q : D, (T.obj (M, P) ⟶ Q) ≃+ (M ⟶ H.obj (op P, Q)))
    (ht : S.tensor = T)
    (hn : ∀ (M P Q : D) (f : T.obj (M, P) ⟶ Q),
      S.transpose M P Q (eqToHom (congrArg (fun T ↦ T.obj (M, P)) ht) ≫ f) =
        τ M P Q f) (P Q P' Q' : D) (f : P' ⟶ P) (g : Q ⟶ Q') :
    T.map (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 P')) ≫
        (τ _ P' Q').symm (𝟙 _) =
      T.map (Prod.mkHom (𝟙 _) f) ≫ (τ _ P Q).symm (𝟙 _) ≫ g := by
  subst T
  simp only [eqToHom_refl, Category.id_comp] at hn
  have he (P Q : D) : (τ (H.obj (op P, Q)) P Q).symm (𝟙 _) = S.evaluation P Q := by
    have hτ (M : D) : (τ M P Q).toEquiv = S.transpose M P Q := by
      ext x
      exact (hn M P Q x).symm
    change ((τ _ P Q).toEquiv).symm (𝟙 _) = _
    rw [hτ]
    exact (S.adjunction P).homEquiv_symm_id Q
  rw [he, he]
  exact closedEvaluation_naturality S P Q P' Q' f g

private theorem inverse_transpose (M P Q : sfIntegralConstructibleCategory l E W)
    (g : M ⟶ (hom l E k hl W).obj (op P, Q)) :
    (transpose l E k hl W M P Q).symm g =
      (tensor l E k hl W).map (Prod.mkHom g (𝟙 P)) ≫ evaluation l E k hl W P Q := by
  obtain ⟨S, ht, _, _, hn⟩ := closed_symmetric_monoidal l E k hl W
  exact normalized_uncurry S (tensor l E k hl W) (transpose l E k hl W) ht hn M P Q g

private theorem inverse_transpose_pre
    (M M' P Q : sfIntegralConstructibleCategory l E W) (f : M' ⟶ M)
    (g : M ⟶ (hom l E k hl W).obj (op P, Q)) :
    (transpose l E k hl W M' P Q).symm (f ≫ g) =
      (tensor l E k hl W).map (Prod.mkHom f (𝟙 P)) ≫
        (transpose l E k hl W M P Q).symm g := by
  obtain ⟨S, ht, _, _, hn⟩ := closed_symmetric_monoidal l E k hl W
  exact normalized_inverse_pre S (tensor l E k hl W) (transpose l E k hl W) ht hn
    M M' P Q f g

private theorem evaluation_naturality
    (P Q P' Q' : sfIntegralConstructibleCategory l E W) (a : P' ⟶ P) (b : Q ⟶ Q') :
    (tensor l E k hl W).map
        (Prod.mkHom ((hom l E k hl W).map (Prod.mkHom a.op b)) (𝟙 P')) ≫
        evaluation l E k hl W P' Q' =
      (tensor l E k hl W).map (Prod.mkHom (𝟙 _) a) ≫
        evaluation l E k hl W P Q ≫ b := by
  obtain ⟨S, ht, _, _, hn⟩ := closed_symmetric_monoidal l E k hl W
  exact normalized_evaluation_naturality S (tensor l E k hl W) (transpose l E k hl W)
    ht hn P Q P' Q' a b

private theorem inverse_transpose_post
    (M P Q P' Q' : sfIntegralConstructibleCategory l E W)
    (g : M ⟶ (hom l E k hl W).obj (op P, Q)) (a : P' ⟶ P) (b : Q ⟶ Q') :
    (transpose l E k hl W M P' Q').symm
        (g ≫ (hom l E k hl W).map (Prod.mkHom a.op b)) =
      (tensor l E k hl W).map (Prod.mkHom (𝟙 M) a) ≫
        (transpose l E k hl W M P Q).symm g ≫ b := by
  rw [inverse_transpose_pre, inverse_transpose, evaluation_naturality]
  rw [inverse_transpose]
  simp only [← Category.assoc, ← Functor.map_comp]
  congr 2
  congr 1
  ext <;> simp

private theorem conjugation_naturality {C : Type a} [Category.{b} C]
    {A B A' B' D E D' E' : C}
    (c : A ≅ A') (c' : B ≅ B') (d : D ≅ D') (d' : E ≅ E')
    (p : A ⟶ B) (p' : A' ⟶ B') (q : D ⟶ E) (q' : D' ⟶ E')
    (e : A ≅ D) (e' : B ≅ E)
    (hc : p ≫ c'.hom = c.hom ≫ p')
    (hd : q ≫ d'.hom = d.hom ≫ q')
    (he : p ≫ e'.hom = e.hom ≫ q) :
    p' ≫ (c'.inv ≫ e'.hom ≫ d'.hom) =
      (c.inv ≫ e.hom ≫ d.hom) ≫ q' := by
  apply (cancel_epi c.hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← hc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, he, Category.assoc, hd]

section Scalar
variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private def scalarTensorComparison :
    tensor l E k hl W ⋙ sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W ≅
    (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).prod
      (sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W) ⋙ tensor l L k hl W := by
  letI := residueInvertible l k hl W
  let S := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
  let U := constructibleIntegralTensor l E W ⋙ S
  let V := S.prod S ⋙ constructibleIntegralTensor l L W
  let e : U ≅ V := NatIso.ofComponents
    (fun K ↦ integralTensorScalarComparison l E L ι W K.1 K.2) (by
      intro K M a
      apply ObjectProperty.hom_ext
      change (integralScalarExtension l E L ι W).map
          ((integralCompletedTensor l E W).map (Prod.mkHom a.1.hom a.2.hom)) ≫
            (scalarTensorCompleted l E L ι W M.1.obj M.2.obj
              M.1.property.1 M.2.property.1
              ((constructibleIntegralTensor l E W).obj M).property.1).hom =
        (scalarTensorCompleted l E L ι W K.1.obj K.2.obj
          K.1.property.1 K.2.property.1
          ((constructibleIntegralTensor l E W).obj K).property.1).hom ≫
          (integralCompletedTensor l L W).map (Prod.mkHom
            ((integralScalarExtension l E L ι W).map a.1.hom)
            ((integralScalarExtension l E L ι W).map a.2.hom))
      dsimp only [scalarTensorCompleted, Iso.trans_hom, Functor.mapIso_hom]
      have hnX := (scalarCompletion l E L ι W).naturality
        ((integralCompletedTensor l E W).map (Prod.mkHom a.1.hom a.2.hom))
      have hnO := (scalarTensorOrdinary l E L ι W).hom.naturality
        (Prod.mkHom a.1.hom a.2.hom)
      dsimp only [Functor.comp_map, Functor.prod_map] at hnO
      exact conjugation_naturality
        (scalarCompletionIso l E L ι W _
          ((constructibleIntegralTensor l E W).obj K).property.1)
        (scalarCompletionIso l E L ι W _
          ((constructibleIntegralTensor l E W).obj M).property.1)
        ((integralCompletedTensor l L W).mapIso (Iso.prod
          (scalarCompletionIso l E L ι W K.1.obj K.1.property.1)
          (scalarCompletionIso l E L ι W K.2.obj K.2.property.1)))
        ((integralCompletedTensor l L W).mapIso (Iso.prod
          (scalarCompletionIso l E L ι W M.1.obj M.1.property.1)
          (scalarCompletionIso l E L ι W M.2.obj M.2.property.1)))
        _ _ _ _
        ((scalarTensorOrdinary l E L ι W).app (K.1.obj, K.2.obj))
        ((scalarTensorOrdinary l E L ι W).app (M.1.obj, M.2.obj))
        hnX
        (by
          have h := congrArg (integralCompletedTensor l L W).map
            (show Prod.mkHom
                ((integralOrdinaryDerivedScalar l E L ι W).map a.1.hom)
                ((integralOrdinaryDerivedScalar l E L ι W).map a.2.hom) ≫
                  Prod.mkHom ((scalarCompletion l E L ι W).app M.1.obj)
                    ((scalarCompletion l E L ι W).app M.2.obj) =
              Prod.mkHom ((scalarCompletion l E L ι W).app K.1.obj)
                  ((scalarCompletion l E L ι W).app K.2.obj) ≫
                Prod.mkHom ((integralScalarExtension l E L ι W).map a.1.hom)
                  ((integralScalarExtension l E L ι W).map a.2.hom) by
              ext
              · exact (scalarCompletion l E L ι W).naturality a.1.hom
              · exact (scalarCompletion l E L ι W).naturality a.2.hom)
          simpa only [Functor.mapIso_hom, scalarCompletionIso, asIso_hom,
            Iso.prod_hom, Functor.map_comp] using h)
        hnO)
  exact e

/-- The scalar comparison is the target transpose of extended evaluation after the
inverse of the recorded completed tensor comparison, on every constructible pair.
Source: node proof Step 8; Stacks 08J9, 08JA
(blueprint: lem-per-adic-closed-constructible). -/
def scalarHom (P Q : sfIntegralConstructibleCategory l E W) :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      E L ι W).obj ((hom l E k hl W).obj (op P, Q)) ⟶
      (hom l L k hl W).obj
        (op ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj P),
          (sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj Q) :=
  transpose l L k hl W _ _ _
    ((@integralTensorScalarComparison l _ E _ _ _ L _ _ _ ι W
      (residueInvertible l k hl W) ((hom l E k hl W).obj (op P, Q)) P).inv ≫
        (sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map
          (evaluation l E k hl W P Q))

/-- Finite scalar extension makes the evaluation-defined comparison invertible.
Source: node proof Step 8; Stacks 08J9, 08JA
(blueprint: lem-per-adic-closed-constructible).

Proof: completed scalar extension equals ordinary finite-free change of rings on
complete objects, including the ambient Hom. Finite-free Hom base change is an
isomorphism, transposed from ordinary extended evaluation. On K-flat representatives
the scalar tensor comparison multiplies the coefficients. Reduction and Roos limit
preserve this formula. Precomposition by the completion unit identifies completed
and ordinary evaluation, so uniqueness of transposition identifies this isomorphism
with scalarHom. No perfect-first-input hypothesis is required. -/
theorem scalarHom_isIso (P Q : sfIntegralConstructibleCategory l E W) :
    IsIso (scalarHom l E k hl W L ι P Q) := by
  sorry

/-- Naturality of the same comparison in both constructible inputs.
Source: node proof Step 9; Stacks 08J9
(blueprint: lem-per-adic-closed-constructible).

Proof: uncurry both routes. Tensor-comparison naturality and evaluation naturality
identify their values with extended evaluation after the given input arrows.
Injectivity of the normalized target transpose gives the displayed equality. -/
theorem scalarHom_naturality (P Q P' Q' : sfIntegralConstructibleCategory l E W)
    (a : P' ⟶ P) (b : Q ⟶ Q') :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      E L ι W).map ((hom l E k hl W).map (Prod.mkHom a.op b)) ≫
        scalarHom l E k hl W L ι P' Q' =
      scalarHom l E k hl W L ι P Q ≫
        (hom l L k hl W).map (Prod.mkHom
          (((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map a).op)
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map b)) := by
  let F := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
  let μ := scalarTensorComparison l E k hl W L ι
  apply (transpose l L k hl W _ _ _).symm.injective
  rw [inverse_transpose_pre, inverse_transpose_post]
  have hb (U V : sfIntegralConstructibleCategory l E W) :
      (transpose l L k hl W _ _ _).symm (scalarHom l E k hl W L ι U V) =
        μ.inv.app ((hom l E k hl W).obj (op U, V), U) ≫
          F.map (evaluation l E k hl W U V) :=
    (transpose l L k hl W _ _ _).symm_apply_apply _
  rw [hb, hb]
  have hn := μ.inv.naturality
    (Prod.mkHom ((hom l E k hl W).map (Prod.mkHom a.op b)) (𝟙 P'))
  have hn' := μ.inv.naturality (Prod.mkHom (𝟙 ((hom l E k hl W).obj (op P, Q))) a)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn hn'
  rw [F.map_id] at hn hn'
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp, evaluation_naturality]
  rw [F.map_comp, F.map_comp]
  simpa only [Category.assoc] using
    congrArg (fun t ↦ t ≫ F.map (evaluation l E k hl W P Q) ≫ F.map b) hn'.symm

/-- Scalar extension carries the restricted ambient evaluation to evaluation.
Source: node proof Steps 8--9; Stacks 08J9
(blueprint: lem-per-adic-closed-constructible).

Proof: the defining transpose of scalarHom has inverse transpose equal to extended
evaluation after the inverse tensor comparison. Compose with the tensor comparison
and use the tensor-Hom counit identity to obtain the displayed evaluation square. -/
theorem scalarHom_evaluation (P Q : sfIntegralConstructibleCategory l E W) :
    (@integralTensorScalarComparison l _ E _ _ _ L _ _ _ ι W
      (residueInvertible l k hl W) ((hom l E k hl W).obj (op P, Q)) P).hom ≫
      (tensor l L k hl W).map (Prod.mkHom (scalarHom l E k hl W L ι P Q) (𝟙 _)) ≫
        evaluation l L k hl W
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj P)
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj Q) =
      (sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map
          (evaluation l E k hl W P Q) := by
  let μ := @integralTensorScalarComparison l _ E _ _ _ L _ _ _ ι W
    (residueInvertible l k hl W) ((hom l E k hl W).obj (op P, Q)) P
  have h := inverse_transpose l L k hl W _ _ _ (scalarHom l E k hl W L ι P Q)
  have hb : (transpose l L k hl W _ _ _).symm (scalarHom l E k hl W L ι P Q) =
      μ.inv ≫ (sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map
          (evaluation l E k hl W P Q) :=
    (transpose l L k hl W _ _ _).symm_apply_apply _
  rw [← h, hb]
  exact μ.hom_inv_id_assoc _

/-- Scalar extension carries every tensor-Hom transpose to the target transpose.
Source: node proof Step 9; Stacks 08J9
(blueprint: lem-per-adic-closed-constructible).

Proof: write an inverse transpose as evaluation after tensoring its transpose with
the identity of P. Apply scalar extension. The evaluation square and naturality of
the completed tensor comparison give the target inverse transpose; transpose back. -/
theorem scalarHom_transpose (M P Q : sfIntegralConstructibleCategory l E W)
    (f : (tensor l E k hl W).obj (M, P) ⟶ Q) :
    transpose l L k hl W _ _ _
        ((@integralTensorScalarComparison l _ E _ _ _ L _ _ _ ι W
          (residueInvertible l k hl W) M P).inv ≫
            (sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map f) =
      (sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map
          (transpose l E k hl W M P Q f) ≫ scalarHom l E k hl W L ι P Q := by
  let F := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
  let μ := scalarTensorComparison l E k hl W L ι
  apply (transpose l L k hl W _ _ _).symm.injective
  rw [AddEquiv.symm_apply_apply, inverse_transpose_pre]
  have hb : (transpose l L k hl W _ _ _).symm (scalarHom l E k hl W L ι P Q) =
      μ.inv.app ((hom l E k hl W).obj (op P, Q), P) ≫
        F.map (evaluation l E k hl W P Q) :=
    (transpose l L k hl W _ _ _).symm_apply_apply _
  rw [hb]
  have hn := μ.inv.naturality
    (Prod.mkHom (transpose l E k hl W M P Q f) (𝟙 P))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [F.map_id] at hn
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp]
  rw [← inverse_transpose, AddEquiv.symm_apply_apply]
  rfl

/-- Composition uses the canonical scalar associators and the contravariant inverse.
Source: node proof Step 9; Stacks 08J9
(blueprint: lem-per-adic-closed-constructible).

Proof: uncurry both routes through the completed tensor adjunction. For a tower
E -> L -> F both maps send (h tensor s tensor t, p tensor u) to h(p) tensor s*t*u.
Associativity of coefficient multiplication proves equality on K-flat representatives,
compatible with differentials, reductions and completion. Injectivity of the target
transpose proves the equation with the normalized scalar composition isomorphisms. -/
theorem scalar_tower (F : Type u) [Field F] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] F] (j : L →ₐ[ℚ_[l]] F)
    (P Q : sfIntegralConstructibleCategory l E W) :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      L F j W).map (scalarHom l E k hl W L ι P Q) ≫
      scalarHom l L k hl W F j
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj P)
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj Q) ≫
      (hom l F k hl W).map (Prod.mkHom
        (((sfIntegralScalarComp l E L ι W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).inv.app P).op)
        ((sfIntegralScalarComp l E L ι W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).hom.app Q)) =
      (sfIntegralScalarComp l E L ι W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).hom.app
          ((hom l E k hl W).obj (op P, Q)) ≫
        scalarHom l E k hl W F (j.comp ι) P Q := by
  let U := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
  let V := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L F j W
  let Z := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E F (j.comp ι) W
  let μ := scalarTensorComparison l E k hl W L ι
  let ν := scalarTensorComparison l L k hl W F j
  let ξ := scalarTensorComparison l E k hl W F (j.comp ι)
  let α := sfIntegralScalarComp l E L ι W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j
  have ht (X Y : sfIntegralConstructibleCategory l E W) :
      V.map (μ.hom.app (X, Y)) ≫ ν.hom.app (U.obj X, U.obj Y) ≫
        (tensor l F k hl W).map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) =
      α.hom.app ((tensor l E k hl W).obj (X, Y)) ≫ ξ.hom.app (X, Y) := by
    let := residueInvertible l k hl W
    exact integralTensor_tower l W E L ι F j X Y
  have hi (X Y : sfIntegralConstructibleCategory l E W) :
      ν.inv.app (U.obj X, U.obj Y) ≫ V.map (μ.inv.app (X, Y)) ≫
          α.hom.app ((tensor l E k hl W).obj (X, Y)) =
        (tensor l F k hl W).map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) ≫
          ξ.inv.app (X, Y) := by
    apply (cancel_mono (ξ.hom.app (X, Y))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← ht]
    simp only [← Category.assoc, ← V.map_comp, Iso.inv_hom_id_app]
    change ((ν.inv.app (U.obj X, U.obj Y) ≫
        V.map (𝟙 ((tensor l L k hl W).obj (U.obj X, U.obj Y)))) ≫
        ν.hom.app (U.obj X, U.obj Y)) ≫
        (tensor l F k hl W).map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) =
      (tensor l F k hl W).map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) ≫ 𝟙 _
    simp only [V.map_id]
    erw [Category.comp_id, Iso.inv_hom_id_app, Category.id_comp, Category.comp_id]
  have beta (X Y : sfIntegralConstructibleCategory l E W) :
      (transpose l L k hl W _ _ _).symm (scalarHom l E k hl W L ι X Y) =
        μ.inv.app ((hom l E k hl W).obj (op X, Y), X) ≫
          U.map (evaluation l E k hl W X Y) :=
    (transpose l L k hl W _ _ _).symm_apply_apply _
  have beta' (X Y : sfIntegralConstructibleCategory l L W) :
      (transpose l F k hl W _ _ _).symm (scalarHom l L k hl W F j X Y) =
        ν.inv.app ((hom l L k hl W).obj (op X, Y), X) ≫
          V.map (evaluation l L k hl W X Y) :=
    (transpose l F k hl W _ _ _).symm_apply_apply _
  have beta'' (X Y : sfIntegralConstructibleCategory l E W) :
      (transpose l F k hl W _ _ _).symm (scalarHom l E k hl W F (j.comp ι) X Y) =
        ξ.inv.app ((hom l E k hl W).obj (op X, Y), X) ≫
          Z.map (evaluation l E k hl W X Y) :=
    (transpose l F k hl W _ _ _).symm_apply_apply _
  have he : (transpose l F k hl W _ _ _).symm
      (V.map (scalarHom l E k hl W L ι P Q) ≫
        scalarHom l L k hl W F j (U.obj P) (U.obj Q)) =
      ν.inv.app (U.obj ((hom l E k hl W).obj (op P, Q)), U.obj P) ≫
        V.map (μ.inv.app ((hom l E k hl W).obj (op P, Q), P)) ≫
        V.map (U.map (evaluation l E k hl W P Q)) := by
    rw [inverse_transpose_pre, beta']
    have hn := ν.inv.naturality
      (Prod.mkHom (scalarHom l E k hl W L ι P Q) (𝟙 (U.obj P)))
    dsimp only [Functor.comp_map, Functor.prod_map] at hn
    rw [V.map_id] at hn
    rw [← Category.assoc, hn, Category.assoc, ← V.map_comp]
    rw [← inverse_transpose, beta, V.map_comp]
  apply (transpose l F k hl W _ _ _).symm.injective
  rw [← Category.assoc, inverse_transpose_post, he, inverse_transpose_pre, beta'']
  have hn := α.hom.naturality (evaluation l E k hl W P Q)
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [hn, reassoc_of% hi ((hom l E k hl W).obj (op P, Q)) P]
  rw [← Category.assoc, ← Functor.map_comp]
  congr 2
  ext <;> simp [α]

/-- The identity comparison is the canonical scalar unit on Hom.
Source: node proof Step 9; Stacks 08J9
(blueprint: lem-per-adic-closed-constructible).

Proof: uncurry after the scalar unit identifications. On representatives both maps
send (h,p) to h(p). The normalized tensor comparison and completion preserve this
identity, so injectivity of transposition proves the equation. -/
theorem scalar_identity (P Q : sfIntegralConstructibleCategory l E W) :
    scalarHom l E k hl W E (AlgHom.id ℚ_[l] E) P Q ≫
      (hom l E k hl W).map (Prod.mkHom
        (((sfIntegralScalarUnit l E W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime))).inv.app P).op)
        ((sfIntegralScalarUnit l E W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app Q)) =
      (sfIntegralScalarUnit l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app
        ((hom l E k hl W).obj (op P, Q)) := by
  let T := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E E (AlgHom.id ℚ_[l] E) W
  let e := sfIntegralScalarUnit l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
  let H := hom l E k hl W
  let α : H ⋙ T ≅ T.op.prod T ⋙ H := NatIso.ofComponents
    (fun X ↦ by
      let := scalarHom_isIso l E k hl W E (AlgHom.id ℚ_[l] E) X.1.unop X.2
      exact asIso (scalarHom l E k hl W E (AlgHom.id ℚ_[l] E) X.1.unop X.2))
    (by
      intro X Y f
      exact scalarHom_naturality l E k hl W E (AlgHom.id ℚ_[l] E)
        X.1.unop X.2 Y.1.unop Y.2 f.1.unop f.2)
  have hc (K : sfIntegralConstructibleCategory l E W) :
      (sfIntegralScalarComp l E E (AlgHom.id ℚ_[l] E) W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E (AlgHom.id ℚ_[l] E)).app K =
        e.app (T.obj K) :=
    Iso.ext (integral_target_unit l E E (AlgHom.id ℚ_[l] E) W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) K)
  have hch (K : sfIntegralConstructibleCategory l E W) :
      (sfIntegralScalarComp l E E (AlgHom.id ℚ_[l] E) W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E (AlgHom.id ℚ_[l] E)).hom.app K =
        e.hom.app (T.obj K) := congrArg Iso.hom (hc K)
  have hci (K : sfIntegralConstructibleCategory l E W) :
      (sfIntegralScalarComp l E E (AlgHom.id ℚ_[l] E) W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E (AlgHom.id ℚ_[l] E)).inv.app K =
        e.inv.app (T.obj K) := congrArg Iso.inv (hc K)
  have ht : ∀ X, T.map (α.hom.app X) ≫ α.hom.app ((T.op.prod T).obj X) ≫
      H.map ((NatIso.prod (NatIso.op e.symm) e).hom.app ((T.op.prod T).obj X)) =
        e.hom.app (T.obj (H.obj X)) ≫ α.hom.app X := by
    rintro ⟨U, V⟩
    have h := scalar_tower l E k hl W E (AlgHom.id ℚ_[l] E)
      E (AlgHom.id ℚ_[l] E) U.unop V
    change T.map (scalarHom l E k hl W E (AlgHom.id ℚ_[l] E) U.unop V) ≫
        scalarHom l E k hl W E (AlgHom.id ℚ_[l] E) (T.obj U.unop) (T.obj V) ≫
        H.map (Prod.mkHom (e.inv.app (T.obj U.unop)).op (e.hom.app (T.obj V))) =
      e.hom.app (T.obj (H.obj (U, V))) ≫
        scalarHom l E k hl W E (AlgHom.id ℚ_[l] E) U.unop V
    simpa only [AlgHom.comp_id, hch, hci] using h
  have h := unit_of_idempotent H (T.op.prod T) T
    (NatIso.prod (NatIso.op e.symm) e) e α ht (op P, Q)
  have h' : α.hom.app (op P, Q) ≫
      H.map ((NatIso.prod (NatIso.op e.symm) e).hom.app (op P, Q)) =
        e.hom.app (H.obj (op P, Q)) := by
    rw [← cancel_epi (e.inv.app (H.obj (op P, Q)))]
    rw [← Category.assoc, h, ← H.map_comp]
    simp
  exact h'

end Scalar
end WeilConjectures.AdicClosed
