/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientSiteHomArrow
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomIntrinsicTensorComposition
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomDomainCalculus
import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescentData
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorAmplitude
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomSiteTensorNaturalEquality
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomSiteHomInvertible
import all WeilConjectures.CategoryTheory.Ringed.RingedScalarTensorMonoidal
import all WeilConjectures.SixFunctors.Finite.Hom.FiniteHomTensorAssociatorModel
public import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomEtaleIso
public import WeilConjectures.SixFunctors.FiniteHomSiteTensorNaturalEqualityLegacy

/-! # Finite coefficient change for internal Hom

Source: blueprint sec-six-functors/sk-prop-sf-biduality-general,
node thm-coef-finite-hom (blueprint: thm-coef-finite-hom).
Indices n and m below denote exponents n + 1 and m + 1; thus every positive
exponent, including the identity quotient, occurs. All comparison maps are
closed transposes of reduced evaluation, never choices of arbitrary arrows.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a b w c d e f g v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- Evaluation identity and uniqueness of its transpose, for the actual base-change arrow.
Source: blueprint evaluation paragraph (blueprint: thm-coef-finite-hom). -/
def FiniteHomEvaluation
    {A : Type a} {B : Type a} [Category.{b} A] [Category.{b} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) : Prop :=
  ∀ K M : A,
    SB.tensor.map (Prod.mkHom (coefficientBaseChangeHom SA SB F μ K M) (𝟙 (F.obj K))) ≫
        SB.evaluation (F.obj K) (F.obj M) =
      μ.inv.app (HA.obj (op K, M), K) ≫ F.map (SA.evaluation K M) ∧
    ∀ v : F.obj (HA.obj (op K, M)) ⟶ HB.obj (op (F.obj K), F.obj M),
      SB.tensor.map (Prod.mkHom v (𝟙 (F.obj K))) ≫
          SB.evaluation (F.obj K) (F.obj M) =
        μ.inv.app (HA.obj (op K, M), K) ≫ F.map (SA.evaluation K M) →
      v = coefficientBaseChangeHom SA SB F μ K M

/-- Coherence under composition of coefficient functors, with all three canonical arrows.
Source: blueprint displayed A to B to C equation (blueprint: thm-coef-finite-hom). -/
def FiniteHomQuotientCocycleAux
    {A B C : Type a} [Category.{b} A] [Category.{b} B] [Category.{b} C]
    (HA : Aᵒᵖ × A ⥤ A) (HB : Bᵒᵖ × B ⥤ B) (HC : Cᵒᵖ × C ⥤ C)
    (F : A ⥤ B) (G : B ⥤ C) (J : A ⥤ C) (α : F ⋙ G ≅ J)
    (v : ∀ K M : A, F.obj (HA.obj (op K, M)) ⟶ HB.obj (op (F.obj K), F.obj M))
    (w : ∀ K M : B, G.obj (HB.obj (op K, M)) ⟶ HC.obj (op (G.obj K), G.obj M))
    (z : ∀ K M : A, J.obj (HA.obj (op K, M)) ⟶ HC.obj (op (J.obj K), J.obj M)) : Prop :=
  ∀ K M : A, α.hom.app (HA.obj (op K, M)) ≫ z K M =
    G.map (v K M) ≫ w (F.obj K) (F.obj M) ≫
      HC.map (Prod.mkHom (α.inv.app K).op (α.hom.app M))

/-- The intrinsic quotient cocycle, including both input associators and the Hom associator.
Source: blueprint displayed A to B to C equation (blueprint: thm-coef-finite-hom). -/
structure FiniteHomIntrinsicCocycle {n m : ℕ} (h : m ≤ n) : Prop where
  coherence : ∀ (r : ℕ) (k : r ≤ m), FiniteHomQuotientCocycleAux
    (coefficientFiniteInternalHom l E X n) (coefficientFiniteInternalHom l E X m)
    (coefficientFiniteInternalHom l E X r)
    (coefficientFiniteQuotientDerived l E X h) (coefficientFiniteQuotientDerived l E X k)
    (coefficientFiniteQuotientDerived l E X (k.trans h)) (finiteHomIntrinsicAssoc l E X h k)
    (proEtaleFiniteHomCanonical l E X h) (proEtaleFiniteHomCanonical l E X k)
    (proEtaleFiniteHomCanonical l E X (k.trans h))

/-- The cocycle for canonical transposes, with the quotient diagram's data shared.
Source: blueprint A to B to C equation (blueprint: thm-coef-finite-hom). -/
def FiniteHomQuotientClosedData.Cocycle
    {C : ℕ → Type a} [∀ n : ℕ, Category.{b} (C n)]
    {H : ∀ n : ℕ, (C n)ᵒᵖ × C n ⥤ C n}
    {F : ∀ {n m : ℕ}, m ≤ n → C n ⥤ C m}
    (S : FiniteHomQuotientClosedData C H F)
    (α : ∀ {n m r : ℕ} (h : m ≤ n) (k : r ≤ m), F h ⋙ F k ≅ F (k.trans h))
    {n m : ℕ} (h : m ≤ n) : Prop :=
  ∀ (r : ℕ) (k : r ≤ m), FiniteHomQuotientCocycleAux (H n) (H m) (H r)
    (F h) (F k) (F (k.trans h)) (α h k)
    (S.comparison h) (S.comparison k) (S.comparison (k.trans h))

/-- The etale quotient cocycle with the canonical input identifications.
Source: blueprint displayed A to B to C equation (blueprint: thm-coef-finite-hom). -/
def FiniteHomEtaleCocycle {n m : ℕ} (h : m ≤ n) : Prop :=
  (finiteHomEtaleData l E X).Cocycle (finiteHomEtaleAssoc l E X) h

/-- The coefficient-change square under site comparison, expressed with shared functors.
Source: blueprint final site-comparison sentence (blueprint: thm-coef-finite-hom). -/
def FiniteHomSiteSquareAux
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{e} A] [Category.{f} B] [Category.{g} C] [Category.{w} D]
    (HA : Aᵒᵖ × A ⥤ A) (HB : Bᵒᵖ × B ⥤ B)
    (HC : Cᵒᵖ × C ⥤ C) (HD : Dᵒᵖ × D ⥤ D)
    (F : A ⥤ B) (G : C ⥤ D) (U : A ⥤ C) (V : B ⥤ D)
    (β : U ⋙ G ⟶ F ⋙ V) [IsIso β]
    (v : ∀ K M : A, F.obj (HA.obj (op K, M)) ⟶ HB.obj (op (F.obj K), F.obj M))
    (w : ∀ K M : C, G.obj (HC.obj (op K, M)) ⟶ HD.obj (op (G.obj K), G.obj M))
    (s : ∀ K M : A, U.obj (HA.obj (op K, M)) ⟶ HC.obj (op (U.obj K), U.obj M))
    (t : ∀ K M : B, V.obj (HB.obj (op K, M)) ⟶ HD.obj (op (V.obj K), V.obj M)) : Prop :=
  ∀ K M : A, β.app (HA.obj (op K, M)) ≫ V.map (v K M) ≫ t (F.obj K) (F.obj M) =
    G.map (s K M) ≫ w (U.obj K) (U.obj M) ≫
      HD.map (Prod.mkHom (inv (β.app K)).op (β.app M))

/-- The beta/nu_X^* square for the two evaluation-defined finite comparisons.
The inverse beta in the contravariant input is essential.
Source: blueprint final site-comparison sentence (blueprint: thm-coef-finite-hom). -/
structure FiniteHomSiteFormula {n m : ℕ} (h : m ≤ n) : Prop where
  square : FiniteHomSiteSquareAux (finiteHomEtaleInternalHom l E X n)
    (finiteHomEtaleInternalHom l E X m)
    (coefficientFiniteInternalHom l E X n) (coefficientFiniteInternalHom l E X m)
    (finiteHomEtaleReduction l E X h) (coefficientFiniteQuotientDerived l E X h)
    (finiteHomNu l E X n) (finiteHomNu l E X m) (finiteHomSiteBeta l E X h)
    (etaleFiniteHomCanonical l E X h) (proEtaleFiniteHomCanonical l E X h)
    (finiteHomSiteHom l E X n) (finiteHomSiteHom l E X m)

private theorem finiteChange_pro_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) {n m : ℕ} (h : m ≤ n)
    (K M : normalizedDVRDerived l E X n) :
    proEtaleFiniteHomCanonical l E X h K M =
      coefficientBaseChangeHom (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
        (coefficientFiniteQuotientDerived l E X h) (coefFiniteHomProTensor l E X h) K M := by
  rfl

attribute [local implicit_reducible]
  CategoryTheory.uniformProd CategoryTheory.prod CategoryTheory.prod'
  CategoryTheory.catToReflQuiver CoefficientClosedStructure.tensor

attribute [local instance] finiteChange_isIso_prod

private theorem finiteChangeEvaluation_naturality
    {C : Type a} [Category.{c} C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) (K K' M M' : C) (f : K' ⟶ K) (g : M ⟶ M') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 K')) ≫
      S.evaluation K' M' =
    S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K, M))) f) ≫ S.evaluation K M ≫ g := by
  let := S.monoidal
  have hf : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 M))) (𝟙 K')) ≫
      S.evaluation K' M =
      S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K, M))) f) ≫ S.evaluation K M := by
    change S.monoidal.tensorHom (H.map (Prod.mkHom f.op (𝟙 M))) (𝟙 K') ≫ _ =
      S.monoidal.tensorHom (𝟙 (H.obj (op K, M))) f ≫ _
    rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
    exact S.evaluation_naturality K K' M f
  have hg : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op K')) g)) (𝟙 K')) ≫
      S.evaluation K' M' = S.evaluation K' M ≫ g := by
    change S.monoidal.tensorHom (H.map (Prod.mkHom (𝟙 (op K')) g)) (𝟙 K') ≫ _ = _
    rw [MonoidalCategory.tensorHom_id]
    exact (S.adjunction K').counit.naturality g
  have hh : Prod.mkHom f.op g =
      Prod.mkHom f.op (𝟙 M) ≫ Prod.mkHom (𝟙 (op K')) g := by
    ext <;> simp only [prod_comp_fst, prod_comp_snd, Category.comp_id, Category.id_comp]
  rw [hh, H.map_comp]
  have ht : Prod.mkHom
      (H.map (Prod.mkHom f.op (𝟙 M)) ≫ H.map (Prod.mkHom (𝟙 (op K')) g)) (𝟙 K') =
      Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 M))) (𝟙 K') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (op K')) g)) (𝟙 K') := by
    ext <;> simp only [prod_comp_fst, prod_comp_snd, Category.comp_id]
  rw [ht, S.tensor.map_comp, Category.assoc, hg, ← Category.assoc, hf, Category.assoc]

private theorem finiteChangeUncurry
    {D : Type*} [Category.{c} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (T P Q : D) (h : T ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm h =
      S.tensor.map (Prod.mkHom h (𝟙 P)) ≫ S.evaluation P Q := by
  let := S.monoidal
  simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    CoefficientClosedStructure.evaluation] using! (S.adjunction P).homEquiv_counit T Q h

private theorem finiteChangeTensor_comp
    {D : Type*} [Category.{c} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {X Y Z U V W : D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : U ⟶ V) (k : V ⟶ W) :
    S.tensor.map (Prod.mkHom (f ≫ g) (h ≫ k)) =
      S.tensor.map (Prod.mkHom f h) ≫ S.tensor.map (Prod.mkHom g k) :=
  S.tensor.map_comp (Prod.mkHom f h) (Prod.mkHom g k)

private theorem finiteChangeUncurry_pre
    {D : Type*} [Category.{c} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {T U P Q : D}
    (f : T ⟶ U) (h : U ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm (f ≫ h) =
      S.tensor.map (Prod.mkHom f (𝟙 P)) ≫ (S.transpose U P Q).symm h := by
  rw [finiteChangeUncurry, finiteChangeUncurry]
  simpa only [Category.id_comp, Category.assoc] using
    congrArg (fun k => k ≫ S.evaluation P Q) (finiteChangeTensor_comp S f h (𝟙 P) (𝟙 P))

private theorem finiteChangeUncurry_post
    {D : Type*} [Category.{c} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {T P Q P' Q' : D}
    (h : T ⟶ H.obj (op P, Q)) (f : P' ⟶ P) (g : Q ⟶ Q') :
    (S.transpose T P' Q').symm (h ≫ H.map (Prod.mkHom f.op g)) =
      S.tensor.map (Prod.mkHom (𝟙 T) f) ≫ (S.transpose T P Q).symm h ≫ g := by
  rw [finiteChangeUncurry_pre, finiteChangeUncurry, finiteChangeEvaluation_naturality]
  rw [finiteChangeUncurry]
  simp only [← Category.assoc, ← S.tensor.map_comp]
  congr 2
  congr 1
  ext <;> simp

private theorem finiteChangeBaseChangeHom_beta
    {A : Type*} {B : Type*} [Category.{c} A] [Category.{d} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) (P Q : A) :
    (SB.transpose _ (F.obj P) (F.obj Q)).symm (coefficientBaseChangeHom SA SB F μ P Q) =
      μ.inv.app (HA.obj (op P, Q), P) ≫ F.map (SA.evaluation P Q) :=
  Equiv.symm_apply_apply _ _

private theorem finiteChangeBaseChangeHom_tower
    {A : Type a} {B : Type b} {D : Type c}
    [Category.{d} A] [Category.{e} B] [Category.{f} D]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B} {HD : Dᵒᵖ × D ⥤ D}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (SD : CoefficientClosedStructure HD) (F : A ⥤ B) (G : B ⥤ D) (K : A ⥤ D)
    (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (ν : SB.tensor ⋙ G ≅ G.prod G ⋙ SD.tensor)
    (ξ : SA.tensor ⋙ K ≅ K.prod K ⋙ SD.tensor) (α : F ⋙ G ≅ K)
    (ht : ∀ X Y : A,
      G.map (μ.hom.app (X, Y)) ≫ ν.hom.app (F.obj X, F.obj Y) ≫
          SD.tensor.map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) =
        α.hom.app (SA.tensor.obj (X, Y)) ≫ ξ.hom.app (X, Y)) (P Q : A) :
    G.map (coefficientBaseChangeHom SA SB F μ P Q) ≫
        coefficientBaseChangeHom SB SD G ν (F.obj P) (F.obj Q) ≫
        HD.map (Prod.mkHom (α.inv.app P).op (α.hom.app Q)) =
      α.hom.app (HA.obj (op P, Q)) ≫ coefficientBaseChangeHom SA SD K ξ P Q := by
  have hi (X Y : A) :
      ν.inv.app (F.obj X, F.obj Y) ≫ G.map (μ.inv.app (X, Y)) ≫
          α.hom.app (SA.tensor.obj (X, Y)) =
        SD.tensor.map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) ≫ ξ.inv.app (X, Y) := by
    apply (cancel_mono (ξ.hom.app (X, Y))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← ht]
    simp [← G.map_comp, ← Category.assoc]
  have he : (SD.transpose _ (G.obj (F.obj P)) (G.obj (F.obj Q))).symm
      (G.map (coefficientBaseChangeHom SA SB F μ P Q) ≫
        coefficientBaseChangeHom SB SD G ν (F.obj P) (F.obj Q)) =
      ν.inv.app (F.obj (HA.obj (op P, Q)), F.obj P) ≫
        G.map (μ.inv.app (HA.obj (op P, Q), P)) ≫ G.map (F.map (SA.evaluation P Q)) := by
    rw [finiteChangeUncurry_pre, finiteChangeBaseChangeHom_beta]
    have hn := ν.inv.naturality
      (Prod.mkHom (coefficientBaseChangeHom SA SB F μ P Q) (𝟙 (F.obj P)))
    dsimp only [Functor.comp_map, Functor.prod_map] at hn
    erw [G.map_id] at hn
    rw [← Category.assoc, hn, Category.assoc, ← G.map_comp]
    rw [← finiteChangeUncurry, finiteChangeBaseChangeHom_beta, G.map_comp]
  apply (SD.transpose _ (K.obj P) (K.obj Q)).symm.injective
  rw [← Category.assoc, finiteChangeUncurry_post, he, finiteChangeUncurry_pre,
    finiteChangeBaseChangeHom_beta]
  have hn := α.hom.naturality (SA.evaluation P Q)
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [hn, reassoc_of% hi (HA.obj (op P, Q)) P]
  rw [← Category.assoc, ← SD.tensor.map_comp]
  congr 2
  ext <;> simp

private def finiteChangeCompositeTensor
    {A : Type a} {B : Type b} {D : Type c}
    [Category.{d} A] [Category.{e} B] [Category.{f} D]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B} {HD : Dᵒᵖ × D ⥤ D}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (SD : CoefficientClosedStructure HD) (F : A ⥤ B) (G : B ⥤ D)
    (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (ν : SB.tensor ⋙ G ≅ G.prod G ⋙ SD.tensor) :
    SA.tensor ⋙ (F ⋙ G) ≅ (F ⋙ G).prod (F ⋙ G) ⋙ SD.tensor :=
  NatIso.ofComponents
    (fun X ↦ G.mapIso (μ.app X) ≪≫ ν.app (F.obj X.1, F.obj X.2)) (by
      intro X Y z
      have hμ := μ.hom.naturality z
      have hν := ν.hom.naturality ((F.prod F).map z)
      dsimp only [Functor.comp_map, Functor.prod_map, Iso.trans_hom, Functor.mapIso_hom]
      dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj] at hμ hν
      simp only [Iso.app_hom]
      rw [← Category.assoc, ← G.map_comp, hμ, G.map_comp, Category.assoc, hν, Category.assoc])

private theorem finiteChangeCompositeHom
    {A : Type a} {B : Type b} {D : Type c}
    [Category.{d} A] [Category.{e} B] [Category.{f} D]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B} {HD : Dᵒᵖ × D ⥤ D}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (SD : CoefficientClosedStructure HD) (F : A ⥤ B) (G : B ⥤ D)
    (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (ν : SB.tensor ⋙ G ≅ G.prod G ⋙ SD.tensor) (P Q : A) :
    G.map (coefficientBaseChangeHom SA SB F μ P Q) ≫
        coefficientBaseChangeHom SB SD G ν (F.obj P) (F.obj Q) =
      coefficientBaseChangeHom SA SD (F ⋙ G)
        (finiteChangeCompositeTensor SA SB SD F G μ ν) P Q := by
  have hh := finiteChangeBaseChangeHom_tower SA SB SD F G (F ⋙ G) μ ν
      (finiteChangeCompositeTensor SA SB SD F G μ ν) (Iso.refl _) (by
        intro X Y
        simp only [Iso.refl_hom, NatTrans.id_app, ← prod_id, Category.id_comp]
        erw [SD.tensor.map_id, Category.comp_id]
        rfl) P Q
  simp only [Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp,
    op_id, ← prod_id] at hh
  erw [HD.map_id, Category.comp_id] at hh
  exact hh

/-- The forward Hom square is the transpose tower for the two composite routes. -/
private theorem finiteChange_forwardSquare
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{e} A] [Category.{f} B] [Category.{g} C] [Category.{w} D]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    {HC : Cᵒᵖ × C ⥤ C} {HD : Dᵒᵖ × D ⥤ D}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (SC : CoefficientClosedStructure HC) (SD : CoefficientClosedStructure HD)
    (F : A ⥤ B) (G : C ⥤ D) (U : A ⥤ C) (V : B ⥤ D)
    (μF : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (μG : SC.tensor ⋙ G ≅ G.prod G ⋙ SD.tensor)
    (μU : SA.tensor ⋙ U ≅ U.prod U ⋙ SC.tensor)
    (μV : SB.tensor ⋙ V ≅ V.prod V ⋙ SD.tensor)
    (h : F ⋙ V ≅ U ⋙ G)
    (ht : ∀ K M : A,
      h.hom.app (SA.tensor.obj (K, M)) ≫ G.map (μU.hom.app (K, M)) ≫
          μG.hom.app (U.obj K, U.obj M) =
        V.map (μF.hom.app (K, M)) ≫ μV.hom.app (F.obj K, F.obj M) ≫
          SD.tensor.map (Prod.mkHom (h.hom.app K) (h.hom.app M))) (P Q : A) :
    h.hom.app (HA.obj (op P, Q)) ≫
        G.map (coefficientBaseChangeHom SA SC U μU P Q) ≫
        coefficientBaseChangeHom SC SD G μG (U.obj P) (U.obj Q) =
      V.map (coefficientBaseChangeHom SA SB F μF P Q) ≫
        coefficientBaseChangeHom SB SD V μV (F.obj P) (F.obj Q) ≫
        HD.map (Prod.mkHom (h.inv.app P).op (h.hom.app Q)) := by
  have hh := finiteChangeBaseChangeHom_tower SA SB SD F V (U ⋙ G) μF μV
    (finiteChangeCompositeTensor SA SC SD U G μU μG) h (by
      intro K M
      exact (ht K M).symm) P Q
  rw [← finiteChangeCompositeHom SA SC SD U G μU μG P Q] at hh
  exact hh.symm

private theorem finiteChange_square
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{e} A] [Category.{f} B] [Category.{g} C] [Category.{w} D]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    {HC : Cᵒᵖ × C ⥤ C} {HD : Dᵒᵖ × D ⥤ D}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (SC : CoefficientClosedStructure HC) (SD : CoefficientClosedStructure HD)
    (F : A ⥤ B) (G : C ⥤ D) (U : A ⥤ C) (V : B ⥤ D)
    (μF : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (μG : SC.tensor ⋙ G ≅ G.prod G ⋙ SD.tensor)
    (μU : SA.tensor ⋙ U ≅ U.prod U ⋙ SC.tensor)
    (μV : SB.tensor ⋙ V ≅ V.prod V ⋙ SD.tensor)
    (h : F ⋙ V ≅ U ⋙ G)
    (ht : ∀ K M : A,
      h.hom.app (SA.tensor.obj (K, M)) ≫ G.map (μU.hom.app (K, M)) ≫
          μG.hom.app (U.obj K, U.obj M) =
        V.map (μF.hom.app (K, M)) ≫ μV.hom.app (F.obj K, F.obj M) ≫
          SD.tensor.map (Prod.mkHom (h.hom.app K) (h.hom.app M))) (P Q : A) :
    h.inv.app (HA.obj (op P, Q)) ≫
        V.map (coefficientBaseChangeHom SA SB F μF P Q) ≫
        coefficientBaseChangeHom SB SD V μV (F.obj P) (F.obj Q) =
      G.map (coefficientBaseChangeHom SA SC U μU P Q) ≫
        coefficientBaseChangeHom SC SD G μG (U.obj P) (U.obj Q) ≫
        HD.map (Prod.mkHom (h.hom.app P).op (h.inv.app Q)) := by
  have hh := finiteChange_forwardSquare SA SB SC SD F G U V μF μG μU μV h ht P Q
  have he := congrArg (fun z ↦ h.inv.app (HA.obj (op P, Q)) ≫ z ≫
    HD.map (Prod.mkHom (h.hom.app P).op (h.inv.app Q))) hh
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← HD.map_comp,
    prod_comp, ← op_comp, Iso.hom_inv_id_app, op_id, ← prod_id] at he
  erw [HD.map_id, Category.comp_id] at he
  exact he.symm

/-- Evaluation and uniqueness follow directly from the closed adjunction. -/
private theorem finiteHomEvaluation_of_transpose
    {A B : Type a} [Category.{c} A] [Category.{c} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) :
    FiniteHomEvaluation SA SB F μ := by
  intro K M
  have hu (v : F.obj (HA.obj (op K, M)) ⟶ HB.obj (op (F.obj K), F.obj M)) :
      (SB.transpose _ (F.obj K) (F.obj M)).symm v =
        SB.tensor.map (Prod.mkHom v (𝟙 (F.obj K))) ≫
          SB.evaluation (F.obj K) (F.obj M) := by
    simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
      CoefficientClosedStructure.evaluation] using!
      (SB.adjunction (F.obj K)).homEquiv_counit _ (F.obj M) v
  constructor
  · rw [← hu, coefficientBaseChangeHom, Equiv.symm_apply_apply]
  · intro v hv
    apply (SB.transpose _ (F.obj K) (F.obj M)).symm.injective
    rw [hu, hv, coefficientBaseChangeHom, Equiv.symm_apply_apply]

private theorem finiteChange_natural
    {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (K K' M M' : A) (f : K' ⟶ K) (g : M ⟶ M') :
    F.map (HA.map (Prod.mkHom f.op g)) ≫ coefficientBaseChangeHom SA SB F μ K' M' =
      coefficientBaseChangeHom SA SB F μ K M ≫
        HB.map (Prod.mkHom (F.map f).op (F.map g)) := by
  apply (SB.transpose (F.obj (HA.obj (op K, M))) (F.obj K') (F.obj M')).symm.injective
  rw [finiteChangeUncurry_pre, finiteChangeUncurry_post]
  simp only [finiteChangeBaseChangeHom_beta]
  have hμ₁ := μ.inv.naturality
    (Prod.mkHom (HA.map (Prod.mkHom f.op g)) (𝟙 K'))
  have hμ₂ := μ.inv.naturality (Prod.mkHom (𝟙 (HA.obj (op K, M))) f)
  simp only [Functor.comp_map, Functor.prod_map, F.map_id] at hμ₁ hμ₂
  rw [← Category.assoc, hμ₁, Category.assoc, ← F.map_comp,
    finiteChangeEvaluation_naturality SA, F.map_comp, F.map_comp, ← Category.assoc,
    ← Category.assoc, ← hμ₂]
  simp only [Category.assoc]

private theorem finiteChange_transpose
    {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (T K M : A) (f : SA.tensor.obj (T, K) ⟶ M) :
    F.map (SA.transpose T K M f) ≫ coefficientBaseChangeHom SA SB F μ K M =
      SB.transpose (F.obj T) (F.obj K) (F.obj M) (μ.inv.app (T, K) ≫ F.map f) := by
  apply (SB.transpose (F.obj T) (F.obj K) (F.obj M)).symm.injective
  rw [finiteChangeUncurry_pre, finiteChangeBaseChangeHom_beta, Equiv.symm_apply_apply]
  have hn := μ.inv.naturality (Prod.mkHom (SA.transpose T K M f) (𝟙 K))
  simp only [Functor.comp_map, Functor.prod_map, F.map_id] at hn
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp, ← finiteChangeUncurry,
    Equiv.symm_apply_apply]

private theorem finiteChange_composition
    {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (s : CoefFiniteHomStrong SA SB F μ) (P Q V : A) :
    F.map (SA.composition P Q V) ≫ coefficientBaseChangeHom SA SB F μ P V =
      μ.hom.app (HA.obj (op Q, V), HA.obj (op P, Q)) ≫
        SB.tensor.map (Prod.mkHom (coefficientBaseChangeHom SA SB F μ Q V)
          (coefficientBaseChangeHom SA SB F μ P Q)) ≫
        SB.composition (F.obj P) (F.obj Q) (F.obj V) := by
  let := SA.monoidal
  let := SB.monoidal
  let := s.val.toMonoidal
  have hμ (X Y : A) : Functor.LaxMonoidal.μ F X Y = μ.inv.app (X, Y) := by
    change (s.val.μIso X Y).hom = _
    rw [s.property]
    rfl
  have hAssoc (X Y Z : A) :
      SB.tensor.map (Prod.mkHom (μ.inv.app (X, Y)) (𝟙 (F.obj Z))) ≫
        μ.inv.app (SA.tensor.obj (X, Y), Z) ≫
          F.map (SA.monoidal.associator X Y Z).hom =
      (SB.monoidal.associator (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
        SB.tensor.map (Prod.mkHom (𝟙 (F.obj X)) (μ.inv.app (Y, Z))) ≫
          μ.inv.app (X, SA.tensor.obj (Y, Z)) := by
    simpa only [← hμ, CoefficientClosedStructure.tensor, Functor.comp_obj,
      Functor.prod_obj, tensor_obj, tensor_map, MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_tensorHom] using
      Functor.LaxMonoidal.associativity F X Y Z
  apply (cancel_epi (μ.inv.app (HA.obj (op Q, V), HA.obj (op P, Q)))).1
  simp only [Iso.inv_hom_id_app_assoc]
  apply (SB.transpose _ (F.obj P) (F.obj V)).symm.injective
  rw [finiteChangeUncurry_pre, finiteChangeUncurry_pre, finiteChangeBaseChangeHom_beta,
    finiteChangeUncurry_pre]
  have hn := μ.inv.naturality (Prod.mkHom (SA.composition P Q V) (𝟙 P))
  simp only [Functor.comp_map, Functor.prod_map, F.map_id] at hn
  rw [reassoc_of% hn, ← F.map_comp, ← finiteChangeUncurry]
  simp only [CoefficientClosedStructure.composition, Equiv.symm_apply_apply, F.map_comp]
  rw [reassoc_of% hAssoc]
  have hn' := μ.inv.naturality
    (Prod.mkHom (𝟙 (HA.obj (op Q, V))) (SA.evaluation P Q))
  simp only [Functor.comp_map, Functor.prod_map, F.map_id] at hn'
  rw [← reassoc_of% hn']
  have hβ (X Y : A) :
      SB.tensor.map (Prod.mkHom (coefficientBaseChangeHom SA SB F μ X Y)
          (𝟙 (F.obj X))) ≫ SB.evaluation (F.obj X) (F.obj Y) =
        μ.inv.app (HA.obj (op X, Y), X) ≫ F.map (SA.evaluation X Y) := by
    rw [← finiteChangeUncurry, finiteChangeBaseChangeHom_beta]
  let v := coefficientBaseChangeHom SA SB F μ
  have hn'' :
      SB.tensor.map (Prod.mkHom (SB.tensor.map (Prod.mkHom (v Q V) (v P Q)))
          (𝟙 (F.obj P))) ≫
        (SB.monoidal.associator (HB.obj (op (F.obj Q), F.obj V))
          (HB.obj (op (F.obj P), F.obj Q)) (F.obj P)).hom =
      (SB.monoidal.associator (F.obj (HA.obj (op Q, V)))
          (F.obj (HA.obj (op P, Q))) (F.obj P)).hom ≫
        SB.tensor.map (Prod.mkHom (v Q V)
          (SB.tensor.map (Prod.mkHom (v P Q) (𝟙 (F.obj P))))) := by
    simpa only [CoefficientClosedStructure.tensor, tensor_map] using
      MonoidalCategory.associator_naturality (v Q V) (v P Q) (𝟙 (F.obj P))
  rw [reassoc_of% hn'']
  have hex :
      SB.tensor.map (Prod.mkHom (v Q V)
          (SB.tensor.map (Prod.mkHom (v P Q) (𝟙 (F.obj P))))) ≫
        SB.tensor.map (Prod.mkHom (𝟙 (HB.obj (op (F.obj Q), F.obj V)))
          (SB.evaluation (F.obj P) (F.obj Q))) =
      SB.tensor.map (Prod.mkHom (𝟙 (F.obj (HA.obj (op Q, V))))
          (SB.tensor.map (Prod.mkHom (v P Q) (𝟙 (F.obj P))) ≫
            SB.evaluation (F.obj P) (F.obj Q))) ≫
        SB.tensor.map (Prod.mkHom (v Q V) (𝟙 (F.obj Q))) := by
    simp only [← SB.tensor.map_comp]
    congr 1
    ext <;> simp
  rw [reassoc_of% hex, hβ P Q, hβ Q V]
  have hp : Prod.mkHom (𝟙 (F.obj (HA.obj (op Q, V))))
      (μ.inv.app (HA.obj (op P, Q), P) ≫ F.map (SA.evaluation P Q)) =
      Prod.mkHom (𝟙 (F.obj (HA.obj (op Q, V)))) (μ.inv.app (HA.obj (op P, Q), P)) ≫
        Prod.mkHom (𝟙 (F.obj (HA.obj (op Q, V)))) (F.map (SA.evaluation P Q)) := by
    ext <;> simp
  rw [hp, SB.tensor.map_comp]
  simp only [Category.assoc]

private theorem finiteChange_tensor_uncurry {C : Type a} [Category.{b} C]
    [MonoidalCategory C] : tensor C = Functor.uncurry.obj (curriedTensor C) := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro P Q z
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id, tensor_map,
    Functor.uncurry_obj_map, curriedTensor_map_app, curriedTensor_obj_map] using
    (MonoidalCategory.tensorHom_def z.1 z.2)

private theorem finiteChange_closed_tensor {C : Type a} [Category.{b} C]
    {H : Cᵒᵖ × C ⥤ C} (S : CoefficientClosedStructure H) (T : MonoidalCategory C)
    (hT : S.monoidal = T) :
    S.tensor = Functor.uncurry.obj (@curriedTensor C _ T) := by
  let := T
  cases hT
  exact finiteChange_tensor_uncurry

private theorem finiteChange_etale_tensor_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (n : ℕ) :
    (finiteHomEtaleClosed l E X n).tensor =
      Functor.uncurry.obj (Etale.derivedTensor (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X) := by
  have hc := (finiteHomEtaleData_existsUnique l E X).choose_spec.1.closed n
  change HEq (finiteHomEtaleClosed l E X n)
    (finiteHomEtaleClosedGeneral (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X) at hc
  rw [eq_of_heq hc]
  unfold Etale.derivedTensor
  exact finiteChange_closed_tensor _ _
    (finiteHomEtaleClosed_existsUnique _ X).choose_spec.1.1

private theorem finiteChange_etale_tensor_heq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) {n m : ℕ} (h : m ≤ n) :
    HEq (finiteHomEtaleTensor l E X h)
      (Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E h) X) := by
  exact (finiteHomEtaleData_existsUnique l E X).choose_spec.1.tensor n m h

private theorem finiteChange_scalarSquare
    {A : Type a} {B : Type b} {D : Type c}
    [Category.{d} A] [Category.{e} B] [Category.{f} D]
    (T : A × A ⥤ A) (T' : B × B ⥤ B) (T'' : D × D ⥤ D)
    (F : A ⥤ B) (G : B ⥤ D) (J : A ⥤ D) (α : F ⋙ G ≅ J)
    (μ : T ⋙ F ≅ F.prod F ⋙ T') (ν : T' ⋙ G ≅ G.prod G ⋙ T'')
    (ξ : T ⋙ J ≅ J.prod J ⋙ T'')
    {I : A} {I' : B} {I'' : D} {U : Type e} {V W : Type f}
    (e₀ : U) (e₁ : V) (e₂ : W)
    (h : FiniteHomDomainScalarComposition T T' T'' I I' I'' F G J α
      (fun P Q ↦ μ.app (P, Q)) (fun P Q ↦ ν.app (P, Q))
      (fun P Q ↦ ξ.app (P, Q)) e₀ e₁ e₂) :
    ∀ P Q : A,
      G.map (μ.hom.app (P, Q)) ≫ ν.hom.app (F.obj P, F.obj Q) ≫
          T''.map (Prod.mkHom (α.hom.app P) (α.hom.app Q)) =
        α.hom.app (T.obj (P, Q)) ≫ ξ.hom.app (P, Q) := by
  obtain ⟨δ, δ', δ'', ε, ε', ε'', hδ, hδ', hδ'', _, _, _, hc, _⟩ := h
  intro P Q
  have hh := hc P Q
  rw [eq_of_heq (hδ P Q), eq_of_heq (hδ' _ _), eq_of_heq (hδ'' P Q)] at hh
  exact hh.symm

private theorem finiteChange_tensor_coherence
    {A : Type a} {B : Type b} {D : Type c}
    [Category.{d} A] [Category.{e} B] [Category.{f} D]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B} {HD : Dᵒᵖ × D ⥤ D}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (SD : CoefficientClosedStructure HD) (F : A ⥤ B) (G : B ⥤ D) (J : A ⥤ D)
    (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (ν : SB.tensor ⋙ G ≅ G.prod G ⋙ SD.tensor)
    (ξ : SA.tensor ⋙ J ≅ J.prod J ⋙ SD.tensor) (α : F ⋙ G ≅ J)
    (T : A × A ⥤ A) (T' : B × B ⥤ B) (T'' : D × D ⥤ D)
    (hT : SA.tensor = T) (hT' : SB.tensor = T') (hT'' : SD.tensor = T'')
    (μ' : T ⋙ F ≅ F.prod F ⋙ T') (ν' : T' ⋙ G ≅ G.prod G ⋙ T'')
    (ξ' : T ⋙ J ≅ J.prod J ⋙ T'')
    (hμ : HEq μ μ') (hν : HEq ν ν') (hξ : HEq ξ ξ')
    (hc : ∀ X Y : A,
      G.map (μ'.hom.app (X, Y)) ≫ ν'.hom.app (F.obj X, F.obj Y) ≫
          T''.map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) =
        α.hom.app (T.obj (X, Y)) ≫ ξ'.hom.app (X, Y)) :
    ∀ X Y : A,
      G.map (μ.hom.app (X, Y)) ≫ ν.hom.app (F.obj X, F.obj Y) ≫
          SD.tensor.map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) =
        α.hom.app (SA.tensor.obj (X, Y)) ≫ ξ.hom.app (X, Y) := by
  cases hT
  cases hT'
  cases hT''
  cases eq_of_heq hμ
  cases eq_of_heq hν
  cases eq_of_heq hξ
  exact hc

private theorem finiteChange_familyCocycle
    {C : ℕ → Type a} [∀ n : ℕ, Category.{b} (C n)]
    {H : ∀ n : ℕ, (C n)ᵒᵖ × C n ⥤ C n}
    {F : ∀ {n m : ℕ}, m ≤ n → C n ⥤ C m}
    (S : FiniteHomQuotientClosedData C H F)
    (α : ∀ {n m r : ℕ} (h : m ≤ n) (k : r ≤ m), F h ⋙ F k ≅ F (k.trans h))
    (hc : ∀ {n m r : ℕ} (h : m ≤ n) (k : r ≤ m) (P Q : C n),
      (F k).map ((S.tensor h).hom.app (P, Q)) ≫
          (S.tensor k).hom.app ((F h).obj P, (F h).obj Q) ≫
          (S.closed r).tensor.map (Prod.mkHom ((α h k).hom.app P) ((α h k).hom.app Q)) =
        (α h k).hom.app ((S.closed n).tensor.obj (P, Q)) ≫
          (S.tensor (k.trans h)).hom.app (P, Q))
    {n m : ℕ} (h : m ≤ n) : S.Cocycle α h := by
  intro r k K M
  exact (finiteChangeBaseChangeHom_tower (S.closed n) (S.closed m) (S.closed r)
    (F h) (F k) (F (k.trans h)) (S.tensor h) (S.tensor k) (S.tensor (k.trans h))
    (α h k) (hc h k) K M).symm

private theorem finiteChange_compatible
    {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (s : CoefFiniteHomStrong SA SB F μ) : CoefficientEvaluationCompatible SA SB F μ := by
  exact ⟨fun P Q P' Q' f g ↦ finiteChange_natural SA SB F μ P P' Q Q' f g,
    finiteChange_transpose SA SB F μ, finiteChange_composition SA SB F μ s⟩

private theorem finiteHomSupportInterval (Z : ℤ → Prop) (hf : Set.Finite {q | ¬ Z q}) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) → Z q := by
  classical
  obtain ⟨a, ha⟩ := hf.bddBelow
  obtain ⟨b, hb⟩ := hf.bddAbove
  refine ⟨min a b, max a b, min_le_max, ?_⟩
  intro q hq
  by_contra hnz
  rcases hq with hq | hq
  · exact (not_lt_of_ge (ha hnz)) (lt_of_lt_of_le hq (min_le_left _ _))
  · exact (not_lt_of_ge (hb hnz)) (lt_of_le_of_lt (le_max_right _ _) hq)

-- The Tor predicate tests all representatives; conjugating their presentation isomorphism
-- therefore transports the predicate without changing a resolution or tensor calculation.
private theorem finiteHomTorOfIso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {P Q : proEtaleDerivedCategory T A} (e : P ≅ Q) {a b : ℤ}
    (hP : HasProEtaleTorAmplitude T A P a b) : HasProEtaleTorAmplitude T A Q a b := by
  refine ⟨hP.1, ?_⟩
  intro L R hL f hf hR M i hi
  exact hP.2 L R (hL.map (fun eL ↦ eL ≪≫ e.symm)) f hf hR M i hi

/-- Constructible descent component of the finite Hom site descent theorem.
Source: blueprint `lem-coef-finite-hom-site-descent`, proof step 1.
(blueprint: lem-coef-finite-hom-site-descent-core-descent).

Proof: the finite-field characteristic and the structure morphism make l invertible
in every residue field. The intrinsic comparison instances give exactness. Bound the
finite cohomological support of an intrinsic constructible object and apply the
intrinsic finite-ring essential-image criterion to obtain a bounded constructible
etale witness. Its lower bound makes it bounded below, so comparison reflects each
Tor interval, giving finite Tor amplitude of the witness. Comparison preserves each
etale Tor interval as well; transport along the witness isomorphism gives the forward
implication for every witness. Apply preservation to any one interval of an arbitrary
finite-Tor etale input to obtain intrinsic constructibility and finite Tor amplitude,
and apply it separately to each specified interval for the last clause. -/
private theorem finiteChange_siteDescent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    ∀ n : ℕ, CoefFiniteHomDescent l E X n := by
  classical
  let : EssentiallySmall.{u + 1, u, u + 1} X.ProEt :=
    essentiallySmallSelf.{0, u, u + 1} _
  have hunit : IsUnit (l : D.k) := by
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
        (D.card_base.trans D.cardinality_eq))
    let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
    exact (CharP.isUnit_natCast_iff (R := D.k) D.prime).2
      (fun h ↦ _hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 h).symm)
  let residueMap (x : X) : D.k →+* X.residueField x :=
    ((Scheme.ΓSpecIso (.of D.k)).inv ≫
      (X ↘ Spec (.of D.k)).appTop ≫ X.Γevaluation x).hom
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (map_natCast (residueMap x) l) ▸ (hunit.map (residueMap x)).invertible
  intro n
  let := HasDerivedCategory.standard (normalizedDVRModules.{u, u} l E X n)
  let B := Padic.coefficientExtensionRing l E (n + 1)
  have : Finite B := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have hplus (P' : finiteHomEtale l E X n)
      (hP' : coefFiniteHomEtaleConstructible l E X n P') :
      DerivedCategory.TStructure.t.plus P' := by
    obtain ⟨a, b, _, hz⟩ := hP'.2
    exact ⟨a, (DerivedCategory.isGE_iff P' a).mpr (fun q hq ↦ hz q (Or.inl hq))⟩
  have hpres (P' : finiteHomEtale l E X n)
      (hP' : coefFiniteHomEtaleConstructible l E X n P') (a b : ℤ) (hab : a ≤ b)
      (ht : Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1, u} B) X a b P') :=
    finiteCoefficient_comparison_preserves_torAmplitude.{u} D l _hl E (n + 1)
      (Nat.succ_pos n) X a b hab P' hP' ht
  have hrefl (P : normalizedDVRDerived.{u, u} l E X n) (P' : finiteHomEtale l E X n)
      (hP : finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X P)
      (hP' : coefFiniteHomEtaleConstructible l E X n P')
      (e : (finiteHomNu l E X n).obj P' ≅ P) (a b : ℤ)
      (ht : HasProEtaleTorAmplitude X B P a b) :=
    finiteCoefficient_comparison_reflects_torAmplitude.{u} D l _hl E (n + 1)
      (Nat.succ_pos n) X a b P' (hplus P' hP') P hP.1 ht e.symm
  refine ⟨inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro P hP
    have hbound := finiteHomSupportInterval _ hP.1.1
    obtain ⟨P', ⟨e⟩⟩ :=
      ((finiteRing_constructibleDerived_origin.{u} X B).2.2.1 P).mpr ⟨hP.1.2, hbound⟩
    obtain ⟨a, b, ht⟩ := hP.2
    exact ⟨P'.obj, ⟨P'.property, a, b, ht.1,
      hrefl P P'.obj hP P'.property e a b ht⟩, ⟨e⟩⟩
  · intro P P' hP hP' he a b hab
    let e := he.some
    exact ⟨fun ht ↦ finiteHomTorOfIso.{u} X B e (hpres P' hP' a b hab ht).2,
      hrefl P P' hP hP' e a b⟩
  · intro P' hP'
    let a := hP'.2.choose
    let b := hP'.2.choose_spec.choose
    have hab := hP'.2.choose_spec.choose_spec.1
    have ht := hP'.2.choose_spec.choose_spec.2
    have hp := hpres P' hP'.1 a b hab ht
    exact ⟨⟨hp.1, a, b, hp.2⟩, fun a b hab ht ↦ (hpres P' hP'.1 a b hab ht).2⟩

private theorem finiteChange_domainStrong
    {A B : Type _} [Category A] [Category B]
    [mA : MonoidalCategory A] [mB : MonoidalCategory B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (hA : SA.monoidal = mA) (hB : SB.monoidal = mB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (δ : tensor A ⋙ F ≅ F.prod F ⋙ tensor B) {W : Type _} (e : W)
    {BA : A → A → Type _} (σA : ∀ P Q, BA P Q)
    {BB : B → B → Type _} (σB : ∀ P Q, BB P Q)
    (hμ : HEq μ δ)
    (h : FiniteHomDomainMonoidal F (fun P Q ↦ δ.app (P, Q)) e σA σB) :
    Nonempty (CoefFiniteHomStrong SA SB F μ) := by
  cases hA
  cases hB
  let := SA.monoidal
  let := SB.monoidal
  have hμeq : μ = δ := eq_of_heq hμ
  obtain ⟨s, _, ht, _⟩ := h
  refine ⟨⟨s, ?_⟩⟩
  intro P Q
  have he : (s.μIso P Q).symm = μ.app (P, Q) :=
    eq_of_heq ((ht P Q).trans
      (heq_of_eq (congrArg (fun η ↦ η.app (P, Q)) hμeq)).symm)
  exact congrArg Iso.symm he

/-- Extract only the strong core needed for evaluation and internal composition.
The closed normalization identifies the ambient monoidal instances; the domain
calculus fixes the inverse tensorator. No symmetry witness is needed. -/
private theorem finiteChange_etaleStrong
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] {n m : ℕ} (h : m ≤ n) :
    Nonempty (CoefFiniteHomStrong
      (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
      (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h)) := by
  have hc (r : ℕ) : (finiteHomEtaleClosed l E X r).monoidal =
      (inferInstance : MonoidalCategory (finiteHomEtale l E X r)) := by
    have he : finiteHomEtaleClosed l E X r =
        finiteHomEtaleClosedGeneral (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (r + 1)))) X :=
      eq_of_heq ((finiteHomEtaleData_existsUnique l E X).choose_spec.1.closed r)
    rw [he]
    exact (finiteHomEtaleClosed_existsUnique _ X).choose_spec.1.1
  obtain ⟨hm, hμ, _⟩ := finiteHomDomain_monoidal D l hl E X h
  exact finiteChange_domainStrong _ _ (hc n) (hc m)
    (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h) _ _ _ _ hμ hm

private theorem finiteChange_inverseSquare
    {C D : Type*} [Category C] [Category D]
    (T : C × C ⥤ D) {A B E F : D} {K K' M M' : C}
    (s : A ≅ B) (k : K ≅ K') (m : M ≅ M')
    (f₁ : B ⟶ E) (f₂ : E ⟶ T.obj (K', M'))
    (g₁ : A ⟶ F) (g₂ : F ⟶ T.obj (K, M))
    (h : f₁ ≫ f₂ ≫ T.map (Prod.mkHom k.inv m.inv) = s.inv ≫ g₁ ≫ g₂) :
    s.hom ≫ f₁ ≫ f₂ = g₁ ≫ g₂ ≫ T.map (Prod.mkHom k.hom m.hom) := by
  have ht : T.map (Prod.mkHom k.hom m.hom) ≫
      T.map (Prod.mkHom k.inv m.inv) = 𝟙 _ := by
    rw [← T.map_comp]
    change T.map (Prod.mkHom (k.hom ≫ k.inv) (m.hom ≫ m.inv)) = _
    rw [k.hom_inv_id, m.hom_inv_id]
    exact T.map_id _
  have : IsIso (Prod.mkHom k.inv m.inv) :=
    (k.symm.prod m.symm).isIso_hom
  apply (cancel_epi s.inv).mp
  apply (cancel_mono (T.map (Prod.mkHom k.inv m.inv))).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, ht, Category.comp_id] using h

/-- Strong monoidality follows from normalized K-flat tensor squares.
Source: Stacks Project, Tags 07A4 and 0FPT
(blueprint: thm-coef-finite-hom).

Proof: identify the ordinary extension with the sheafified scalar tensor functor.
Its canonical unit and pure-tensor constraints give a strong monoidal functor,
and termwise extension gives one on cochain complexes. Adjunction and pure-tensor
extensionality identify each supplied K-flat chain isomorphism with its inverse
tensorator. Restrict to the K-flat full subcategories. The closed tensor-model
coherences give strong monoidal localization functors on both sides. The counit
is invertible on these representatives, so monoidal localization descends the
composite structure to F. The supplied normalization square identifies the
descended tensorator with the inverse of the prescribed comparison. -/
private theorem finiteChange_scalarCore
    (E : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{c, v, r} J S)
    [E.Additive]
    (hobj : ∀ M, E.obj M = changeOfRings φ M)
    (hmap : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (hobj M) ≫
      changeOfRingsHom φ M f ≫ eqToHom (hobj N).symm)
    (F : DerivedCategory (RingedTensorModules.{c, v, r} J R) ⥤
      DerivedCategory (RingedTensorModules.{c, v, r} J S))
    (ε : DerivedCategory.Q ⋙ F ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (computes : ∀ P, CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      IsIso (ε.app P))
    (AR : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (AS : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J S))
    (MR : CoefficientTensorModels.{r, c, v, w} J R AR)
    (MS : CoefficientTensorModels.{r, c, v, w} J S AS)
    (βR : @SymmetricCategory _ _ AR.monoidal)
    (βS : @SymmetricCategory _ _ AS.monoidal)
    (hR : RingedDerivedTensorCoherence.{c, v, r, w} J R AR MR βR)
    (hS : RingedDerivedTensorCoherence.{c, v, r, w} J S AS MS βS)
    (μ : AR.tensor ⋙ F ≅ F.prod F ⋙ AS.tensor)
    (hk : ∀ P, CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
        ((E.mapHomologicalComplex (.up ℤ)).obj P))
    (hm : ∀ P Q hp hq,
      ∃ e : (E.mapHomologicalComplex (.up ℤ)).obj
          ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≅
        (coefficientTotalTensor.{r, c, v} J S).obj
          ((E.mapHomologicalComplex (.up ℤ)).obj P,
            (E.mapHomologicalComplex (.up ℤ)).obj Q),
        CoefficientScalarTensorGenerators.{r, c, v} J R S E
          (fun M U x ↦ ringedFiniteFreeScalarSection.{c, v, r} J φ E hobj M U 1 x) P Q e ∧
        F.map (MR.iso J R AR P Q hp hq).hom ≫
            μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
            AS.tensor.map (Prod.mkHom (ε.app P) (ε.app Q)) =
          ε.app ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
            DerivedCategory.Q.map e.hom ≫ (MS.iso J S AS _ _ (hk P hp) (hk Q hq)).hom) :
    Nonempty (CoefFiniteHomStrong AR AS F μ) := by
  classical
  have he : E = CochainPullback.extensionFunctor φ :=
    CategoryTheory.Functor.ext hobj (fun _ _ f ↦ hmap f)
  subst E
  let := complexMonoidal.{c, v, r} J R
  let := complexMonoidal.{c, v, r} J S
  let := kFlatMonoidal.{c, v, r} J R
  let := kFlatMonoidal.{c, v, r} J S
  let := AR.monoidal
  let := AS.monoidal
  obtain ⟨d⟩ := scalarExtension_constraint_coherence R S φ
  let := (scalarModuleCore.{c, v, max c v r} J φ d).toMonoidal
  let := (CochainPullback.extensionAdjunction φ).isLeftAdjoint
  let EC := (CochainPullback.extensionFunctor φ).mapHomologicalComplex (.up ℤ)
  let mE := Functor.CoreMonoidal.ofOplaxMonoidal EC
  let K := coefficientKFlatInclusion.{r, c, v} J R
  let KS := coefficientKFlatInclusion.{r, c, v} J S
  let L := K ⋙ DerivedCategory.Q.{w}
  let LS := KS ⋙ DerivedCategory.Q.{w}
  let EE := ObjectProperty.lift
    (CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S))
    (K ⋙ EC) (fun P ↦ hk P.obj P.property)
  let : EE.Monoidal := (restrictCore _ _ _ mE hk).toMonoidal
  let : L.Monoidal := (modelCore.{c, v, r, w}
    (M := MR) (β := βR) (h := hR) J R AR).toMonoidal
  let : LS.Monoidal := (modelCore.{c, v, r, w}
    (M := MS) (β := βS) (h := hS) J S AS).toMonoidal
  let W := (HomologicalComplex.quasiIso (RingedTensorModules.{c, v, r} J R)
    (.up ℤ)).inverseImage K
  let : L.IsLocalization W := RingedDerivedNative.kFlatLocalization.{c, v, r, w} J R
  let eε : L ⋙ F ≅ EE ⋙ LS := NatIso.ofComponents
    (fun P ↦ @asIso _ _ _ _ (ε.app P.obj) (computes P.obj P.property))
    (fun f ↦ by
      change F.map (DerivedCategory.Q.map f.hom) ≫ ε.app _ =
        ε.app _ ≫ DerivedCategory.Q.map (EC.map f.hom)
      exact ε.naturality f.hom)
  obtain ⟨m, hmμ⟩ := normalizedDescent L W F (EE ⋙ LS) eε μ (by
    intro P Q
    obtain ⟨e, hgen, hsquare⟩ := hm P.obj Q.obj P.property Q.property
    have he : e.hom = (mE.μIso P.obj Q.obj).inv := by
      apply HomologicalComplex.hom_ext
      intro n
      apply extendedTotal_ext J φ P.obj Q.obj _ n
      intro p q hpq U x y
      subst n
      have hg := hgen p q (p + q) rfl U x y
      have hc := complexScalar_generators J φ d P.obj Q.obj p q (p + q) rfl U x y
      with_unfolding_all exact hg.trans hc.symm
    with_unfolding_all change (
      F.map (MR.iso J R AR P.obj Q.obj P.property Q.property).hom ≫
          μ.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          AS.tensor.map (Prod.mkHom (ε.app P.obj) (ε.app Q.obj)) =
        ε.app ((coefficientTotalTensor.{r, c, v} J R).obj (P.obj, Q.obj)) ≫
          (DerivedCategory.Q.map ((mE.μIso P.obj Q.obj).inv) ≫
            (MS.iso J S AS _ _ (hk P.obj P.property) (hk Q.obj Q.property)).hom))
    rw [← he]
    exact hsquare)
  exact ⟨m, fun P Q ↦ Iso.ext (hmμ P Q)⟩

/-- The fixed finite quotient tensorator has a strong monoidal core.
Source: blueprint thm-coef-finite-hom, evaluation and composition paragraph;
Stacks Project, Tags 07A4 and 0FPT
(blueprint: thm-coef-finite-hom).

Proof: retain the prescribed quotient functor and its actual counit. The published
finite tensor coherences give the source and target localization structures.
The quotient calculus supplies K-flat preservation and the normalized chain tensor
square. Its scalar-unit section is the sheafification of 1 tensor x, so the
normalization agrees with the generic scalar-core theorem. Apply that theorem
and obtain the required core with exactly the fixed inverse tensorator. -/
private theorem finiteChange_proStrong
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) {n m : ℕ} (h : m ≤ n) :
    Nonempty (CoefFiniteHomStrong (finiteIntrinsicClosed l E X n)
      (finiteIntrinsicClosed l E X m) (coefficientFiniteQuotientDerived l E X h)
      (coefFiniteHomProTensor l E X h)) := by
  classical
  let S := (coefficientDerivedSystemEvaluationCalculus l E X).choose
  obtain ⟨βn, ⟨hβn⟩⟩ := S.finite_tensor_coherence n
  obtain ⟨βm, ⟨hβm⟩⟩ := S.finite_tensor_coherence m
  let : EssentiallySmall.{u + 1} X.ProEt := finiteHomTensorSiteSmall X
  let := coefficientFiniteQuotientExtensionAdditive l E X h
  apply finiteChange_scalarCore (Scheme.ProEt.topology X)
    (coefficientFiniteQuotient l E X h) (coefficientFiniteQuotientExtension l E X h)
    (coefficientFiniteQuotientExtension_obj l E X h)
    (coefficientFiniteQuotientExistence l E X h).choose_spec.choose_spec.choose
    (coefficientFiniteQuotientDerived l E X h) (finiteHomTensorComparison l E X h)
    (fun P hp ↦ by
      rw [comparison_model l E X h P hp]
      infer_instance)
    (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
    (finiteIntrinsicTensorModels l E X n) (finiteIntrinsicTensorModels l E X m)
    βn βm hβn hβm (coefFiniteHomProTensor l E X h)
    (S.quotientCalculus.preservesKFlat h)
  intro P Q hp hq
  obtain ⟨e, he, ht⟩ := S.quotientCalculus.tensor_model h P Q hp hq
  refine ⟨e, ?_, ?_⟩
  · with_unfolding_all exact he
  · rw [comparison_model l E X h P hp, comparison_model l E X h Q hq,
      comparison_model l E X h _
        (coefficientTotalTensor_isKFlat.{u, u + 1, u} (Scheme.ProEt.topology X)
          (integralCoefficientCommRingSheaf l E X n) P Q hp hq)]
    exact ht

/-- Finite coefficient change for internal Hom, including the canonical-map equations.
Source: blueprint thm-coef-finite-hom, evaluation and coefficient-change paragraphs
(blueprint: thm-coef-finite-hom).

Proof:
1. A finite-type scheme over k is Noetherian. Derived scalar extension is computed
on K-flat resolutions, even for a nonflat quotient. A bounded flat constructible
model reduces to a bounded flat constructible model with the same Tor interval.
2. Resolve tensor inputs K-flat and the Hom target K-injective. The total-complex
Hom-tensor identity gives the closed adjunction. Transpose reduced evaluation;
this is exactly coefficientBaseChangeHom and finiteIntrinsicReductionHom.
Finite constructible Hom and scalar reduction put both endpoints in D^b_ctf.
3. For fixed M the invertibility locus in K is thick, by the evaluation-normalized
shift and connecting-map comparison. The flat-model generation theorem supplies
locally closed generators Rs_!L = g_*j_!L with L finite locally projective. On an
etale cover L is finite free, including rank zero, so the bounded-free Hom model
identifies its comparison with the identity on finite sums of the reduced model.
For N = Rs^!M = j^*Rg^!M, the general quasi-compact-open complement theorem
applies over the separably closed field, with l-primary finite coefficients and
finite dimension d. It gives constructibility and cohomological bound 2d on
all sheaves. The closed-exceptional Tor theorem then puts Rg^!M in the Tor
interval [a,b+2d+1]; open pullback preserves the resulting finite-Tor domain.
Finite constructible Hom therefore puts Q = H(L,N) in the required domain.
Locally closed shriek coefficient change supplies its counit-normalized
comparisons. Internal adjunction identifies the generator Hom with Rs_*Q;
finite direct-image coefficient change applies to Q. Compose this comparison,
the local finite-free Hom comparison, and the exceptional comparison. The
open projection formula and the proper projection formula for the closed factor
identify the resulting pairing with reduced evaluation, by their counit identities.
Uniqueness of transpose identifies this invertible composite with the specified v.
Thus v is invertible on every generator. Thick closure, followed by the finite
stupid-truncation triangles of a bounded flat model, proves the etale assertion.
4. The closed transpose bijection proves the evaluation identity and its
uniqueness. Transposing after arbitrary input maps gives naturality; applying it
to an arbitrary tensor-Hom transpose gives the adjunction equation. Uncurry
internal composition to its two evaluations to obtain the composition equation.
5. On three quotient levels the canonical tensor associators identify the two
reduced evaluations. Their unique transposes agree. This gives precisely both
cocycle equations, including the contravariant inverse input associator.
6. Exact comparison nu_X^* commutes with scalar extension by the specified beta
mate and with tensor by its pure-tensor comparison. Applying it to evaluation
and transposing gives FiniteHomSiteFormula. The finite-duality site comparison
identifies internal Hom on finite-Tor constructible etale origins, and every
intrinsic constructible complex has such an origin. This transfers invertibility
and constructibility to the pro-etale site. Evaluation, transpose, naturality,
composition and quotient coherence are the same identities before site transport. -/
theorem finiteCoefficient_derivedHom_change
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (n m : ℕ) (h : m ≤ n) :
    CoefficientEvaluationCompatible
      (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
      (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h) ∧
    FiniteHomEvaluation (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
      (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h) ∧
    (∀ K M : finiteHomEtale l E X n,
      finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X K →
      finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X M →
      finiteTorConstructibleEtale l E (m + 1) (Nat.succ_pos m) X
        ((finiteHomEtaleReduction l E X h).obj
          ((Functor.uncurry.obj (Etale.derivedHom (ModuleCat.{u + 1}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X)).obj (op K, M))) ∧
      finiteTorConstructibleEtale l E (m + 1) (Nat.succ_pos m) X
        ((Functor.uncurry.obj (Etale.derivedHom (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1)))) X)).obj
          (op ((finiteHomEtaleReduction l E X h).obj K),
            (finiteHomEtaleReduction l E X h).obj M)) ∧
      IsIso (etaleFiniteHomCanonical l E X h K M)) ∧
    CoefficientEvaluationCompatible (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
      (coefficientFiniteQuotientDerived l E X h)
      ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.tensor h) ∧
    FiniteHomEvaluation (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
      (coefficientFiniteQuotientDerived l E X h)
      ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.tensor h) ∧
    (∀ K M : normalizedDVRDerived l E X n,
      finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X K →
      finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X M →
      finiteTorConstructible l E (m + 1) (Nat.succ_pos m) X
        ((coefficientFiniteQuotientDerived l E X h).obj
          ((coefficientFiniteInternalHom l E X n).obj (op K, M))) ∧
      finiteTorConstructible l E (m + 1) (Nat.succ_pos m) X
        ((coefficientFiniteInternalHom l E X m).obj
          (op ((coefficientFiniteQuotientDerived l E X h).obj K),
            (coefficientFiniteQuotientDerived l E X h).obj M)) ∧
      IsIso (proEtaleFiniteHomCanonical l E X h K M)) ∧
    FiniteHomEtaleCocycle l E X h ∧ FiniteHomIntrinsicCocycle l E X h ∧
    FiniteHomSiteFormula l E X h := by
  have hd := finiteChange_siteDescent D l _hl E X
  obtain ⟨sF⟩ := finiteChange_etaleStrong D l _hl E X h
  obtain ⟨sG⟩ := finiteChange_proStrong l E X h
  have ht : ∀ K M : finiteHomEtale l E X n,
      (coefFiniteHomSiteIso l E X h).hom.app
          ((finiteHomEtaleClosed l E X n).tensor.obj (K, M)) ≫
        (coefficientFiniteQuotientDerived l E X h).map
          ((finiteHomNuTensor l E X n).hom.app (K, M)) ≫
        (coefFiniteHomProTensor l E X h).hom.app
          ((finiteHomNu l E X n).obj K, (finiteHomNu l E X n).obj M) =
      (finiteHomNu l E X m).map ((finiteHomEtaleTensor l E X h).hom.app (K, M)) ≫
        (finiteHomNuTensor l E X m).hom.app
          ((finiteHomEtaleReduction l E X h).obj K,
            (finiteHomEtaleReduction l E X h).obj M) ≫
        (finiteIntrinsicClosed l E X m).tensor.map
          (Prod.mkHom ((coefFiniteHomSiteIso l E X h).hom.app K)
            ((coefFiniteHomSiteIso l E X h).hom.app M)) := by
    intro K M
    have hKM := congrArg (fun z ↦ z.app (K, M))
      (finiteHomSiteTensorNaturalEquality_legacy l E X h)
    exact finiteChange_inverseSquare ((finiteIntrinsicClosed l E X m).tensor)
      ((coefFiniteHomSiteIso l E X h).app
        ((finiteHomEtaleClosed l E X n).tensor.obj (K, M)))
      ((coefFiniteHomSiteIso l E X h).app K) ((coefFiniteHomSiteIso l E X h).app M)
      ((coefficientFiniteQuotientDerived l E X h).map
        ((finiteHomNuTensor l E X n).hom.app (K, M)))
      ((coefFiniteHomProTensor l E X h).hom.app
        ((finiteHomNu l E X n).obj K, (finiteHomNu l E X n).obj M))
      ((finiteHomNu l E X m).map ((finiteHomEtaleTensor l E X h).hom.app (K, M)))
      ((finiteHomNuTensor l E X m).hom.app
        ((finiteHomEtaleReduction l E X h).obj K,
          (finiteHomEtaleReduction l E X h).obj M)) hKM
  have he : ∀ K M : finiteHomEtale l E X n,
      finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X K →
      finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X M →
      finiteTorConstructibleEtale l E (m + 1) (Nat.succ_pos m) X
        ((finiteHomEtaleReduction l E X h).obj
          ((finiteHomEtaleInternalHom l E X n).obj (op K, M))) ∧
      finiteTorConstructibleEtale l E (m + 1) (Nat.succ_pos m) X
        ((finiteHomEtaleInternalHom l E X m).obj
          (op ((finiteHomEtaleReduction l E X h).obj K),
            (finiteHomEtaleReduction l E X h).obj M)) ∧
      IsIso (etaleFiniteHomCanonical l E X h K M) := by
    intro K M hK hM
    have hh := finiteHomDomain_endpoints D l _hl E X h K M hK.1 hM.1 hK.2 hM.2
    exact ⟨hh.1, hh.2, finiteHomEtale_isIso D l _hl E X h K M hK hM⟩
  refine ⟨finiteChange_compatible _ _ _ _ sF,
    finiteHomEvaluation_of_transpose _ _ _ _, he,
    finiteChange_compatible _ _ _ _ sG,
    finiteHomEvaluation_of_transpose _ _ _ _, ?_, ?_, ?_, ?_⟩
  · intro K M hK hM
    let F := finiteHomEtaleReduction l E X h
    let G := coefficientFiniteQuotientDerived l E X h
    let U := finiteHomNu l E X n
    let V := finiteHomNu l E X m
    let Hn := coefficientFiniteInternalHom l E X n
    let Hm := coefficientFiniteInternalHom l E X m
    let α := coefFiniteHomSiteIso l E X h
    let :
        (finiteTorConstructible l E (m + 1) (Nat.succ_pos m) X).IsClosedUnderIsomorphisms :=
      (finite_ctf_isTriangulated l E (m + 1) (Nat.succ_pos m) X).1
    obtain ⟨K', hK', ⟨eK⟩⟩ := (hd n).2.2.1 K hK
    obtain ⟨M', hM', ⟨eM⟩⟩ := (hd n).2.2.1 M hM
    obtain ⟨hsource, htarget, hv⟩ := he K' M' hK' hM'
    have hνn := finiteHomSiteHomInvertible D l _hl E X n K' M' hK' hM'.1
    have hKr : finiteTorConstructibleEtale l E (m + 1) (Nat.succ_pos m) X
        ((finiteHomEtaleReduction l E X h).obj K') := by
      obtain ⟨a, b, hab, hTor⟩ := hK'.2
      have hf := finiteHomDomain_flatModel D l _hl E X h a b hab K' hK'.1 hTor
      exact ⟨hf.2.2.1, a, b, hab, hf.2.2.2⟩
    have hMr : finiteTorConstructibleEtale l E (m + 1) (Nat.succ_pos m) X
        ((finiteHomEtaleReduction l E X h).obj M') := by
      obtain ⟨a, b, hab, hTor⟩ := hM'.2
      have hf := finiteHomDomain_flatModel D l _hl E X h a b hab M' hM'.1 hTor
      exact ⟨hf.2.2.1, a, b, hab, hf.2.2.2⟩
    have hνm := finiteHomSiteHomInvertible D l _hl E X m _ _ hKr hMr.1
    have hsq := finiteChange_forwardSquare
      (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
      (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
      (finiteHomEtaleReduction l E X h) (coefficientFiniteQuotientDerived l E X h)
      (finiteHomNu l E X n) (finiteHomNu l E X m)
      (finiteHomEtaleTensor l E X h) (coefFiniteHomProTensor l E X h)
      (finiteHomNuTensor l E X n) (finiteHomNuTensor l E X m)
      (coefFiniteHomSiteIso l E X h) ht K' M'
    change (coefFiniteHomSiteIso l E X h).hom.app
        ((finiteHomEtaleInternalHom l E X n).obj (op K', M')) ≫
        G.map (finiteHomSiteHom l E X n K' M') ≫
        coefficientBaseChangeHom (finiteIntrinsicClosed l E X n)
          (finiteIntrinsicClosed l E X m) G (coefFiniteHomProTensor l E X h)
          (U.obj K') (U.obj M') =
      V.map (etaleFiniteHomCanonical l E X h K' M') ≫
        finiteHomSiteHom l E X m (F.obj K') (F.obj M') ≫
        Hm.map (Prod.mkHom ((coefFiniteHomSiteIso l E X h).inv.app K').op
          ((coefFiniteHomSiteIso l E X h).hom.app M')) at hsq
    rw [← finiteChange_pro_eq] at hsq
    let := hv
    let := hνn
    let := hνm
    let eH : Hn.obj (op (U.obj K'), U.obj M') ≅ Hn.obj (op K, M) :=
      Hn.mapIso (Iso.prod eK.symm.op eM)
    let eSource : V.obj (F.obj ((finiteHomEtaleInternalHom l E X n).obj (op K', M'))) ≅
        G.obj (Hn.obj (op K, M)) :=
      α.app _ ≪≫ G.mapIso (asIso (finiteHomSiteHom l E X n K' M')) ≪≫ G.mapIso eH
    let dK : V.obj (F.obj K') ≅ G.obj K := α.app K' ≪≫ G.mapIso eK
    let dM : V.obj (F.obj M') ≅ G.obj M := α.app M' ≪≫ G.mapIso eM
    let eTarget : V.obj ((finiteHomEtaleInternalHom l E X m).obj
        (op (F.obj K'), F.obj M')) ≅ Hm.obj (op (G.obj K), G.obj M) :=
      asIso (finiteHomSiteHom l E X m (F.obj K') (F.obj M')) ≪≫
        Hm.mapIso (Iso.prod dK.symm.op dM)
    refine ⟨(finiteTorConstructible l E (m + 1) (Nat.succ_pos m) X).prop_of_iso
      eSource ((hd m).2.2.2.2 _ hsource).1,
      (finiteTorConstructible l E (m + 1) (Nat.succ_pos m) X).prop_of_iso
        eTarget ((hd m).2.2.2.2 _ htarget).1, ?_⟩
    have hi : IsIso (proEtaleFiniteHomCanonical l E X h (U.obj K') (U.obj M')) := by
      have : IsIso ((coefFiniteHomSiteIso l E X h).hom.app
          ((finiteHomEtaleInternalHom l E X n).obj (op K', M')) ≫
          G.map (finiteHomSiteHom l E X n K' M') ≫
          proEtaleFiniteHomCanonical l E X h (U.obj K') (U.obj M')) := by
        rw [hsq]
        infer_instance
      have : IsIso (G.map (finiteHomSiteHom l E X n K' M') ≫
          proEtaleFiniteHomCanonical l E X h (U.obj K') (U.obj M')) :=
        IsIso.of_isIso_comp_left ((coefFiniteHomSiteIso l E X h).hom.app _) _
      exact IsIso.of_isIso_comp_left (G.map (finiteHomSiteHom l E X n K' M')) _
    rw [finiteChange_pro_eq] at hi
    let := hi
    have hn := finiteChange_natural (finiteIntrinsicClosed l E X n)
      (finiteIntrinsicClosed l E X m) G (coefFiniteHomProTensor l E X h)
      (U.obj K') K (U.obj M') M eK.inv eM.hom
    have : IsIso (G.map (Hn.map (Prod.mkHom eK.inv.op eM.hom)) ≫
        proEtaleFiniteHomCanonical l E X h K M) := by
      dsimp only [Hn]
      rw [finiteChange_pro_eq, hn]
      infer_instance
    exact IsIso.of_isIso_comp_left (G.map (Hn.map (Prod.mkHom eK.inv.op eM.hom))) _
  · apply finiteChange_familyCocycle (finiteHomEtaleData l E X)
      (finiteHomEtaleAssoc l E X) ?_ h
    intro n' m' r h' k
    apply finiteChange_tensor_coherence _ _ _ _ _ _ _ _ _ _ _ _ _
      (finiteChange_etale_tensor_eq l E X n') (finiteChange_etale_tensor_eq l E X m')
      (finiteChange_etale_tensor_eq l E X r)
      (Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E h') X)
      (Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E k) X)
      (Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E (k.trans h')) X)
      (finiteChange_etale_tensor_heq l E X h')
      (finiteChange_etale_tensor_heq l E X k)
      (finiteChange_etale_tensor_heq l E X (k.trans h'))
    exact finiteChange_scalarSquare _ _ _ _ _ _ _
      (Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E h') X)
      (Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E k) X)
      (Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E (k.trans h')) X) _ _ _
      (finiteHomDomain_scalarCoherence D l _hl E X h' k).1
  · refine ⟨fun r k K M ↦ ?_⟩
    simp only [finiteChange_pro_eq]
    exact (finiteChangeBaseChangeHom_tower (finiteIntrinsicClosed l E X n)
      (finiteIntrinsicClosed l E X m) (finiteIntrinsicClosed l E X r)
      (coefficientFiniteQuotientDerived l E X h) (coefficientFiniteQuotientDerived l E X k)
      (coefficientFiniteQuotientDerived l E X (k.trans h))
      (coefFiniteHomProTensor l E X h) (coefFiniteHomProTensor l E X k)
      (coefFiniteHomProTensor l E X (k.trans h)) (finiteHomIntrinsicAssoc l E X h k)
      (finiteHomIntrinsic_tensorComposition l E X h k) K M).symm
  · refine ⟨fun K M ↦ ?_⟩
    simpa only [coefFiniteHomSiteIso, Iso.symm_hom, Iso.symm_inv,
      asIso_hom, asIso_inv, NatIso.isIso_inv_app, finiteHomSiteHom,
      etaleFiniteHomCanonical, finiteChange_pro_eq] using
      finiteChange_square (finiteHomEtaleClosed l E X n)
      (finiteHomEtaleClosed l E X m) (finiteIntrinsicClosed l E X n)
      (finiteIntrinsicClosed l E X m) (finiteHomEtaleReduction l E X h)
      (coefficientFiniteQuotientDerived l E X h) (finiteHomNu l E X n)
      (finiteHomNu l E X m) (finiteHomEtaleTensor l E X h)
      (coefFiniteHomProTensor l E X h) (finiteHomNuTensor l E X n)
      (finiteHomNuTensor l E X m) (coefFiniteHomSiteIso l E X h) ht K M

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
section ScalarMonoidal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open SheafOfModules CategoryTheory.ScalarMonoidalProof
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J S)]
set_option maxHeartbeats 5000000 in
-- Comparing the fixed and localized tensor structures needs a larger unification budget.
attribute [local irreducible] CategoryTheory.Localization.lift
  CategoryTheory.MorphismProperty.instCategoryLocalization
  _root_.instCategoryDerivedCategory in
end ScalarMonoidal
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 5000000 in
-- The native quotient and ringed-site models have separately recorded instances.
end

end WeilConjectures
