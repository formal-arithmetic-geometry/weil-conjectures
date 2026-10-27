/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.Paper.FiniteCoefficientSiteHomArrow
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.FiniteHomEtaleIso
import Sheaf.Paper.FiniteHomIntrinsicTensorComposition
import Sheaf.Paper.FiniteCtfTriangulated
import Sheaf.Paper.FiniteHomDomainCalculus
import Sheaf.Paper.CoefFiniteHomSiteDescent


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
universe u a b w c d e f g
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

attribute [local implicit_reducible]
  CategoryTheory.uniformProd CategoryTheory.prod CategoryTheory.prod'
  CategoryTheory.catToReflQuiver CoefficientClosedStructure.tensor

private theorem finiteChange_isIso_prod
    {C : Type a} {D : Type b} [Category.{c} C] [Category.{d} D]
    {X Y : C} {U V : D} (f : X ⟶ Y) (g : U ⟶ V) [IsIso f] [IsIso g] :
    IsIso (Prod.mkHom f g) :=
  (isIso_prod_iff (f := Prod.mkHom f g)).mpr ⟨inferInstance, inferInstance⟩

attribute [local instance] finiteChange_isIso_prod

private theorem finiteChange_pro_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) {n m : ℕ} (h : m ≤ n)
    (K M : normalizedDVRDerived l E X n) :
    proEtaleFiniteHomCanonical l E X h K M =
      coefficientBaseChangeHom (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
        (coefficientFiniteQuotientDerived l E X h) (coefFiniteHomProTensor l E X h) K M := by
  rfl

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
  have hh := finiteChangeBaseChangeHom_tower SA SB SD F V (U ⋙ G) μF μV
    (finiteChangeCompositeTensor SA SC SD U G μU μG) h (by
      intro K M
      exact (ht K M).symm) P Q
  rw [← finiteChangeCompositeHom SA SC SD U G μU μG P Q] at hh
  have he := congrArg (fun z ↦ h.inv.app (HA.obj (op P, Q)) ≫ z ≫
    HD.map (Prod.mkHom (h.hom.app P).op (h.inv.app Q))) hh
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← HD.map_comp,
    prod_comp, ← op_comp, Iso.hom_inv_id_app, op_id, ← prod_id] at he
  erw [HD.map_id, Category.comp_id] at he
  exact he

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
  obtain ⟨hd, βet, βpro, hβet, hβpro, hβnu, hs⟩ :=
    coefFiniteHomSiteDescent D l _hl E X
  obtain ⟨sF, sG, sU, sV, ht, _⟩ := (hs n m h).1
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
    obtain ⟨hνn, hνm, hsq⟩ := (hs n m h).2.2.2.2.1 K' M' hK' hM'
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

end WeilConjectures
