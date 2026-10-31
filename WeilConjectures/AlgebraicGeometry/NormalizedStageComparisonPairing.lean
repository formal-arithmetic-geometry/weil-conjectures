/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalizedStageComparisonObligations
import WeilConjectures.AlgebraicGeometry.NormalizedStageSiteEvaluation
import all WeilConjectures.AlgebraicGeometry.EtaleScalarMonoidal
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficientMaps
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Trace

/-! # Pairing part of normalized stage comparison coherence

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraph 3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed


private theorem pro_scalar_braiding
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (μ : Sites.TensorComparison true φ X)
    (hμ : Sites.NormalizedTensor true φ X μ) (K L : Sites.D true A X) :
    (WeilConjectures.finiteHomKoszulIso
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))
        ((Sites.scalar true φ X).obj K) ((Sites.scalar true φ X).obj L)).hom ≫
        μ.inv.app (L, K) =
      μ.inv.app (K, L) ≫ (Sites.scalar true φ X).map
        (WeilConjectures.finiteHomKoszulIso
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) K L).hom := by
  let := φ.toAlgebra
  let J := Scheme.ProEt.topology X
  let E := finiteVerdierOrdinaryExtension J φ
  let U := Sheaf.restrictScalars J φ
  let adj : E ⊣ U := finiteVerdierOrdinaryAdjunction J φ
  let : E.IsLeftAdjoint := adj.isLeftAdjoint
  let : E.PreservesFlat := ProEtale.preservesFlat_sheafExtendScalars X φ
  let : E.PreservesKFlatQuasiIso :=
    ProEtale.preservesKFlatQuasiIso_sheafExtendScalars A B X
  let : E.Monoidal := ProEtale.monoidal_sheafExtendScalars φ X
  let G := ProEtale.pbcFixedScalarExtension J φ
  let ad : G ⊣ U.mapDerivedCategory := Adjunction.ofIsRightAdjoint _
  let b : E.leftDerivedFunctor ⊣ U.mapDerivedCategory :=
    adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
  let e : G ≅ E.leftDerivedFunctor := ad.leftAdjointUniq b
  have hr : ∀ P, finiteVerdierScalarRepresentative J φ P =
      e.hom.app (DerivedCategory.Q.obj P) ≫ E.rightExact_cochainCounit P := by
    intro P
    unfold finiteVerdierScalarRepresentative finiteVerdierScalarRepresentativeAux
    erw [← Etale.ExceptionalCoefficients.mapComplex_unit_formula]
    exact (Adjunction.leftDerivedCochainCounit E U adj ad P).symm
  obtain ⟨δ, hn, he⟩ := hμ
  have he' : μ = δ := eq_of_heq he
  subst μ
  let := E.leftDerivedFunctorMonoidal
  let c := Functor.Monoidal.coreMonoidalTransport e.symm
  have hc (P Q : Sites.D true A X) : (c.μIso P Q).symm = δ.app (P, Q) := by
    apply Iso.ext
    exact Functor.core_tensor_normalized E G e (finiteVerdierScalarRepresentative J φ) hr
      (fun P Q ↦ (δ.app (P, Q)).symm)
      ⟨Etale.ExceptionalCoefficients.productIso_natural₁ _ _ _ δ,
        Etale.ExceptionalCoefficients.productIso_natural₂ _ _ _ δ,
        Etale.ExceptionalCoefficients.tensor_normalization_flat E G
          (finiteVerdierScalarRepresentative J φ) δ hn⟩ P Q
  have hb := Functor.core_braiding E G e
    (ProEtale.sheafExtendScalars_map_braiding_hom_δ φ X) K L
  have hK := congrArg Iso.inv (hc K L)
  have hL := congrArg Iso.inv (hc L K)
  simp only [Iso.symm_inv, Iso.app_inv] at hK hL
  dsimp only [c] at hK hL
  erw [hK, hL] at hb
  exact hb

private theorem scalar_braiding
    (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (μ : Sites.TensorComparison pro φ X)
    (hμ : Sites.NormalizedTensor pro φ X μ)
    (bA : Sites.tensor pro A X ≅ (Sites.tensor pro A X).flip)
    (bB : Sites.tensor pro B X ≅ (Sites.tensor pro B X).flip)
    (hA : Sites.NormalizedSymmetry pro A X bA)
    (hB : Sites.NormalizedSymmetry pro B X bB) (K L : Sites.D pro A X) :
    (bB.hom.app ((Sites.scalar pro φ X).obj K)).app ((Sites.scalar pro φ X).obj L) ≫
        μ.inv.app (L, K) =
      μ.inv.app (K, L) ≫ (Sites.scalar pro φ X).map ((bA.hom.app K).app L) := by
  cases pro
  · obtain ⟨c, _, hc, hb⟩ :=
      Etale.ExceptionalCoefficients.scalarExtension_coreMonoidal A B φ X
    have hK := congrArg Iso.inv (hc K L)
    have hL := congrArg Iso.inv (hc L K)
    simp only [Iso.symm_inv, Iso.app_inv] at hK hL
    have he : μ = Etale.ExceptionalCoefficients.tensorIso φ X := eq_of_heq hμ
    have hsA := eq_of_heq (hA K L)
    have hsB := eq_of_heq (hB ((Sites.scalar false φ X).obj K)
      ((Sites.scalar false φ X).obj L))
    simp only [Iso.app_hom] at hsA hsB
    erw [hsA, hsB, he, ← hK, ← hL]
    exact hb K L
  · have hsA := eq_of_heq (hA K L)
    have hsB := eq_of_heq (hB ((Sites.scalar true φ X).obj K)
      ((Sites.scalar true φ X).obj L))
    erw [hsA, hsB]
    exact pro_scalar_braiding φ X μ hμ K L

attribute [local irreducible] Sites.tensor Sites.hom Sites.scalar

private theorem homMap_evaluation
    (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (μ : Sites.TensorComparison pro φ X)
    (K M : Sites.D pro A X) :
    ((Sites.tensor pro B X).obj ((Sites.scalar pro φ X).obj K)).map
        (Sites.homMap pro φ X μ K M) ≫
        (Sites.adj pro B X ((Sites.scalar pro φ X).obj K)).counit.app
          ((Sites.scalar pro φ X).obj M) =
      μ.inv.app (K, ((Sites.hom pro A X).obj (op K)).obj M) ≫
        (Sites.scalar pro φ X).map ((Sites.adj pro A X K).counit.app M) := by
  dsimp only [Sites.TensorComparison] at μ
  exact ((Sites.adj pro B X ((Sites.scalar pro φ X).obj K)).homEquiv_counit _ _
    (Sites.homMap pro φ X μ K M)).symm.trans
      (((Sites.adj pro B X ((Sites.scalar pro φ X).obj K)).homEquiv _ _).symm_apply_apply _)

private theorem dualMap_evaluation_left
    (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} {aX : X ⟶ S} (c : Compactification aX)
    (μ : Sites.TensorComparison pro φ X)
    (w : (Sites.scalar pro φ X).obj (Sites.omega pro A c) ⟶ Sites.omega pro B c)
    (K : Sites.D pro A X) :
    ((Sites.tensor pro B X).obj ((Sites.scalar pro φ X).obj K)).map
        (Sites.dualMap pro φ c μ w K) ≫
        (Sites.adj pro B X ((Sites.scalar pro φ X).obj K)).counit.app
          (Sites.omega pro B c) =
      μ.inv.app (K, (Sites.dual pro A c).obj (op K)) ≫
        (Sites.scalar pro φ X).map
          ((Sites.adj pro A X K).counit.app (Sites.omega pro A c)) ≫ w := by
  dsimp only [Sites.TensorComparison] at μ
  simp only [Sites.dual, Functor.flip_obj_obj] at *
  dsimp only [Sites.dualMap]
  erw [Functor.map_comp, Category.assoc,
    (Sites.adj pro B X ((Sites.scalar pro φ X).obj K)).counit.naturality w,
    ← Category.assoc, homMap_evaluation, Category.assoc]
  rfl

private theorem dualMap_evaluation
    (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} {aX : X ⟶ S} (c : Compactification aX)
    (μ : Sites.TensorComparison pro φ X)
    (bA : Sites.tensor pro A X ≅ (Sites.tensor pro A X).flip)
    (bB : Sites.tensor pro B X ≅ (Sites.tensor pro B X).flip)
    (hb : ∀ K L : Sites.D pro A X,
      (bB.hom.app ((Sites.scalar pro φ X).obj K)).app ((Sites.scalar pro φ X).obj L) ≫
        μ.inv.app (L, K) =
      μ.inv.app (K, L) ≫ (Sites.scalar pro φ X).map ((bA.hom.app K).app L))
    (w : (Sites.scalar pro φ X).obj (Sites.omega pro A c) ⟶ Sites.omega pro B c)
    (K : Sites.D pro A X) :
    ((Sites.tensor pro B X).map (Sites.dualMap pro φ c μ w K)).app
        ((Sites.scalar pro φ X).obj K) ≫
        Sites.evaluation pro B X bB (Sites.omega pro B c) ((Sites.scalar pro φ X).obj K) =
      μ.inv.app ((Sites.dual pro A c).obj (op K), K) ≫
        (Sites.scalar pro φ X).map (Sites.evaluation pro A X bA (Sites.omega pro A c) K) ≫
          w := by
  dsimp only [Sites.TensorComparison] at μ
  simp only [Sites.dual, Functor.flip_obj_obj] at *
  dsimp only [Sites.evaluation]
  have hn := NatTrans.congr_app (bB.hom.naturality (Sites.dualMap pro φ c μ w K))
    ((Sites.scalar pro φ X).obj K)
  dsimp only [NatTrans.comp_app, Functor.flip_map_app] at hn
  erw [← Category.assoc, hn, Category.assoc, dualMap_evaluation_left,
    ← Category.assoc, hb, Category.assoc, Functor.map_comp, Category.assoc]
  rfl

private theorem bidual_by_transpose
    {C : Type v₁} [Category.{w₁} C] {D : Type v₂} [Category.{w₂} D]
    (TA : C ⥤ C ⥤ C) (TB : D ⥤ D ⥤ D) (F : C ⥤ D)
    (μ : Functor.uncurry.obj TA ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj TB)
    {U K L W : C} {U' V' : D} (R : D ⥤ D) (a : TB.obj (F.obj U) ⊣ R)
    (WB : D) (d₁ : F.obj L ⟶ R.obj WB) (d₀ : F.obj U ⟶ U')
    (α : K ⟶ L) (β : F.obj K ⟶ V') (z : V' ⟶ R.obj WB)
    (ε : (TA.obj U).obj L ⟶ W) (ε' : (TB.obj U').obj V' ⟶ WB)
    (w : F.obj W ⟶ WB)
    (hleft : (TB.obj (F.obj U)).map d₁ ≫ a.counit.app WB =
      μ.inv.app (U, L) ≫ F.map ε ≫ w)
    (hd : (TB.obj (F.obj U)).map z ≫ a.counit.app WB =
      (TB.map d₀).app V' ≫ ε')
    (he : (TB.map d₀).app (F.obj K) ≫ (TB.obj U').map β ≫ ε' =
      μ.inv.app (U, K) ≫ F.map ((TA.obj U).map α ≫ ε) ≫ w) :
    F.map α ≫ d₁ = β ≫ z := by
  apply ((a.homEquiv (F.obj K) WB).symm).injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  conv_lhs => rw [Functor.map_comp, Category.assoc, hleft]
  conv_rhs => rw [Functor.map_comp, Category.assoc, hd]
  have hn := μ.inv.naturality (Prod.mkHom (𝟙 U) α)
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.uncurry_obj_map] at hn
  simp only [_root_.CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  conv_rhs => rw [← Category.assoc, (TB.map d₀).naturality β, Category.assoc]
  exact he.symm

private theorem dualMap_bidual
    (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} {aX : X ⟶ S} (c : Compactification aX)
    (μ : Sites.TensorComparison pro φ X)
    (bA : Sites.tensor pro A X ≅ (Sites.tensor pro A X).flip)
    (bB : Sites.tensor pro B X ≅ (Sites.tensor pro B X).flip)
    (w : (Sites.scalar pro φ X).obj (Sites.omega pro A c) ⟶ Sites.omega pro B c)
    (K : Sites.D pro A X)
    (he : ((Sites.tensor pro B X).map (Sites.dualMap pro φ c μ w K)).app
        ((Sites.scalar pro φ X).obj K) ≫
        Sites.evaluation pro B X bB (Sites.omega pro B c) ((Sites.scalar pro φ X).obj K) =
      μ.inv.app ((Sites.dual pro A c).obj (op K), K) ≫
        (Sites.scalar pro φ X).map (Sites.evaluation pro A X bA (Sites.omega pro A c) K) ≫
          w) :
    (Sites.scalar pro φ X).map (Sites.bidual pro A X bA (Sites.omega pro A c) K) ≫
        Sites.dualMap pro φ c μ w ((Sites.dual pro A c).obj (op K)) =
      Sites.bidual pro B X bB (Sites.omega pro B c) ((Sites.scalar pro φ X).obj K) ≫
        (Sites.dual pro B c).map (Sites.dualMap pro φ c μ w K).op := by
  let F := Sites.scalar pro φ X
  let WA := Sites.omega pro A c
  let WB := Sites.omega pro B c
  let DA := ((Sites.hom pro A X).obj (op K)).obj WA
  let DB := ((Sites.hom pro B X).obj (op (F.obj K))).obj WB
  let d : F.obj DA ⟶ DB := Sites.dualMap pro φ c μ w K
  have hδA : ((Sites.tensor pro A X).obj DA).map
        (Sites.bidual pro A X bA WA K) ≫
      (Sites.adj pro A X DA).counit.app WA = Sites.evaluation pro A X bA WA K := by
    dsimp only [Sites.bidual]
    exact ((Sites.adj pro A X DA).homEquiv_counit _ _ _).symm.trans
      (((Sites.adj pro A X DA).homEquiv _ _).symm_apply_apply _)
  have hδB : ((Sites.tensor pro B X).obj DB).map
        (Sites.bidual pro B X bB WB (F.obj K)) ≫
      (Sites.adj pro B X DB).counit.app WB =
        Sites.evaluation pro B X bB WB (F.obj K) := by
    dsimp only [Sites.bidual]
    exact ((Sites.adj pro B X DB).homEquiv_counit _ _ _).symm.trans
      (((Sites.adj pro B X DB).homEquiv _ _).symm_apply_apply _)
  have hd : ((Sites.tensor pro B X).obj (F.obj DA)).map
        (((Sites.hom pro B X).map d.op).app WB) ≫
      (Sites.adj pro B X (F.obj DA)).counit.app WB =
      ((Sites.tensor pro B X).map d).app (((Sites.hom pro B X).obj (op DB)).obj WB) ≫
        (Sites.adj pro B X DB).counit.app WB := by
    simpa only [Functor.uncurry_obj_map, _root_.CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp, Category.comp_id] using
      normalized_stage_site_evaluation_dinaturality pro B X DB (F.obj DA) WB d
  refine bidual_by_transpose (Sites.tensor pro A X) (Sites.tensor pro B X) F μ
    ((Sites.hom pro B X).obj (op (F.obj DA))) (Sites.adj pro B X (F.obj DA)) WB
    (Sites.dualMap pro φ c μ w DA) d (Sites.bidual pro A X bA WA K)
    (Sites.bidual pro B X bB WB (F.obj K)) (((Sites.hom pro B X).map d.op).app WB)
    ((Sites.adj pro A X DA).counit.app WA) ((Sites.adj pro B X DB).counit.app WB)
    w ?_ hd ?_
  · exact dualMap_evaluation_left pro φ c μ w DA
  · exact (congrArg (fun z ↦ ((Sites.tensor pro B X).map d).app (F.obj K) ≫ z)
      hδB).trans (he.trans (congrArg
        (fun z ↦ μ.inv.app (DA, K) ≫ F.map z ≫ w) hδA.symm))

/-- The evaluation and double-dual equations, separated from transport and site equations.
Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraph 3;
(blueprint: lem-sf-normalized-stage-comparison-pairing). -/
def StageComparisonPairing (pro : Bool)
    (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T X Z S : Scheme.{u}} (_f : T ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    {aX : X ⟶ S} (c : Compactification aX)
    (μ : ∀ {s t : Stage l E} (a : Arrow s t), Sites.TensorComparison pro a.ringMap X)
    (σ : ∀ s : Stage l E, Sites.tensor pro s.ring X ≅ (Sites.tensor pro s.ring X).flip) : Prop :=
  (∀ {s t : Stage l E} (a : Arrow s t) (K : Sites.D pro s.ring X),
    Sites.Ctf pro s.ring X K →
      ((Sites.tensor pro t.ring X).map
        (Sites.dualMap pro a.ringMap c (μ a) (Sites.stageOmegaMap pro a c) K)).app
          ((Sites.scalar pro a.ringMap X).obj K) ≫
        Sites.evaluation pro t.ring X (σ t) (Sites.omega pro t.ring c)
          ((Sites.scalar pro a.ringMap X).obj K) =
      (μ a).inv.app ((Sites.dual pro s.ring c).obj (op K), K) ≫
        (Sites.scalar pro a.ringMap X).map
          (Sites.evaluation pro s.ring X (σ s) (Sites.omega pro s.ring c) K) ≫
          Sites.stageOmegaMap pro a c) ∧
  (∀ {s t : Stage l E} (a : Arrow s t) (K : Sites.D pro s.ring X),
    Sites.Ctf pro s.ring X K →
      (Sites.scalar pro a.ringMap X).map
          (Sites.bidual pro s.ring X (σ s) (Sites.omega pro s.ring c) K) ≫
        Sites.dualMap pro a.ringMap c (μ a) (Sites.stageOmegaMap pro a c)
          ((Sites.dual pro s.ring c).obj (op K)) =
      Sites.bidual pro t.ring X (σ t) (Sites.omega pro t.ring c)
          ((Sites.scalar pro a.ringMap X).obj K) ≫
        (Sites.dual pro t.ring c).map
          (Sites.dualMap pro a.ringMap c (μ a) (Sites.stageOmegaMap pro a c) K).op)

/-- The fixed maps satisfy evaluation and biduality coherence.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraph 3;
(blueprint: lem-sf-normalized-stage-comparison-pairing).

Proof: transpose the evaluation equation through the tensor-Hom adjunction and use the
ordinary balanced tensor normalization. Transpose once more for the double-dual equation;
the two resulting composites are the same extended evaluation pairing, with the Koszul
interchange supplied by the normalized symmetry. -/
theorem normalized_stage_comparison_pairing
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T X Z : Scheme.{u})
    [T.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (T ↘ Spec (.of D.k))] [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    (f : T ⟶ X) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of D.k))]
    (c : Compactification (X ↘ Spec (.of D.k)))
    (μ : ∀ pro : Bool, ∀ {s t : Stage l E} (a : Arrow s t),
      Sites.TensorComparison pro a.ringMap X)
    (hμ : ∀ (pro : Bool) {s t : Stage l E} (a : Arrow s t),
      Sites.NormalizedTensor pro a.ringMap X (μ pro a))
    (σ : ∀ (pro : Bool) (s : Stage l E),
      Sites.tensor pro s.ring X ≅ (Sites.tensor pro s.ring X).flip)
    (hσ : ∀ (pro : Bool) (s : Stage l E),
      Sites.NormalizedSymmetry pro s.ring X (σ pro s))
    (hi : ∀ pro : Bool, Sites.StageComparisonIsomorphisms pro l E f i c (μ pro))
    (hsi : letI := c.hasCompactification
      Sites.StageComparisonSiteIsomorphisms l E f i c) :
    ∀ pro : Bool, StageComparisonPairing pro l E f i c (μ pro) (σ pro) := by
  have _ := hl
  have _ := hi
  have _ := hsi
  intro pro
  constructor
  · intro s t a K _
    exact dualMap_evaluation pro a.ringMap c (μ pro a) (σ pro s) (σ pro t)
      (scalar_braiding pro a.ringMap X (μ pro a) (hμ pro a)
        (σ pro s) (σ pro t) (hσ pro s) (hσ pro t)) (Sites.stageOmegaMap pro a c) K
  · intro s t a K _
    exact dualMap_bidual pro a.ringMap c (μ pro a) (σ pro s) (σ pro t)
      (Sites.stageOmegaMap pro a c) K
      (dualMap_evaluation pro a.ringMap c (μ pro a) (σ pro s) (σ pro t)
        (scalar_braiding pro a.ringMap X (μ pro a) (hμ pro a)
          (σ pro s) (σ pro t) (hσ pro s) (hσ pro t)) (Sites.stageOmegaMap pro a c) K)

end WeilConjectures.FiniteFreeCoefficients
