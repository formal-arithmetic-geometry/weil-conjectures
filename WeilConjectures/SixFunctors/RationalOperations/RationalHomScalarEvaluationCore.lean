/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalOperations.RationalHomScalarCounitNormalization
import WeilConjectures.SixFunctors.Rational.RationalHomScalarTranspose
import WeilConjectures.SixFunctors.Rational.RationalTensorSymmetry

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalOperations

private theorem inverseTranspose_evaluation
    {C : Type v} [Category.{w} C] [Preadditive C]
    {T : C × C ⥤ C} {J : ObjectProperty (Cᵒᵖ × C)} {H : J.FullSubcategory ⥤ C}
    (S : PodPartialClosed T J H) (A : C) (P : J.FullSubcategory) (f : A ⟶ H.obj P) :
    (S.transpose A P).symm f = T.map (Prod.mkHom f (𝟙 _)) ≫ S.evaluation P := by
  apply (S.transpose A P).injective
  rw [AddEquiv.apply_symm_apply, S.parameter_naturality]
  simp only [PodPartialClosed.evaluation, AddEquiv.apply_symm_apply, Category.comp_id]

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]

variable (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- Closed transpose transports normalized counits through the rational tensor and Hom
scalar comparisons. This is the categorical core of finite scalar evaluation.
Source: finite scalar evaluation argument, transpose paragraph
(blueprint: lem-sf-rational-hom-scalar-evaluation). -/
theorem scalarEvaluation_of_normalizedCounits
    (hE : ∀ K M : sfRationalConstructibleCategory l E X,
      constructibleRationalHomPairs l E X (op K, M))
    (hL : ∀ K M : sfRationalConstructibleCategory l L X,
      constructibleRationalHomPairs l L X (op K, M))
    (eE : ∀ K M : sfRationalConstructibleCategory l E X,
      (RationalVerdier.tensor D l hl X E).obj
          (K, (homRight l E X hE K).obj M) ⟶ M)
    (eL : ∀ K M : sfRationalConstructibleCategory l L X,
      (RationalVerdier.tensor D l hl X L).obj
          (K, (homRight l L X hL K).obj M) ⟶ M)
    (heE : ∀ K M, eE K M = normalizedCounit D l hl X E hE K M)
    (heL : ∀ K M, eL K M = normalizedCounit D l hl X L hL K M) :
    ∀ K M : sfRationalConstructibleCategory l E X,
      (RationalVerdier.tensor D l hl X L).map
          (Prod.mkHom (𝟙 ((RationalVerdier.scalar l X E L ι).obj K))
            (rationalHomScalarComparison l E L ι X
              ⟨(op K, M), hE K M⟩).hom) ≫ eL
          ((RationalVerdier.scalar l X E L ι).obj K)
          ((RationalVerdier.scalar l X E L ι).obj M) =
        (@rationalTensorScalarComparison l _ E _ _ _ L _ _ _ ι X
          (RationalVerdier.units D l hl X)).inv.app
            (K, (homRight l E X hE K).obj M) ≫
          (RationalVerdier.scalar l X E L ι).map (eE K M) := by
  let := RationalVerdier.units D l hl X
  intro K M
  let F := RationalVerdier.scalar l X E L ι
  let T := RationalVerdier.tensor D l hl X L
  let S := @podRationalClosed l _ E _ _ _ X (RationalVerdier.units D l hl X)
  let SL := @podRationalClosed l _ L _ _ _ X (RationalVerdier.units D l hl X)
  let PE : (constructibleRationalHomPairs l E X).FullSubcategory :=
    ⟨(op K, M), hE K M⟩
  let PL := rationalHomScalarPair l E L ι X PE
  let H := (rationalDerivedInternalHom l E X).obj PE
  let HL := (rationalDerivedInternalHom l L X).obj PL
  let c := (rationalHomScalarComparison l E L ι X PE).hom
  have ht := (rationalHomScalar_transpose D l hl X E L ι).1 H K M
    (hE K M) (S.evaluation PE)
  have ht' : SL.transpose (F.obj H) PL
      ((rationalTensorScalarComparison l E L ι X).inv.app (H, K) ≫
        F.map (S.evaluation PE)) = c := by
    change SL.transpose (F.obj H) PL
      ((rationalTensorScalarComparison l E L ι X).inv.app (H, K) ≫
        F.map (S.evaluation PE)) = F.map (S.transpose H PE (S.evaluation PE)) ≫ c at ht
    have hid : S.transpose H PE (S.evaluation PE) = 𝟙 H :=
      (S.transpose H PE).apply_symm_apply (𝟙 H)
    rw [hid, F.map_id, Category.id_comp] at ht
    exact ht
  have hev : T.map (Prod.mkHom c (𝟙 (F.obj K))) ≫ SL.evaluation PL =
      (rationalTensorScalarComparison l E L ι X).inv.app (H, K) ≫
        F.map (S.evaluation PE) := by
    calc
      _ = (SL.transpose (F.obj H) PL).symm c :=
        (inverseTranspose_evaluation SL (F.obj H) PL c).symm
      _ = _ := (congrArg (SL.transpose (F.obj H) PL).symm ht').symm.trans
        ((SL.transpose (F.obj H) PL).symm_apply_apply _)
  have hn := (rationalTensorSymmetry_laws D l hl X L).1
    HL (F.obj K) (F.obj H) (F.obj K) c (𝟙 _)
  have hs := (rationalHomScalar_transpose D l hl X E L ι).2 H K
  rw [heL, heE]
  change T.map (Prod.mkHom (𝟙 (F.obj K)) c) ≫
      (pullbackTensorRationalBraiding l L X (F.obj K) HL).hom ≫ SL.evaluation PL =
    (rationalTensorScalarComparison l E L ι X).inv.app (K, H) ≫
      F.map ((pullbackTensorRationalBraiding l E X K H).hom ≫ S.evaluation PE)
  rw [← reassoc_of% hn, hev, ← Category.assoc, hs, Category.assoc,
    ← CategoryTheory.Functor.map_comp]

end WeilConjectures.RationalOperations
