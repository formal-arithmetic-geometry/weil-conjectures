/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import all WeilConjectures.SmoothPurity.Sf.SfRationalDirectImageAdjunction
import WeilConjectures.SixFunctors.Integral.IntegralFiniteTorProperProjection
import all WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorNaturality
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # The proper projection mate over one finite coefficient field

Source: thm-sf-pf-field; BS 6.8.14--6.8.15.
(blueprint: lem-sf-rational-proper-projection-invertible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.commonStageDerivedPullback WeilConjectures.commonStageDerivedTensor

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

-- The calculation is performed in abstract linear categories, before instantiating
-- the large constructible derived categories.
namespace CategoryTheory.ScalarLocalization
open TensorProduct
universe r c d v w
variable {R : Type r} [CommRing R] (p : R)
  {C : Type c} [Category.{v} C] [Preadditive C] [Linear R C]
  {D : Type d} [Category.{w} D] [Preadditive D] [Linear R D]
  (F : C ⥤ D) [F.Additive] [F.Linear R]
  (G : D ⥤ C) [G.Additive] [G.Linear R] (a : F ⊣ G)

private theorem localized_unit_heq {M : ScalarLocalization R C p} {N : C}
    (h : M = (localization R C p).obj N) :
    HEq ((liftAdjunction R p F G a).unit.app M)
      ((localization R C p).map (a.unit.app N)) := by
  cases h
  rfl

private theorem localized_map_heq {M N : ScalarLocalization R C p} {M' N' : C}
    (hM : M = (localization R C p).obj M')
    (hN : N = (localization R C p).obj N')
    {f : M ⟶ N} {g : M' ⟶ N'}
    (hf : HEq f ((localization R C p).map g)) :
    HEq ((liftLinear R p F).map f) ((localization R D p).map (F.map g)) := by
  cases hM
  cases hN
  cases hf
  exact heq_of_eq (liftLinear_tmul R p F 1 g)

private theorem localized_projection_isIso
    (T : C × C ⥤ C) (U : D × D ⥤ D)
    (mu : ∀ M N, F.obj (T.obj (M, N)) ⟶ U.obj (F.obj M, F.obj N))
    (Tq : ScalarLocalization R C p × ScalarLocalization R C p ⥤
      ScalarLocalization R C p)
    (Uq : ScalarLocalization R D p × ScalarLocalization R D p ⥤
      ScalarLocalization R D p)
    (hT : ∀ M N, Tq.obj (M, N) = (localization R C p).obj (T.obj (M.obj, N.obj)))
    (hU : ∀ M N, Uq.obj (M, N) = (localization R D p).obj (U.obj (M.obj, N.obj)))
    (mU : ∀ (M M' N N' : ScalarLocalization R D p)
      (f : M.obj ⟶ M'.obj) (g : N.obj ⟶ N'.obj),
      HEq (Uq.map (Prod.mkHom ((localization R D p).map f)
        ((localization R D p).map g)))
        ((localization R D p).map (U.map (Prod.mkHom f g))))
    (F' : ScalarLocalization R C p ⥤ ScalarLocalization R D p)
    (hF' : F' = liftLinear R p F)
    (aq' : F' ⊣ liftLinear R p G)
    (haq' : HEq aq' (liftAdjunction R p F G a))
    (muq : ∀ M N, F'.obj (Tq.obj (M, N)) ⟶
      Uq.obj (F'.obj M, F'.obj N))
    (hmu : ∀ M N, HEq (muq M N) ((localization R D p).map (mu M.obj N.obj)))
    (K : ScalarLocalization R D p) (L : ScalarLocalization R C p)
    (hi : IsIso (a.homEquiv _ _ (mu (G.obj K.obj) L.obj ≫
      U.map (Prod.mkHom (a.counit.app K.obj) (𝟙 _))))) :
    IsIso (aq'.homEquiv _ _
      (muq ((liftLinear R p G).obj K) L ≫
        Uq.map (Prod.mkHom (aq'.counit.app K) (𝟙 _)))) := by
  subst F'
  cases haq'
  let Q := localization R C p
  let S := localization R D p
  let Fq := liftLinear R p F
  let Gq := liftLinear R p G
  let aq := liftAdjunction R p F G a
  let z := mu (G.obj K.obj) L.obj ≫ U.map (Prod.mkHom (a.counit.app K.obj) (𝟙 _))
  have hs := hT (Gq.obj K) L
  have hm := hU (Fq.obj (Gq.obj K)) (Fq.obj L)
  have ht := hU K (Fq.obj L)
  have hmid : Fq.obj (Tq.obj (Gq.obj K, L)) = S.obj (F.obj (T.obj
      (G.obj K.obj, L.obj))) := congrArg Fq.obj hs
  have hz : HEq (muq (Gq.obj K) L ≫
      Uq.map (Prod.mkHom (aq.counit.app K) (𝟙 _))) (S.map z) := by
    have hc := mU (Fq.obj (Gq.obj K)) K (Fq.obj L) (Fq.obj L)
      (a.counit.app K.obj) (𝟙 (F.obj L.obj))
    have hcomp := heq_comp hmid hm ht (hmu (Gq.obj K) L) hc
    exact hcomp.trans (heq_of_eq (S.map_comp _ _).symm)
  have hg := localized_map_heq p G hmid ht hz
  have hunit := localized_unit_heq p F G a hs
  have he := heq_comp hs (congrArg Gq.obj hmid) (congrArg Gq.obj ht) hunit hg
  have he' : HEq (aq.homEquiv _ _ (muq (Gq.obj K) L ≫
      Uq.map (Prod.mkHom (aq.counit.app K) (𝟙 _))))
      (Q.map (a.homEquiv _ _ z)) := by
    rw [aq.homEquiv_unit, a.homEquiv_unit, Q.map_comp]
    exact he
  have hii : IsIso (Q.map (a.homEquiv _ _ z)) := by
    let := hi
    exact Q.map_isIso _
  have heq := (conj_eqToHom_iff_heq _ _ hs (congrArg Gq.obj ht)).mpr he'
  rw [heq]
  infer_instance
end CategoryTheory.ScalarLocalization

namespace CategoryTheory
private theorem adjunction_transport_heq
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G : D ⥤ C} (h : F = F') (a : F ⊣ G) :
    HEq (h ▸ a : F' ⊣ G) a := by
  cases h
  rfl

private theorem projection_isIso_of_rightAdjoint
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G H : D ⥤ C} (a : F ⊣ G) (b : F ⊣ H)
    (T : C × C ⥤ C) (U : D × D ⥤ D)
    (mu : T ⋙ F ⟶ F.prod F ⋙ U) (K : D) (L : C)
    (hi : IsIso (a.homEquiv _ _ (mu.app (G.obj K, L) ≫
      U.map (Prod.mkHom (a.counit.app K) (𝟙 _))))) :
    IsIso (b.homEquiv _ _ (mu.app (H.obj K, L) ≫
      U.map (Prod.mkHom (b.counit.app K) (𝟙 _)))) := by
  let e := a.rightAdjointUniq b
  have h : T.map (Prod.mkHom (e.hom.app K) (𝟙 L)) ≫
      b.homEquiv _ _ (mu.app (H.obj K, L) ≫
        U.map (Prod.mkHom (b.counit.app K) (𝟙 _))) =
    a.homEquiv _ _ (mu.app (G.obj K, L) ≫
      U.map (Prod.mkHom (a.counit.app K) (𝟙 _))) ≫
        e.hom.app (U.obj (K, F.obj L)) := by
    apply (b.homEquiv _ _).symm.injective
    rw [b.homEquiv_naturality_left_symm, Equiv.symm_apply_apply,
      b.homEquiv_counit]
    simp only [F.map_comp, Category.assoc]
    dsimp only [Functor.id_obj, Functor.comp_obj]
    rw [show F.map (e.hom.app (U.obj (K, F.obj L))) ≫
      b.counit.app (U.obj (K, F.obj L)) = a.counit.app _ from
        a.rightAdjointUniq_hom_app_counit b _]
    rw [← a.homEquiv_counit, Equiv.symm_apply_apply]
    have hn := mu.naturality (Prod.mkHom (e.hom.app K) (𝟙 L))
    dsimp only [Functor.comp_map, Functor.prod_map] at hn
    rw [← Category.assoc, hn, Category.assoc, ← U.map_comp]
    congr 2
    ext
    · exact a.rightAdjointUniq_hom_app_counit b K
    · simp
  have : IsIso (Prod.mkHom (e.hom.app K) (𝟙 L)) :=
    (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
  have : IsIso (T.map (Prod.mkHom (e.hom.app K) (𝟙 L)) ≫
      b.homEquiv _ _ (mu.app (H.obj K, L) ≫
        U.map (Prod.mkHom (b.counit.app K) (𝟙 _)))) := by
    rw [h]
    let := hi
    infer_instance
  exact (isIso_comp_left_iff _ _).mp this
end CategoryTheory

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- The normalized counit projection at a finite rational coefficient stage.
Source: def-exchange-projection, with the identity open factor.
(blueprint: lem-sf-rational-proper-projection-invertible). -/
def rationalProperProjection (f : X ⟶ Y)
    (G : sfRationalConstructibleCategory l E X ⥤ sfRationalConstructibleCategory l E Y)
    (a : rationalDerivedPullback l E f ⊣ G)
    (K : sfRationalConstructibleCategory l E X)
    (L : sfRationalConstructibleCategory l E Y) :
    (rationalDerivedTensor l E Y).obj (G.obj K, L) ⟶
      G.obj ((rationalDerivedTensor l E X).obj
        (K, (rationalDerivedPullback l E f).obj L)) :=
  a.homEquiv _ _ ((canonicalRationalPullbackTensor l E f (G.obj K) L).hom ≫
    (rationalDerivedTensor l E X).map (Prod.mkHom (a.counit.app K) (𝟙 _)))

/-- The proper counit projection is invertible at a finite rational coefficient field.
Source: thm-sf-pf-field.proof.md, rational stage and compatibility;
BS Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-rational-proper-projection-invertible).

Proof: every object of the raw rational constructible category is the image of
its integral object. The integral residue-field Tor criterion supplies a uniform
Tor interval for each constructible derived-complete representative. Apply the
integral projection formula and rationalize its map and inverse. Use the
compactification (identity,f). The identity extension and its tensor comparison
cancel by the adjunction unit identity. The integral/rational pullback and tensor
normalizations identify the resulting transpose with the canonical rational
pullback tensor comparison followed by the counit. The localized integral
pullback/direct-image adjunction supplies one right adjoint. For any supplied a,
the unique right-adjoint comparison intertwines the counits; transposing this
equation identifies rationalProperProjection with the preceding isomorphism
conjugated by that comparison and its tensor. Hence it too is invertible.
This is a statement at one finite coefficient field, with no common-stage descent
or continuous-coefficient realization. Zero complexes and empty schemes use the
same localization and identity-open calculation. -/
theorem rationalProperProjection_isIso
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (G : sfRationalConstructibleCategory l E X ⥤ sfRationalConstructibleCategory l E Y)
    (a : rationalDerivedPullback l E f ⊣ G)
    (K : sfRationalConstructibleCategory l E X)
    (L : sfRationalConstructibleCategory l E Y) :
    IsIso (rationalProperProjection l E f G a K L) := by
  let O := Padic.coefficientExtensionIntegers l E
  let p := Padic.coefficientExtensionUniformizer l E
  let I := constructibleIntegralPullback l E f
  obtain ⟨R, ⟨adj⟩, hAdd, hLin⟩ := sfIntegralPullbackLinearAdjunction l E k hl f
  have : R.Additive := hAdd
  have : R.Linear O := hLin
  have : I.Additive := CategoryTheory.additiveLeftOfLinearRight adj
  have : I.Linear O := CategoryTheory.linearLeftOfLinearRight O adj
  let Fq := ScalarLocalization.liftLinear O p I
  let Rq := ScalarLocalization.liftLinear O p R
  have hF : Fq = rationalDerivedPullback l E f := by
    apply (rationalDerivedPullback_existsUnique l E f).unique _
      (rationalDerivedPullback_existsUnique l E f).exists.choose_spec
    refine ⟨inferInstance, (fun _ ↦ rfl), ?_⟩
    intro M N b c
    exact heq_of_eq (ScalarLocalization.liftLinear_tmul O p I c b)
  let aq : rationalDerivedPullback l E f ⊣ Rq :=
    hF ▸ ScalarLocalization.liftAdjunction O p I R adj
  have haq : HEq aq (ScalarLocalization.liftAdjunction O p I R adj) :=
    CategoryTheory.adjunction_transport_heq hF _
  let TX := rationalDerivedTensor l E X
  let TY := rationalDerivedTensor l E Y
  have tensorObj (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :
      ∀ M N : sfRationalConstructibleCategory l E W,
        (rationalDerivedTensor l E W).obj (M, N) =
          (sfRationalConstructibleLocalization l E W).obj
            ((constructibleIntegralTensor l E W).obj (M.obj, N.obj)) :=
    fun M N ↦ (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1 (M, N)
  have tensorMap (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
      (M M' N N' : sfRationalConstructibleCategory l E W)
      (b : M.obj ⟶ M'.obj) (c : N.obj ⟶ N'.obj) :
      HEq ((rationalDerivedTensor l E W).map
        (Prod.mkHom ((sfRationalConstructibleLocalization l E W).map b)
          ((sfRationalConstructibleLocalization l E W).map c)))
        ((sfRationalConstructibleLocalization l E W).map
          ((constructibleIntegralTensor l E W).map (Prod.mkHom b c))) := by
    obtain ⟨β, hβ, hm⟩ :=
      (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.2 M M' N N'
    dsimp only [rationalDerivedTensor]
    rw [hβ]
    simpa only [sfRationalConstructibleLocalization, ScalarLocalization.localization,
      one_mul] using hm b c 1 1
  have hp : IsIso (rationalProperProjection l E f Rq aq K L) := by
    apply ScalarLocalization.localized_projection_isIso p I R adj
      (constructibleIntegralTensor l E Y) (constructibleIntegralTensor l E X)
      (fun M N ↦ (canonicalIntegralPullbackTensor l E f M N).hom) TY TX
      (tensorObj Y) (tensorObj X) (tensorMap X) (rationalDerivedPullback l E f)
      hF.symm aq haq (fun M N ↦ (canonicalRationalPullbackTensor l E f M N).hom)
      (fun M N ↦ (canonicalRationalPullbackTensor_existsUnique l E f M N).exists.choose_spec)
      K L
    obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (l + 1)
    let D : FiniteFieldDatum.{u} := residueTestDatum q hprime
    have hlq : l ≠ D.p := by
      change l ≠ q
      omega
    have tor (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
        (M : sfIntegralConstructibleCategory l E W) :
        finiteTorConstructibleIntegral l E W M.obj :=
      Eq.mp (congrFun (integral_residue_tor D l hlq E W).2 M.obj) M.property
    exact integralFiniteTorProperProjection_isIso l E k hl f R adj K.obj L.obj
      (tor X K.obj) (tor Y L.obj)
  let mu : TY ⋙ rationalDerivedPullback l E f ⟶
      (rationalDerivedPullback l E f).prod (rationalDerivedPullback l E f) ⋙ TX :=
    { app MN := (canonicalRationalPullbackTensor l E f MN.1 MN.2).hom
      naturality {MN MN'} h := canonicalRationalPullbackTensor_naturality l E f h.1 h.2 }
  exact CategoryTheory.projection_isIso_of_rightAdjoint aq a TY TX mu K L hp

end WeilConjectures
