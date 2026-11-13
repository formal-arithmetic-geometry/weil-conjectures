/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphPresentation
public import WeilConjectures.AlgebraicGeometry.EtaleProperOpenExchangeCube
import WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonOpenShrink
import WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonProperAmbient

/-! # Pairwise product-graph normalization of étale presentation comparisons

Source: Stacks Project, more-etale.tex, Tags 0F7B, 0F7C, 0F7D and 0F7J;
`LowerShriekComposition.lean`, lines 193--268, product-graph formula, extended to two
proper/open/proper presentations.

The auxiliary declarations construct the literal fibre products and the displayed lambda
maps. Only their geometric properties and the final comparison equation are postponed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

namespace EtaleGraphPresentation.PairwiseProduct

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (s t : EtaleGraphPresentation f)

/-- The proper ambient product (Stacks, Tag 0F7J). -/
abbrev P : Scheme.{u} := pullback s.p t.p

/-- The product of the supporting opens over the base (Stacks, Tag 0F7J). -/
abbrev U : Scheme.{u} := pullback (s.e ≫ s.p) (t.e ≫ t.p)

/-- The graph of the two proper first factors (Stacks, Tag 0F7J). -/
def a : X ⟶ U s t := pullback.lift s.a t.a (s.fac.trans t.fac.symm)

/-- The actual product of the open immersions, over the identity of the base (Stacks, Tag 0F7J). -/
def b : U s t ⟶ P s t :=
  pullback.map (s.e ≫ s.p) (t.e ≫ t.p) s.p t.p s.e t.e (𝟙 Y)
    (Category.comp_id _) (Category.comp_id _)

/-- The structural map of the product. Its other expression is `pullback.condition`
(Stacks, Tag 0F7J). -/
def p : P s t ⟶ Y := pullback.fst s.p t.p ≫ s.p

/-- The first supporting neighborhood (Stacks, Tag 0F7J). -/
abbrev O₁ : Scheme.{u} := pullback (pullback.fst s.p t.p) s.e

/-- The second supporting neighborhood (Stacks, Tag 0F7J). -/
abbrev O₂ : Scheme.{u} := pullback (pullback.snd s.p t.p) t.e

/-- The projection equations defining the induced maps to both neighborhoods (Stacks, Tag 0F7J). -/
theorem b_projections :
    b s t ≫ pullback.fst s.p t.p = pullback.fst (s.e ≫ s.p) (t.e ≫ t.p) ≫ s.e ∧
    b s t ≫ pullback.snd s.p t.p = pullback.snd (s.e ≫ s.p) (t.e ≫ t.p) ≫ t.e := by
  constructor <;> simp [b]

/-- The canonical map to the first neighborhood (Stacks, Tag 0F7J). -/
def v₁ : U s t ⟶ O₁ s t :=
  pullback.lift (b s t) (pullback.fst (s.e ≫ s.p) (t.e ≫ t.p)) (b_projections s t).1

/-- The canonical map to the second neighborhood (Stacks, Tag 0F7J). -/
def v₂ : U s t ⟶ O₂ s t :=
  pullback.lift (b s t) (pullback.snd (s.e ≫ s.p) (t.e ≫ t.p)) (b_projections s t).2

/-- The first neighborhood graph (Stacks, Tag 0F7J). -/
def z₁ : X ⟶ O₁ s t := a s t ≫ v₁ s t

/-- The second neighborhood graph (Stacks, Tag 0F7J). -/
def z₂ : X ⟶ O₂ s t := a s t ≫ v₂ s t

/-- The geometric properties of the explicitly constructed product diagram
(Stacks, Tags 01W3, 01W4, 01W6 and 0F7J). -/
structure Geometry : Prop where
  properA : IsProper (a s t)
  openB : IsOpenImmersion (b s t)
  properP : IsProper (p s t)
  openV₁ : IsOpenImmersion (v₁ s t)
  openV₂ : IsOpenImmersion (v₂ s t)
  properZ₁ : IsProper (z₁ s t)
  properZ₂ : IsProper (z₂ s t)
  fac : a s t ≫ b s t ≫ p s t = f
  z₁_q : z₁ s t ≫ pullback.snd (pullback.fst s.p t.p) s.e = s.a
  z₂_q : z₂ s t ≫ pullback.snd (pullback.snd s.p t.p) t.e = t.a
  v₁_b : v₁ s t ≫ pullback.fst (pullback.fst s.p t.p) s.e = b s t
  v₂_b : v₂ s t ≫ pullback.fst (pullback.snd s.p t.p) t.e = b s t

/-- The products form a proper/open/proper presentation, with both neighborhood graphs proper
(Stacks, Tags 01W3, 01W4, 01W6 and 0F7J). -/
theorem geometry : Geometry s t := by
  have hb : IsOpenImmersion (b s t) := by
    exact MorphismProperty.pullbackMap (P := @IsOpenImmersion)
      inferInstance inferInstance rfl rfl
  have hv₁ : IsOpenImmersion (v₁ s t) := by
    have : IsOpenImmersion
        (v₁ s t ≫ pullback.fst (pullback.fst s.p t.p) s.e) := by
      simpa [v₁] using hb
    exact IsOpenImmersion.of_comp _ (pullback.fst (pullback.fst s.p t.p) s.e)
  have hv₂ : IsOpenImmersion (v₂ s t) := by
    have : IsOpenImmersion
        (v₂ s t ≫ pullback.fst (pullback.snd s.p t.p) t.e) := by
      simpa [v₂] using hb
    exact IsOpenImmersion.of_comp _ (pullback.fst (pullback.snd s.p t.p) t.e)
  have hz₁ : z₁ s t ≫ pullback.snd (pullback.fst s.p t.p) s.e = s.a := by
    simp [z₁, v₁, a]
  have hz₂ : z₂ s t ≫ pullback.snd (pullback.snd s.p t.p) t.e = t.a := by
    simp [z₂, v₂, a]
  have ha : IsProper (a s t) := by
    have : IsProper
        (a s t ≫ pullback.fst (s.e ≫ s.p) (t.e ≫ t.p)) := by
      simpa [a] using s.properA
    exact IsProper.of_comp _ (pullback.fst (s.e ≫ s.p) (t.e ≫ t.p))
  refine ⟨ha, hb, ?_, hv₁, hv₂, ?_, ?_, ?_, hz₁, hz₂, ?_, ?_⟩
  · dsimp [p]
    infer_instance
  · have : IsProper (z₁ s t ≫ pullback.snd (pullback.fst s.p t.p) s.e) := by
      rw [hz₁]
      infer_instance
    exact IsProper.of_comp _ (pullback.snd (pullback.fst s.p t.p) s.e)
  · have : IsProper (z₂ s t ≫ pullback.snd (pullback.snd s.p t.p) t.e) := by
      rw [hz₂]
      infer_instance
    exact IsProper.of_comp _ (pullback.snd (pullback.snd s.p t.p) t.e)
  · simpa [a, b, p] using s.fac
  · simp [v₁]
  · simp [v₂]

/-- The product presentation with exactly the constructed maps (Stacks, Tag 0F7J). -/
def presentation : EtaleGraphPresentation f where
  U := U s t
  P := P s t
  a := a s t
  e := b s t
  p := p s t
  properA := (geometry s t).properA
  openE := (geometry s t).openB
  properP := (geometry s t).properP
  fac := (geometry s t).fac

end EtaleGraphPresentation.PairwiseProduct

/-- The displayed lambda word for one projection of the product presentation.
The first exchange is Gamma_D. The shrinking isomorphism is Gamma_E with its identity-open
factor removed; its inverse has the orientation in lambda. Both squares are Cartesian, so
these are exactly the normalized maps of the proper/open exchange cube
(Stacks, Tags 0F7B, 0F7C, 0F7D and 0F7J). -/
def etaleProductGraphLambda
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (s t : EtaleGraphPresentation f)
    {O : Scheme.{u}} (pr : t.P ⟶ s.P) [IsProper pr]
    (q : O ⟶ s.U) (j : O ⟶ t.P) [IsOpenImmersion j]
    (v : t.U ⟶ O) [IsOpenImmersion v] (z : X ⟶ O) [IsProper z]
    (Dsq : IsPullback q j s.e pr)
    (hz : z ≫ q = s.a) (hp : pr ≫ s.p = t.p)
    (hav : t.a ≫ v = z) (hvb : v ≫ j = t.e) :
    s.functor A ≅ t.functor A :=
  Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) z q s.a hz).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (openImmersionLowerShriekLowerStarExchangeIso A Dsq) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) pr s.p t.p hp)) ≪≫
    Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A t.a v z hav).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) v j).symm ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) hvb) _)

namespace EtaleGraphPresentation.PairwiseProduct

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (s t : EtaleGraphPresentation f)

/-- Lambda₁, with the literal first product projection and its pullback neighborhood
(Stacks, Tags 0F7B, 0F7D and 0F7J). -/
def lambda₁ (A : Type (u + 1)) [CommRing A] [Finite A] :
    s.functor A ≅ (presentation s t).functor A :=
  letI := (geometry s t).openV₁
  letI := (geometry s t).properZ₁
  etaleProductGraphLambda A s (presentation s t) (pullback.fst s.p t.p)
    (pullback.snd (pullback.fst s.p t.p) s.e)
    (pullback.fst (pullback.fst s.p t.p) s.e) (v₁ s t) (z₁ s t)
    (IsPullback.of_hasPullback (pullback.fst s.p t.p) s.e).flip
    (geometry s t).z₁_q rfl rfl (geometry s t).v₁_b

/-- Lambda₂, with the second product projection and the same product structural map
(Stacks, Tags 0F7B, 0F7D and 0F7J). -/
def lambda₂ (A : Type (u + 1)) [CommRing A] [Finite A] :
    t.functor A ≅ (presentation s t).functor A :=
  letI := (geometry s t).openV₂
  letI := (geometry s t).properZ₂
  etaleProductGraphLambda A t (presentation s t) (pullback.snd s.p t.p)
    (pullback.snd (pullback.snd s.p t.p) t.e)
    (pullback.fst (pullback.snd s.p t.p) t.e) (v₂ s t) (z₂ s t)
    (IsPullback.of_hasPullback (pullback.snd s.p t.p) t.e).flip
    (geometry s t).z₂_q pullback.condition.symm rfl (geometry s t).v₂_b

end EtaleGraphPresentation.PairwiseProduct

private theorem comparisonFromOpen_productGraphLambda
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (s t : EtaleGraphPresentation f) {O : Scheme.{u}}
    (pr : t.P ⟶ s.P) [IsProper pr]
    (q : O ⟶ s.U) (j : O ⟶ t.P) [IsOpenImmersion j]
    (v : t.U ⟶ O) [IsOpenImmersion v] (z : X ⟶ O) [IsProper z]
    (sq : IsPullback q j s.e pr) (hz : z ≫ q = s.a) (hp : pr ≫ s.p = t.p)
    (hav : t.a ≫ v = z) (hvb : v ≫ j = t.e) :
    etaleGraphComparisonFromOpen A c s ≪≫
        etaleProductGraphLambda A s t pr q j v z sq hz hp hav hvb =
      etaleGraphComparisonFromOpen A c t := by
  let H : EtaleGraphPresentation f := {
    U := O
    P := t.P
    a := z
    e := j
    p := t.p
    fac := by
      rw [← hp]
      calc
        z ≫ j ≫ pr ≫ s.p = z ≫ (q ≫ s.e) ≫ s.p := by
          rw [sq.w]
          simp only [Category.assoc]
        _ = f := by simpa only [← Category.assoc, hz] using s.fac }
  let l : s.functor A ≅ H.functor A :=
    Functor.isoWhiskerRight
        (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) z q s.a hz).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (openImmersionLowerShriekLowerStarExchangeIso A sq) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) pr s.p t.p hp))
  let r : H.functor A ≅ t.functor A :=
    Functor.isoWhiskerRight
        (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A t.a v z hav).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          ((mapDerivedCategoryOpenImmersionLowerShriekComp
              (ModuleCat.{u + 1} A) v j).symm ≪≫
            mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) hvb) _)
  have hl : etaleGraphComparisonFromOpen A c s ≪≫ l =
      etaleGraphComparisonFromOpen A c H :=
    etaleGraphComparisonFromOpen_properAmbient A c s H pr q sq hz hp
  have hr : etaleGraphComparisonFromOpen A c H ≪≫ r =
      etaleGraphComparisonFromOpen A c t :=
    etaleGraphComparisonFromOpen_openShrink A c H t.a v t.e hav hvb
  calc
    _ = (etaleGraphComparisonFromOpen A c s ≪≫ l) ≪≫ r := by
      simp only [etaleProductGraphLambda, l, r, H, Iso.trans_assoc]
    _ = etaleGraphComparisonFromOpen A c t := by rw [hl, hr]

/-- The specified pairwise graph comparison is `lambda₂⁻¹ lambda₁` (Stacks, Tags 0F7B, 0F7C,
0F7D and 0F7J). -/
theorem etalePairwiseProductGraphNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (s t : EtaleGraphPresentation f) :
    etaleGraphComparison A c s t =
      EtaleGraphPresentation.PairwiseProduct.lambda₁ s t A ≪≫
        (EtaleGraphPresentation.PairwiseProduct.lambda₂ s t A).symm := by
  let r := EtaleGraphPresentation.PairwiseProduct.presentation s t
  have h₁ : etaleGraphComparisonFromOpen A c s ≪≫
      EtaleGraphPresentation.PairwiseProduct.lambda₁ s t A =
        etaleGraphComparisonFromOpen A c r := by
    let := (EtaleGraphPresentation.PairwiseProduct.geometry s t).openV₁
    let := (EtaleGraphPresentation.PairwiseProduct.geometry s t).properZ₁
    exact comparisonFromOpen_productGraphLambda A c s r _ _ _ _ _ _ _ _ _ _
  have h₂ : etaleGraphComparisonFromOpen A c t ≪≫
      EtaleGraphPresentation.PairwiseProduct.lambda₂ s t A =
        etaleGraphComparisonFromOpen A c r := by
    let := (EtaleGraphPresentation.PairwiseProduct.geometry s t).openV₂
    let := (EtaleGraphPresentation.PairwiseProduct.geometry s t).properZ₂
    exact comparisonFromOpen_productGraphLambda A c t r _ _ _ _ _ _ _ _ _ _
  change (etaleGraphComparisonFromOpen A c s).symm ≪≫
    etaleGraphComparisonFromOpen A c t = _
  have h := congrArg
    (fun k ↦ k ≪≫ (EtaleGraphPresentation.PairwiseProduct.lambda₂ s t A).symm)
    (h₁.trans h₂.symm)
  simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] at h
  rw [← h]
  simp only [Iso.symm_self_id_assoc]

end AlgebraicGeometry.Etale
