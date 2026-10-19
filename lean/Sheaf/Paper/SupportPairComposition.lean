/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.Paper.SupportPairChainCoherence

/-!
# Composition coherence for adjoint restriction-kernel diagrams

Source: Milne, *Lectures on Étale Cohomology*, Section 9, Theorem 9.4,
pp. 65--67; Stacks Project, Sites, Tag 03CB and Derived Categories, Tag 070I
(blueprint: lem-pur-support-pair-composition).
-/

@[expose] public section

noncomputable section

universe u v u' v' u'' v'' w₀ wQc wQd wQe

open CategoryTheory CategoryTheory.Limits CategoryTheory.ShortComplex

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]
variable {E : Type u''} [Category.{v''} E]
variable (Jc : GrothendieckTopology C) (Jd : GrothendieckTopology D)
  (Je : GrothendieckTopology E)
variable [HasSheafify Jc AddCommGrpCat.{w₀}] [HasSheafify Jd AddCommGrpCat.{w₀}]
  [HasSheafify Je AddCommGrpCat.{w₀}]

/-- The composite support-pair condition uses the composite site functor and
composite adjunction. Source: Milne, Section 9, Theorem 9.4
(blueprint: lem-pur-support-pair-composition). -/
def compositeSupportPairMapCondition
    (u : C ⥤ D) (v : D ⥤ E) [u.IsContinuous Jc Jd] [v.IsContinuous Jd Je]
    (L : Sheaf Jc AddCommGrpCat.{w₀} ⥤ Sheaf Jd AddCommGrpCat.{w₀})
    (M : Sheaf Jd AddCommGrpCat.{w₀} ⥤ Sheaf Je AddCommGrpCat.{w₀})
    (adjL : L ⊣ u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd)
    (adjM : M ⊣ v.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jd Je)
    [L.Additive] [M.Additive]
    (P : SupportPair (C := C)) (P'' : SupportPair (C := E))
    (t : P''.T ⟶ (u ⋙ v).obj P.T) (s : P''.V ⟶ (u ⋙ v).obj P.V)
    {I : CochainComplex (Sheaf Jc AddCommGrpCat.{w₀}) ℤ}
    {N : CochainComplex (Sheaf Je AddCommGrpCat.{w₀}) ℤ}
    (h : ((L ⋙ M).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ N)
    (φ : supportDiagram Jc P I ⟶ supportDiagram Je P'' N) : Prop := by
  letI : (u ⋙ v).IsContinuous Jc Je := Functor.isContinuous_comp u v Jc Jd Je
  exact supportPairMapCondition Jc Je (u ⋙ v) (L ⋙ M) (adjL.comp adjM)
    P P'' t s h φ

omit [HasSheafify Jc AddCommGrpCat.{w₀}] [HasSheafify Jd AddCommGrpCat.{w₀}]
  [HasSheafify Je AddCommGrpCat.{w₀}] in
private theorem adjointSection_comp
    (u : C ⥤ D) (v : D ⥤ E) [u.IsContinuous Jc Jd] [v.IsContinuous Jd Je]
    (L : Sheaf Jc AddCommGrpCat.{w₀} ⥤ Sheaf Jd AddCommGrpCat.{w₀})
    (M : Sheaf Jd AddCommGrpCat.{w₀} ⥤ Sheaf Je AddCommGrpCat.{w₀})
    (adjL : L ⊣ u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd)
    (adjM : M ⊣ v.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jd Je)
    (F : Sheaf Jc AddCommGrpCat.{w₀}) (G : Sheaf Jd AddCommGrpCat.{w₀})
    (H : Sheaf Je AddCommGrpCat.{w₀}) (h : L.obj F ⟶ G) (k : M.obj G ⟶ H)
    (T : C) (T' : D) (T'' : E) (t : T' ⟶ u.obj T) (t' : T'' ⟶ v.obj T') :
    (sectionFunctor Jc T).map ((adjL.comp adjM).homEquiv F H (M.map h ≫ k)) ≫
        (sectionRestriction Je (t' ≫ v.map t)).app H =
      ((sectionFunctor Jc T).map (adjL.homEquiv F G h) ≫
        (sectionRestriction Jd t).app G) ≫
      ((sectionFunctor Jd T').map (adjM.homEquiv G H k) ≫
        (sectionRestriction Je t').app H) := by
  rw [Adjunction.comp_homEquiv]
  change (sectionFunctor Jc T).map
    (adjL.homEquiv F _ (adjM.homEquiv _ H (M.map h ≫ k))) ≫ _ = _
  rw [adjM.homEquiv_naturality_left, adjL.homEquiv_naturality_right,
    Functor.map_comp]
  change ((adjL.homEquiv F G h).hom.app (Opposite.op T) ≫
      (adjM.homEquiv G H k).hom.app (Opposite.op (u.obj T))) ≫
      H.obj.map (t' ≫ v.map t).op = _
  simp only [op_comp, H.obj.map_comp, Category.assoc]
  have hn := (adjM.homEquiv G H k).hom.naturality t.op
  change G.obj.map t.op ≫ (adjM.homEquiv G H k).hom.app (Opposite.op T') =
    (adjM.homEquiv G H k).hom.app (Opposite.op (u.obj T)) ≫
      H.obj.map (v.map t).op at hn
  change _ = ((adjL.homEquiv F G h).hom.app (Opposite.op T) ≫ G.obj.map t.op) ≫
    ((adjM.homEquiv G H k).hom.app (Opposite.op T') ≫ H.obj.map t'.op)
  rw [Category.assoc, ← Category.assoc (G.obj.map t.op), hn]
  simp only [Category.assoc]

omit [HasSheafify Jc AddCommGrpCat.{w₀}] [HasSheafify Jd AddCommGrpCat.{w₀}]
  [HasSheafify Je AddCommGrpCat.{w₀}] in
private theorem supportPair_comp_condition
    (u : C ⥤ D) (v : D ⥤ E) [u.IsContinuous Jc Jd] [v.IsContinuous Jd Je]
    (L : Sheaf Jc AddCommGrpCat.{w₀} ⥤ Sheaf Jd AddCommGrpCat.{w₀})
    (M : Sheaf Jd AddCommGrpCat.{w₀} ⥤ Sheaf Je AddCommGrpCat.{w₀})
    (adjL : L ⊣ u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd)
    (adjM : M ⊣ v.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jd Je)
    [L.Additive] [M.Additive]
    (P : SupportPair (C := C)) (P' : SupportPair (C := D))
    (P'' : SupportPair (C := E))
    (t : P'.T ⟶ u.obj P.T) (s : P'.V ⟶ u.obj P.V)
    (t' : P''.T ⟶ v.obj P'.T) (s' : P''.V ⟶ v.obj P'.V)
    {I : CochainComplex (Sheaf Jc AddCommGrpCat.{w₀}) ℤ}
    {K : CochainComplex (Sheaf Jd AddCommGrpCat.{w₀}) ℤ}
    {N : CochainComplex (Sheaf Je AddCommGrpCat.{w₀}) ℤ}
    (h : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ K)
    (k : (M.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ N)
    (φ : supportDiagram Jc P I ⟶ supportDiagram Jd P' K)
    (ψ : supportDiagram Jd P' K ⟶ supportDiagram Je P'' N)
    (hφ : supportPairMapCondition Jc Jd u L adjL P P' t s h φ)
    (hψ : supportPairMapCondition Jd Je v M adjM P' P'' t' s' k ψ) :
    compositeSupportPairMapCondition Jc Jd Je u v L M adjL adjM P P''
      (t' ≫ v.map t) (s' ≫ v.map s)
      ((M.mapHomologicalComplex (ComplexShape.up ℤ)).map h ≫ k) (φ ≫ ψ) := by
  constructor
  · intro n
    change φ.τ₂.f n ≫ ψ.τ₂.f n = _
    rw [hφ.1 n, hψ.1 n]
    exact (adjointSection_comp Jc Jd Je u v L M adjL adjM
      (I.X n) (K.X n) (N.X n) (h.f n) (k.f n) P.T P'.T P''.T t t').symm
  · intro n
    change φ.τ₃.f n ≫ ψ.τ₃.f n = _
    rw [hφ.2 n, hψ.2 n]
    exact (adjointSection_comp Jc Jd Je u v L M adjL adjM
      (I.X n) (K.X n) (N.X n) (h.f n) (k.f n) P.V P'.V P''.V s s').symm

set_option linter.unusedVariables false in
/-- Composition of the adjoint restriction-kernel maps is the map for the
composite adjunction, and this equality is preserved on cohomology.

Source: Milne, *Lectures on Étale Cohomology*, Section 9, Theorem 9.4,
pp. 65--67; Stacks Project, Sites, Tag 03CB and Derived Categories, Tag 070I
(blueprint: lem-pur-support-pair-composition).

Step 1. Take the degreewise adjoints b of h and c of k. The composite
site functor has precomposition R ∘ R_v, the composite left adjoint is additive
and exact, and the pair square follows by functoriality and the two given
squares. The composite Hom bijection sends k ∘ M(h) to R(c) ∘ b.
On the ambient component, naturality of c along t gives
N(v(t)) ∘ c_(uT) = c_(T') ∘ K(t). Together with restriction along t',
this identifies the composite ambient map with ψ.τ₂ ∘ φ.τ₂. The same
calculation along s,s' gives the restricted component. The kernel maps agree
by their universal property and the monomorphism of the kernel inclusion.
This proves the equality of the two three-component diagram maps, using
clause (1) of lem-pur-support-pair-chain-coherence.

Step 2. A homotopy replacing h induces compatible homotopies on all three
components by clause (2) of lem-pur-support-pair-chain-coherence. Composing
with k gives the homotopy for the composite. Replacing k works in the same
way. Thus the identity persists on cohomology under either replacement.

Step 3. For bounded-below injective I,K,N, clause (2) of
lem-pur-support-pair-chain-coherence identifies derived morphisms with chain
representatives modulo homotopy. Exactness of M implies that M(h) represents
the image of a under derived M. Consequently k ∘ M(h) represents the derived
composite Q(M(h)) ≫ b. Every g representing that same composite is homotopic
to k ∘ M(h), so Step 2 identifies its three cohomology maps with the composite
of those of h and k. The quantifiers over all representatives make the result
independent of their choices; the comparison clause of chain coherence also
transports it between bounded-below injective models.
-/
theorem supportPairComposition
    (u : C ⥤ D) (v : D ⥤ E) [u.IsContinuous Jc Jd] [v.IsContinuous Jd Je]
    (L : Sheaf Jc AddCommGrpCat.{w₀} ⥤ Sheaf Jd AddCommGrpCat.{w₀})
    (M : Sheaf Jd AddCommGrpCat.{w₀} ⥤ Sheaf Je AddCommGrpCat.{w₀})
    (adjL : L ⊣ u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd)
    (adjM : M ⊣ v.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jd Je)
    [L.Additive] [M.Additive] [PreservesFiniteLimits L]
    [PreservesFiniteColimits L] [PreservesFiniteLimits M]
    [PreservesFiniteColimits M]
    (P : SupportPair (C := C)) (P' : SupportPair (C := D))
    (P'' : SupportPair (C := E))
    (t : P'.T ⟶ u.obj P.T) (s : P'.V ⟶ u.obj P.V)
    (t' : P''.T ⟶ v.obj P'.T) (s' : P''.V ⟶ v.obj P'.V)
    (square : s ≫ u.map P.m = P'.m ≫ t)
    (square' : s' ≫ v.map P'.m = P''.m ≫ t') :
    (∀ (I : CochainComplex (Sheaf Jc AddCommGrpCat.{w₀}) ℤ)
      (K : CochainComplex (Sheaf Jd AddCommGrpCat.{w₀}) ℤ)
      (N : CochainComplex (Sheaf Je AddCommGrpCat.{w₀}) ℤ)
      (h : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ K)
      (k : (M.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ N)
      (φ : supportDiagram Jc P I ⟶ supportDiagram Jd P' K)
      (ψ : supportDiagram Jd P' K ⟶ supportDiagram Je P'' N)
      (χ : supportDiagram Jc P I ⟶ supportDiagram Je P'' N),
      supportPairMapCondition Jc Jd u L adjL P P' t s h φ →
      supportPairMapCondition Jd Je v M adjM P' P'' t' s' k ψ →
      compositeSupportPairMapCondition Jc Jd Je u v L M adjL adjM P P''
        (t' ≫ v.map t) (s' ≫ v.map s)
        ((M.mapHomologicalComplex (ComplexShape.up ℤ)).map h ≫ k) χ →
      χ = φ ≫ ψ) ∧
    (∀ [HasDerivedCategory.{wQc} (Sheaf Jc AddCommGrpCat.{w₀})]
      [HasDerivedCategory.{wQd} (Sheaf Jd AddCommGrpCat.{w₀})]
      [HasDerivedCategory.{wQe} (Sheaf Je AddCommGrpCat.{w₀})]
      (I : CochainComplex (Sheaf Jc AddCommGrpCat.{w₀}) ℤ)
      (K : CochainComplex (Sheaf Jd AddCommGrpCat.{w₀}) ℤ)
      (N : CochainComplex (Sheaf Je AddCommGrpCat.{w₀}) ℤ)
      (hI : BoundedBelow I) (hK : BoundedBelow K) (hN : BoundedBelow N)
      (hinjI : ∀ n : ℤ, Injective (I.X n))
      (hinjK : ∀ n : ℤ, Injective (K.X n))
      (hinjN : ∀ n : ℤ, Injective (N.X n))
      (a : (standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).obj
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ⟶
        (standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).obj K)
      (b : (standardDerivedQ (A := Sheaf Je AddCommGrpCat.{w₀})).obj
          ((M.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
        (standardDerivedQ (A := Sheaf Je AddCommGrpCat.{w₀})).obj N)
      (h : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ K)
      (k : (M.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ N)
      (g : ((L ⋙ M).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ N),
      (standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).map h = a →
      (standardDerivedQ (A := Sheaf Je AddCommGrpCat.{w₀})).map k = b →
      (standardDerivedQ (A := Sheaf Je AddCommGrpCat.{w₀})).map g =
        (standardDerivedQ (A := Sheaf Je AddCommGrpCat.{w₀})).map
          ((M.mapHomologicalComplex (ComplexShape.up ℤ)).map h) ≫ b →
      ∀ (φ : supportDiagram Jc P I ⟶ supportDiagram Jd P' K)
        (ψ : supportDiagram Jd P' K ⟶ supportDiagram Je P'' N)
        (χ : supportDiagram Jc P I ⟶ supportDiagram Je P'' N),
        supportPairMapCondition Jc Jd u L adjL P P' t s h φ →
        supportPairMapCondition Jd Je v M adjM P' P'' t' s' k ψ →
        compositeSupportPairMapCondition Jc Jd Je u v L M adjL adjM P P''
          (t' ≫ v.map t) (s' ≫ v.map s) g χ →
        supportCohomologyEqual (φ ≫ ψ) χ) := by
  constructor
  · intro I K N h k φ ψ χ hφ hψ hχ
    have hc := supportPair_comp_condition Jc Jd Je u v L M adjL adjM
      P P' P'' t s t' s' h k φ ψ hφ hψ
    have h₂ : χ.τ₂ = (φ ≫ ψ).τ₂ := by
      ext1 n
      exact (hχ.1 n).trans (hc.1 n).symm
    have h₃ : χ.τ₃ = (φ ≫ ψ).τ₃ := by
      ext1 n
      exact (hχ.2 n).trans (hc.2 n).symm
    apply ShortComplex.Hom.ext _ h₂ h₃
    have : Mono (supportDiagram Je P'' N).f := by
      change Mono (kernel.ι _)
      infer_instance
    apply (cancel_mono (supportDiagram Je P'' N).f).1
    rw [χ.comm₁₂, (φ ≫ ψ).comm₁₂, h₂]
  · intro instI instK instN I K N hI hK hN hinjI hinjK hinjN a b h k g ha hb hg
      φ ψ χ hφ hψ hχ
    let : (u ⋙ v).IsContinuous Jc Je := Functor.isContinuous_comp u v Jc Jd Je
    have sq : (s' ≫ v.map s) ≫ (u ⋙ v).map P.m = P''.m ≫ (t' ≫ v.map t) := by
      change (s' ≫ v.map s) ≫ v.map (u.map P.m) = _
      calc
        _ = s' ≫ v.map (s ≫ u.map P.m) := by
          simp only [Functor.map_comp, Category.assoc]
        _ = s' ≫ v.map (P'.m ≫ t) := by rw [square]
        _ = (s' ≫ v.map P'.m) ≫ v.map t := by
          simp only [Functor.map_comp, Category.assoc]
        _ = P''.m ≫ (t' ≫ v.map t) := by rw [square', Category.assoc]
    have hc := supportPair_comp_condition Jc Jd Je u v L M adjL adjM
      P P' P'' t s t' s' h k φ ψ hφ hψ
    have hq : (standardDerivedQ (A := Sheaf Je AddCommGrpCat.{w₀})).map
        ((M.mapHomologicalComplex (ComplexShape.up ℤ)).map h ≫ k) =
        (standardDerivedQ (A := Sheaf Je AddCommGrpCat.{w₀})).map g := by
      rw [Functor.map_comp, hb, hg]
    let : PreservesFiniteLimits (L ⋙ M) := comp_preservesFiniteLimits L M
    let : PreservesFiniteColimits (L ⋙ M) := comp_preservesFiniteColimits L M
    exact (((supportPairChainCoherence Jc Je (u ⋙ v) (L ⋙ M) (adjL.comp adjM)
      P P'' (t' ≫ v.map t) (s' ≫ v.map s) sq I N).2 hI hN hinjI hinjN).2.1
      _ _ hq).2 (φ ≫ ψ) χ hc hχ

end CategoryTheory
