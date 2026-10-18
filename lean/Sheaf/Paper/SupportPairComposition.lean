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
  sorry

end CategoryTheory
