/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil SHEAF project
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-!
# Coefficient compositor pasting through replacement and model isomorphisms

Source: the Weil conjectures blueprint, main-20261015, `sec-smooth-purity`,
`sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md`, Charts, coefficient
compatibility for the specified left identification
(blueprint: lem-sp-scalar-compositor-replacement-pasting).

The records below only bundle the functors, isomorphisms and equations in this node.
All categories, functors, natural transformations and natural isomorphisms are Mathlib's.
Composition `≫` is in diagrammatic order, the reverse of the source's written order.

## Main statements

- `CategoryTheory.ScalarCompositorReplacement.pasting`: replacement, model transport,
  cancellation of the first model, and identity/composition coherence.
-/

@[expose] public section

set_option autoImplicit false

universe v0A v1A v2A v0B v1B v2B u0A u1A u2A u0B u1B u2B

namespace CategoryTheory.ScalarCompositorReplacement

open CategoryTheory.Functor

variable {C0A : Type u0A} [Category.{v0A} C0A]
  {C1A : Type u1A} [Category.{v1A} C1A] {C2A : Type u2A} [Category.{v2A} C2A]
  {C0B : Type u0B} [Category.{v0B} C0B] {C1B : Type u1B} [Category.{v1B} C1B]
  {C2B : Type u2B} [Category.{v2B} C2B]
  (T0 : C0A ⥤ C0B) (T1 : C1A ⥤ C1B) (T2 : C2A ⥤ C2B)
  (EA : C0A ⥤ C1A) (EB : C0B ⥤ C1B) (σ : EA ⋙ T1 ⟶ T0 ⋙ EB)

/-- The data and the two assumed squares of one system, with `Tᵢ`, `E_R` and `σ` fixed.
Source: blueprint, exceptional reduction proof, Charts, coefficient compatibility
(blueprint: lem-sp-scalar-compositor-replacement-pasting). -/
structure System where
  FA : C0A ⥤ C1A
  FB : C0B ⥤ C1B
  PA : C1A ⥤ C2A
  PB : C1B ⥤ C2B
  QA : C0A ⥤ C2A
  QB : C0B ⥤ C2B
  cA : FA ≅ EA
  cB : FB ≅ EB
  αA : FA ⋙ PA ≅ QA
  αB : FB ⋙ PB ≅ QB
  βF : FA ⋙ T1 ⟶ T0 ⋙ FB
  βP : PA ⋙ T2 ⟶ T1 ⋙ PB
  βQ : QA ⋙ T2 ⟶ T0 ⋙ QB
  replacement_square : βF ≫ whiskerLeft T0 cB.hom = whiskerRight cA.hom T1 ≫ σ
  compositor_square : whiskerRight αA.hom T2 ≫ βQ =
    whiskerLeft FA βP ≫ whiskerRight βF PB ≫ whiskerLeft T0 αB.hom

variable {T0 T1 T2 EA EB σ}

/-- The specified replacement compositor `λ_A = α_A ∘ P_A(c_A⁻¹)`.
Source: blueprint, exceptional reduction proof, Charts, coefficient compatibility
(blueprint: lem-sp-scalar-compositor-replacement-pasting). -/
def System.lambdaA (S : System T0 T1 T2 EA EB σ) : EA ⋙ S.PA ≅ S.QA :=
  isoWhiskerRight S.cA.symm S.PA ≪≫ S.αA

/-- The specified replacement compositor `λ_B = α_B ∘ P_B(c_B⁻¹)`.
Source: blueprint, exceptional reduction proof, Charts, coefficient compatibility
(blueprint: lem-sp-scalar-compositor-replacement-pasting). -/
def System.lambdaB (S : System T0 T1 T2 EA EB σ) : EB ⋙ S.PB ≅ S.QB :=
  isoWhiskerRight S.cB.symm S.PB ≪≫ S.αB

/-- The left side of the displayed coefficient equation for the replacement compositor.
Source: blueprint, exceptional reduction proof, Charts, coefficient compatibility
(blueprint: lem-sp-scalar-compositor-replacement-pasting). -/
def System.coefficientLeft (S : System T0 T1 T2 EA EB σ) :
    (EA ⋙ S.PA) ⋙ T2 ⟶ T0 ⋙ S.QB :=
  whiskerRight S.lambdaA.hom T2 ≫ S.βQ

/-- The right side of the displayed coefficient equation for the replacement compositor.
Source: blueprint, exceptional reduction proof, Charts, coefficient compatibility
(blueprint: lem-sp-scalar-compositor-replacement-pasting). -/
def System.coefficientRight (S : System T0 T1 T2 EA EB σ) :
    (EA ⋙ S.PA) ⋙ T2 ⟶ T0 ⋙ S.QB :=
  whiskerLeft EA S.βP ≫ whiskerRight σ S.PB ≫ whiskerLeft T0 S.lambdaB.hom

/-- The six specified model isomorphisms, before imposing their commuting squares.
Source: blueprint, exceptional reduction proof, Charts, model refinements
(blueprint: lem-sp-scalar-compositor-replacement-pasting). -/
structure ModelMaps (S S' : System T0 T1 T2 EA EB σ) where
  fA : S.FA ≅ S'.FA
  fB : S.FB ≅ S'.FB
  pA : S.PA ≅ S'.PA
  pB : S.PB ≅ S'.PB
  qA : S.QA ≅ S'.QA
  qB : S.QB ≅ S'.QB

/-- Exactly the replacement, compositor and coefficient squares required of model maps.
Source: blueprint, exceptional reduction proof, Charts, model refinements
(blueprint: lem-sp-scalar-compositor-replacement-pasting). -/
def ModelMaps.Compatible {S S' : System T0 T1 T2 EA EB σ} (r : ModelMaps S S') : Prop :=
  (r.fA.hom ≫ S'.cA.hom = S.cA.hom) ∧
  (r.fB.hom ≫ S'.cB.hom = S.cB.hom) ∧
  (whiskerLeft S.FA r.pA.hom ≫ whiskerRight r.fA.hom S'.PA ≫ S'.αA.hom =
    S.αA.hom ≫ r.qA.hom) ∧
  (whiskerLeft S.FB r.pB.hom ≫ whiskerRight r.fB.hom S'.PB ≫ S'.αB.hom =
    S.αB.hom ≫ r.qB.hom) ∧
  (whiskerRight r.fA.hom T1 ≫ S'.βF = S.βF ≫ whiskerLeft T0 r.fB.hom) ∧
  (whiskerRight r.pA.hom T2 ≫ S'.βP = S.βP ≫ whiskerLeft T1 r.pB.hom) ∧
  (whiskerRight r.qA.hom T2 ≫ S'.βQ = S.βQ ≫ whiskerLeft T0 r.qB.hom)

/-- The identity choices for all six model isomorphisms.
Source: blueprint, exceptional reduction proof, Charts, identity model change
(blueprint: lem-sp-scalar-compositor-replacement-pasting). -/
def ModelMaps.refl (S : System T0 T1 T2 EA EB σ) : ModelMaps S S where
  fA := Iso.refl S.FA
  fB := Iso.refl S.FB
  pA := Iso.refl S.PA
  pB := Iso.refl S.PB
  qA := Iso.refl S.QA
  qB := Iso.refl S.QB

/-- Componentwise composition of the six specified model isomorphisms.
Source: blueprint, exceptional reduction proof, Charts, composite model changes
(blueprint: lem-sp-scalar-compositor-replacement-pasting). -/
def ModelMaps.trans {S S' S'' : System T0 T1 T2 EA EB σ}
    (r : ModelMaps S S') (r' : ModelMaps S' S'') : ModelMaps S S'' where
  fA := r.fA ≪≫ r'.fA
  fB := r.fB ≪≫ r'.fB
  pA := r.pA ≪≫ r'.pA
  pB := r.pB ≪≫ r'.pB
  qA := r.qA ≪≫ r'.qA
  qB := r.qB ≪≫ r'.qB

/-- Source endpoint identification for the coefficient equation under model change.
Source: blueprint, exceptional reduction proof, Charts, coefficient/refinement calculation
(blueprint: lem-sp-scalar-compositor-replacement-pasting). -/
def ModelMaps.sourceIso {S S' : System T0 T1 T2 EA EB σ} (r : ModelMaps S S') :
    (EA ⋙ S.PA) ⋙ T2 ≅ (EA ⋙ S'.PA) ⋙ T2 :=
  isoWhiskerRight (isoWhiskerLeft EA r.pA) T2

/-- Target endpoint identification for the coefficient equation under model change.
Source: blueprint, exceptional reduction proof, Charts, coefficient/refinement calculation
(blueprint: lem-sp-scalar-compositor-replacement-pasting). -/
def ModelMaps.targetIso {S S' : System T0 T1 T2 EA EB σ} (r : ModelMaps S S') :
    T0 ⋙ S.QB ≅ T0 ⋙ S'.QB :=
  isoWhiskerLeft T0 r.qB

private theorem inverse_replacement (S : System T0 T1 T2 EA EB σ) :
    whiskerRight S.cA.inv T1 ≫ S.βF = σ ≫ whiskerLeft T0 S.cB.inv := by
  apply (cancel_mono (whiskerLeft T0 S.cB.hom)).1
  simp only [Category.assoc, S.replacement_square]
  simp [← whiskerRight_comp_assoc, ← whiskerLeft_comp]

private theorem coefficient (S : System T0 T1 T2 EA EB σ) :
    S.coefficientLeft = S.coefficientRight := by
  ext x
  have hα := congrArg (fun t ↦ t.app x) S.compositor_square
  have hc := congrArg (fun t ↦ t.app x) (inverse_replacement S)
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] at hα hc
  simp only [System.coefficientLeft, System.coefficientRight, System.lambdaA,
    System.lambdaB, Iso.trans_hom, isoWhiskerRight_hom, Iso.symm_hom,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.map_comp]
  rw [Category.assoc, hα]
  have hn := S.βP.naturality (S.cA.inv.app x)
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← S.PB.map_comp_assoc, hc, S.PB.map_comp]
  simp only [Category.assoc]

private theorem lambda_transport
    {F F' E : C0A ⥤ C1A} {P P' : C1A ⥤ C2A} {Q Q' : C0A ⥤ C2A}
    (c : F ≅ E) (c' : F' ≅ E) (α : F ⋙ P ≅ Q) (α' : F' ⋙ P' ≅ Q')
    (f : F ≅ F') (p : P ≅ P') (q : Q ≅ Q')
    (hc : f.hom ≫ c'.hom = c.hom)
    (hα : whiskerLeft F p.hom ≫ whiskerRight f.hom P' ≫ α'.hom = α.hom ≫ q.hom) :
    whiskerLeft E p.hom ≫ (isoWhiskerRight c'.symm P' ≪≫ α').hom =
      (isoWhiskerRight c.symm P ≪≫ α).hom ≫ q.hom := by
  have hi : c'.inv = c.inv ≫ f.hom := by
    apply (cancel_mono c'.hom).1
    simp [Category.assoc, hc]
  simp only [Iso.trans_hom, isoWhiskerRight_hom, Iso.symm_hom, hi,
    whiskerRight_comp, Category.assoc]
  rw [← Category.assoc, whiskerLeft_comp_whiskerRight]
  simp only [Category.assoc]
  rw [hα]

private theorem compositor_trans
    {F F' F'' : C0A ⥤ C1A} {P P' P'' : C1A ⥤ C2A}
    {Q Q' Q'' : C0A ⥤ C2A}
    (α : F ⋙ P ≅ Q) (α' : F' ⋙ P' ≅ Q') (α'' : F'' ⋙ P'' ≅ Q'')
    (f : F ≅ F') (f' : F' ≅ F'') (p : P ≅ P') (p' : P' ≅ P'')
    (q : Q ≅ Q') (q' : Q' ≅ Q'')
    (h : whiskerLeft F p.hom ≫ whiskerRight f.hom P' ≫ α'.hom = α.hom ≫ q.hom)
    (h' : whiskerLeft F' p'.hom ≫ whiskerRight f'.hom P'' ≫ α''.hom =
      α'.hom ≫ q'.hom) :
    whiskerLeft F (p ≪≫ p').hom ≫ whiskerRight (f ≪≫ f').hom P'' ≫ α''.hom =
      α.hom ≫ (q ≪≫ q').hom := by
  simp only [Iso.trans_hom, whiskerLeft_comp, whiskerRight_comp, Category.assoc]
  rw [whiskerLeft_comp_whiskerRight_assoc f.hom p'.hom, h']
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ q'.hom) h

/-- Replacement pasting and its compatibility with all specified model isomorphisms.
Source: blueprint, main-20261015, exceptional reduction proof, Charts, coefficient
compatibility and model refinements
(blueprint: lem-sp-scalar-compositor-replacement-pasting).

Proof (the eight elementary steps of the node, using only `def-nagata-category`):
1. Work componentwise. Reassociate using category laws; functors preserve inverse pairs.
2. Multiply the replacement square by `c_B⁻¹` on the target and by `T₁(c_A⁻¹)`
on the source, obtaining the inverse replacement square.
3. Apply naturality of `β_P` to `c_A⁻¹`; substitute the compositor square and Step 2.
Functoriality combines the adjacent factors and gives the coefficient equation for `λ`.
4. Write a model change as `(r,s,t)`. The first square gives `c'⁻¹ = r c⁻¹`.
Naturality of `s` at `c⁻¹` and the compositor model square give `λ'(sE) = tλ`
for each of A and B. Taking `s` and `t` to be identities cancels a change of F alone.
5. Precompose the primed coefficient left side with `T₂(s_A E_A)`. Step 4 and the
Q coefficient model square identify it with the old left side followed by `t_B T₀`.
6. For the right side use the P coefficient model square, naturality of `s_B` at `σ`,
and Step 4. The result is the old right side followed by `t_B T₀`. Both endpoint
identifications are isomorphisms, so the coefficient equations are equivalent.
7. Identity model changes delete identity factors. For two changes, naturality of
`s'` at `r` gives the composite compositor square; compose each coefficient square.
The lambda and endpoint identities compose by functoriality and associativity.
8. Composites, whiskerings and inverses of natural transformations are natural,
so all displayed equalities are equalities of natural transformations, also for empty
input categories. No coefficient map has been inverted. -/
theorem pasting (S : System T0 T1 T2 EA EB σ) :
    (whiskerRight S.cA.inv T1 ≫ S.βF = σ ≫ whiskerLeft T0 S.cB.inv) ∧
    (S.coefficientLeft = S.coefficientRight) ∧
    (ModelMaps.refl S).Compatible ∧
    ((ModelMaps.refl S).sourceIso = Iso.refl ((EA ⋙ S.PA) ⋙ T2)) ∧
    ((ModelMaps.refl S).targetIso = Iso.refl (T0 ⋙ S.QB)) ∧
    (∀ (S' : System T0 T1 T2 EA EB σ) (r : ModelMaps S S'), r.Compatible →
      (whiskerLeft EA r.pA.hom ≫ S'.lambdaA.hom = S.lambdaA.hom ≫ r.qA.hom) ∧
      (whiskerLeft EB r.pB.hom ≫ S'.lambdaB.hom = S.lambdaB.hom ≫ r.qB.hom) ∧
      (r.sourceIso.hom ≫ S'.coefficientLeft = S.coefficientLeft ≫ r.targetIso.hom) ∧
      (r.sourceIso.hom ≫ S'.coefficientRight = S.coefficientRight ≫ r.targetIso.hom) ∧
      ((S'.coefficientLeft = S'.coefficientRight) ↔
        S.coefficientLeft = S.coefficientRight) ∧
      (∀ (S'' : System T0 T1 T2 EA EB σ) (r' : ModelMaps S' S''), r'.Compatible →
        (r.trans r').Compatible ∧
        (whiskerLeft EA (r.trans r').pA.hom ≫ S''.lambdaA.hom =
          S.lambdaA.hom ≫ (r.trans r').qA.hom) ∧
        (whiskerLeft EB (r.trans r').pB.hom ≫ S''.lambdaB.hom =
          S.lambdaB.hom ≫ (r.trans r').qB.hom) ∧
        ((r.trans r').sourceIso = r.sourceIso ≪≫ r'.sourceIso) ∧
        ((r.trans r').targetIso = r.targetIso ≪≫ r'.targetIso))) ∧
    (∀ (FA' : C0A ⥤ C1A) (FB' : C0B ⥤ C1B)
      (cA' : FA' ≅ EA) (cB' : FB' ≅ EB)
      (αA' : FA' ⋙ S.PA ≅ S.QA) (αB' : FB' ⋙ S.PB ≅ S.QB)
      (rA : S.FA ≅ FA') (rB : S.FB ≅ FB'),
      (rA.hom ≫ cA'.hom = S.cA.hom) →
      (rB.hom ≫ cB'.hom = S.cB.hom) →
      (whiskerRight rA.hom S.PA ≫ αA'.hom = S.αA.hom) →
      (whiskerRight rB.hom S.PB ≫ αB'.hom = S.αB.hom) →
      ((isoWhiskerRight cA'.symm S.PA ≪≫ αA').hom = S.lambdaA.hom) ∧
      ((isoWhiskerRight cB'.symm S.PB ≪≫ αB').hom = S.lambdaB.hom)) := by
  refine ⟨inverse_replacement S, coefficient S, ?_, ?_, ?_, ?_, ?_⟩
  · simp [ModelMaps.Compatible, ModelMaps.refl]
  · simp [ModelMaps.sourceIso, ModelMaps.refl]
  · simp [ModelMaps.targetIso, ModelMaps.refl]
  · intro S' r hr
    rcases hr with ⟨hcA, hcB, hαA, hαB, hF, hP, hQ⟩
    have hLamA := lambda_transport S.cA S'.cA S.αA S'.αA r.fA r.pA r.qA hcA hαA
    have hLamB := lambda_transport S.cB S'.cB S.αB S'.αB r.fB r.pB r.qB hcB hαB
    change whiskerLeft EA r.pA.hom ≫ S'.lambdaA.hom =
      S.lambdaA.hom ≫ r.qA.hom at hLamA
    change whiskerLeft EB r.pB.hom ≫ S'.lambdaB.hom =
      S.lambdaB.hom ≫ r.qB.hom at hLamB
    have hL : r.sourceIso.hom ≫ S'.coefficientLeft =
        S.coefficientLeft ≫ r.targetIso.hom := by
      ext x
      have hLam := congrArg (fun t ↦ t.app x) hLamA
      have hβ := congrArg (fun t ↦ t.app x) hQ
      simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] at hLam hβ
      simp only [ModelMaps.sourceIso, ModelMaps.targetIso, isoWhiskerRight_hom,
        isoWhiskerLeft_hom, System.coefficientLeft, NatTrans.comp_app,
        whiskerRight_app, whiskerLeft_app]
      rw [← T2.map_comp_assoc, hLam, T2.map_comp, Category.assoc, hβ, ← Category.assoc]
    have hR : r.sourceIso.hom ≫ S'.coefficientRight =
        S.coefficientRight ≫ r.targetIso.hom := by
      ext x
      have hβ := congrArg (fun t ↦ t.app (EA.obj x)) hP
      have hLam := congrArg (fun t ↦ t.app (T0.obj x)) hLamB
      have hn := r.pB.hom.naturality (σ.app x)
      simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] at hβ hLam
      simp only [ModelMaps.sourceIso, ModelMaps.targetIso, isoWhiskerRight_hom,
        isoWhiskerLeft_hom, System.coefficientRight, NatTrans.comp_app,
        whiskerRight_app, whiskerLeft_app]
      calc
        _ = (S.βP.app (EA.obj x) ≫ r.pB.hom.app (T1.obj (EA.obj x))) ≫
            S'.PB.map (σ.app x) ≫ S'.lambdaB.hom.app (T0.obj x) := by
          rw [← hβ]
          simp only [Category.assoc]
        _ = S.βP.app (EA.obj x) ≫ S.PB.map (σ.app x) ≫
            (r.pB.hom.app (EB.obj (T0.obj x)) ≫
              S'.lambdaB.hom.app (T0.obj x)) := by
          rw [Category.assoc, ← reassoc_of% hn]
        _ = _ := by simp only [hLam, Category.assoc]
    refine ⟨hLamA, hLamB, hL, hR, ?_, ?_⟩
    · constructor
      · intro h
        apply (cancel_mono r.targetIso.hom).1
        rw [← hL, ← hR, h]
      · intro h
        apply (cancel_epi r.sourceIso.hom).1
        rw [hL, hR, h]
    · intro S'' r' hr'
      rcases hr' with ⟨hcA', hcB', hαA', hαB', hF', hP', hQ'⟩
      have hcomp : (r.trans r').Compatible := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [ModelMaps.trans, Category.assoc, hcA'] using hcA
        · simpa [ModelMaps.trans, Category.assoc, hcB'] using hcB
        · exact compositor_trans S.αA S'.αA S''.αA r.fA r'.fA r.pA r'.pA
            r.qA r'.qA hαA hαA'
        · exact compositor_trans S.αB S'.αB S''.αB r.fB r'.fB r.pB r'.pB
            r.qB r'.qB hαB hαB'
        · simp only [ModelMaps.trans, Iso.trans_hom, whiskerRight_comp,
            whiskerLeft_comp, Category.assoc]
          rw [hF', ← Category.assoc, hF, Category.assoc]
        · simp only [ModelMaps.trans, Iso.trans_hom, whiskerRight_comp,
            whiskerLeft_comp, Category.assoc]
          rw [hP', ← Category.assoc, hP, Category.assoc]
        · simp only [ModelMaps.trans, Iso.trans_hom, whiskerRight_comp,
            whiskerLeft_comp, Category.assoc]
          rw [hQ', ← Category.assoc, hQ, Category.assoc]
      refine ⟨hcomp, ?_, ?_, ?_, ?_⟩
      · exact lambda_transport S.cA S''.cA S.αA S''.αA
          (r.trans r').fA (r.trans r').pA (r.trans r').qA hcomp.1 hcomp.2.2.1
      · exact lambda_transport S.cB S''.cB S.αB S''.αB
          (r.trans r').fB (r.trans r').pB (r.trans r').qB hcomp.2.1 hcomp.2.2.2.1
      · simp [ModelMaps.sourceIso, ModelMaps.trans]
      · simp [ModelMaps.targetIso, ModelMaps.trans]
  · intro FA' FB' cA' cB' αA' αB' rA rB hcA hcB hαA hαB
    have hA := lambda_transport S.cA cA' S.αA αA' rA (Iso.refl S.PA)
      (Iso.refl S.QA) hcA (by simpa using hαA)
    have hB := lambda_transport S.cB cB' S.αB αB' rB (Iso.refl S.PB)
      (Iso.refl S.QB) hcB (by simpa using hαB)
    simpa [System.lambdaA, System.lambdaB] using And.intro hA hB

end CategoryTheory.ScalarCompositorReplacement
