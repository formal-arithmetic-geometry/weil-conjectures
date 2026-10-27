/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Sheaf.Paper.CompactSupportCoefficientAction
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.CompactSupportNormalizedScalarDescent

/-! # Independence of the finite coefficient field

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/
lem-weil-compact-support-finite-field-independence.md, node order 1495
(blueprint: lem-weil-compact-support-finite-field-independence).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Coefficient)

/-- The compact-support values at any two finite coefficient stages are canonically
isomorphic via the specified beta-conjugated representative. A single normalized
finite action supplies all comparisons simultaneously. Identity and composition,
and independence under changing both the field and representative, are explicit. The
compactification is universally quantified because the source operation is defined
using an arbitrary compactification and the assertion is independent of that choice.

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/
lem-weil-compact-support-finite-field-independence.md, node order 1495
(blueprint: lem-weil-compact-support-finite-field-independence).

Proof (the four paragraphs of the DAG node): finite-stage scalar extension and
compact-support compatibility give the comparison maps; representing the specified
common-stage isomorphism and its inverse over one larger finite field gives inverse
output maps; the common-stage equality criterion and scalar associators make the
result independent of auxiliary fields and representatives; identity and composition
follow by cancellation of the coefficient comparisons. -/
theorem sfCompactSupportFiniteFieldIndependence
    (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (K₀ : Type u) [Field K₀] (_hl : IsUnit (l : K₀))
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))]
    [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))]
    [QuasiCompact (Y ↘ Spec (.of K₀))]
    [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] :
    ∀ (c : Compactification f),
    ∃ S : SfCompactSupportCoefficientAction l K₀ _hl Ω c,
      (∀ (A P : Pair l Ω X) (α : A ≅ P),
        S.comparison α α = Iso.refl (S.value A)) ∧
      (∀ (A B C P : Pair l Ω X) (α : A ≅ P) (β : B ≅ P) (γ : C ≅ P),
        S.comparison α β ≪≫ S.comparison β γ = S.comparison α γ) ∧
      (∀ (A B : Pair l Ω X) (M N : Padic.FiniteCoefficientFields l Ω)
        (hAM : A.stage ≤ M) (hBM : B.stage ≤ M)
        (hAN : A.stage ≤ N) (hBN : B.stage ≤ N)
        (uM : StageHom A B ⟨M, hAM, hBM⟩)
        (uN : StageHom A B ⟨N, hAN, hBN⟩),
        ofHom A B M hAM hBM uM = ofHom A B N hAN hBN uN →
          S.representative A B M hAM hBM uM = S.representative A B N hAN hBN uN) ∧
      (∀ (E L : Padic.FiniteCoefficientFields l Ω) (_hEL : E ≤ L)
        (K_E : Stage l Ω X E) (K_L : Stage l Ω X L) (Kq : Pair l Ω X)
        (α_E : (⟨E, K_E⟩ : Pair l Ω X) ≅ Kq)
        (α_L : (⟨L, K_L⟩ : Pair l Ω X) ≅ Kq),
        ∀ (M : Padic.FiniteCoefficientFields l Ω) (hE : E ≤ M) (hL : L ≤ M)
          (uM : StageHom (⟨E, K_E⟩ : Pair l Ω X) (⟨L, K_L⟩ : Pair l Ω X)
            ⟨M, hE, hL⟩),
          ofHom (⟨E, K_E⟩ : Pair l Ω X) (⟨L, K_L⟩ : Pair l Ω X) M hE hL uM =
            α_E.hom ≫ α_L.inv →
          (S.comparison α_E α_L).hom =
            S.representative (⟨E, K_E⟩ : Pair l Ω X) (⟨L, K_L⟩ : Pair l Ω X)
              M hE hL uM) := by
  classical
  intro c
  choose b hb hs β hβ using sfCompactSupportNormalizedScalarIsomorphisms
    l K₀ _hl c Ω
  have hc := (sfCompactSupportNormalizedScalarDescent l K₀ _hl c Ω b hb hs β hβ).2
  let SX : StageSystem (Stage l Ω X) :=
    { T := fun {E L} h ↦ transition l Ω X E L h
      assoc := fun {E L M} h k ↦ associator l Ω X E L M h k
      cocycle := fun h k m K ↦ associator_cocycle l Ω X _ _ _ _ h k m K }
  let SY : StageSystem (Stage l Ω Y) :=
    { T := fun {E L} h ↦ transition l Ω Y E L h
      assoc := fun {E L M} h k ↦ associator l Ω Y E L M h k
      cocycle := fun h k m K ↦ associator_cocycle l Ω Y _ _ _ _ h k m K }
  have hX : SX = stageSystem l Ω X :=
    (stageSystem_existsUnique l Ω X).unique
      ⟨fun _ _ _ ↦ rfl, fun _ _ _ _ _ ↦ HEq.rfl⟩
      (stageSystem_existsUnique l Ω X).exists.choose_spec
  have hY : SY = stageSystem l Ω Y :=
    (stageSystem_existsUnique l Ω Y).unique
      ⟨fun _ _ _ ↦ rfl, fun _ _ _ _ _ ↦ HEq.rfl⟩
      (stageSystem_existsUnique l Ω Y).exists.choose_spec
  let F : SX.Morphism SY :=
    { Φ := fun E ↦ sfCompactSupportFiniteFunctor l K₀ _hl c (Coefficient l Ω E)
      β := fun {E L} h ↦ β E L h
      coh := fun {E L M} h k K ↦ (hc E L M h k K).symm }
  have hF : ∃ F : (stageSystem l Ω X).Morphism (stageSystem l Ω Y),
      (∀ E, F.Φ E = sfCompactSupportFiniteFunctor l K₀ _hl c (Coefficient l Ω E)) ∧
      (∀ {E L} (h : E ≤ L) (K : Stage l Ω X E),
        HEq ((F.β h).hom.app K)
          ((sfRationalConstructibleLocalization l (Coefficient l Ω L) Y).map
            ((b E L h).hom.app K.obj))) := by
    rw [← hX, ← hY]
    exact ⟨F, fun _ ↦ rfl, fun {E L} h K ↦ hβ E L h K⟩
  obtain ⟨F, hfinite, hrat⟩ := hF
  let S : SfCompactSupportCoefficientAction l K₀ _hl Ω c :=
    { system := F
      finite_eq := hfinite
      value_eq := by
        intro A
        change (⟨A.stage, (F.Φ A.stage).obj A.obj⟩ : Pair l Ω Y) = _
        rw [hfinite]
        change (⟨A.stage, ⟨_⟩⟩ : Pair l Ω Y) = ⟨A.stage, ⟨_⟩⟩
        congr 2
        exact sfCompactSupportFiniteIntegralFunctor_obj l K₀ _hl c
          (Coefficient l Ω A.stage) A.obj.obj
      integralBeta := fun {E L} h ↦ b E L h
      integralBeta_spec := fun {E L} h ↦ hb E L h
      rationalBeta := hrat }
  have hrep (A B : Pair l Ω X) (M : Padic.FiniteCoefficientFields l Ω)
      (hA : A.stage ≤ M) (hB : B.stage ≤ M)
      (u : StageHom A B ⟨M, hA, hB⟩) :
      S.representative A B M hA hB u =
        eqToHom (S.value_eq A).symm ≫
          S.system.functor.map (ofHom A B M hA hB u) ≫ eqToHom (S.value_eq B) := by
    rfl
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · intro A P α
    apply Iso.ext
    simp [SfCompactSupportCoefficientAction.comparison]
  · intro A B C P α β γ
    apply Iso.ext
    simp [SfCompactSupportCoefficientAction.comparison]
  · intro A B M N hAM hBM hAN hBN uM uN h
    rw [hrep, hrep, h]
  · intro E L hEL K_E K_L Kq α_E α_L M hE hL uM h
    rw [hrep, h]
    rfl

end WeilConjectures
