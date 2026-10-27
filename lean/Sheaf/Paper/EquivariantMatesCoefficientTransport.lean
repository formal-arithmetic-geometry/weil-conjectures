/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SfWeilSheafComplex
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra

import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients

/-! # Equivariant mates and coefficient transport

Source: blueprint prop-weil-operations, proof sentence 1, and lem-fix-weil-operations,
ordinary adjunction and exchange-pasting paragraphs
(blueprint: lem-pod-equivariant-mates-coefficient-transport).

The declarations give the fixed-pair lift, its exact carrier, all four pasting laws,
coefficient transport of the specified mate, and common-stage representative independence.
The auxiliary records package the supplied data; they assert no existence of operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe uA uB uC uD uE uF vA vB vC vD vE vF
universe uA' uB' uC' uD' vA' vB' vC' vD' u v

open CategoryTheory CategoryTheory.Functor CategoryTheory.Endofunctor CategoryTheory.TwoSquare
open CategoryTheory.SuppliedExchangeProjection

namespace CategoryTheory.EquivariantMates

variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
  [Category.{vA} A] [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]

private instance forget_faithful (P : C ⥤ C) : (IsoAlgebra.forget P).Faithful where
  map_injective h := ObjectProperty.hom_ext _ (Algebra.Hom.ext h)

private theorem app_heq {F G : C ⥤ D} (η : F ⟶ G) {X Y : C}
    (h : X = Y) : HEq (η.app X) (η.app Y) := by
  cases h
  rfl

private theorem id_heq {X Y : C} (h : X = Y) : HEq (𝟙 X) (𝟙 Y) := by
  cases h
  rfl

private theorem lift_obj_eq {PA : A ⥤ A} {PB : B ⥤ B}
    {L : IsoAlgebra PA ⥤ IsoAlgebra PB} {F : A ⥤ B}
    (hL : L ⋙ IsoAlgebra.forget PB = IsoAlgebra.forget PA ⋙ F) (K : IsoAlgebra PA) :
    (L.obj K).carrier = F.obj K.carrier := by
  simpa only [Functor.comp_obj, IsoAlgebra.forget_obj] using Functor.congr_obj hL K

private theorem map_heq {X Y X' Y' : C} (F : C ⥤ D)
    (hX : X = X') (hY : Y = Y') {f : X ⟶ Y} {g : X' ⟶ Y'}
    (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hX
  cases hY
  cases h
  rfl

private theorem lift_map_heq {PA : A ⥤ A} {PB : B ⥤ B}
    (L : IsoAlgebra PA ⥤ IsoAlgebra PB) (F : A ⥤ B)
    (hL : L ⋙ IsoAlgebra.forget PB = IsoAlgebra.forget PA ⋙ F)
    {K H : IsoAlgebra PA} (f : K ⟶ H) : HEq (L.map f).hom.f (F.map f.hom.f) :=
  Functor.hcongr_hom hL f

private def lift_adjunction {PA : A ⥤ A} {PB : B ⥤ B}
    {L : IsoAlgebra PA ⥤ IsoAlgebra PB} {R : IsoAlgebra PB ⥤ IsoAlgebra PA}
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    (hL : L ⋙ IsoAlgebra.forget PB = IsoAlgebra.forget PA ⋙ F)
    (hR : R ⋙ IsoAlgebra.forget PA = IsoAlgebra.forget PB ⋙ G)
    (η : 𝟭 (IsoAlgebra PA) ⟶ L ⋙ R) (ε : R ⋙ L ⟶ 𝟭 (IsoAlgebra PB))
    (hη : ∀ K, HEq (η.app K).hom.f (adj.unit.app K.carrier))
    (hε : ∀ H, HEq (ε.app H).hom.f (adj.counit.app H.carrier)) : L ⊣ R where
  unit := η
  counit := ε
  left_triangle_components K := by
    apply (IsoAlgebra.forget PB).map_injective
    change (L.map (η.app K)).hom.f ≫ (ε.app (L.obj K)).hom.f = 𝟙 _
    have hl := lift_obj_eq hL K
    have hr := (lift_obj_eq hR (L.obj K)).trans (congrArg G.obj hl)
    have hm := (lift_map_heq L F hL (η.app K)).trans (map_heq F rfl hr (hη K))
    have hc := (hε (L.obj K)).trans (app_heq adj.counit hl)
    have hx := (lift_obj_eq hL (R.obj (L.obj K))).trans (congrArg F.obj hr)
    exact eq_of_heq ((heq_comp hl hx hl hm hc).trans
      ((heq_of_eq (adj.left_triangle_components K.carrier)).trans (id_heq hl.symm)))
  right_triangle_components H := by
    apply (IsoAlgebra.forget PA).map_injective
    change (η.app (R.obj H)).hom.f ≫ (R.map (ε.app H)).hom.f = 𝟙 _
    have hr := lift_obj_eq hR H
    have hl := (lift_obj_eq hL (R.obj H)).trans (congrArg F.obj hr)
    have hu := (hη (R.obj H)).trans (app_heq adj.unit hr)
    have hm := (lift_map_heq R G hR (ε.app H)).trans (map_heq G hl rfl (hε H))
    have hx := (lift_obj_eq hR (L.obj (R.obj H))).trans (congrArg G.obj hl)
    exact eq_of_heq ((heq_comp hr hx hr hu hm).trans
      ((heq_of_eq (adj.right_triangle_components H.carrier)).trans (id_heq hr.symm)))

/-- One of the two specified carrier adjunctions together with its square.
Source: prop-weil-operations, mate-calculus expansion, proof steps 1--2
(blueprint: lem-pod-equivariant-mates-coefficient-transport). -/
structure Square (A : Type uA) (B : Type uB) (C : Type uC) (D : Type uD)
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C] [Category.{vD} D] where
  left₁ : A ⥤ B
  right₁ : B ⥤ A
  adj₁ : left₁ ⊣ right₁
  left₂ : C ⥤ D
  right₂ : D ⥤ C
  adj₂ : left₂ ⊣ right₂
  horizontal : A ⥤ C
  vertical : B ⥤ D
  square : TwoSquare horizontal left₁ left₂ vertical

/-- The specified mate, using the recorded Mathlib mate construction.
Source: prop-weil-operations, proof step 2
(blueprint: lem-pod-equivariant-mates-coefficient-transport). -/
def Square.mate (S : Square A B C D) := mateEquiv S.adj₁ S.adj₂ S.square

/-- Arbitrary specified lifts with their carrier equalities (strict lifting, not an
unspecified natural isomorphism). The supplied unit and counit are not assumed to
satisfy the triangle identities upstairs.
Source: prop-weil-operations, proof steps 1--2
(blueprint: lem-pod-equivariant-mates-coefficient-transport). -/
structure FixedLift (S : Square A B C D)
    (PA : A ⥤ A) (PB : B ⥤ B) (PC : C ⥤ C) (PD : D ⥤ D) where
  left₁ : IsoAlgebra PA ⥤ IsoAlgebra PB
  right₁ : IsoAlgebra PB ⥤ IsoAlgebra PA
  left₂ : IsoAlgebra PC ⥤ IsoAlgebra PD
  right₂ : IsoAlgebra PD ⥤ IsoAlgebra PC
  horizontal : IsoAlgebra PA ⥤ IsoAlgebra PC
  vertical : IsoAlgebra PB ⥤ IsoAlgebra PD
  left₁_over : left₁ ⋙ IsoAlgebra.forget PB = IsoAlgebra.forget PA ⋙ S.left₁
  right₁_over : right₁ ⋙ IsoAlgebra.forget PA = IsoAlgebra.forget PB ⋙ S.right₁
  left₂_over : left₂ ⋙ IsoAlgebra.forget PD = IsoAlgebra.forget PC ⋙ S.left₂
  right₂_over : right₂ ⋙ IsoAlgebra.forget PC = IsoAlgebra.forget PD ⋙ S.right₂
  horizontal_over : horizontal ⋙ IsoAlgebra.forget PC = IsoAlgebra.forget PA ⋙ S.horizontal
  vertical_over : vertical ⋙ IsoAlgebra.forget PD = IsoAlgebra.forget PB ⋙ S.vertical
  unit₁ : 𝟭 (IsoAlgebra PA) ⟶ left₁ ⋙ right₁
  counit₁ : right₁ ⋙ left₁ ⟶ 𝟭 (IsoAlgebra PB)
  unit₂ : 𝟭 (IsoAlgebra PC) ⟶ left₂ ⋙ right₂
  counit₂ : right₂ ⋙ left₂ ⟶ 𝟭 (IsoAlgebra PD)
  unit₁_over : ∀ K, HEq (unit₁.app K).hom.f (S.adj₁.unit.app K.carrier)
  counit₁_over : ∀ K, HEq (counit₁.app K).hom.f (S.adj₁.counit.app K.carrier)
  unit₂_over : ∀ K, HEq (unit₂.app K).hom.f (S.adj₂.unit.app K.carrier)
  counit₂_over : ∀ K, HEq (counit₂.app K).hom.f (S.adj₂.counit.app K.carrier)
  square : TwoSquare horizontal left₁ left₂ vertical
  square_over : ∀ K, HEq (square.app K).hom.f (S.square.app K.carrier)

/-- The specified units/counits lift to adjunctions and the mate has exactly the
three-factor carrier, with no replacement by an isomorphic map.
Source: prop-weil-operations, proof steps 1--2
(blueprint: lem-pod-equivariant-mates-coefficient-transport).
Proof: forget the two triangle identities. Faithfulness proves them upstairs, giving
adjunctions with the supplied unit and counit. Form mateEquiv using these adjunctions.
Each of its unit, square and counit factors is a fixed-pair arrow; their composite is
natural. Forgetting it gives eta₂ followed by R₂(alpha) and R₂V(epsilon₁), exactly. -/
theorem fixedPair_mate (S : Square A B C D)
    (PA : A ⥤ A) (PB : B ⥤ B) (PC : C ⥤ C) (PD : D ⥤ D)
    (W : FixedLift S PA PB PC PD) :
    ∃ (a₁ : W.left₁ ⊣ W.right₁) (a₂ : W.left₂ ⊣ W.right₂),
      a₁.unit = W.unit₁ ∧ a₁.counit = W.counit₁ ∧
      a₂.unit = W.unit₂ ∧ a₂.counit = W.counit₂ ∧
      ∀ K : IsoAlgebra PB,
        HEq ((mateEquiv a₁ a₂ W.square).app K).hom.f
          (S.adj₂.unit.app (S.horizontal.obj (S.right₁.obj K.carrier)) ≫
            S.right₂.map (S.square.app (S.right₁.obj K.carrier)) ≫
            S.right₂.map (S.vertical.map (S.adj₁.counit.app K.carrier))) := by
  let a₁ := lift_adjunction S.adj₁ W.left₁_over W.right₁_over
    W.unit₁ W.counit₁ W.unit₁_over W.counit₁_over
  let a₂ := lift_adjunction S.adj₂ W.left₂_over W.right₂_over
    W.unit₂ W.counit₂ W.unit₂_over W.counit₂_over
  refine ⟨a₁, a₂, rfl, rfl, rfl, rfl, ?_⟩
  intro K
  have hR := lift_obj_eq W.right₁_over K
  have hU := (lift_obj_eq W.horizontal_over (W.right₁.obj K)).trans
    (congrArg S.horizontal.obj hR)
  have hV := lift_obj_eq W.vertical_over K
  have hL := (lift_obj_eq W.left₁_over (W.right₁.obj K)).trans
    (congrArg S.left₁.obj hR)
  have hVL := (lift_obj_eq W.vertical_over (W.left₁.obj (W.right₁.obj K))).trans
    (congrArg S.vertical.obj hL)
  have hLU := (lift_obj_eq W.left₂_over (W.horizontal.obj (W.right₁.obj K))).trans
    (congrArg S.left₂.obj hU)
  have h₁ := (W.unit₂_over (W.horizontal.obj (W.right₁.obj K))).trans
    (app_heq S.adj₂.unit hU)
  have hα := (W.square_over (W.right₁.obj K)).trans (app_heq S.square.natTrans hR)
  have h₂ := (lift_map_heq W.right₂ S.right₂ W.right₂_over
    (W.square.app (W.right₁.obj K))).trans (map_heq S.right₂ hLU hVL hα)
  have hε := (lift_map_heq W.vertical S.vertical W.vertical_over (W.counit₁.app K)).trans
    (map_heq S.vertical hL rfl (W.counit₁_over K))
  have h₃ := (lift_map_heq W.right₂ S.right₂ W.right₂_over
    (W.vertical.map (W.counit₁.app K))).trans (map_heq S.right₂ hVL hV hε)
  have hx₁ := (lift_obj_eq W.right₂_over
    (W.left₂.obj (W.horizontal.obj (W.right₁.obj K)))).trans (congrArg S.right₂.obj hLU)
  have hx₂ := (lift_obj_eq W.right₂_over
    (W.vertical.obj (W.left₁.obj (W.right₁.obj K)))).trans (congrArg S.right₂.obj hVL)
  have hx₃ := (lift_obj_eq W.right₂_over (W.vertical.obj K)).trans
    (congrArg S.right₂.obj hV)
  have hm := heq_comp hU hx₁ hx₃ h₁ (heq_comp hx₁ hx₂ hx₃ h₂ h₃)
  simpa [mateEquiv, a₁, a₂, lift_adjunction] using hm

section Pasting

variable {E : Type uE} {F : Type uF} [Category.{vE} E] [Category.{vF} F]
  (PA : A ⥤ A) (PB : B ⥤ B) (PC : C ⥤ C) (PD : D ⥤ D)
  (PE : E ⥤ E) (PF : F ⥤ F)

/-- Pasting on the non-adjoint sides is an equality of fixed-pair arrows.
Source: prop-weil-operations, proof step 3, mate-pasting clause (1)
(blueprint: lem-pod-equivariant-mates-coefficient-transport).
Proof: apply mateEquiv_vcomp in the fixed-pair categories to the specified lifted
adjunctions. Step 2 identifies every factor's carrier with the given carrier factor. -/
theorem fixedPair_mate_pasting
    {L₁ : IsoAlgebra PA ⥤ IsoAlgebra PB} {R₁ : IsoAlgebra PB ⥤ IsoAlgebra PA}
    {L₂ : IsoAlgebra PC ⥤ IsoAlgebra PD} {R₂ : IsoAlgebra PD ⥤ IsoAlgebra PC}
    {L₃ : IsoAlgebra PE ⥤ IsoAlgebra PF} {R₃ : IsoAlgebra PF ⥤ IsoAlgebra PE}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    {G₁ : IsoAlgebra PA ⥤ IsoAlgebra PC} {H₁ : IsoAlgebra PB ⥤ IsoAlgebra PD}
    {G₂ : IsoAlgebra PC ⥤ IsoAlgebra PE} {H₂ : IsoAlgebra PD ⥤ IsoAlgebra PF}
    (α : TwoSquare G₁ L₁ L₂ H₁) (β : TwoSquare G₂ L₂ L₃ H₂) :
    mateEquiv a₁ a₃ (α ≫ₕ β) = (mateEquiv a₁ a₂ α) ≫ᵥ (mateEquiv a₂ a₃ β) := by
  exact mateEquiv_vcomp a₁ a₂ a₃ α β

/-- Composition of the adjunctions uses their specified composite units and counits.
Source: prop-weil-operations, proof step 3, mate-pasting clause (2)
(blueprint: lem-pod-equivariant-mates-coefficient-transport).
Proof: apply mateEquiv_hcomp to the lifted adjunctions. Adjunction.comp has unit
R₁ eta₃ L₁ after eta₁ and counit epsilon₃ after L₃ epsilon₁ R₃, as required. -/
theorem fixedPair_mate_adjunctionComposition
    {L₁ : IsoAlgebra PA ⥤ IsoAlgebra PB} {R₁ : IsoAlgebra PB ⥤ IsoAlgebra PA}
    {L₃ : IsoAlgebra PB ⥤ IsoAlgebra PC} {R₃ : IsoAlgebra PC ⥤ IsoAlgebra PB}
    {L₂ : IsoAlgebra PD ⥤ IsoAlgebra PE} {R₂ : IsoAlgebra PE ⥤ IsoAlgebra PD}
    {L₄ : IsoAlgebra PE ⥤ IsoAlgebra PF} {R₄ : IsoAlgebra PF ⥤ IsoAlgebra PE}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    {G : IsoAlgebra PA ⥤ IsoAlgebra PD} {H : IsoAlgebra PB ⥤ IsoAlgebra PE}
    {K : IsoAlgebra PC ⥤ IsoAlgebra PF}
    (α : TwoSquare G L₁ L₂ H) (β : TwoSquare H L₃ L₄ K) :
    mateEquiv (a₁.comp a₃) (a₂.comp a₄) (α ≫ᵥ β) =
      (mateEquiv a₃ a₄ β) ≫ₕ (mateEquiv a₁ a₂ α) := by
  exact mateEquiv_hcomp a₁ a₂ a₃ a₄ α β

/-- Changing the second adjunction by a transformation gives its conjugate mate.
Source: prop-weil-operations, proof step 3, mate-pasting clause (3a)
(blueprint: lem-pod-equivariant-mates-coefficient-transport).
Proof: apply mateEquiv_conjugateEquiv_vcomp in the fixed-pair categories. -/
theorem fixedPair_mate_changeSecond
    {L₁ : IsoAlgebra PA ⥤ IsoAlgebra PB} {R₁ : IsoAlgebra PB ⥤ IsoAlgebra PA}
    {L₂ L₃ : IsoAlgebra PC ⥤ IsoAlgebra PD} {R₂ R₃ : IsoAlgebra PD ⥤ IsoAlgebra PC}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    {G : IsoAlgebra PA ⥤ IsoAlgebra PC} {H : IsoAlgebra PB ⥤ IsoAlgebra PD}
    (α : TwoSquare G L₁ L₂ H) (τ : L₃ ⟶ L₂) :
    mateEquiv a₁ a₃ (α.whiskerRight τ) =
      (mateEquiv a₁ a₂ α).whiskerBottom (conjugateEquiv a₂ a₃ τ) := by
  exact mateEquiv_conjugateEquiv_vcomp a₁ a₂ a₃ α τ

/-- Changing the first adjunction by a transformation gives its conjugate mate.
Source: prop-weil-operations, proof step 3, mate-pasting clause (3b)
(blueprint: lem-pod-equivariant-mates-coefficient-transport).
Proof: apply conjugateEquiv_mateEquiv_vcomp in the fixed-pair categories. -/
theorem fixedPair_mate_changeFirst
    {L₀ L₁ : IsoAlgebra PA ⥤ IsoAlgebra PB} {R₀ R₁ : IsoAlgebra PB ⥤ IsoAlgebra PA}
    {L₂ : IsoAlgebra PC ⥤ IsoAlgebra PD} {R₂ : IsoAlgebra PD ⥤ IsoAlgebra PC}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    {G : IsoAlgebra PA ⥤ IsoAlgebra PC} {H : IsoAlgebra PB ⥤ IsoAlgebra PD}
    (σ : L₁ ⟶ L₀) (α : TwoSquare G L₁ L₂ H) :
    mateEquiv a₀ a₂ (α.whiskerLeft σ) =
      (mateEquiv a₁ a₂ α).whiskerTop (conjugateEquiv a₀ a₁ σ) := by
  exact conjugateEquiv_mateEquiv_vcomp a₀ a₁ a₂ σ α

end Pasting

/-- An equivariant map with invertible carrier has its actual carrier inverse upstairs.
Source: prop-weil-operations, proof step 10
(blueprint: lem-pod-equivariant-mates-coefficient-transport).
Proof: from P(u) theta_H = theta_K u, multiply by u inverse and P(u inverse).
This gives equivariance of the carrier inverse. Its inverse identities hold by
faithfulness. The argument assumes invertibility; the zero map with identity structures
on a nonzero vector space shows that equivariance alone supplies none. -/
theorem fixedPair_inverse (P : C ⥤ C) {K H : IsoAlgebra P} (f : K ⟶ H)
    [IsIso f.hom.f] :
    ∃ g : H ⟶ K, g.hom.f = inv f.hom.f ∧ f ≫ g = 𝟙 K ∧ g ≫ f = 𝟙 H := by
  let g : H ⟶ K := ⟨(Algebra.isoMk (asIso f.hom.f) f.hom.h).inv⟩
  refine ⟨g, rfl, ?_, ?_⟩
  · apply (IsoAlgebra.forget P).map_injective
    simp [g]
  · apply (IsoAlgebra.forget P).map_injective
    simp [g]


section CoefficientComparison

variable {A' : Type uA'} {B' : Type uB'} {C' : Type uC'} {D' : Type uD'}
  [Category.{vA'} A'] [Category.{vB'} B'] [Category.{vC'} C'] [Category.{vD'} D']

/-- Compose the actual supplied scalar comparisons, retaining their direction.
Source: prop-weil-operations, proof step 6, formula c_GF = G(c_F)c_G
(blueprint: lem-pod-equivariant-mates-coefficient-transport). -/
def compositeComparison
    {F : A ⥤ B} {G : B ⥤ C} {F' : A' ⥤ B'} {G' : B' ⥤ C'}
    {a : A ⥤ A'} {b : B ⥤ B'} {c : C ⥤ C'}
    (eF : F ⋙ b ≅ a ⋙ F') (eG : G ⋙ c ≅ b ⋙ G') :
    (F ⋙ G) ⋙ c ≅ a ⋙ (F' ⋙ G') :=
  Functor.associator F G c ≪≫ isoWhiskerLeft F eG ≪≫
    (Functor.associator F b G').symm ≪≫ isoWhiskerRight eF G' ≪≫
    Functor.associator a F' G'

/-- The supplied comparisons intertwine both units, both counits, and alpha.
The adjunction compatibility is the recorded exchange/projection interface.
Source: prop-weil-operations, proof steps 4 and 6
(blueprint: lem-pod-equivariant-mates-coefficient-transport). -/
structure CoefficientComparison (S : Square A B C D) (T : Square A' B' C' D')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D') where
  adj₁ : ExchangeProjectionAdjunctionComparison S.adj₁ T.adj₁ a b
  adj₂ : ExchangeProjectionAdjunctionComparison S.adj₂ T.adj₂ c d
  horizontal : S.horizontal ⋙ c ≅ a ⋙ T.horizontal
  vertical : S.vertical ⋙ d ≅ b ⋙ T.vertical
  square : ExchangeProjectionComparisonPreserves a d
    (compositeComparison horizontal adj₂.left)
    (compositeComparison adj₁.left vertical) S.square.natTrans T.square.natTrans

/-- The actual source comparison for the mate, not a freely chosen isomorphism.
Source: prop-weil-operations, proof step 6
(blueprint: lem-pod-equivariant-mates-coefficient-transport). -/
def CoefficientComparison.source
    {S : Square A B C D} {T : Square A' B' C' D'}
    {a : A ⥤ A'} {b : B ⥤ B'} {c : C ⥤ C'} {d : D ⥤ D'}
    (e : CoefficientComparison S T a b c d) :=
  compositeComparison e.adj₁.right e.horizontal

/-- The actual target comparison for the mate.
Source: prop-weil-operations, proof step 6
(blueprint: lem-pod-equivariant-mates-coefficient-transport). -/
def CoefficientComparison.target
    {S : Square A B C D} {T : Square A' B' C' D'}
    {a : A ⥤ A'} {b : B ⥤ B'} {c : C ⥤ C'} {d : D ⥤ D'}
    (e : CoefficientComparison S T a b c d) :=
  compositeComparison e.vertical e.adj₂.right

/-- Coefficient transport of the specified mate, including localization and finite
field extension. The equation is equality of maps with the actual endpoint comparisons.
Source: prop-weil-operations, proof steps 4--6
(blueprint: lem-pod-equivariant-mates-coefficient-transport).
Proof: expand the three-factor mate. Unit compatibility gives the first factor;
naturality of the right-adjoint comparison and square compatibility give the second;
counit compatibility gives the third. Multiply the three equations. The intermediate
comparison and its inverse cancel. For rationalization this is Q(a₁a₂a₃) = Q(a₁)Q(a₂)Q(a₃).
Linearity gives naturality for finite sums of pure tensors, so no integral lift of an
arbitrary rational arrow, or integral inverse of a Weil structure, is used. -/
theorem mate_coefficientTransport
    (S : Square A B C D) (T : Square A' B' C' D')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    (e : CoefficientComparison S T a b c d) :
    ∀ K : B,
      e.source.inv.app K ≫ c.map (S.mate.app K) ≫ e.target.hom.app K =
        T.mate.app (b.obj K) := by
  intro K
  apply (cancel_epi (e.source.hom.app K)).1
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  dsimp [CoefficientComparison.source, CoefficientComparison.target, compositeComparison,
    Square.mate, mateEquiv]
  simp only [Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc]
  have hc : b.map (S.adj₁.counit.app K) =
      e.adj₁.left.hom.app (S.right₁.obj K) ≫
        T.left₁.map (e.adj₁.right.hom.app K) ≫ T.adj₁.counit.app (b.obj K) := by
    rw [e.adj₁.counit]
    simp
  have hs := e.square (S.right₁.obj K)
  dsimp [ExchangeProjectionComparisonPreserves, compositeComparison] at hs
  simp only [Category.id_comp, Category.comp_id, Category.assoc] at hs
  have hn₁ := e.adj₂.right.hom.naturality (S.vertical.map (S.adj₁.counit.app K))
  have hn₂ := e.adj₂.right.hom.naturality (S.square.app (S.right₁.obj K))
  have hv := e.vertical.hom.naturality (S.adj₁.counit.app K)
  dsimp at hn₁ hn₂ hv
  rw [reassoc_of% hn₁, reassoc_of% hn₂]
  rw [← T.right₂.map_comp, ← T.right₂.map_comp, hv, hc]
  simp only [Functor.map_comp]
  have hsm := T.right₂.congr_map hs
  simp only [Functor.map_comp] at hsm
  rw [reassoc_of% hsm]
  rw [reassoc_of% (e.adj₂.unit (S.horizontal.obj (S.right₁.obj K)))]
  have hu := T.adj₂.unit.naturality (e.horizontal.hom.app (S.right₁.obj K))
  have hur := T.adj₂.unit.naturality (T.horizontal.map (e.adj₁.right.hom.app K))
  have ht := T.square.natTrans.naturality (e.adj₁.right.hom.app K)
  dsimp at hu hur ht
  rw [← reassoc_of% hu, reassoc_of% hur]
  rw [← T.right₂.map_comp_assoc, ← ht]
  simp only [Functor.map_comp, Category.assoc]
end CoefficientComparison

/-- Coefficient transport preserves any pasted mate: it preserves a finite composite
of whiskered factors, with all middle endpoint comparisons cancelled.
Source: prop-weil-operations, proof steps 6 and 9
(blueprint: lem-pod-equivariant-mates-coefficient-transport).
Proof: functoriality sends the composite to the composite of images. Insert each
middle comparison followed by its inverse. The inverse identities cancel them. This
applies to every composite displayed in the four fixed-pair pasting identities above. -/
theorem pasted_coefficientTransport
    (T : C ⥤ D) {X₀ X₁ X₂ X₃ : C} {Y₀ Y₁ Y₂ Y₃ : D}
    (e₀ : T.obj X₀ ≅ Y₀) (e₁ : T.obj X₁ ≅ Y₁)
    (e₂ : T.obj X₂ ≅ Y₂) (e₃ : T.obj X₃ ≅ Y₃)
    (a₁ : X₀ ⟶ X₁) (a₂ : X₁ ⟶ X₂) (a₃ : X₂ ⟶ X₃) :
    e₀.inv ≫ T.map (a₁ ≫ a₂ ≫ a₃) ≫ e₃.hom =
      (e₀.inv ≫ T.map a₁ ≫ e₁.hom) ≫
      (e₁.inv ≫ T.map a₂ ≫ e₂.hom) ≫
      (e₂.inv ≫ T.map a₃ ≫ e₃.hom) := by
  simp [Functor.map_comp, Category.assoc]

/-- Composite vertex comparisons inherit the specified identity and tower laws.
Apply this to R₁ followed by U and to V followed by R₂ for the mate endpoints, and
iteratively to each vertex of a pasted mate.
Source: prop-weil-operations, proof step 7
(blueprint: lem-pod-equivariant-mates-coefficient-transport).
Proof: expand compositeComparison. For identities, the two supplied identity equations
and naturality give the composite identity. For a tower, use naturality to interchange
the two middle comparisons, then the supplied cocycles for F and G. Functor
associativity and the transition associators give the displayed composite cocycle. -/
theorem compositeComparison_cocycle
    {I : Type u} [Preorder I]
    (CA : I → Type uA) (CB : I → Type uB) (CC : I → Type uC)
    [∀ i, Category.{vA} (CA i)] [∀ i, Category.{vB} (CB i)]
    [∀ i, Category.{vC} (CC i)]
    (F : ∀ i, CA i ⥤ CB i) (G : ∀ i, CB i ⥤ CC i)
    (a : ∀ i j, i ≤ j → CA i ⥤ CA j)
    (b : ∀ i j, i ≤ j → CB i ⥤ CB j)
    (c : ∀ i j, i ≤ j → CC i ⥤ CC j)
    (aId : ∀ i, a i i le_rfl ≅ 𝟭 (CA i))
    (bId : ∀ i, b i i le_rfl ≅ 𝟭 (CB i))
    (cId : ∀ i, c i i le_rfl ≅ 𝟭 (CC i))
    (aComp : ∀ i j k (h : i ≤ j) (h' : j ≤ k), a i j h ⋙ a j k h' ≅ a i k (h.trans h'))
    (bComp : ∀ i j k (h : i ≤ j) (h' : j ≤ k), b i j h ⋙ b j k h' ≅ b i k (h.trans h'))
    (cComp : ∀ i j k (h : i ≤ j) (h' : j ≤ k), c i j h ⋙ c j k h' ≅ c i k (h.trans h'))
    (eF : ∀ i j (h : i ≤ j), F i ⋙ b i j h ≅ a i j h ⋙ F j)
    (eG : ∀ i j (h : i ≤ j), G i ⋙ c i j h ≅ b i j h ⋙ G j)
    (hF : ExchangeProjectionScalarCocycle CA CB F a b aId bId aComp bComp eF)
    (hG : ExchangeProjectionScalarCocycle CB CC G b c bId cId bComp cComp eG) :
    ExchangeProjectionScalarCocycle CA CC (fun i ↦ F i ⋙ G i) a c
      aId cId aComp cComp (fun i j h ↦ compositeComparison (eF i j h) (eG i j h)) := by
  constructor
  · intro i x
    dsimp [compositeComparison]
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
    rw [← (G i).map_comp, hF.identity, hG.identity]
  · intro i j k h h' x
    dsimp [compositeComparison]
    simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
    have hn := (eG j k h').hom.naturality ((eF i j h).hom.app x)
    dsimp at hn
    rw [reassoc_of% hn]
    rw [← (G k).map_comp_assoc, ← (G k).map_comp, Category.assoc, hF.composition]
    rw [(G k).map_comp]
    rw [reassoc_of% (hG.composition i j k h h' ((F i).obj x))]
end CategoryTheory.EquivariantMates

namespace WeilConjectures

open CategoryTheory.EquivariantMates
open AlgebraicGeometry

section ConcreteCoefficients

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (YA YB YC YD : Scheme.{u})

/-- Rationalization of the actual integral mate equals the rational mate, conjugated
only by the supplied operation comparisons (identities in strict coordinates).
Source: prop-weil-operations, proof steps 4--5
(blueprint: lem-pod-equivariant-mates-coefficient-transport).
Proof: use mate_coefficientTransport with the four recorded localization functors.
They act on maps by tensoring with one. Their multiplicativity identifies all three
factors. The resulting transformation is natural for every rational arrow, since
finite sums of pure tensors span its Hom group and all specified maps are linear. -/
theorem rational_mate_coefficientTransport
    (S : Square (sfIntegralConstructibleCategory l E YA)
      (sfIntegralConstructibleCategory l E YB) (sfIntegralConstructibleCategory l E YC)
      (sfIntegralConstructibleCategory l E YD))
    (T : Square (sfRationalConstructibleCategory l E YA)
      (sfRationalConstructibleCategory l E YB) (sfRationalConstructibleCategory l E YC)
      (sfRationalConstructibleCategory l E YD))
    (e : CoefficientComparison S T
      (sfRationalConstructibleLocalization l E YA) (sfRationalConstructibleLocalization l E YB)
      (sfRationalConstructibleLocalization l E YC) (sfRationalConstructibleLocalization l E YD)) :
    ∀ K : sfIntegralConstructibleCategory l E YB,
      e.source.inv.app K ≫ (sfRationalConstructibleLocalization l E YC).map (S.mate.app K) ≫
        e.target.hom.app K =
          T.mate.app ((sfRationalConstructibleLocalization l E YB).obj K) := by
  exact mate_coefficientTransport S T _ _ _ _ e

/-- In the literal localization coordinates, the rational image is exactly the
three-factor mate of the images. No comparison isomorphism or choice enters this equality.
Source: prop-weil-operations, proof step 4
(blueprint: lem-pod-equivariant-mates-coefficient-transport).
Proof: expand the recorded mate formula and use the localization functor's map_comp
on its three factors. On pure tensors multiplication multiplies scalars, so the three
unit scalars give one. The general rational-map naturality is supplied by the rational
mate natural transformation and its linear construction. -/
theorem rational_mate_exact
    (S : Square (sfIntegralConstructibleCategory l E YA)
      (sfIntegralConstructibleCategory l E YB) (sfIntegralConstructibleCategory l E YC)
      (sfIntegralConstructibleCategory l E YD))
    (K : sfIntegralConstructibleCategory l E YB) :
    (sfRationalConstructibleLocalization l E YC).map (S.mate.app K) =
      (sfRationalConstructibleLocalization l E YC).map
        (S.adj₂.unit.app (S.horizontal.obj (S.right₁.obj K))) ≫
      (sfRationalConstructibleLocalization l E YC).map
        (S.right₂.map (S.square.app (S.right₁.obj K))) ≫
      (sfRationalConstructibleLocalization l E YC).map
        (S.right₂.map (S.vertical.map (S.adj₁.counit.app K))) := by
  simp [Square.mate, mateEquiv, Functor.map_comp]

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The transported finite-coefficient-field mate is the mate at the extended field.
These are the actual rational scalar transitions of the common-stage construction.
Source: prop-weil-operations, proof step 6
(blueprint: lem-pod-equivariant-mates-coefficient-transport).
Proof: specialize mate_coefficientTransport to the recorded stageTransition functors.
The two adjunction comparisons supply the unit/counit equations and e.square supplies
alpha compatibility. The intermediate comparisons cancel, including for E = L. -/
theorem finiteExtension_mate_coefficientTransport
    (I J : AlgebraicallyClosedCoefficients.Index l Ω) (h : I ≤ J)
    (S : Square (GeneralAlgebraicallyClosedCoefficients.Stage l Ω YA I)
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω YB I)
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω YC I)
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω YD I))
    (T : Square (GeneralAlgebraicallyClosedCoefficients.Stage l Ω YA J)
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω YB J)
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω YC J)
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω YD J))
    (e : CoefficientComparison S T
      (GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω YA I J h)
      (GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω YB I J h)
      (GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω YC I J h)
      (GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω YD I J h)) :
    ∀ K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω YB I,
      e.source.inv.app K ≫
        (GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω YC I J h).map
          (S.mate.app K) ≫ e.target.hom.app K =
        T.mate.app ((GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω YB I J h).obj K)
          := by
  exact mate_coefficientTransport S T _ _ _ _ e

/-- A mate represented at a finite coefficient field is exactly its common-stage class,
with the supplied endpoint comparisons; no idempotent completion is inserted.
Source: prop-weil-operations, proof steps 7--9
(blueprint: lem-pod-equivariant-mates-coefficient-transport).
Proof: apply mate_coefficientTransport to the four actual inclusions. Their map is
the normalized common-stage representative. Identity and tower normalization of the
operation comparisons, preserved by compositeComparison_cocycle, identify the endpoint
comparisons after every further extension. Thus the same equality holds at every stage. -/
theorem commonStage_mate_coefficientTransport
    (I : AlgebraicallyClosedCoefficients.Index l Ω)
    (S : Square (GeneralAlgebraicallyClosedCoefficients.Stage l Ω YA I)
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω YB I)
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω YC I)
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω YD I))
    (T : Square (generalAlgebraicallyClosedConstructibleCategory l Ω YA)
      (generalAlgebraicallyClosedConstructibleCategory l Ω YB)
      (generalAlgebraicallyClosedConstructibleCategory l Ω YC)
      (generalAlgebraicallyClosedConstructibleCategory l Ω YD))
    (e : CoefficientComparison S T
      (GeneralAlgebraicallyClosedCoefficients.inclusion I)
      (GeneralAlgebraicallyClosedCoefficients.inclusion I)
      (GeneralAlgebraicallyClosedCoefficients.inclusion I)
      (GeneralAlgebraicallyClosedCoefficients.inclusion I)) :
    ∀ K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω YB I,
      e.source.inv.app K ≫ (GeneralAlgebraicallyClosedCoefficients.inclusion I).map
        (S.mate.app K) ≫ e.target.hom.app K =
          T.mate.app ((GeneralAlgebraicallyClosedCoefficients.inclusion I).obj K) := by
  exact mate_coefficientTransport S T _ _ _ _ e

/-- Naturality for every common-stage arrow and independence from both its finite field
and representative, using the literal quotient Hom relation.
Source: prop-weil-operations, proof steps 8--9
(blueprint: lem-pod-equivariant-mates-coefficient-transport).
Proof: represent an arbitrary arrow at one finite field. Equality of two representatives
means equality after some further common extension (representatives). Apply the actual
operation functors there; the endpoint comparisons agree by the cocycle. Their conjugated
images are equal. Finite-stage naturality descends to the quotient; equivalently it is
naturality of T.mate on the common-stage category. This argument also applies to pasted
mates because their composites have the same coefficient-transport cancellation. -/
theorem commonStage_mate_representatives
    (T : Square (generalAlgebraicallyClosedConstructibleCategory l Ω YA)
      (generalAlgebraicallyClosedConstructibleCategory l Ω YB)
      (generalAlgebraicallyClosedConstructibleCategory l Ω YC)
      (generalAlgebraicallyClosedConstructibleCategory l Ω YD)) :
    (∀ (K H : GeneralAlgebraicallyClosedCoefficients.Pair l Ω YB) (f : K ⟶ H),
      (T.right₁ ⋙ T.horizontal).map f ≫ T.mate.app H =
        T.mate.app K ≫ (T.vertical ⋙ T.right₂).map f) ∧
    (∀ (K H : GeneralAlgebraicallyClosedCoefficients.Pair l Ω YB)
      (I J : GeneralAlgebraicallyClosedCoefficients.Common K H)
      (f : GeneralAlgebraicallyClosedCoefficients.StageHom K H I)
      (g : GeneralAlgebraicallyClosedCoefficients.StageHom K H J),
      (∃ (N : GeneralAlgebraicallyClosedCoefficients.Common K H) (hI : I ≤ N) (hJ : J ≤ N),
        GeneralAlgebraicallyClosedCoefficients.transport K H I N hI f =
          GeneralAlgebraicallyClosedCoefficients.transport K H J N hJ g) →
      (T.right₁ ⋙ T.horizontal).map
          (GeneralAlgebraicallyClosedCoefficients.ofHom K H I.val I.property.1 I.property.2 f) ≫
          T.mate.app H =
        T.mate.app K ≫ (T.vertical ⋙ T.right₂).map
          (GeneralAlgebraicallyClosedCoefficients.ofHom K H J.val J.property.1 J.property.2 g))
          := by
  constructor
  · intro K H f
    exact T.mate.naturality f
  · intro K H I J f g h
    have he := ((GeneralAlgebraicallyClosedCoefficients.representatives K H).2 I J f g).mpr h
    rw [← he]
    exact T.mate.naturality _

end ConcreteCoefficients

section ArbitraryWeilStructures

variable (D₀ : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D₀.p)
  (YA YB YC YD : Over (Spec (.of D₀.k₀)))
  [LocallyOfFiniteType YA.hom] [QuasiCompact YA.hom]
  [LocallyOfFiniteType YB.hom] [QuasiCompact YB.hom]
  [LocallyOfFiniteType YC.hom] [QuasiCompact YC.hom]
  [LocallyOfFiniteType YD.hom] [QuasiCompact YD.hom]

variable (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Every rational Weil structure is allowed, including ones with no stable integral lattice.
Source: prop-weil-operations, proof steps 2, 5 and 9
(blueprint: lem-pod-equivariant-mates-coefficient-transport).
Proof: apply fixedPair_mate in the recorded constructible coefficient categories with
geometric Frobenius pullback. Its input is any fixed pair, not an integral pair or an
integrally invertible representative. Naturality holds for every fixed-pair arrow
because the mate is a natural transformation in that category. Faithfulness identifies
its carrier with the specified three factors. -/
theorem rational_weil_mate
    (S : Square
      (sfRationalConstructibleCategory l E (D₀.geometricFiber YA).left)
      (sfRationalConstructibleCategory l E (D₀.geometricFiber YB).left)
      (sfRationalConstructibleCategory l E (D₀.geometricFiber YC).left)
      (sfRationalConstructibleCategory l E (D₀.geometricFiber YD).left))
    (W : FixedLift S
      (sfWeilFrobeniusPullback D₀ l hl YA E)
      (sfWeilFrobeniusPullback D₀ l hl YB E)
      (sfWeilFrobeniusPullback D₀ l hl YC E)
      (sfWeilFrobeniusPullback D₀ l hl YD E)) :
    ∃ (a₁ : W.left₁ ⊣ W.right₁) (a₂ : W.left₂ ⊣ W.right₂),
      a₁.unit = W.unit₁ ∧ a₁.counit = W.counit₁ ∧
      a₂.unit = W.unit₂ ∧ a₂.counit = W.counit₂ ∧
      (∀ K : sfWeilComplex D₀ l hl YB E,
        HEq ((mateEquiv a₁ a₂ W.square).app K).hom.f
          (S.adj₂.unit.app (S.horizontal.obj (S.right₁.obj K.carrier)) ≫
            S.right₂.map (S.square.app (S.right₁.obj K.carrier)) ≫
            S.right₂.map (S.vertical.map (S.adj₁.counit.app K.carrier)))) ∧
      (∀ (K H : sfWeilComplex D₀ l hl YB E) (f : K ⟶ H),
        (W.right₁ ⋙ W.horizontal).map f ≫ (mateEquiv a₁ a₂ W.square).app H =
          (mateEquiv a₁ a₂ W.square).app K ≫ (W.vertical ⋙ W.right₂).map f) := by
  obtain ⟨a₁, a₂, h₁, h₂, h₃, h₄, hm⟩ := fixedPair_mate S _ _ _ _ W
  exact ⟨a₁, a₂, h₁, h₂, h₃, h₄, hm, fun K H f ↦
    (mateEquiv a₁ a₂ W.square).naturality f⟩

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Every commonStage Weil structure is allowed, including ones with no stable integral lattice.
Source: prop-weil-operations, proof steps 2, 5 and 9
(blueprint: lem-pod-equivariant-mates-coefficient-transport).
Proof: apply fixedPair_mate in the recorded constructible coefficient categories with
geometric Frobenius pullback. Its input is any fixed pair, not an integral pair or an
integrally invertible representative. Naturality holds for every fixed-pair arrow
because the mate is a natural transformation in that category. Faithfulness identifies
its carrier with the specified three factors. -/
theorem commonStage_weil_mate
    (S : Square
      (generalAlgebraicallyClosedConstructibleCategory l Ω (D₀.geometricFiber YA).left)
      (generalAlgebraicallyClosedConstructibleCategory l Ω (D₀.geometricFiber YB).left)
      (generalAlgebraicallyClosedConstructibleCategory l Ω (D₀.geometricFiber YC).left)
      (generalAlgebraicallyClosedConstructibleCategory l Ω (D₀.geometricFiber YD).left))
    (W : FixedLift S
      (sfCommonStageWeilFrobeniusPullback D₀ l hl YA Ω)
      (sfCommonStageWeilFrobeniusPullback D₀ l hl YB Ω)
      (sfCommonStageWeilFrobeniusPullback D₀ l hl YC Ω)
      (sfCommonStageWeilFrobeniusPullback D₀ l hl YD Ω)) :
    ∃ (a₁ : W.left₁ ⊣ W.right₁) (a₂ : W.left₂ ⊣ W.right₂),
      a₁.unit = W.unit₁ ∧ a₁.counit = W.counit₁ ∧
      a₂.unit = W.unit₂ ∧ a₂.counit = W.counit₂ ∧
      (∀ K : sfCommonStageWeilComplex D₀ l hl YB Ω,
        HEq ((mateEquiv a₁ a₂ W.square).app K).hom.f
          (S.adj₂.unit.app (S.horizontal.obj (S.right₁.obj K.carrier)) ≫
            S.right₂.map (S.square.app (S.right₁.obj K.carrier)) ≫
            S.right₂.map (S.vertical.map (S.adj₁.counit.app K.carrier)))) ∧
      (∀ (K H : sfCommonStageWeilComplex D₀ l hl YB Ω) (f : K ⟶ H),
        (W.right₁ ⋙ W.horizontal).map f ≫ (mateEquiv a₁ a₂ W.square).app H =
          (mateEquiv a₁ a₂ W.square).app K ≫ (W.vertical ⋙ W.right₂).map f) := by
  obtain ⟨a₁, a₂, h₁, h₂, h₃, h₄, hm⟩ := fixedPair_mate S _ _ _ _ W
  exact ⟨a₁, a₂, h₁, h₂, h₃, h₄, hm, fun K H f ↦
    (mateEquiv a₁ a₂ W.square).naturality f⟩

end ArbitraryWeilStructures

end WeilConjectures
