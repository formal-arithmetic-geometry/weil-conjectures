/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q39 and Y9
-/
module

public import Sheaf.Paper.FiniteStageRationalExchangeData

import Sheaf.Paper.RationalOperationCoherence
import Sheaf.Paper.RationalSquareExchangeCoherence

/-! # Finite-stage rational exchange and its coefficient coherence

Source: sketch32, lines 1191--1228, 1262--1279 and 1291--1321
(blueprint: lem-sbc-finite-stage-rational-exchange-coherence).

The raw composites and exchange are the already published `sbcRationalLeft`,
`sbcRationalRight` and `sbcRationalExchange`. The witness propositions below specify
individual operations, canonical tensor comparisons, their units and towers, and
both raw and finite-stage Karoubi exchange equations. They are conclusions, not
additional hypotheses. No constructible landing or invertibility is required.

## Main definitions

* `rawPull`, `rawPush`: the existing localization applied to the actual operations.
* `HasOperationCoherence`: canonical comparisons, units and towers for one operation pair.
* `HasCoherence`: the four operation pairs and their coefficient-compatible exchange.

## Main statements

* `between_karoubi_spec`: the additive pure-tensor extension formula.
* `additive_karoubi_extension_spec`: supported Karoubi formulas, including comparisons.
* `finiteStageRationalExchangeCoherence`: the full finite-stage conclusion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures TensorProduct

namespace CategoryTheory.ScalarLocalization

universe r a b x y
variable (R : Type r) [CommRing R] (t : R)
  {C : Type a} [Category.{x} C] [Preadditive C] [Linear R C]
  {D : Type b} [Category.{y} D] [Preadditive D] [Linear R D]
  (H : C ⥤ D) [H.Additive] [H.Linear R]

/-- Explicit formulas for the extensions used in the finite-stage statement.
The coefficient-first tensor convention is the existing raw localization convention;
its tensor commutor gives the Hom-first convention in sketch32. The scalar algebra
of lem-weil-l-adic-integers-localization-uniformizer identifies the localized
coefficient ring with E when this is applied to the complete coefficient categories.
Source: sketch32, lines 1191--1228 and 1300--1321
(blueprint: lem-sbc-finite-stage-rational-exchange-coherence).
Proof: use the additive/identity-semilinear clauses of
lem-pur-semilinear-scalar-localization, or expand betweenHom on pure tensors.
Tensor induction gives additivity, with the existing base-changed linear map
sending each pure tensor to the displayed pure tensor. This is proof step 2. -/
theorem between_karoubi_spec :
    (between R t H).Additive ∧
    (∀ (K L : C) (f : K ⟶ L) (c : Localization.Away t),
      (between R t H).map
          (c ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶
            ScalarLocalization.mk (R := R) (p := t) L) =
        c ⊗ₜ[R] H.map f) := by
  constructor
  · exact ⟨fun {K L} f g ↦ (betweenHom R t H K.obj L.obj).map_add f g⟩
  · intro K L f c
    exact LinearMap.baseChange_tmul _ _ _

end CategoryTheory.ScalarLocalization

namespace CategoryTheory.Idempotents

universe a b x y
variable {A : Type a} [Category.{x} A] [Preadditive A]
  {B : Type b} [Category.{y} B] [Preadditive B]
  (F G : A ⥤ B) [F.Additive] [G.Additive]

set_option linter.unusedSectionVars false in
/-- Supported formulas for additive Karoubi extensions of arbitrary raw functors.
In particular these apply to the semilinear scalar comparisons, whose source and
target raw categories can have different coefficient fields.
Source: sketch32, lines 1208--1228 and 1308--1321
(blueprint: lem-sbc-finite-stage-rational-exchange-coherence).
Proof: functorExtension₂ applies a functor to the underlying object, projector
and supported arrow. Naturality at p equates F(p) alpha with alpha G(p), and
idempotence inserts the second projector. At p=1 both projectors disappear.
For b and its inverse the same calculation gives both supported formulas;
their composites reduce to the two projectors, the respective Karoubi identities.
Additivity is inherited on supported arrows. These are proof steps 6--9. -/
theorem additive_karoubi_extension_spec (α : F ⟶ G) :
    ((functorExtension₂ _ _).obj F).Additive ∧
    (∀ P : Karoubi A,
      (((functorExtension₂ _ _).obj F).obj P).X =
          F.obj P.X ∧
        (((functorExtension₂ _ _).obj F).obj P).p =
          F.map P.p) ∧
    (∀ (P Q : Karoubi A) (f : P ⟶ Q),
      (((functorExtension₂ _ _).obj F).map f).f =
        F.map f.f) ∧
    (∀ P : Karoubi A,
      (((functorExtension₂ _ _).map α).app P).f =
        F.map P.p ≫ α.app P.X ≫
          G.map P.p) ∧
    (∀ K : A,
      HEq (((functorExtension₂ _ _).map α).app
          ((toKaroubi _).obj K))
        ((toKaroubi _).map (α.app K))) ∧
    (∀ (b : F ≅ G) (P : Karoubi A),
      (((functorExtension₂ _ _).mapIso b).hom.app P).f =
          F.map P.p ≫ b.hom.app P.X ≫ G.map P.p ∧
        (((functorExtension₂ _ _).mapIso b).inv.app P).f =
          G.map P.p ≫ b.inv.app P.X ≫ F.map P.p) := by
  have supported {H J : A ⥤ B} (η : H ⟶ J) (P : Karoubi A) :
      (((functorExtension₂ _ _).map η).app P).f =
        H.map P.p ≫ η.app P.X ≫ J.map P.p := by
    change H.map P.p ≫ η.app P.X = H.map P.p ≫ η.app P.X ≫ J.map P.p
    rw [← η.naturality P.p, ← Category.assoc, ← H.map_comp, P.idem]
  refine ⟨?_, ?_, ?_, supported α, ?_, ?_⟩
  · constructor
    intro P Q f g
    ext
    exact F.map_add
  · intro P
    exact ⟨rfl, rfl⟩
  · intro P Q f
    rfl
  · intro K
    have hom_heq {P Q P' Q' : Karoubi B} (hP : P = P') (hQ : Q = Q')
        (a : P ⟶ Q) (b : P' ⟶ Q') (hab : HEq a.f b.f) : HEq a b := by
      subst P'
      subst Q'
      exact heq_of_eq (Karoubi.hom_ext a b (eq_of_heq hab))
    have hF : ((functorExtension₂ A B).obj F).obj ((toKaroubi A).obj K) =
        (toKaroubi B).obj (F.obj K) := by
      refine Karoubi.ext ?_ ?_
      · rfl
      · change F.map (𝟙 K) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
        rw [F.map_id]
    have hG : ((functorExtension₂ A B).obj G).obj ((toKaroubi A).obj K) =
        (toKaroubi B).obj (G.obj K) := by
      refine Karoubi.ext ?_ ?_
      · rfl
      · change G.map (𝟙 K) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
        rw [G.map_id]
    apply hom_heq hF hG
    apply heq_of_eq
    change F.map (𝟙 K) ≫ α.app K = α.app K
    rw [F.map_id, Category.id_comp]
  · intro b P
    exact ⟨supported b.hom P, supported b.inv P⟩

end CategoryTheory.Idempotents

attribute [local irreducible] pbcAmbientCompleteRawSystem

namespace AlgebraicGeometry.Scheme.FiniteStageRationalExchange

variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
  [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [dS : Fact (∃ n : ℕ, topologicalKrullDim S ≤ n)]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [iS : Fact (∀ x : S, IsUnit (l : S.presheaf.stalk x))]
  (sq : ChosenCartesianSquare h e f g)

/-- Canonical additive raw rational and finite-stage Karoubi operations, specified
scalar comparisons with units and towers, and coefficient-compatible exchange.
Only invertibility on S is assumed: the existential Fact witnesses at the other
corners are obtained by mapping units through their structure maps to S.
They add no geometric assumption. The exchange itself is not asserted invertible.
Source: sketch32, lines 1191--1228, 1262--1279 and 1291--1321
(blueprint: lem-sbc-finite-stage-rational-exchange-coherence).
Proof:
1. lem-sbc-completed-operations-linear-natural-exchange supplies the actual integral
   linear operations and natural completed mate on all complete objects.
2. lem-pur-semilinear-scalar-localization and
   lem-weil-l-adic-integers-localization-uniformizer extend the operations and mate
   by the pure-tensor formula; between_karoubi_spec records that formula.
3. prop-weil-pbc-scalar-extension supplies the tensor-unit-normalized operation
   comparisons and their integral coefficient towers. Compare the two published
   coefficient maps on every finite projection. Transport the scalar push mate by
   conjugateIsoEquiv and transport completed pullback by the strict-tower comparison.
   Fullness gives precisely the displayed integral components, uniquely.
4. Localize these maps and their inverses using semilinear scalar localization.
   The source uniformizer maps to a unit after target localization. Conjugate by
   pbcAmbientCompleteIntegralComparison, retaining its equal-field tensor-unit branch.
   This gives the raw beta normalizations and the operation unit and tower fields.
5. The scalar-exchange equation of prop-weil-pbc-scalar-extension uses the ambient
   mate followed by completion and gamma. By lem-weil-pbc-ringed-pushforward-completion,
   gamma kappa = R_h(kappa). The completed-pullback unit therefore factors this map
   as R_h(k_e) times the ambient mate. Apply
   lem-sbc-reflected-compositor-unit-normalization to both compositors to identify
   their completed square comparison. Then the uniqueness clause of
   lem-sbc-reflector-square-mate-factorization identifies this map with sbcExchange.
   Localization gives rawAlpha.comm for the specified integral comparison composites.
6. Apply Mathlib's functorExtension₂ to objects, maps, comparisons and exchange.
   The formulas are those of additive_karoubi_extension_spec, including p=0 and p=1.
7. Naturality at the projector proves naturality on every supported arrow. The two
   comparison composites reduce to the source and target projectors, proving that
   the supported inverses are the required Karoubi inverses.
8. The supported formulas preserve identities, composition and both whiskerings:
   move projectors through each natural component, then use idempotence. Thus raw
   comparison equations give the same equations with the ambient Karoubi associators.
9. For composite operations, expand beta and the two individual tower equations.
   Naturality of the outer comparison at the inner comparison moves the two middle
   factors past each other. The result is exactly StageSystem.Morphism.coh. At an
   identity transition the composite is the identity. Do this for F and G, and then
   extend both equations by the supported formulas.
10. Apply that preservation calculation to the raw exchange equation of step 5.
    It gives karAlpha.comm on every (K,p), with precisely the specified beta maps.
    These are all the unit, tower and exchange assertions before and after Karoubi
    extension. No smoothness, admissible lattice or constructible landing is used. -/
theorem finiteStageRationalExchangeCoherence :
    ∃ (iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x)))
      (iT : Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x)))
      (iY : Fact (∀ x : Y, IsUnit (l : Y.presheaf.stalk x))),
      HasCoherence l Ω (iX := iX) (iT := iT) (iY := iY) sq := by
  have iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x)) := ⟨fun x ↦ by
    simpa only [map_natCast] using (iS.out (f x)).map (f.stalkMap x).hom⟩
  have iT : Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x)) := ⟨fun x ↦ by
    simpa only [map_natCast] using (iS.out (g x)).map (g.stalkMap x).hom⟩
  have iY : Fact (∀ x : Y, IsUnit (l : Y.presheaf.stalk x)) := ⟨fun x ↦ by
    simpa only [map_natCast] using (iX.out (h x)).map (h.stalkMap x).hom⟩
  refine ⟨iX, iT, iY, ?_⟩
  let := iX
  let := iT
  let := iY
  obtain ⟨fPush, fPull, fRawPush, fRawPull, hf⟩ := rationalOperationCoherence l Ω f
  obtain ⟨gPush, gPull, gRawPush, gRawPull, hg⟩ := rationalOperationCoherence l Ω g
  obtain ⟨hPush, hPull, hRawPush, hRawPull, hh⟩ := rationalOperationCoherence l Ω h
  obtain ⟨ePush, ePull, eRawPush, eRawPull, he⟩ := rationalOperationCoherence l Ω e
  refine ⟨@fPush, @fPull, fRawPush, fRawPull, @gPush, @gPull, gRawPush, gRawPull,
    @hPush, @hPull, hRawPush, hRawPull, @ePush, @ePull, eRawPush, eRawPull,
    hf, hg, hh, he, ?_⟩
  exact rationalSquareExchangeCoherence l Ω sq
    @fPush @fPull fRawPush fRawPull @gPush @gPull gRawPush gRawPull
    @hPush @hPull hRawPush hRawPull @ePush @ePull eRawPush eRawPull hf hg hh he

end AlgebraicGeometry.Scheme.FiniteStageRationalExchange
