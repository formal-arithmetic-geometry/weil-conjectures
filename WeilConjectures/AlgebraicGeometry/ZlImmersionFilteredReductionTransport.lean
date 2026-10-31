/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicPunctualWeights
public import WeilConjectures.AlgebraicGeometry.SfWeilSheafComplex
public import WeilConjectures.AlgebraicGeometry.SfConstructibleHeart
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.WeilIndSheafCategory
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.SfCommonStageDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # Immersion images and reduction transport of prescribed Weil filtrations

Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-general/
sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md, reduction paragraph
and final open-closed gluing paragraph
(blueprint: lem-zl-immersion-filtered-reduction-transport).

Finite functors from Fin (n + 1), with monic arrows and zero initial object,
encode individual filtrations. The unit transport includes its commuting endpoint
square; it therefore specifies the inverse-image subobjects under the actual unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {Y X : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]

/-- The filtration clauses of the immersion lemma, including exactness, purity
of every real weight, and the quotient isomorphisms with their cokernel equations.
These equations specify the usual quotient comparison in the Weil heart.
The last object of G is the sheaf being filtered, up to its given identification.
Source: source final paragraph
(blueprint: lem-zl-immersion-filtered-reduction-transport). -/
def ZlImmersionImageFiltration (iota : Ω ≃+* ℂ)
    (T : sfCommonStageWeilSheaf D l hl Y Ω ⥤ sfCommonStageWeilSheaf D l hl X Ω) :
    Prop :=
  PreservesFiniteLimits T ∧ PreservesFiniteColimits T ∧
    (∀ (F : sfCommonStageWeilSheaf D l hl Y Ω) (w : ℝ),
      SfIsPunctuallyPureOfWeight D l hl Ω Y iota F w →
        SfIsPunctuallyPureOfWeight D l hl Ω X iota (T.obj F) w) ∧
    (∀ (n : ℕ) (G : Fin (n + 1) ⥤ sfCommonStageWeilSheaf D l hl Y Ω)
      (weights : Fin n → ℝ),
      IsZero (G.obj 0) →
      (∀ (a b : Fin (n + 1)) (h : a ≤ b), Mono (G.map (homOfLE h))) →
      (∀ s : Fin n, SfIsPunctuallyPureOfWeight D l hl Ω Y iota
        (cokernel (G.map (homOfLE s.castSucc_le_succ))) (weights s)) →
      IsZero (T.obj (G.obj 0)) ∧
        (∀ (a b : Fin (n + 1)) (h : a ≤ b), Mono (T.map (G.map (homOfLE h)))) ∧
        (∀ s : Fin n,
          ∃ e : cokernel (T.map (G.map (homOfLE s.castSucc_le_succ))) ≅
              T.obj (cokernel (G.map (homOfLE s.castSucc_le_succ))),
            cokernel.π (T.map (G.map (homOfLE s.castSucc_le_succ))) ≫ e.hom =
                T.map (cokernel.π (G.map (homOfLE s.castSucc_le_succ))) ∧
              SfIsPunctuallyPureOfWeight D l hl Ω X iota
                (cokernel (T.map (G.map (homOfLE s.castSucc_le_succ)))) (weights s)) ∧
        (∀ w : ℝ, (∀ s, weights s ≤ w) →
          SfIsMixedOfWeightsAtMost D l hl Ω X iota (T.obj (G.obj (Fin.last n))) w)) ∧
    (∀ (F : sfCommonStageWeilSheaf D l hl Y Ω) (w : ℝ),
      SfIsMixedOfWeightsAtMost D l hl Ω Y iota F w →
        SfIsMixedOfWeightsAtMost D l hl Ω X iota (T.obj F) w)

/-- The prescribed filtration transported through a unit. The natural isomorphism
identifies every P_s with I G_s and all inclusion maps. The endpoint equation says
that its inclusion into H, followed by eta, is the given inclusion into I e*H.
Thus P represents exactly eta^{-1}(I G), rather than an unrelated mixed filtration.
Source: source reduction paragraph and final paragraph
(blueprint: lem-zl-immersion-filtered-reduction-transport). -/
def ZlImmersionUnitFiltration (iota : Ω ≃+* ℂ)
    (I : sfCommonStageWeilSheaf D l hl Y Ω ⥤ sfCommonStageWeilSheaf D l hl X Ω)
    (H : sfCommonStageWeilSheaf D l hl X Ω)
    (K : sfCommonStageWeilSheaf D l hl Y Ω) (eta : H ⟶ I.obj K) : Prop :=
  ∀ (n : ℕ) (G : Fin (n + 1) ⥤ sfCommonStageWeilSheaf D l hl Y Ω)
    (last : G.obj (Fin.last n) ≅ K) (weights : Fin n → ℝ),
    IsZero (G.obj 0) →
    (∀ (a b : Fin (n + 1)) (h : a ≤ b), Mono (G.map (homOfLE h))) →
    (∀ s : Fin n, SfIsPunctuallyPureOfWeight D l hl Ω Y iota
      (cokernel (G.map (homOfLE s.castSucc_le_succ))) (weights s)) →
    ∃ (P : Fin (n + 1) ⥤ sfCommonStageWeilSheaf D l hl X Ω)
      (comparison : P ≅ G ⋙ I) (finish : P.obj (Fin.last n) ≅ H),
      finish.hom ≫ eta = comparison.hom.app (Fin.last n) ≫ I.map last.hom ∧
        IsZero (P.obj 0) ∧
        (∀ (a b : Fin (n + 1)) (h : a ≤ b), Mono (P.map (homOfLE h))) ∧
        (∀ s : Fin n,
          Nonempty (cokernel (P.map (homOfLE s.castSucc_le_succ)) ≅
            I.obj (cokernel (G.map (homOfLE s.castSucc_le_succ)))) ∧
          SfIsPunctuallyPureOfWeight D l hl Ω X iota
            (cokernel (P.map (homOfLE s.castSucc_le_succ))) (weights s)) ∧
        (∀ w : ℝ, (∀ s, weights s ≤ w) →
          SfIsMixedOfWeightsAtMost D l hl Ω X iota H w)

variable [IsSeparated Y.hom] [IsSeparated X.hom]

/-- Open and closed images preserve each prescribed pure quotient and its assigned
weight. A surjective closed immersion has invertible actual adjunction unit, along
which every specified mixed filtration transports with the same weights and bounds.
The closed image is normalized on both its derived carrier and its actual unit;
the existential merely restricts this uniquely specified operation to the heart.
The open image is pinned by its left adjunction to the recorded inverse image.
There is no relation required between the open and closed immersions.

In particular take Y to be X.left.nilradical.subscheme over k₀ and i its
subschemeι: the reduction theorem gives the required surjective closed immersion.
No reducedness or reality assumption is used.

Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-general/
sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md, reduction and final paragraphs
(blueprint: lem-zl-immersion-filtered-reduction-transport).

Proof (the seven DAG steps):
1. Apply lem-zl-extension-by-zero-punctual to j. Exactness and the zero stalks
   outside its image give purity preservation, independently of i.
2. A closed immersion is finite (lem-weil-pbc-closed-immersion-finite).
   Apply lem-zl-finite-adic-direct-image. The normalized closed Frobenius mate of
   lem-sf-open-closed-weil-mate-structures and t-exact Frobenius pullback from
   lem-a1-constructible-pullback-t-exact lift it to the exact fixed-pair heart
   as in lem-zl-texact-fixed-pair-heart-cohomology.
3. A closed fibre is empty or a single point with the same residue field
   (lem-zl-immersion-weil-local-behavior). The local point-transport naturality
   lem-weil-frobenius-point-transport-natural intertwines local Frobenius. Thus
   closed image preserves the eigenvalues and their weights, with zero off support.
4. Apply lem-sp-exact-functor-preserves-homology to every inclusion of the specified
   filtration: its cokernel comparison is a Weil isomorphism. The same eigenvalues
   prove purity of the quotient at its original weight, hence each common bound.
5. For a surjective closed immersion the complementary open is empty. By
   lem-per-adic-heart-pullback-fibres its restriction is zero. The actual localization
   triangle of prop-sf-open-closed-triangle-all-stages, followed by heart cohomology
   (lem-weil-heart-short-exact-triangles), makes the actual unit invertible.
6. Push the given filtration forward, then use the inverse of this very unit at
   its endpoint. Naturality supplies the displayed commuting square for every
   inclusion; exactness preserves quotients, purity and every common bound.
7. Apply lem-weil-pbc-reduction-universal-homeomorphism to the nilradical immersion.
   Repeated terms and zero quotients cause no change; length zero forces H to be zero.
-/
theorem zlImmersionFilteredReductionTransport (iota : Ω ≃+* ℂ)
    {V : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (j : V ⟶ X) [IsOpenImmersion j.left] (i : Y ⟶ X) [IsClosedImmersion i.left] :
    ∃ (J : sfCommonStageWeilSheaf D l hl V Ω ⥤ sfCommonStageWeilSheaf D l hl X Ω)
      (_adjJ : J ⊣ zlWeilPull D l hl Ω j)
      (I : sfCommonStageWeilSheaf D l hl Y Ω ⥤ sfCommonStageWeilSheaf D l hl X Ω)
      (adj : zlWeilPull D l hl Ω i ⊣ I),
      I ⋙ ObjectProperty.ι _ = ObjectProperty.ι _ ⋙ sfModelWeilDerivedPush D l hl Ω i ∧
        (∀ H : sfCommonStageWeilSheaf D l hl X Ω,
          HEq ((ObjectProperty.ι _).map (adj.unit.app H))
            ((sfModelWeilDerivedAdjunction D l hl Ω i).unit.app H.obj)) ∧
        ZlImmersionImageFiltration D l hl Ω iota J ∧
        ZlImmersionImageFiltration D l hl Ω iota I ∧
        (Surjective i.left → ∀ H : sfCommonStageWeilSheaf D l hl X Ω,
          IsIso (adj.unit.app H) ∧
            ZlImmersionUnitFiltration D l hl Ω iota I H
              ((zlWeilPull D l hl Ω i).obj H) (adj.unit.app H)) := by
  sorry

end WeilConjectures
