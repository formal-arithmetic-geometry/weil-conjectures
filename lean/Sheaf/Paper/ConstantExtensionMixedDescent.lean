/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.Paper.ConstantExtensionWeilHeartEquivalence
public import Sheaf.Paper.AdicPunctualWeights
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.AdicLocalCharacteristicFactor
public import Sheaf.Paper.SfCommonStageDirectImage
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfDerivedDirectImage

import Sheaf.Paper.SfConstructibleHeart
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
import Sheaf.Paper.MixedWeightsStability
import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius
import Sheaf.Paper.FiniteClopenDerivedDecomposition
import Sheaf.Paper.ZlFiniteAdicDirectImage
import Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual
import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-! # Reality and mixedness under finite constant extension

Source: main-20261015, thm-zl-real-mixed-by-curves.proof.md, paragraphs 1, 5 and 9
(blueprint: lem-zl-constant-extension-mixed-descent).

The direct image is the recorded derived direct image with its induced Weil structure,
restricted to the constructible heart. The trace is specified by counit restrictions
at every geometric lift, with the prescribed pullback composition comparisons. Thus
its stalk map is summation in the actual sheet coordinates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Separatedness of the base change is inherited from the original model.
Source: blueprint separated finite-type hypothesis
(blueprint: lem-zl-constant-extension-mixed-descent). -/
instance constantExtensionMixedDescentModelSeparated :
    IsSeparated (constantExtensionModel D m hm X₀).hom :=
  inferInstanceAs (IsSeparated (pullback.snd X₀.hom
    (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))))

/-- The actual Weil inverse image has a constructible-heart right adjoint.
Source: blueprint descent paragraph 5
(blueprint: lem-zl-constant-extension-mixed-descent).
Proof: the projection is finite by a finite basis of k_m over k_0. Its geometric
base change is finite, so lem-zl-finite-adic-direct-image makes the prescribed
derived image t-exact. Restrict the inverse/derived-direct-image adjunction to the
hearts. The normalized Frobenius exchange and its inverse lift this adjunction to
Weil morphisms. Thus the sectionwise ordinary image, with its induced Weil map,
is right adjoint to exactly zlWeilPull. Its adjunction fixes it up to the unique
adjunction-compatible isomorphism, including its unit and counit. -/
theorem constantExtensionWeilPull_isLeftAdjoint :
    (zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀)).IsLeftAdjoint := by
  sorry

/-- Direct image on the constructible Weil heart, specified by its universal property
as the right adjoint of the actual inverse image. Finiteness identifies it with the
heart restriction of the prescribed derived direct image, with its induced Weil map.
Source: blueprint descent paragraph 5
(blueprint: lem-zl-constant-extension-mixed-descent). -/
def constantExtensionWeilPush :
    sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω ⥤
      sfCommonStageWeilSheaf D l hl X₀ Ω :=
  @Functor.rightAdjoint _ _ _ _
    (zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀))
    (constantExtensionWeilPull_isLeftAdjoint D m hm X₀ l hl Ω)

/-- The inverse/direct-image adjunction on the prescribed constructible Weil hearts.
Source: blueprint descent paragraph 5
(blueprint: lem-zl-constant-extension-mixed-descent). -/
def constantExtensionWeilAdjunction :
    zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀) ⊣
      constantExtensionWeilPush D m hm X₀ l hl Ω :=
  @Adjunction.ofIsLeftAdjoint _ _ _ _
    (zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀))
    (constantExtensionWeilPull_isLeftAdjoint D m hm X₀ l hl Ω)

/-- The diagonal unit is the unit of the prescribed inverse/direct-image adjunction.
Source: blueprint descent paragraph 5
(blueprint: lem-zl-constant-extension-mixed-descent). -/
def constantExtensionWeilUnit (F : sfCommonStageWeilSheaf D l hl X₀ Ω) :
    F ⟶ (constantExtensionWeilPush D m hm X₀ l hl Ω).obj
      ((zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀)).obj F) :=
  (constantExtensionWeilAdjunction D m hm X₀ l hl Ω).unit.app F

/-- Geometric-point inverse image in the actual common-stage category, before H^0.
Source: blueprint geometric-stalk summation clause
(blueprint: lem-zl-constant-extension-mixed-descent). -/
def constantExtensionPointPull
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) :=
  @commonStageDerivedPullback l _ Ω _ _ _ _ _ x
    (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl X₀)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The component in one geometric sheet is restriction by the prescribed counit,
followed by the canonical identification of the pullback stalk with the original
stalk. The equality h fixes the lift over x, so no arbitrary stalk isomorphism enters.
Source: blueprint descent paragraph 5, sheetwise summation
(blueprint: lem-zl-constant-extension-mixed-descent). -/
def constantExtensionCounitComponent (F : sfCommonStageWeilSheaf D l hl X₀ Ω)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (z : Spec (.of D.k) ⟶
      (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left)
    (h : z ≫ zlFiberMap D (constantExtensionProjection D m hm X₀) = x) :
    (constantExtensionPointPull D X₀ l hl Ω x).obj
        (((constantExtensionWeilPush D m hm X₀ l hl Ω).obj
          ((zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀)).obj F)).obj.carrier)
      ⟶ (constantExtensionPointPull D X₀ l hl Ω x).obj F.obj.carrier :=
  let hS := frobeniusPointPrimeInvertible D l hl
  let hY := sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀)
  let hX := sfWeilPrimeInvertible D l hl X₀
  let f := zlFiberMap D (constantExtensionProjection D m hm X₀)
  let N := (zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀)).obj F
  let P := (constantExtensionWeilPush D m hm X₀ l hl Ω).obj N
  let c := @zlPullComp l _ Ω _ _ _ _ _ _ hS hY hX z f
  let ε := ((constantExtensionWeilAdjunction D m hm X₀ l hl Ω).counit.app N).hom.hom.f
  eqToHom (congrArg (fun t : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left ↦
      (@commonStageDerivedPullback l _ Ω _ _ _ _ _ t hS hX).obj P.obj.carrier) h.symm) ≫
    c.hom.app P.obj.carrier ≫
    (@commonStageDerivedPullback l _ Ω _ _ _ _ _ z hS hY).map ε ≫
    c.inv.app F.obj.carrier ≫
    eqToHom (congrArg (fun t : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left ↦
      (@commonStageDerivedPullback l _ Ω _ _ _ _ _ t hS hX).obj F.obj.carrier) h)

/-- Reality survives constant extension; pushing forward a bounded mixed filtration
and the normalized trace retract descend mixedness in the constructible Weil heart.
Source: main-20261015, thm-zl-real-mixed-by-curves.proof.md, paragraphs 1, 5 and 9
(blueprint: lem-zl-constant-extension-mixed-descent).

Proof:
1. The local operator after extension is conjugate to F_x^f, with
f=m/gcd(deg(x),m), by lem-zl-constant-extension-weil-heart-equivalence.
Triangularize over Ω using p-linear-triangular. Its diagonal powers give all
roots with multiplicity. Conjugation commutes with positive powers, so the
conjugation-stable spectrum remains stable, including repeated roots and zero stalks.
2. Transport the mixed filtration through the exact cyclic-sheet equivalence of
lem-zl-constant-extension-weil-heart-equivalence. It identifies all subobjects,
quotients, local operators and absolute residue sizes, hence their purity weights.
3. The finite projection has exact direct image on these hearts by
lem-zl-finite-adic-direct-image. Apply it to the transported filtration. Its
quotients are the images of the pure quotients and remain pure of the same
weights by lem-zl-finite-pushforward-punctual; this gives the stated bound on P.
4. The clopen decomposition of lem-pur-finite-clopen-derived-decomposition, at
every coefficient stage, identifies the geometric image of the pullback with m
copies of the original object. The prescribed counit restrictions are their
projections and the prescribed adjunction unit is their diagonal. Sum the
components to define the trace globally. This proves the displayed point-pullback
identity, hence the geometric-stalk summation identity after point fibres and H^0.
5. The induced Weil map permutes the sheets and applies theta in every component,
by lem-fix-weil-operations and semilinear naturality of finite direct image.
Summation commutes with both, so the trace is a morphism of Weil sheaves.
6. Sum after diagonal is m times the identity. Characteristic zero makes m
invertible even if l divides m. Divide the trace by m; its Weil morphism r is
specified without an additional scalar-action instance by m • r = Tr. It is a
retraction of the actual unit.
7. Apply lem-a1-mixed-direct-summand to this retract of P. This descends the same
upper weight bound, independently of reality. The empty scheme, m=1, length-zero
filtrations and nonsemisimple Frobenius are included. -/
theorem constantExtensionMixedDescent (iota : Ω ≃+* ℂ)
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω) :
    ∃ e : sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω ≌
        sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
          (constantExtensionModel D m hm X₀) Ω,
      ConstantExtensionSheetSpec D m hm X₀ l hl Ω e.functor ∧
      PreservesFiniteLimits e.functor ∧ PreservesFiniteColimits e.functor ∧
      PreservesFiniteLimits e.inverse ∧ PreservesFiniteColimits e.inverse ∧
      ConstantExtensionRestrictionSpec D m hm X₀ l hl Ω
        (constantExtensionRestriction D m hm X₀ l hl Ω e) ∧
      (∀ (N : sfCommonStageWeilSheaf D l hl
          (constantExtensionOriginalModel D m hm X₀) Ω) (w : ℝ),
        (SfIsPunctuallyPureOfWeight D l hl Ω (constantExtensionOriginalModel D m hm X₀)
            iota N w ↔
          SfIsPunctuallyPureOfWeight (constantExtensionDatum D m hm) l hl Ω
            (constantExtensionModel D m hm X₀) iota (e.functor.obj N) w) ∧
        (SfIsMixedOfWeightsAtMost D l hl Ω (constantExtensionOriginalModel D m hm X₀)
            iota N w ↔
          SfIsMixedOfWeightsAtMost (constantExtensionDatum D m hm) l hl Ω
            (constantExtensionModel D m hm X₀) iota (e.functor.obj N) w)) ∧
      (SfIsReal D l hl Ω X₀ iota F →
        SfIsReal (constantExtensionDatum D m hm) l hl Ω
          (constantExtensionModel D m hm X₀) iota
          ((constantExtensionRestriction D m hm X₀ l hl Ω e).obj F)) ∧
      (∀ w : ℝ,
        SfIsMixedOfWeightsAtMost (constantExtensionDatum D m hm) l hl Ω
          (constantExtensionModel D m hm X₀) iota
          ((constantExtensionRestriction D m hm X₀ l hl Ω e).obj F) w →
        SfIsMixedOfWeightsAtMost D l hl Ω X₀ iota
          ((constantExtensionWeilPush D m hm X₀ l hl Ω).obj
            ((zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀)).obj F)) w) ∧
      (∃ (Tr r : (constantExtensionWeilPush D m hm X₀ l hl Ω).obj
          ((zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀)).obj F) ⟶ F),
        constantExtensionWeilUnit D m hm X₀ l hl Ω F ≫ Tr = m • 𝟙 F ∧
        m • r = Tr ∧ constantExtensionWeilUnit D m hm X₀ l hl Ω F ≫ r = 𝟙 F ∧
        (∀ x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left,
          Nonempty (Fin m ≃ {z : Spec (.of D.k) ⟶
              (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left //
            z ≫ zlFiberMap D (constantExtensionProjection D m hm X₀) = x})) ∧
        (∀ (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
          (s : Fin m ≃ {z : Spec (.of D.k) ⟶
              (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left //
            z ≫ zlFiberMap D (constantExtensionProjection D m hm X₀) = x}),
          (constantExtensionPointPull D X₀ l hl Ω x).map Tr.hom.hom.f =
            ∑ i : Fin m,
              constantExtensionCounitComponent D m hm X₀ l hl Ω F x (s i).val
                (s i).property)) ∧
      (∀ w : ℝ,
        SfIsMixedOfWeightsAtMost (constantExtensionDatum D m hm) l hl Ω
          (constantExtensionModel D m hm X₀) iota
          ((constantExtensionRestriction D m hm X₀ l hl Ω e).obj F) w →
        SfIsMixedOfWeightsAtMost D l hl Ω X₀ iota F w) := by
  sorry

end WeilConjectures
