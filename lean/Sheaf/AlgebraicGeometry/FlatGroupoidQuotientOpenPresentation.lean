/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.AlgebraicGeometry.SchemeGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StackPointTopology
public import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatLfpUniversallyOpen
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Open presentations of flat scheme-groupoid quotients

Source: Stacks Project, criteria.tex, Tags 06FI and 06FH; spaces-groupoids.tex,
Tag 04M9; stacks-properties.tex, Tag 0507; algebraic.tex, Tag 04WY
(blueprint: lem-sfb-flat-groupoid-quotient-open-presentation).

The existing quotient-presentation interface specifies the fppf stackification up to
based equivalence. No quotient object or canonical arrow is chosen from bare existence.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- The actual open subscheme with its inherited map to the base.
Source: Stacks Project, Tag 0507
(blueprint: lem-sfb-flat-groupoid-quotient-open-presentation). -/
def quotientOpenScheme {S : Scheme.{u}} (U : Over S) (V : U.left.Opens) : Over S :=
  Over.mk (V.ι ≫ U.hom)

/-- The actual inclusion of the open subscheme, over the original base.
Source: Stacks Project, Tag 0507
(blueprint: lem-sfb-flat-groupoid-quotient-open-presentation). -/
def quotientOpenInclusion {S : Scheme.{u}} (U : Over S) (V : U.left.Opens) :
    quotientOpenScheme U V ⟶ U :=
  Over.homMk V.ι rfl

/-- A flat locally finitely presented scheme groupoid has an algebraic quotient and
an fppf presentation. Finite relations give a finite finitely presented presentation.
Open substacks correspond, preserving and reflecting inclusion, to invariant opens;
each is the quotient of the restricted relation, with the two base-change squares.
Source: Stacks Project, Tags 06FI, 06FH, 04M9, 0507, 04WY and 0DUM
(blueprint: lem-sfb-flat-groupoid-quotient-open-presentation).

Proof, following the eight steps of the node:
1. Apply lem-sfb-flat-groupoid-algebraic-quotient over Spec k. It gives algebraicity,
representability, flatness, local finite presentation, the canonical relation equivalence,
and point lifting.
2. For T mapping to the quotient, the local-description theorem
lem-sfb-groupoid-stackification-local-description gives an fppf covering with lifts to U.
There the base change of the presentation is R times_U T_i, finite by
lem-trf-finite-radicial-basechange. Apply lem-sfb-space-finite-fppf-descent to descend
finiteness. An affine morphism is quasi-compact and quasi-separated by
lem-weil-pbc-affine-morphism-permanence; combine with local finite presentation.
3. An open substack pulls back to an open V. Its two inverse images on R agree because
objects identified by an arrow have the same membership in a strictly full substack.
Pullback preserves inclusion (lem-sfb-invariant-open-substack-descent).
4. Conversely choose a smooth atlas A. On E=U times_Q A pull back V to D and put B=q(D).
The chartwise calculus and lem-sfb-flat-lfp-space-universally-open make B open.
The common-field fibre-product calculation of lem-a1-space-point-open-calculus and
invariance show q inverse(B)=D. Use lem-a1-space-etale-open-image to identify opens.
5. A field representative of an arrow of A times_Q A, lifted to E after extension,
shows B is invariant. Apply lem-sfb-invariant-open-substack-descent on the smooth atlas.
6. Surjectivity of E to U and A shows the descended substack pulls back to V and is
unique. The same images preserve inclusions in the reverse direction.
7. The open substack is algebraic: descent is local, its diagonal is the restriction
of the ambient diagonal, and the restriction of A is a smooth atlas. Its fppf
presentation V has relation s inverse(V)=t inverse(V); all operations restrict.
Apply lem-sfb-fppf-groupoid-stack-presentations to identify its quotient.
8. The restricted projections are the two displayed base changes. Apply the chartwise
calculus and lem-trf-finite-radicial-basechange to their three finite-locally-free
properties. The empty open and the whole open are included throughout. -/
theorem flat_groupoid_quotient_open_presentation
    (k : Type u) [Field k] (U R : Over (Spec (.of k)))
    (s t : R ⟶ U) (e : U.left ⟶ R.left) (i : R.left ⟶ R.left)
    (c : pullback s.left t.left ⟶ R.left)
    (hG : IsGroupoidScheme s.left t.left e i c)
    [Flat s.left] [Flat t.left]
    [LocallyOfFinitePresentation s.left] [LocallyOfFinitePresentation t.left]
    (Q : BasedCategory.{v, w} (Over (Spec (.of k))))
    (p : BasedFunctor (discreteModuli (yoneda.obj U)) Q)
    (P : SchemeGroupoidQuotientPresentation s t e i c Q p) :
    IsAlgebraicModuliStack Q ∧
    IsRepresentableByAlgebraicSpaces p ∧ IsSurjectiveModuliMap p ∧
    ModuliSpaceTest @Flat p ∧ ModuliSpaceTest @LocallyOfFinitePresentation p ∧
    (moduliTwoFiberLift
      (discreteModuliMap (yoneda.map s)) (discreteModuliMap (yoneda.map t))
      (BasedNatIso.mkNatIso P.arrows.val P.arrows.property)).toFunctor.IsEquivalence ∧
    (IsFinite s.left → IsFinite t.left →
      ModuliSchemeTest @IsFinite p ∧
      ModuliSchemeTest
        (fun _ _ f ↦ LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f) p) ∧
    (∃ b : OpenModuliSubstack Q ≃ {V : U.left.Opens // s.left ⁻¹ᵁ V = t.left ⁻¹ᵁ V},
      (∀ W₁ W₂ : OpenModuliSubstack Q,
        W₁.IsContainedIn W₂ ↔ (b W₁).val ≤ (b W₂).val) ∧
      ∀ W : OpenModuliSubstack Q,
        (∃ a : BasedFunctor (discreteModuli (yoneda.obj (quotientOpenScheme U (b W).val)))
            (moduliTwoFiberProduct p (fullModuliInclusion Q W.property)),
          IsSchemeModuliBaseChange a (quotientOpenInclusion U (b W).val)) ∧
        ∃ (sV tV : quotientOpenScheme R (s.left ⁻¹ᵁ (b W).val) ⟶
            quotientOpenScheme U (b W).val)
          (eV : (quotientOpenScheme U (b W).val).left ⟶
            (quotientOpenScheme R (s.left ⁻¹ᵁ (b W).val)).left)
          (iV : (quotientOpenScheme R (s.left ⁻¹ᵁ (b W).val)).left ⟶
            (quotientOpenScheme R (s.left ⁻¹ᵁ (b W).val)).left)
          (cV : pullback sV.left tV.left ⟶
            (quotientOpenScheme R (s.left ⁻¹ᵁ (b W).val)).left)
          (hs : sV.left ≫ (b W).val.ι = (s.left ⁻¹ᵁ (b W).val).ι ≫ s.left)
          (ht : tV.left ≫ (b W).val.ι = (s.left ⁻¹ᵁ (b W).val).ι ≫ t.left)
          (q : BasedFunctor (discreteModuli (yoneda.obj (quotientOpenScheme U (b W).val)))
            W.category),
          eV ≫ (s.left ⁻¹ᵁ (b W).val).ι = (b W).val.ι ≫ e ∧
          iV ≫ (s.left ⁻¹ᵁ (b W).val).ι = (s.left ⁻¹ᵁ (b W).val).ι ≫ i ∧
          cV ≫ (s.left ⁻¹ᵁ (b W).val).ι =
            pullback.map sV.left tV.left s.left t.left
              (s.left ⁻¹ᵁ (b W).val).ι (s.left ⁻¹ᵁ (b W).val).ι (b W).val.ι hs ht ≫ c ∧
          Nonempty (SchemeGroupoidQuotientPresentation sV tV eV iV cV W.category q) ∧
          Nonempty (ModuliTwoIso (q.comp (fullModuliInclusion Q W.property))
            ((discreteModuliMap (yoneda.map (quotientOpenInclusion U (b W).val))).comp p)) ∧
          IsPullback (s.left ⁻¹ᵁ (b W).val).ι sV.left s.left (b W).val.ι ∧
          IsPullback (s.left ⁻¹ᵁ (b W).val).ι tV.left t.left (b W).val.ι ∧
          (s.left.IsFiniteLocallyFree → t.left.IsFiniteLocallyFree →
            sV.left.IsFiniteLocallyFree ∧ tV.left.IsFiniteLocallyFree)) ∧
    Function.Surjective (moduliSchemePointMap p) := by
  sorry

end CategoryTheory
