/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralProjectionEvaluationFactors
public import Sheaf.Paper.SystemProjectionFormulaCoherence

/-! # Compatibility of a finite intrinsic projection realization

Source: fix-prop-projection-formula.proof.md, comparison of the same projection map.
(blueprint: new-sf-finite-intrinsic-projection-compatibility).

Proof: transpose the proper and open factors through their actual adjunctions,
using the normalized inverse-image comparison. Naturality of the tensor, support,
and finite pullback comparisons then transports the two ambient finite inputs. The
resulting pasted square is exactly the fixed-presentation component. This statement
assumes the tensor comparison family and proves only its projection compatibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus CompactSupportFiniteProjection.tensor sfIntrinsicDerivedEquivalence

/-- The projection compatibility equation for a supplied finite tensor realization.

STATEMENT-DISPUTED: the family `e` has no naturality or compatibility hypothesis across
`SixFunctorSpace` morphisms, so twisting `e Y` by an automorphism changes the right side
without changing the left-side comparison at `X`. More explicitly, the hypotheses permit
independent replacement of one component `(e Y)` by its composite with any automorphism;
none of the supplied data relates that replacement to `(e X)`, while the displayed equation
contains both components. A valid compatibility theorem therefore needs a naturality or
normalization hypothesis on `e` and cannot be proved from the current statement.

(blueprint: new-sf-finite-intrinsic-projection-compatibility).

Proof: transpose the proper and open projection factors through their actual adjunctions,
using the normalized inverse-image comparison. Naturality of the tensor, support, and finite
pullback comparisons transports the two ambient finite inputs. The pasted square is exactly
the fixed-presentation component. -/
theorem finiteIntrinsicProjectionCompatibility
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    (S : SixFunctorFiniteOperations D C E (m + 1) (Nat.le_add_left 1 m))
    (e : ∀ X : SixFunctorSpace D,
        finiteIntrinsicDerivedTensor C.l E X.obj.left m ≅
          evaluatedTensor (C := C) (E := E) m X) :
      ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
        (c : Compactification f.hom.left)
        (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
        (L : finiteTorConstructibleCategory C.l E (m + 1)
          (Nat.le_add_left 1 m) Y.obj.left)
        (U : normalizedDVRDerived C.l E X.obj.left m)
        (V : normalizedDVRDerived C.l E Y.obj.left m)
        (k : U ≅ K.obj) (l : V ≅ L.obj),
        SystemProjectionFormula.finiteProjection C.l E D C.different c
            X.obj.hom Y.obj.hom m U V ≫
          (sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c).map
            ((e X).hom.app (U, (finiteDerivedPullback C.l E m f.hom.left).obj V) ≫
              (evaluatedTensor (C := C) (E := E) m X).map
                (Prod.mkHom k.hom
                  ((finiteDerivedPullback C.l E m f.hom.left).map l.hom ≫
                    (S.finitePullback f).inv.app ⟨L.obj, L.property.1⟩))) ≫
          (S.finiteSupport f c).inv.app
            (((CompactSupportFiniteProjection.partialTensor S X).obj K).obj
              ((CompactSupportFiniteProjection.torPull S f).obj L)) =
        (e Y).hom.app
            ((sixFunctorFiniteSupport D C E (m + 1)
              (Nat.le_add_left 1 m) f c).obj U, V) ≫
          (evaluatedTensor (C := C) (E := E) m Y).map
            (Prod.mkHom
              ((sixFunctorFiniteSupport D C E (m + 1)
                (Nat.le_add_left 1 m) f c).map k.hom ≫
                (S.finiteSupport f c).inv.app K) l.hom) ≫
          (finiteInclusion (C := C) (E := E) m Y).map
            (CompactSupportFiniteProjection.component S f c K L) := by sorry

end WeilConjectures.IntegralProjectionReduction
