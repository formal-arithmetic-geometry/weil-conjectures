/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProjectionEvaluationFactors
public import WeilConjectures.SmoothPurity.SystemProjectionFormula.SystemProjectionFormulaCoherence
import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProjectionCompatibility

/-! # Finite projection under the constant coefficient realization

Source: fix-prop-projection-formula.proof.md, comparison of the same projection map.
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

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- Constant coefficient realization identifies the intrinsic finite projection with
its fixed coefficient presentation. Only finite coefficients occur in this statement;
there are no coefficient systems, integral inputs or integral reconstruction maps.

Source: fix-prop-projection-formula.proof.md, comparison of the same projection map;
Stacks 07A4, 07A6 and 0E48.
(blueprint: lem-sf-finite-intrinsic-projection-realization).

Proof: restriction along the constant scalar unit is inverse to module sheafification.
The ordinary balanced tensor comparison sends a pure tensor to the same two sections.
Apply this comparison in every bidegree of simultaneous flat K-flat representatives;
it commutes with the signed total differential and descends through the K-flat
localization, giving the natural tensor comparison e on all ambient finite inputs.
The section-normalized inverse-image comparison preserves the adjunction unit and
counit. Transpose the proper projection through this adjunction: both presentations
are tensor of the counit with identity after the tensor/pullback comparison.
Transpose the open factor: both presentations are tensor of the open unit with
identity followed by the inverse tensor/pullback comparison. Adjunction injectivity
identifies both factors. Their composition agrees with the normalized inverse-image
compositor, since its section maps agree. Paste these squares. The definition of
component conjugates the fixed proper/open word by sourceComparison and
targetComparison; the coefficient-equivalence units in these comparisons cancel by
naturality. Finally transport the two inputs by k and l, and use the specified
finiteSupport and finitePullback comparisons to obtain precisely the equation below.
No invertibility of the full projection is used. This includes exponent one, zero
inputs, empty schemes and identity or empty open immersions. -/
theorem finiteIntrinsicProjectionRealization
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    (S : SixFunctorFiniteOperations D C E (m + 1) (Nat.le_add_left 1 m)) :
    ∃ e : ∀ X : SixFunctorSpace D,
        finiteIntrinsicDerivedTensor C.l E X.obj.left m ≅
          evaluatedTensor (C := C) (E := E) m X,
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
            (CompactSupportFiniteProjection.component S f c K L) := by
  exact ⟨canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m,
    finiteIntrinsicProjectionCompatibility m S⟩

end WeilConjectures.IntegralProjectionReduction
