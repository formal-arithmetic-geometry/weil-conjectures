/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.TensorExchangePresentation

/-! # Coherent exchange on normalized adjunction ingredients

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
fix-lem-tensor-adjunction.proof.md (blueprint: lem-sf-tensor-exchange-coherent-conclusions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.TensorAdjunctionExchange
open ConstructibleExceptionalCoefficients

/-- Five-arrow representability and coefficient/shift coherence on normalized inputs.
Source: Step 1, Step 2 and the three subsequent coefficient-stage paragraphs
(blueprint: lem-sf-tensor-exchange-coherent-conclusions).

Proof: form the five Hom bijections from the two closed adjunctions, the inverse
projection, the exceptional adjunction and the ordinary adjunction. Transpose
identity morphisms to construct the two representing arrows. Naturality in the
test object shows that their composites are identities. The inverse arrow is
literally Model.inverseComponent, since uncurrying identity gives evaluation.
Naturality of the same five arrows gives bifunctor naturality. At finite level,
one may equivalently test against shifted quasi-compact etale extensions by zero
and use geometric stalk conservativity, as in the current blueprint Step 2.
At the integral level all Hom targets are complete; coefficient transposition
identifies reduction of this map with the finite map, and derived Nakayama
proves invertibility. The rational case follows by exactness in both variables
and generation by integral models; the common-stage case follows by descent of
both inputs to one finite field and naturality under their realization isomorphisms.
For any Change, transpose the two inverse-exchange routes. Its projection equation,
evaluation transposes and the exceptional mate counit equation identify them;
this proves the displayed unrestricted coefficient-naturality equation, which
does not assert unrestricted shift compatibility. For the four actual coefficient
maps of System, use the coefficient-transposition theorem and field-descent
identities to obtain the specified comparisons and their invertibility clauses.
Transpose the signed source and unsigned target shift squares through the same
five bijections. Each constituent commutes with its published shift; the ringed
normalizations give RingShifts. These shift structures and these actual
coefficient comparisons give CoefficientComparisons. Arbitrary tensor comparisons
are never claimed to commute with shifts. All constructions retain the stipulated
admissibility at each stage and the same realization by the supplied datum. -/
theorem coherent_conclusions
    (D : FiniteFieldDatum.{u}) (A : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic A.l) E]
    [FiniteDimensional (Padic A.l) E] (n : ℕ) (hn : 1 ≤ n)
    (six : SixFunctorOperationDatum D A E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (S : System A.l A.Qbar D A.different (f := f.hom.left))
    (c : Compactification f.hom.left)
    (core : Presentation A.l A.Qbar D A.different f.hom.left S c)
    (_normalized : NormalizedDatum D A E n hn six f S c core) :
    ∃ conclusion : ∀ (s : Stage.{u} A.l)
        (_h : Admissible A.l A.Qbar D f.hom.left c s),
        Conclusion A.l A.Qbar (core.stage s),
      (∀ (L : FieldStage.{u} A.l) (m : ℕ+)
        (h : Admissible A.l A.Qbar D f.hom.left c (.finite L m)),
        Nonempty (RingShifts A.l A.Qbar (core.ring (.finite L m))
          (conclusion (.finite L m) h))) ∧
      (∀ {s t : Stage.{u} A.l}
        {TX : C.{u} A.l A.Qbar X.obj.left s ⥤ C.{u} A.l A.Qbar X.obj.left t}
        {TY : C.{u} A.l A.Qbar Y.obj.left s ⥤ C.{u} A.l A.Qbar Y.obj.left t}
        (a : Change A.l A.Qbar (core.stage s) (core.stage t) TX TY),
        Compatible A.l A.Qbar a) ∧
      Nonempty (CoefficientComparisons A.l A.Qbar D A.different f.hom.left S c
        core.stage conclusion) := by
  sorry

end WeilConjectures.TensorAdjunctionExchange
