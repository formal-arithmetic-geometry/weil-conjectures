/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TwistedPullbackReductionData
import WeilConjectures.AlgebraicGeometry.SignedTwistFirstReduction
import WeilConjectures.AlgebraicGeometry.SignedLineTensorEquivalence
import WeilConjectures.Algebra.Homology.LineUnboundedDerivedTensor
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparisonSupplement

/-! # Normalized signed Tate-line reduction

Source: blueprint integral-adjunction-bijection, Purity paragraph.
(blueprint: lem-sp-twisted-pullback-tate-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] WeilConjectures.scalarReductionExistence
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped ChangeOfRings
namespace WeilConjectures.SpTwistedPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem line_cover (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1, u, u + 1, u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    [M.IsFiniteLocallyFreeOfRank 1] :
    ∃ (I : Type (u + 1)) (V : I → X.ProEt),
      (Scheme.ProEt.topology X).CoversTop V ∧
      ∀ i, Nonempty (M.over (V i) ≅ SheafOfModules.unit
        (((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over (V i))) := by
  classical
  obtain ⟨I, V, hV, e⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u + 1, u, u + 1}
      (M := M) (r := 1)).mp inferInstance
  exact ⟨I, V, hV, fun i ↦ ⟨(e i).some ≪≫
    SheafOfModules.freeUniqueIso.{u + 1, u, u + 1} _⟩⟩

private theorem extension_iso_tmul (X : Scheme.{u})
    (n : ℕ) (M : scalarReductionSource.{u, u} l E X) (U : X.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf.{u, u} l E X n).obj.obj U)
    (x : M.val.obj U) :
    ((eqToIso ((scalarReductionExistence.{u, u} l E X n).choose_spec.choose M) ≪≫
      SheafOfModules.ScalarHomOrdinary.extensionIso.{u + 1, u, u + 1}
        (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n) M).hom.val.app U)
        (sfReductionTensor l E X n M U a x) =
      SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n) M U a x := by
  let α := completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (integralCoefficientCommRingSheaf.{u, u} l E X n)).obj)
  have hn := adj.unit.naturality
    (SheafOfModules.ScalarHomOrdinary.extensionPresheafIso.{u + 1, u, u + 1} α M).hom
  have hh := congrArg (fun f ↦ f.app U
    (a ⊗ₜ[(completedIntegralCommRingSheafUnrestricted.{u, u} l E X).obj.obj U,
      (α.hom.app U).hom] x)) hn
  let h := (scalarReductionExistence.{u, u} l E X n).choose_spec.choose M
  change (SheafOfModules.ScalarHomOrdinary.extensionIso.{u + 1, u, u + 1}
    α M).hom.val.app U (((eqToHom h.symm ≫ eqToHom h).val.app U) _) = _
  simp only [eqToHom_trans, eqToHom_refl]
  exact hh.symm

/-- The ordinary and derived signed Tate reductions with their prescribed formulas.
Source: blueprint integral-adjunction-bijection, Purity paragraph; Stacks 03EK,
07A4; Bhatt--Scholze 3.4.12.
(blueprint: lem-sp-twisted-pullback-tate-reduction).

Proof: the completed Tate line is the scalar extension of the compatible root
system. Reduce its defining quotient map to obtain first, sending 1 tensor x
to 1 tensor x; this gives first_unit. Apply signedLineComparison to this first
comparison. The zero power is multiplication, positive powers are reassociated
balanced tensor products, and negative powers are the dual comparison carrying
phi tensor c to the functional x tensor t mapped to residue(phi(x))*c*t.
These formulas give signed and signed_normalized. Identify ordinary scalar
extension with the recorded tensor-extension presentation by its universal
property. Its generator formula gives ordinary_normalized. Every signed power
is locally free of rank one, hence flat; its degree-zero complex is K-flat.
Define level to be the composite in level_formula: the single-complex
localization comparison, reduction evaluation, the K-flat reduction counit,
and ordinary. Each factor is an isomorphism. This construction works for zero,
positive and negative powers and for the empty scheme. -/
theorem twistedPullbackTateReduction (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] :
    Nonempty (TateReduction l E X) := by
  classical
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let Q (n : ℕ) := integralCoefficientCommRingSheaf l E X n
  let p (n : ℕ) := completedIntegralCommRingProjectionUnrestricted l E X n
  let L := Scheme.purTwistIntegralModule X l E
  let N (n : ℕ) := Scheme.purTwistFiniteOne X l E n
  choose first hfirst using signedTwistFirstReduction l E X
  have hs (n : ℕ) := SheafOfModules.exists_signedLineComparison.{u + 1, u, u + 1}
    (p n) L (N n) (line_cover X R L) (line_cover X (Q n) (N n)) (first n)
  choose signed hsigned hnegative hlocal using hs
  let comparison (n : ℕ) (M : scalarReductionSource l E X) :
      (scalarReductionExtension l E X n).obj M ≅
        SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} (p n) M :=
    eqToIso ((scalarReductionExistence l E X n).choose_spec.choose M) ≪≫
      SheafOfModules.ScalarHomOrdinary.extensionIso.{u + 1, u, u + 1} (p n) M
  let ordinary (n : ℕ) (m : ℤ) :
      (scalarReductionExtension l E X n).obj (integralTwistLine l E X m) ≅
        finiteCoefficientTwist l E X n m :=
    comparison n (integralTwistLine l E X m) ≪≫ signed n m
  have kflat (m : ℤ) : CochainComplex.IsKFlatIndependentCoefficients
      (R := R) ((CochainComplex.singleFunctor _ 0).obj (integralTwistLine l E X m)) := by
    have : (integralTwistLine l E X m).IsFiniteLocallyFreeOfRank 1 :=
      (signedLineTensor_equivalence X R L m).1
    exact (SheafOfModules.LineUnbounded.line_unbounded_derived_tensor.{u, u, u + 2}
      X R (integralTwistLine l E X m)).2.2.choose
  refine ⟨{
    first := first
    first_unit := hfirst
    signed := signed
    signed_normalized := hsigned
    ordinary := ordinary
    ordinary_normalized := ?_
    kflat := kflat
    level := ?_
    level_formula := ?_ }⟩
  · intro n m U a x
    change (signed n m).hom.val.app U ((comparison n _).hom.val.app U _) = _
    exact congrArg (fun y ↦ (signed n m).hom.val.app U y)
      (extension_iso_tmul l E X n (integralTwistLine l E X m) U a x)
  · intro n m
    exact (coefficientSequenceDerivedEvaluation l E X n).mapIso
        ((coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction.mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (integralTwistLine l E X m))) ≪≫
      ((coefficientDerivedSystemEvaluationCalculus l E X).choose.reductionEvaluation n).app _ ≪≫
      coefficientFiniteReductionModel l E X _ (kflat m) n ≪≫
      DerivedCategory.Q.mapIso
        (((scalarReductionExtension l E X n).mapCochainComplexSingleFunctor 0).app _ ≪≫
          (CochainComplex.singleFunctor _ 0).mapIso (ordinary n m)) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (scalarReductionTarget l E X n) 0).app
        (finiteCoefficientTwist l E X n m)).symm
  · intro n m
    rfl

end WeilConjectures.SpTwistedPullback
