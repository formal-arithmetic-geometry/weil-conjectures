/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompositionTensorMate
public import WeilConjectures.AlgebraicGeometry.PurityCompositionComparisons
public import WeilConjectures.AlgebraicGeometry.PurityDncComparisons

/-! # Finite tensor composition with its realization unit

Source: latest blueprint, smooth-purity composition proof, Step 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

section Geometry
variable (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [Z.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]

/-- The current cohomological tensor-composition identity with the intermediate
realization unit retained. It has no Tate orientation, purity map or shifted source.
Source: latest blueprint, thm-pur-composition-coherence.proof.md, Step 1's tensor formula,
and thm-pur-cohomological-smoothness, composition clause
(blueprint: lem-pur-finite-composition-tensor-realization).

Proof: take an etale representative of K using bounded constructible origin. Apply
smoothTensorCompositionEquation to its ordinary etale tensor maps. Transport through
the canonical monoidal comparison, pullback compositor and compact-support comparisons.
For a source identification i from comparison of N to Q, expand the standing Hom
bijection into precomposition by F(i), inverse compact-support comparison, comparison
adjunction, etale adjunction, comparison on maps, then precomposition by i inverse.
The comparison adjunction triangles identify this chain with the bounded-site chain
of finiteSiteCounitAndTranspose. finiteSiteThetaTransport computes theta in that chain;
finiteSiteDiagramTransposes computes the pasted compositor and counit. Hence the
transported exceptional compositor is standingExceptionalComposition. At the coefficient unit,
the comparison unit identifies the transported dualizing comparison with sigma, namely
symmetry followed by theta_f at omega_g and the inverse compositor. Naturality of
theta_f moves the realization unit from the target to its pullback tensor source;
retain it there rather than cancelling it. Faithfulness of etale comparison identifies
the two transposes. This proves the equation for the original K and its original finite
Tor witness, with no orientation or source-normalization assertion. -/
theorem finiteCompositionTensorRealization
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (K : Scheme.proEtaleDerivedCategory Z P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Z K) :
    letI := P.noetherian (Z ↘ Spec (.of P.field.k))
    letI := P.noetherian (Y ↘ Spec (.of P.field.k))
    letI := Dnc.compactifiable P f (Y ↘ Spec (.of P.field.k))
    letI := Dnc.compactifiable P g (Z ↘ Spec (.of P.field.k))
    letI := Dnc.compactifiable P (f ≫ g) (Z ↘ Spec (.of P.field.k))
    letI : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
    letI := ProEtale.upperStarPreservesFlat_moduleCat P.Coefficient
    letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
      (Y ↘ Spec (.of P.field.k))
    letI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace
      (Z ↘ Spec (.of P.field.k))
    let M := (Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).inverse.obj K
    let F := ProEtale.CompositionTensorMate.S P.Coefficient f
    let G := ProEtale.CompositionTensorMate.G P.Coefficient f
    let R := ProEtale.CompositionTensorMate.G P.Coefficient g
    let J := Scheme.sfIntrinsicDerivedEquivalence Y P.Ring
    (ProEtale.CompositionTensorMate.S P.Coefficient (f ≫ g)).obj M ◁
        ProEtale.CompositionTensorMate.sigma P.Coefficient f g ≫
      ProEtale.CompositionTensorMate.theta P.Coefficient (f ≫ g) M ≫
      ProEtale.standingExceptionalComposition P f g
        ⟨M, P.compositionInput_bounded K hK⟩ ≫ G.map (J.unitIso.hom.app (R.obj M)) =
    ProEtale.CompositionTensorMate.r P.Coefficient f g M ≫
      F.map (ProEtale.CompositionTensorMate.theta P.Coefficient g M) ▷
        ProEtale.CompositionTensorMate.omega P.Coefficient f ≫
      F.map (J.unitIso.hom.app (R.obj M)) ▷
        ProEtale.CompositionTensorMate.omega P.Coefficient f ≫
      ProEtale.CompositionTensorMate.theta P.Coefficient f
        (J.inverse.obj (J.functor.obj (R.obj M))) := by
  sorry

end Geometry
end WeilConjectures.PurityFiniteSetting
