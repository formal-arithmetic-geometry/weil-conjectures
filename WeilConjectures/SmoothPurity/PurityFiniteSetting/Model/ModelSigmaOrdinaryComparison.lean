/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions

/-! # The standing tensor mate in ordinary dualizing coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The orientation-free standing sigma is the ordinary exceptional tensor mate
under the coefficient-unit, pullback, and monoidal site comparisons.
Source: latest blueprint composition-coherence proof Step 1, diagonal-section-pasting
Steps 2--5; the specified standing Hom equivalence and finite exceptional compositor.
(blueprint: lem-pur-model-sigma-ordinary-comparison).

Proof: write nu and Rnu for the comparison adjoints, E_h and L_h for the
ordinary exceptional right and left adjoints, and D_h(M) for the specified
compact-support comparison from L_h^pro(nu M) to nu(L_h M). For a bounded-below
etale representative e : nu M ≅ K, compute the standing Hom bijection on a as
  e.inv followed by nu applied to
  adjunction_h(adjunction_nu(D_h(M).inv followed by L_h^pro(e.hom) followed by a)).
To prove this formula, compare e with the representative chosen by the standing
bijection. Full faithfulness of nu lifts their transition; naturality of D_h
and of the two adjunctions removes that transition. Thus the formula is
independent of the chosen representative.

Apply this formula with M = E_h(Rnu L) and e the identity. D_h.inv D_h cancels;
the two Hom-equivalence inverse identities show that the standing counit is
D_h(M).hom followed by the comparison-adjunction transpose of the ordinary
counit. For composition, transpose alpha followed by this counit successively
through g and f. Compact-support site coherence and the bounded-below
restriction of the specified unbounded etale compositor identify its transpose
with the ordinary exceptional compositor. The intervening Rnu nu factors are
removed by the inverse comparison units at the bounded-below E_g(Rnu L).

Now transpose the two tensor mates. ProjectionComparisonEtaleOrigin identifies
the actual standing projection with the ordinary projection through D_h and
the monoidal and pullback comparisons. Use their invertibility on the
finite-Tor dualizing inputs, supplied by composition_tensor_mate. The counit
formula just proved identifies the remaining factors. Both transposes are the
inverse projection for f, its counit at the coefficient unit, and the counit
for g, with the same source symmetry. Naturality and the comparison-adjunction
triangles cancel the coefficient-unit changes in Cf, Cg and Cfg. Injectivity
of the successive Hom equivalences gives the stated equation. No orientation
or orientation composition assertion is used. The same unit and triangle
equations cover empty schemes and either relative dimension zero. -/
theorem model_sigma_ordinary_comparison (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ] :
    letI := P.noetherian aZ
    letI := P.noetherian (g ≫ aZ)
    letI := Dnc.compactifiable P f (g ≫ aZ)
    letI := Dnc.compactifiable P g aZ
    letI := Dnc.compactifiable P (f ≫ g) aZ
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    letI : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
    letI := ProEtale.upperStarPreservesFlat_moduleCat P.Coefficient
    let F := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
    let Cf := P.modelOrientationUnit f ≪≫ P.diagonalDualizingComparison f ≪≫
      F.mapIso (P.chartDualizingUnit f).symm
    let Cg := P.modelOrientationUnit g ≪≫ P.diagonalDualizingComparison g ≪≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.mapIso
          (P.chartDualizingUnit g).symm
    let Cfg := P.modelOrientationUnit (f ≫ g) ≪≫
      P.diagonalDualizingComparison (f ≫ g) ≪≫ F.mapIso (P.chartDualizingUnit (f ≫ g)).symm
    let S := P.compatibleTensorIso Cf
      ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso Cg ≪≫
        Dnc.pullComparison P f (Etale.dualizingComplex P.Coefficient g)) ≪≫
      (compatibleComparisonTensor P.Coefficient X (Etale.dualizingComplex P.Coefficient f)
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.obj
          (Etale.dualizingComplex P.Coefficient g))).symm
    ProEtale.CompositionTensorMate.sigma P.Coefficient f g ≫ Cfg.hom =
      S.hom ≫ F.map (DiagonalPasting.sigma P.Coefficient P d f g (f ≫ g ≫ aZ)).hom := by
  sorry

end WeilConjectures.PurityFiniteSetting
