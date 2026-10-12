module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import Mathlib.Algebra.Homology.SingleHomology

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A nonzero module placed in degree -1 violates negative homology vanishing,
even after pullback along the identity. This diagnostic uses no project sorries. -/
private theorem single_negative_homology_obstruction (S : Scheme.{u}) (M : S.Modules)
    (hM : ¬ IsZero M) :
    ¬ IsZero ((((Modules.pullback (𝟙 S)).mapHomologicalComplex _).obj
      ((HomologicalComplex.single S.Modules (ComplexShape.up ℤ) (-1)).obj M)).homology
        (-1)) := by
  intro h
  let C := (HomologicalComplex.single S.Modules (ComplexShape.up ℤ) (-1)).obj M
  let e := (NatIso.mapHomologicalComplex (Modules.pullbackId S) (ComplexShape.up ℤ)).app C
    ≪≫ (Functor.mapHomologicalComplexIdIso S.Modules (ComplexShape.up ℤ)).app C
  let eH := (HomologicalComplex.homologyFunctor S.Modules (ComplexShape.up ℤ) (-1)).mapIso e
    ≪≫ HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) (-1) M
  exact hM (h.of_iso eH.symm)

-- STATEMENT-DISPUTED: C is arbitrary: no hypothesis identifies it with Rf_* F.
-- A nonzero finite free module in degree -1 meets the displayed boundedness,
-- flatness and finiteness hypotheses but contradicts the negative-homology clause.
/-- Base-change and negative-homology bridge for the bounded model of the
proper flat direct image.
Source: Stacks Project, Tags 0B91(2), 0A1H and 08EB.
(blueprint: lem-pc-proper-flat-bounded-presentation-comparison-core).
The proof uses the derived base-change theorem for bounded flat complexes,
the derived-model identification produced by the perfect direct-image
construction, and the standard comparison of derived direct-image homology
with higher direct images. -/
theorem proper_flat_boundedPresentation_model_baseChange
    {X T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasInjectiveResolutions X.Modules] [F.IsFinitePresentation]
    (hF : F.IsFlatOver f) (U : T.Opens) (hU : IsAffine U.toScheme)
    (C : CochainComplex U.toScheme.Modules ℤ) (a : ℤ) (b : ℕ)
    (hge : C.IsStrictlyGE a) (hle : C.IsStrictlyLE b)
    (hflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme))
    (hqc : ∀ n : ℤ, (C.X n).IsQuasicoherent)
    (hfp : ∀ n : ℤ, (C.X n).IsFinitePresentation) :
      (∀ {S : Scheme.{u}} (g : S ⟶ U.toScheme) (i : ℤ), i < 0 →
        IsZero ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology i)) ∧
      (∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj F))) := by sorry

end AlgebraicGeometry.Scheme.Modules
