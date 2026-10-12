module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

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
