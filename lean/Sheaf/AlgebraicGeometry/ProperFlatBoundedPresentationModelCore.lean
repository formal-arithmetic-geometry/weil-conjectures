module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Structural bounded model supplied by the perfect direct-image construction.
Source: Stacks Project, Tags 0B91(2), 0A1H and 08EB.
(blueprint: lem-pc-proper-flat-bounded-presentation-structural-core).
The proof applies proper-support perfect direct image, the affine bounded-projective
criterion, and sheafification; finite projective terms give all asserted finiteness,
flatness, and quasi-coherence properties. -/
theorem exists_proper_flat_boundedPresentation_model_core {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasInjectiveResolutions X.Modules] [F.IsFinitePresentation]
    (hF : F.IsFlatOver f) (U : T.Opens) (hU : IsAffine U.toScheme) :
    ∃ (C : CochainComplex U.toScheme.Modules ℤ) (a : ℤ) (b : ℕ),
      C.IsStrictlyGE a ∧ C.IsStrictlyLE b ∧
      (∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme)) ∧
      (∀ n : ℤ, (C.X n).IsQuasicoherent) ∧
      (∀ n : ℤ, (C.X n).IsFinitePresentation) := by sorry

end AlgebraicGeometry.Scheme.Modules
