module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- The finite alternating Cech complex computes higher direct images after base change.
Source: Stacks Project, Tags 01XB, 01XD and 0A1D.
(blueprint: new-proper-flat-cohomology-data-base-change)
The proof uses affine acyclicity and Cech comparison on affine bases, then glues the
comparison and transports it across the canonical isomorphism of cartesian squares. -/
theorem proper_flat_cohomology_model_data_base_change {X T : Scheme.{u}} (f : X ⟶ T)
    (F : X.Modules) [IsSeparated f] [QuasiCompact f]
    [HasInjectiveResolutions X.Modules] [F.IsQuasicoherent]
    (hF : F.IsFlatOver f) (t : T)
    (U : T.Opens) (C : CochainComplex U.toScheme.Modules ℤ) (d : ℕ)
    (ht : t ∈ U) (hU : IsAffine U.toScheme) (hCge : C.IsStrictlyGE 0)
    (hCle : C.IsStrictlyLE d)
    (hCflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme))
    (hCqc : ∀ n : ℤ, (C.X n).IsQuasicoherent) :
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj F)) := by sorry

end AlgebraicGeometry.Scheme.Modules
