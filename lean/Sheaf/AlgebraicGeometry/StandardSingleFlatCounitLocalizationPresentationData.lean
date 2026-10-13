module

public import Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation

/-! # Local affine presentation data

Source: Stacks Project, Tags 0DJ9, 06YB and 0D5S.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Concrete localized presentation witnesses used by completion.
Source: Stacks Project, Tags 0DJ9, 06YB and 0D5S.
(blueprint: lem-pc-standard-single-flat-counit-localization-presentation-data).
Proof: choose an affine open S containing g(a), then an affine open V containing a
inside the open inverse image of S. Put W = p inverse-image S. Restrict M to W
and p to W -> S. Quasi-compactness and quasi-separatedness persist under this
open base change; quasi-coherence and relative flatness restrict, since sections
on affine subopens and their scalar actions are identified by open restriction.
Apply h_affine to W -> S and V -> S, and then to the restriction of M to the top
open of W. The top-open inclusion is an isomorphism. Transport its direct image,
ordinary pullback and canonical comparison along that isomorphism, using the
unit and counit identities. This gives the displayed presentation on S, including
its bounded flat K, both identifications and their equation. Nothing is extended
from S to the whole base B. The chosen point ensures the opens are nonempty;
there is no assertion to check when A is empty. -/
theorem standardSingleFlatCounit_localization_presentation_data
    (h_affine : ∀ {Y₀ B₀ A₀ : Scheme.{u}} (p₀ : Y₀ ⟶ B₀)
      [QuasiCompact p₀] [QuasiSeparated p₀] [IsAffine B₀] [IsAffine A₀]
      (g₀ : A₀ ⟶ B₀), StandardSingleFlatCounitOnOpen p₀ g₀ ⊤)
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p) (g : A ⟶ B) (a : A) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    ∃ (S : B.Opens) (V : A.Opens), g a ∈ S ∧ a ∈ V ∧
      IsAffine S.toScheme ∧ IsAffine V.toScheme ∧
      ∃ hVS : V ≤ g ⁻¹ᵁ S,
        StandardSingleFlatCounitPresentation (p ∣_ S)
          (M.restrict (p ⁻¹ᵁ S).ι) (g.resLE S V hVS) := by
  sorry

end AlgebraicGeometry
