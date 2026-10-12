module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Limits.Shapes.Products

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry
/-- The second-page coproduct comparison is an epimorphism.
Source: Stacks Project, Tag 08DZ, second-page direct-sum reduction, using
Tag 07TB for filtered colimits and hence direct sums of module sheaves. Tag 015J identifies
these ordinary higher images as second-page terms. This is the surjectivity half only.
(blueprint: lem-pc-truncated-direct-image-second-page-coproduct-epi).

Proof: Put M_i = H^r(tau_GE(a) E_i) and M = H^r(tau_GE(a) S). Choose complex
representatives of the E_i and their termwise coproduct. Exact direct sums in
module sheaves compute its cohomology as the coproduct of the individual
cohomology sheaves. The universal property hc transports this computation to
S, naturally in the given coprojections. If r >= a, the natural cohomology
identifications for lower truncation give the same coproduct cofan on M_i and
M; if r < a all these sheaves are zero. Each M_i is quasi-coherent since E_i
has quasi-coherent cohomology; the coproduct M is quasi-coherent as well.
On an affine open V of Y, f^(-1)(V) is qcqs. Restriction of module sheaves to
this open preserves their coproduct. The qcqs cohomology direct-sum theorem
makes the map from the direct sum of H^p(f^(-1)(V), M_i) onto
H^p(f^(-1)(V), M) surjective. These maps commute with restriction and with
the coefficient morphisms. Ordinary R^p f_* is the sheafification of the
cohomology presheaf V |-> H^p(f^(-1)(V), -), and module sheafification
preserves coproducts. Since affine opens form a basis, the sectionwise
surjectivity just proved on that basis gives local surjectivity of the
sheafified comparison, hence an epimorphism of module sheaves. Finally,
compute each degree-zero module by an ordinary injective resolution, viewed
as a bounded-below K-injective complex. This gives the natural identification
of the ordinary R^p f_* with schemeModuleHigherDirectImage f p; naturality
identifies the sheafified comparison with the displayed Sigma.desc map.
For an empty family or r < a both sides are zero, and for p = 0 the same
presheaf computation is the ordinary direct image. No assertion that
arbitrary sheaf coproducts are sectionwise coproducts is used. -/
theorem truncated_directImage_secondPage_coproduct_epi
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (I : Type u) (E : I → schemeDerivedQCohCategory X)
    (S : schemeDerivedCategory X) (ι : ∀ i, (E i).obj ⟶ S)
    (hc : IsColimit (Cofan.mk S ι)) (a : ℤ) (p : ℕ) (r : ℤ) :
    Epi (Sigma.desc (fun i ↦ (schemeModuleHigherDirectImage f (p : ℤ)).map
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) r).map
          ((DerivedCategory.TStructure.t.truncGE a).map (ι i))))) := by
  sorry

end AlgebraicGeometry
