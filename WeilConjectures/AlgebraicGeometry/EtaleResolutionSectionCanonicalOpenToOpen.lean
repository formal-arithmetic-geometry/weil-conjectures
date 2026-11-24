/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalOpenToOpenCycle

/-!
# Open-to-open restriction of normalized resolution comparisons

## References

* Stacks Project, Tags 03F3 and 0A50
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- Open-to-open restriction identity for a normalized comparison.
(Stacks, Tags 03F3 and 0A50) -/
theorem resolutionSection_canonical_open_to_open {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G)
    (c : ResolutionSectionCanonicalComparison G I) :
    ∀ (A B : X.Opens) (h : A ≤ B) q x,
      c.openEquiv A q (HomologicalComplex.homologyMap (etaleSectionMap
        (MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι _) :
          Scheme.Etale.mk A.ι ⟶ Scheme.Etale.mk B.ι) I.cocomplex) q x) =
        openCohomologyRestriction h G q (c.openEquiv B q x) := by
  intro A B h q x
  let K := (((etaleSectionFunctor (Scheme.Etale.mk B.ι)).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex)
  let L := (((etaleSectionFunctor (Scheme.Etale.mk A.ι)).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex)
  let φ := etaleSectionMap
    (MorphismProperty.Over.homMk (P := @Etale) (Q := ⊤)
      (X := X) (A := Scheme.Etale.mk A.ι) (B := Scheme.Etale.mk B.ι)
      (X.homOfLE h) (X.homOfLE_ι h) trivial) I.cocomplex
  have hs : Function.Surjective (K.homologyπ q) :=
    (AddCommGrpCat.epi_iff_surjective (K.homologyπ q)).mp inferInstance
  obtain ⟨z, rfl⟩ := hs x
  have hmap : HomologicalComplex.homologyMap φ q (K.homologyπ q z) =
      L.homologyπ q ((HomologicalComplex.cyclesMap φ q) z) := by
    have hn := HomologicalComplex.homologyπ_naturality φ q
    exact congrArg (fun f => f z) hn
  rw [hmap]
  exact resolutionSection_canonical_open_to_open_cycle G I c A B h q z
end AlgebraicGeometry.Etale
