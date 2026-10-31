module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionMonoidalChange

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ] (X : Scheme.{u})
variable {Λ' : Type (u + 1)} [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a})


set_option profiler true in
noncomputable def testBraided :
    letI := derivedExtendScalarsMonoidal hρ ha X
    letI := DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    letI := DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
    (derivedExtendScalars hρ ha X).Braided :=
  haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
  (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorBraided
    (sheafExtendScalars_map_braiding_comp_δ X)

set_option profiler true in
lemma testBraidedδ₁ (M N : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    letI := DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    letI := DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
    letI := testBraided X hρ ha
    (derivedExtendScalars hρ ha X).map (β_ M N).hom ≫
        Functor.OplaxMonoidal.δ (derivedExtendScalars hρ ha X) N M =
      Functor.OplaxMonoidal.δ (derivedExtendScalars hρ ha X) M N ≫
        (β_ ((derivedExtendScalars hρ ha X).obj M)
          ((derivedExtendScalars hρ ha X).obj N)).hom := by
  letI := DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  letI := DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
  letI := testBraided X hρ ha
  rw [Functor.map_braiding, Category.assoc, Category.assoc, Functor.Monoidal.μ_δ,
    Category.comp_id]

set_option profiler true in
lemma testδeq (M N : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (letI := derivedExtendScalarsMonoidal hρ ha X
    Functor.OplaxMonoidal.δ (derivedExtendScalars hρ ha X) M N) =
    (letI := DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    letI := DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
    letI := testBraided X hρ ha
    Functor.OplaxMonoidal.δ (derivedExtendScalars hρ ha X) M N) :=
  rfl

end AlgebraicGeometry.Etale
