/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement

/-! Local complexes under an isomorphism of base schemes. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {X Y U : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (g : U ⟶ Y)

/-- The local coefficient comparison uses composition of inverse images followed by
inverse image of the completed coefficient comparison for the inverse isomorphism.
Source: blueprint order 2106, preservation of local models
(blueprint: def-wf-pbc-automorphism-local-coefficient). -/
def pbcIsoLocalCoefficient :
    (adicTowerInverseImage (g ≫ inv f)).obj (pbcAdicCompletion X d) ≅
      (adicTowerInverseImage g).obj (pbcAdicCompletion Y d) :=
  (proEtaleRingInverseImageComp g (inv f)).app (pbcAdicCompletion X d) ≪≫
    (adicTowerInverseImage g).mapIso (d.integralRingIso (inv f))

/-- Relabel the scalar action of each term through the specified local coefficient
isomorphism. Differentials and underlying sheaves are unchanged. No witness is chosen.
Source: blueprint order 2106, preservation of local models
(blueprint: def-wf-pbc-automorphism-local-complex). -/
def pbcIsoLocalComplex
    (C : CochainComplex (pbcModules U
      ((adicTowerInverseImage g).obj (pbcAdicCompletion Y d))) ℤ) :
    CochainComplex (pbcModules U
      ((adicTowerInverseImage (g ≫ inv f)).obj (pbcAdicCompletion X d))) ℤ :=
  ((pbcRestrict (pbcIsoLocalCoefficient f d g).hom).mapHomologicalComplex (.up ℤ)).obj C

/-- Relabeling the completed action preserves adic-lisse terms and finite-lisse
cohomology of each reduction.
Source: blueprint order 2106, preservation clause; Stacks Tags 09AI and 09BT.
Proof: restriction along the displayed coefficient isomorphism is an exact equivalence,
so it identifies homology after scalar extension. On each
trivializing cover of a term, compose its linear trivialization with the constant-ring
comparison for the inverse isomorphism; the presenting finite adic module is unchanged.
For a finite reduction use the analogous finite constant-ring comparison and the
projection square, which identifies reduction of the relabeled complex with relabeling
of the original reduction. Transport its finite constant trivializations through this
identification. These operations retain both the original degree window and the finite
module witnesses, with covers allowed to depend on the degree and the reduction level.
(blueprint: lem-wf-pbc-automorphism-local-complex-properties). -/
theorem pbcIsoLocalComplex_properties
    (M : AdicTower Y d) (a b : ℤ) (L : AdicTowerLocalModel d g M a b) :
    (∀ q : ℤ, @IsRelativelyAdicLisseModule _ _ (g ≫ inv f) A _ d.noetherian d.ideal
      ((pbcRestrict ((adicTowerInverseImage (g ≫ inv f)).map
        (pbcCompletedComparison X d).hom)).obj ((pbcIsoLocalComplex f d g L.complex).X q))) ∧
    (∀ (n : ℕ) (q : ℤ), IsRelativelyFiniteLisseModule (g ≫ inv f)
      (A ⧸ d.ideal ^ (n + 1))
      ((pbcRestrict ((adicTowerInverseImage (g ≫ inv f)).map
        (pbcLevelConstantComparison X d n).hom)).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            (adicTowerLocalReduction d (g ≫ inv f) (pbcIsoLocalComplex f d g L.complex) n)))) := by
  sorry

end AlgebraicGeometry.Scheme
