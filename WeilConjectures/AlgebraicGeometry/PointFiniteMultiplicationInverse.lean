/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointFrobeniusNormalizationDefinitions
import WeilConjectures.AlgebraicGeometry.PointAutomorphismDerivedTransportInverse

/-! Canonical point-comparison component of Frobenius normalization. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointFrobeniusNormalization
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

include hl in
/-- The finite tensor-unit comparison has its normalized multiplication inverse.
Source: Stacks Project, sites-modules.tex, Tags 03CZ and 03EK; point normalization
step 1 (blueprint: lem-pur-point-finite-multiplication-inverse).

Proof: identify module inverse image for the isomorphism with sectionwise reindexing.
The ring map c is invertible. Scalar extension along c is inverse to scalar restriction
along c inverse, by exists_scalarExtensionRingIso. Its multiplication map sends the
sheafification image of x tensor b to c inverse(b) times x. The inverse inserts one.
The pullback adjunction identification preserves its unit, so this insertion is exactly
inverseImageFiniteComparisonComplex, by its unique sectionwise specification. Both
inverse identities hold before sheafification by balancing and c inverse(c(b)) = b;
the sheafification universal property preserves them. Naturality in the module makes
these maps commute with every differential, giving the asserted complex isomorphism.
The proof works for the zero module and positive exponent one, without a freeness or
constructibility hypothesis. In Lean specialize point_automorphism_finite_transport_inverse;
its two inverse equations build e, and the unique comparison formula identifies its
sectionwise input with the specified generator. -/
theorem pointFiniteMultiplicationInverse
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
  ∃ e : ((integralOperationsLevelPullback l E g n).mapHomologicalComplex
      (.up ℤ)).obj K ≅
      ((inverseImageFiniteModules l E g n).mapHomologicalComplex (.up
          ℤ)).obj K,
    (∀ (i : ℤ) (U : (Spec (.of D.k)).ProEt)
      (x : (K.X i).val.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (b : (integralCoefficientSheaf l E (Spec (.of D.k)) n).obj.obj (op U)),
      (e.hom.f i).val.app (op U)
        (b • ((inverseImageFiniteComparisonComplex l E g n
          K).f i).val.app (op U) x) =
        (inv (inverseImageFiniteCoefficientMap l E g n)).hom.app
          (op U) b • x) ∧
    (∀ (i : ℤ) (U : (Spec (.of D.k)).ProEt)
      (x : (K.X i).val.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (b : (integralCoefficientSheaf l E (Spec (.of D.k)) n).obj.obj (op U)),
      (e.hom.f i).val.app (op U)
        (b • (((integralOperationsLevelPullback l E g n).obj
          (K.X i)).val.map (proEtaleIsoCommaArrow g U).op
            (integralOperationsPullbackGenerator l E g n (K.X i)
              ((proEtaleIsoPostcompose g).obj U) x))) =
        (inv (inverseImageFiniteCoefficientMap l E g n)).hom.app
          (op U) b • x) ∧
    (inverseImageFiniteComparisonComplex l E g n
      K = e.inv)  := by
  obtain ⟨δ, hδ, hmul, _⟩ :=
    point_automorphism_finite_transport_inverse l E D hl g n
  let e : ((integralOperationsLevelPullback l E g n).mapHomologicalComplex
       (.up ℤ)).obj K ≅
      ((inverseImageFiniteModules l E g n).mapHomologicalComplex
         (.up ℤ)).obj K :=
    ⟨δ K, inverseImageFiniteComparisonComplex l E g n K,
      (hδ K).2, (hδ K).1⟩
  refine ⟨e, ?_, hmul K, rfl⟩
  intro i U x b
  change ((δ K).f i).val.app (op U) (b • _) = _
  have hspec := inverseImageFiniteComparison_existsUnique l E g n K
  have hx := hspec.exists.choose_spec i U x
  exact (congrArg (fun z ↦ ((δ K).f i).val.app (op U) (b • z)) hx).trans
    (hmul K i U x b)

end WeilConjectures.PointFrobeniusNormalization
