module

public import Sheaf.Paper.ProEtaleVectorIntegration

/-! # Pro-etale vector integration with local normalization
Source: main-20261015, vector-bundle integration; Stacks 09AF and 099R
(blueprint: def-pur-proetale-vector-integration-arrows).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)
variable (S : Scheme.{u}) [IsNoetherian S]
variable (r : ℕ)
  (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
variable (d : ℕ) (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]

/-- The ordinary coefficient-first twisted inverse image used in integration transposes.
Source: vector-bundle purity (blueprint: def-pur-proetale-vector-integration-arrows). -/
abbrev vectorTwisted (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) S) :=
  Etale.vectorBundlePurityTwistedPullback (Scheme.finiteTateCoefficient l E n)
    (l ^ (r + 1)) hA S d F K

/-- The canonical source comparison for the tensor projection map.
Source: exact monoidal site comparison and geometric inverse-image comparison
(blueprint: def-pur-proetale-vector-integration-arrows). -/
@[irreducible]
def vectorTwistedComparison
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) S) :=
  tensorPullbackComparison (Scheme.finiteTateCoefficient l E n)
    (VectorBundleZeroSection.π S d F) K
    (Etale.vectorIntegrationCoefficient _ (l ^ (r + 1)) hA S d F)

/-- Canonical pro-etale coefficient-first compact-support projection on the bundle.
Source: Stacks 0944 and 0GL1 (blueprint: def-pur-proetale-vector-integration-arrows). -/
@[irreducible]
def vectorProjection
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) S) :=
  moduleProjection (Scheme.finiteTateCoefficient l E n)
    (Etale.vectorBundlePurityCompactification S d F)
    (Etale.vectorIntegrationCoefficient _ (l ^ (r + 1)) hA S d F) K

/-- The same ordinary Brown right adjoint used by the recorded bundle adjunction.
Source: ordinary exceptional inverse image
(blueprint: def-pur-proetale-vector-integration-arrows). -/
abbrev vectorExceptional :=
  letI := (Etale.vectorIntegration_geometry S d F).1
  letI := (Etale.vectorIntegration_geometry S d F).2.1
  Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
    (VectorBundleZeroSection.π S d F)

/-- Hom type of ordinary vector integration with coefficients K.
Source: vector-bundle purity (blueprint: def-pur-proetale-vector-integration-arrows). -/
@[implicit_reducible]
def OrdinaryVectorIntegrationHom
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) S) :=
  (Etale.vectorBundlePurityLower (Scheme.finiteTateCoefficient l E n) S d F).obj
    (vectorTwisted l E n S r hA d F K) ⟶ K

/-- Hom type of the pro-etale integration, in canonical comparison source coordinates.
Source: vector-bundle purity (blueprint: def-pur-proetale-vector-integration-arrows). -/
@[implicit_reducible]
def ProVectorIntegrationHom
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) S) :=
  (rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
    (Etale.vectorBundlePurityCompactification S d F)).obj
      ((comparison (Scheme.finiteTateCoefficient l E n) _).obj
        (vectorTwisted l E n S r hA d F K)) ⟶
    (comparison (Scheme.finiteTateCoefficient l E n) S).obj K

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
