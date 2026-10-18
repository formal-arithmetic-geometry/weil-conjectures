/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.PointDerivedHomEvaluation
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.CategoryTheory.DerivedCategory.PerfectCohomologyAssembly
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.FiniteRingConstructibleSheafOrigin
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.Paper.PointSectionsDerivedReduction
import Sheaf.Paper.PointSectionsFiniteness
import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.RingTheory.FiniteFreeResolution
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant

/-!
# Point sections and constant-sheaf reconstruction

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
`sk-thm-sf-package/lem-pod-point-dualizing-complex.proof.md`, second sentence
(blueprint: lem-pod-point-sections-reconstruction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.PointDerivedHom
namespace WeilConjectures

/-- Reconstruction for the specified ordinary tensor extension and its explicit adjunction.
The Boolean selects the finite or completed integral coefficient sheaf. The local
instance only supplies the additivity implied by that adjunction; it chooses no data.
Source: blueprint point-dualizing proof, second sentence
(blueprint: lem-pod-point-sections-reconstruction). -/
def pointSectionsReconstructionResult
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (hn : 1 ≤ n) (integral : Bool) :
    ∀ (L : ModuleCat.{u + 1} (coefficientRing.{u, u} l E n integral) ⥤
      PointDerivedHom.Modules.{u, u} k (coefficientSheaf.{u, u} k l E n integral))
    (_adj : L ⊣ sections.{u, u} k (coefficientSheaf.{u, u} k l E n integral)
      (coefficientMap.{u, u} k l E n integral))
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits (sections.{u, u} k (coefficientSheaf.{u, u} k l E n integral)
      (coefficientMap.{u, u} k l E n integral))]
    [PreservesFiniteColimits (sections.{u, u} k (coefficientSheaf.{u, u} k l E n integral)
      (coefficientMap.{u, u} k l E n integral))], Prop :=
  match integral with
  | false => fun L adj hLl hLc hRl hRc ↦
    letI := hLl
    letI := hLc
    letI := hRl
    letI := hRc
    letI := adj.left_adjoint_additive
    (∀ c : (DerivedCategory.pointFiniteCohomology
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))).FullSubcategory,
      IsIso (adj.mapDerivedCategoryAdjunction.unit.app c.obj) ∧
        intrinsicFiniteTorsionConstructible l E n hn (Spec (.of k))
          (L.mapDerivedCategory.obj c.obj)) ∧
    (∀ C : (Spec (.of k)).proEtaleDerivedCategory
        (Padic.coefficientExtensionRing l E n),
      intrinsicFiniteTorsionConstructible l E n hn (Spec (.of k)) C →
        IsIso (adj.mapDerivedCategoryAdjunction.counit.app C))
  | true => fun L adj hLl hLc hRl hRc ↦
    letI := hLl
    letI := hLc
    letI := hRl
    letI := hRc
    letI := adj.left_adjoint_additive
    (∀ c : DerivedCategory (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))),
      (∃ s : Finset ℤ, (∀ i : ℤ, i ∉ s →
        IsZero ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (ULift.{u + 1, u}
            (Padic.coefficientExtensionIntegers l E))) i).obj c)) ∧
        (∀ i : ℤ, Module.Finite (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
          ((DerivedCategory.homologyFunctor
            (ModuleCat.{u + 1} (ULift.{u + 1, u}
              (Padic.coefficientExtensionIntegers l E))) i).obj c))) →
        IsIso (adj.mapDerivedCategoryAdjunction.unit.app c) ∧
          sfIntegralConstructible l E (Spec (.of k)) (L.mapDerivedCategory.obj c) ∧
          ∃ (P : CochainComplex (ModuleCat.{u + 1}
              (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ) (a b : ℤ),
            P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
            (∀ i : ℤ, Module.Projective
              (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) (P.X i) ∧
              Module.Finite (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
                (P.X i)) ∧
            Nonempty (c ≅ DerivedCategory.Q.obj P) ∧
            sfIntegralConstructible l E (Spec (.of k))
              (L.mapDerivedCategory.obj (DerivedCategory.Q.obj P))) ∧
    (∀ C : sfIntegralConstructibleCategory l E (Spec (.of k)),
      IsIso (adj.mapDerivedCategoryAdjunction.counit.app C.obj))

/--
The extension-of-scalars/sections reconstruction at the algebraically closed point.
The extension functor is fixed on objects and morphisms to
`B ⊗_underline R underline(-)`. The assumed explicit abelian adjunction
records both pure-tensor formulas. Its canonical termwise derived adjunction,
not an independently chosen derived adjunction, supplies the unit and counit.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
`sk-thm-sf-package/lem-pod-point-dualizing-complex.proof.md`, second sentence
(blueprint: lem-pod-point-sections-reconstruction).

Proof (the eight steps recorded by the node). (1) On modules, use the pure
tensor formulas from `def-pur-sheaf-tensor-product` and
`def-weil-proetale-locally-constant-sheaf`; balancing and sheafification make
the formulas well-defined, and the triangle identities descend through the
exact derived factorizations of `lem-weil-pbc-exact-functor-derived-factorization`.
(2) At finite level, `lem-weil-l-adic-extension-integers-dvr` gives finite
coefficient rings. Finite presentations and
`lem-weil-proetale-constant-sheaf-stalk` prove the unit and finite torsion
constructibility for each finite module, hence for bounded finite cohomology.
(3) The finite constructible comparison nodes
`lem-weil-pbc-finite-ring-constructible-sheaf-origin`,
`lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant`, and
`prop-weil-pbc-site-comparison-finite-level` identify each target with its
constant sections, so evaluation is the finite counit.
(4) Exactness and `lem-sp-exact-functor-preserves-homology` identify the
cohomology of termwise extension and sections; the cohomology criterion
`lem-weil-pbc-unbounded-derived-iso-cohomology` upgrades the module maps to
the finite derived unit and the constructible finite counit.
(5) For integral coefficients, the DVR/PID and finite-free-resolution lemmas
`lem-weil-l-adic-extension-integers-dvr`, `lem-weil-pbc-pid-noetherian-normal`,
`lem-weil-pbc-finite-free-resolution-noetherian`, and
`lem-sc-dvr-fg-torsionfree-free`, followed by
`lem-sf-perfect-cohomology-assembly`, supply the bounded finite-projective
representative required for every bounded finitely generated complex.
(6) Apply `lem-weil-pbc-integral-stratified-perfect-characterization` on the
single point, using `lem-weil-pbc-independent-bounded-flat-kflat` and the
integral constructibility definition, to show that extension of this model is
constructible and that its unit is invertible on projective summands.
(7) For a constructible integral target, take the counit cone. Exact sections
(`lem-weil-point-proetale-sections-exact`), the comparison
`lem-pod-point-sections-derived-reduction`, finite reconstruction, and the
derived-completeness triangle force the cone to vanish, giving the counit on
`sfIntegralConstructibleCategory`.
(8) The chain-level pure-generator formulas are natural; localization and
inverses of quasi-isomorphisms preserve these equations, so both derived
units and counits are natural in their arguments.
-/
theorem pointSectionsReconstruction
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (hn : 1 ≤ n) (integral : Bool)
    (L : ModuleCat.{u + 1} (coefficientRing.{u, u} l E n integral) ⥤
      PointDerivedHom.Modules.{u, u} D.k (coefficientSheaf.{u, u} D.k l E n integral))
    (hobj : ∀ M : ModuleCat.{u + 1} (coefficientRing.{u, u} l E n integral),
      L.obj M = extensionObject.{u, u} D.k (coefficientSheaf.{u, u} D.k l E n integral)
        (coefficientMap.{u, u} D.k l E n integral) M)
    (hmap : ∀ (M N : ModuleCat.{u + 1} (coefficientRing.{u, u} l E n integral))
      (f : M ⟶ N), L.map f = eqToHom (hobj M) ≫
        extensionMorphism.{u, u} D.k (coefficientSheaf.{u, u} D.k l E n integral)
          (coefficientMap.{u, u} D.k l E n integral) f ≫ eqToHom (hobj N).symm)
    (adj : L ⊣ sections.{u, u} D.k (coefficientSheaf.{u, u} D.k l E n integral)
      (coefficientMap.{u, u} D.k l E n integral))
    (hexplicit : ExplicitAdjunction.{u, u} D.k
      (coefficientSheaf.{u, u} D.k l E n integral)
      (coefficientMap.{u, u} D.k l E n integral) L hobj adj)
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits (sections.{u, u} D.k (coefficientSheaf.{u, u} D.k l E n integral)
      (coefficientMap.{u, u} D.k l E n integral))]
    [PreservesFiniteColimits (sections.{u, u} D.k (coefficientSheaf.{u, u} D.k l E n integral)
      (coefficientMap.{u, u} D.k l E n integral))]
    (hsections : Function.Bijective (scalar.{u, u} D.k
      (coefficientSheaf.{u, u} D.k l E n integral)
      (coefficientMap.{u, u} D.k l E n integral) (op (finalObject D.k)))) :
    pointSectionsReconstructionResult D.k l E n hn integral L adj := by
  sorry

end WeilConjectures
