/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q131
-/
module

public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.AlgebraicGeometry.ProEtaleModulePullbackComposition
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.Paper.PointSectionsFiniteness

/-!
# Exact point models and the normalized derived compositor

Source: Stacks Project, Tags 0D6D, 015F and 04VG; the point-fibre clause of
blueprint `def-weil-finite-coefficient-point`
(blueprint: lem-trf-point-exact-derived-model).

The abbreviations specialize existing module pullbacks, exact derived factorizations,
and point sections. The ordinary compositor is determined by fibre-product pasting
and adjunction conjugation. The derived compositor is the prescribed K-flat-normalized
comparison, specialized to the actual constant-section coefficient maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PointExactDerivedModel

/-- Spec of geometric field Frobenius on the fixed closure.
Source: Deligne, Weil II (1.1.7); Stacks Tag 0D6D
(blueprint: lem-trf-point-exact-derived-model). -/
def frobenius (D : FiniteFieldDatum.{u}) : Spec (.of D.k) ⟶ Spec (.of D.k) :=
  letI := Fintype.ofFinite D.k₀
  Spec.map (CommRingCat.ofHom
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).toRingHom)

/-- Iterated geometric Frobenius, with the positive recursion exposing composition.
Source: Stacks Tag 0D6D, applied to powers of geometric Frobenius
(blueprint: lem-trf-point-exact-derived-model). -/
def power (D : FiniteFieldDatum.{u}) : ℕ → (Spec (.of D.k) ⟶ Spec (.of D.k))
  | 0 => 𝟙 _
  | 1 => frobenius D
  | r + 2 => frobenius D ≫ power D (r + 1)

/-- The actual constant-ring module category on the original small pro-etale point.
Source: Stacks, Modules on Sites, Tag 03CW
(blueprint: lem-trf-point-exact-derived-model). -/
abbrev modules (D : FiniteFieldDatum.{u}) (A : Type u) [CommRing A] :=
  proEtaleRingModules (Spec (.of D.k)) (proEtaleConstantRing (Spec (.of D.k)) A)

/-- Ordinary tensor module pullback with the canonical constant-section coefficient map.
Source: Stacks Tags 03D2 and 0D6D
(blueprint: lem-trf-point-exact-derived-model). -/
abbrev pullback (D : FiniteFieldDatum.{u}) (A : Type u) [CommRing A] (r : ℕ) :=
  proEtaleConstantRingPullback A (power D r)

/-- The ambient derived pullback in the recorded canonical ring-sheaf presentation.
Source: Stacks Tag 0D6D
(blueprint: lem-trf-point-exact-derived-model). -/
abbrev derivedPullback (D : FiniteFieldDatum.{u}) (A : Type u) [CommRing A] (r : ℕ) :=
  proEtaleConstantRingDerivedPullback A (power D r)

/-- Canonical exact-functor comparison on every complex, without flatness conditions.
Source: Stacks Tag 015F and Mathlib `Functor.mapDerivedCategoryFactors`
(blueprint: lem-trf-point-exact-derived-model). -/
abbrev pullbackFactors (D : FiniteFieldDatum.{u}) (A : Type u) [CommRing A] (r : ℕ) :=
  (pullback D A r).mapDerivedCategoryFactors

/-- Derived final-object sections using the recorded constant scalar action.
Source: blueprint `def-weil-finite-coefficient-point`, clause 1; Stacks Tag 015F
(blueprint: lem-trf-point-exact-derived-model). -/
abbrev evaluation (D : FiniteFieldDatum.{u}) (A : Type u) [CommRing A] :=
  (pointFiniteSections D.k A).mapDerivedCategory

/-- The canonical comparison with termwise final-object sections on every representative.
Source: Stacks Tag 015F and Mathlib `Functor.mapDerivedCategoryFactors`
(blueprint: lem-trf-point-exact-derived-model). -/
abbrev evaluationFactors (D : FiniteFieldDatum.{u}) (A : Type u) [CommRing A] :=
  (pointFiniteSections D.k A).mapDerivedCategoryFactors

/-- The ordinary compositor T_(m+1), in the iterated-to-composite direction.
The defining theorem determines its direct-image conjugate on every section by the
fibre-product associator. That fixes the conjugate and hence this isomorphism uniquely.
Source: Stacks Tag 03D8
(blueprint: lem-trf-point-exact-derived-model). -/
def ordinaryComposition (D : FiniteFieldDatum.{u}) (A : Type u) [CommRing A] (m : ℕ) :
    pullback D A (m + 1) ⋙ pullback D A 1 ≅ pullback D A (m + 2) :=
  (Classical.choose (proEtaleConstantRingModulePullbackComposition
    (frobenius D) (power D (m + 1)) A)).symm

/-- The inverse of the prescribed K-flat-normalized comparison, with the composite
coefficient identification transported by the published constant-section equality.
Source: Stacks Tag 0D6D
(blueprint: lem-trf-point-exact-derived-model). -/
def derivedComposition (D : FiniteFieldDatum.{u}) (A : Type u) [CommRing A] (m : ℕ) :
    derivedPullback D A (m + 1) ⋙ derivedPullback D A 1 ≅
      derivedPullback D A (m + 2) :=
  proEtaleConstantRingPullbackComposition (frobenius D) (power D (m + 1)) A

/-- Exactness and preservation of quasi-isomorphisms for all positive powers and sections.
Source: Stacks Tags 0982, 098H and 015F
(blueprint: lem-trf-point-exact-derived-model).
Proof (node steps 1--2): constant-coefficient module inverse image is exact. Final-object
sections over the algebraically closed point are exact. Restrict scalars by the actual
constant-section map; this preserves kernels and cokernels. Exact additive functors
preserve cohomology and hence quasi-isomorphisms. Their canonical factorization maps
are precisely `pullbackFactors` and `evaluationFactors`, on arbitrary complexes. -/
theorem exactness (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (_ι : E →ₐ[ℚ_[l]] Ω)
    (n : ℕ) (_hn : 1 ≤ n) :
    (∀ r : ℕ,
      PreservesFiniteLimits (pullback D (Padic.coefficientExtensionRing l E n) (r + 1)) ∧
      PreservesFiniteColimits (pullback D (Padic.coefficientExtensionRing l E n) (r + 1)) ∧
      ∀ (K L : CochainComplex (modules D (Padic.coefficientExtensionRing l E n)) ℤ)
        (f : K ⟶ L), QuasiIso f →
        QuasiIso (((pullback D (Padic.coefficientExtensionRing l E n) (r + 1)).mapHomologicalComplex
          (.up ℤ)).map f)) ∧
    PreservesFiniteLimits (pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)) ∧
    PreservesFiniteColimits (pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)) ∧
    ∀ (K L : CochainComplex (modules D (Padic.coefficientExtensionRing l E n)) ℤ)
      (f : K ⟶ L), QuasiIso f →
      QuasiIso (((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E n)).mapHomologicalComplex (.up ℤ)).map f) := by
  sorry

/-- The prescribed derived compositor equals localization of the ordinary compositor
on every complex, with all iterated exact-functor identifications displayed.
Source: Stacks Tag 0D6D
(blueprint: lem-trf-point-exact-derived-model).
Proof (node steps 3--5): constant-section coefficient maps compose by
lem-trf-constant-coefficient-composition. Resolve an arbitrary K by a K-flat complex P
with flat terms. On P the normalization of the recorded derived comparison gives the
ordinary termwise compositor. Its first pullback remains K-flat with flat terms.
Naturality of both compositors and of the factorization maps gives two squares along
P -> K. Exactness makes the localized iterated pullback of this quasi-isomorphism
invertible. Cancel it to get the same equation on K, without a flatness hypothesis. -/
theorem composition (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (_ι : E →ₐ[ℚ_[l]] Ω)
    (n : ℕ) (_hn : 1 ≤ n) (m : ℕ)
    (K : CochainComplex (modules D (Padic.coefficientExtensionRing l E n)) ℤ) :
    (derivedComposition D (Padic.coefficientExtensionRing l E n) m).hom.app
        (DerivedCategory.Q.obj K) ≫
      (pullbackFactors D (Padic.coefficientExtensionRing l E n) (m + 2)).hom.app K =
    (derivedPullback D (Padic.coefficientExtensionRing l E n) 1).map
        ((pullbackFactors D (Padic.coefficientExtensionRing l E n) (m + 1)).hom.app K) ≫
      (pullbackFactors D (Padic.coefficientExtensionRing l E n) 1).hom.app
        (((pullback D (Padic.coefficientExtensionRing l E n) (m + 1)).mapHomologicalComplex
          (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        (((ordinaryComposition D (Padic.coefficientExtensionRing l E n) m).hom.mapHomologicalComplex
          (.up ℤ)).app K) := by
  sorry

/-- Positive Frobenius pullbacks preserve the full bounded constructible subcategory.
Source: blueprint `lem-weil-isomorphism-derived-pullback`, finite-level clause
(blueprint: lem-trf-point-exact-derived-model).
Proof (node step 6): geometric Frobenius and every positive power are scheme
isomorphisms. The prime l is invertible on Spec k because l differs from p. Apply the
isomorphism-pullback theorem at the positive finite level n. Its termwise inverse image
is the same constant-coefficient pullback, so it preserves the recorded predicate. -/
theorem preserves_constructible (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (_ι : E →ₐ[ℚ_[l]] Ω)
    (n : ℕ) (hn : 1 ≤ n) (r : ℕ)
    (K : proEtaleDerivedCategory (Spec (.of D.k)) (Padic.coefficientExtensionRing l E n)) :
    intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k)) K →
      intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k))
        ((derivedPullback D (Padic.coefficientExtensionRing l E n) (r + 1)).obj K) := by
  sorry

/-- Restriction of ambient evaluation is precisely the recorded point fibre functor,
with its finite-cohomology target included in the ambient coefficient derived category.
Source: blueprint `def-weil-finite-coefficient-point`, clause 1
(blueprint: lem-trf-point-exact-derived-model).
Proof (node step 6): the point fibre functor is defined by restricting this very
termwise final-object section functor. Point-sections finiteness puts its cohomology in
the finite bounded target. The full-subcategory inclusion forgets only that proof. -/
theorem evaluation_restriction (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (_ι : E →ₐ[ℚ_[l]] Ω)
    (n : ℕ) (hn : 1 ≤ n) :
    pointFiniteFibre D l hl E n hn ⋙
        (DerivedCategory.pointFiniteCohomology
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))).ι =
      (intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k))).ι ⋙
        evaluation D (Padic.coefficientExtensionRing l E n) := by
  sorry

/-- Every ordinary natural transformation of section functors descends uniquely on
all ambient derived objects, with its degreewise chain-map formula on every complex.
Source: Stacks Tag 04VG; Mathlib `Localization.liftNatTrans` and `natTrans_ext`
(blueprint: lem-trf-point-exact-derived-model).
Proof (node steps 7--9): naturality of alpha at differentials makes its components a
chain map, and naturality at module maps makes these chain maps a natural transformation.
Both exact termwise functors invert quasi-isomorphisms. Use the localization universal
property with the displayed evaluation and pullback factorizations. Full faithfulness
of precomposition gives existence and uniqueness of the derived transformation. Its
type enforces naturality at every derived morphism, including inverses of localized
quasi-isomorphisms. No component of alpha is required to be invertible. -/
theorem descent (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (_ι : E →ₐ[ℚ_[l]] Ω)
    (n : ℕ) (_hn : 1 ≤ n) (r : ℕ)
    (α : pointFiniteSections D.k (Padic.coefficientExtensionRing l E n) ⟶
      pullback D (Padic.coefficientExtensionRing l E n) (r + 1) ⋙
        pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)) :
    ∃! αD : evaluation D (Padic.coefficientExtensionRing l E n) ⟶
        derivedPullback D (Padic.coefficientExtensionRing l E n) (r + 1) ⋙
          evaluation D (Padic.coefficientExtensionRing l E n),
      ∀ K : CochainComplex (modules D (Padic.coefficientExtensionRing l E n)) ℤ,
        αD.app (DerivedCategory.Q.obj K) ≫
          (evaluation D (Padic.coefficientExtensionRing l E n)).map
            ((pullbackFactors D (Padic.coefficientExtensionRing l E n) (r + 1)).hom.app K) ≫
          (evaluationFactors D (Padic.coefficientExtensionRing l E n)).hom.app
            (((pullback D (Padic.coefficientExtensionRing l E n) (r + 1)).mapHomologicalComplex
              (.up ℤ)).obj K) =
        (evaluationFactors D (Padic.coefficientExtensionRing l E n)).hom.app K ≫
          DerivedCategory.Q.map ((α.mapHomologicalComplex (.up ℤ)).app K) := by
  sorry

/-- The unique ambient descent characterized by `descent`, with no choice of its maps.
Source: Stacks Tag 04VG, localization of natural transformations
(blueprint: lem-trf-point-exact-derived-model). -/
def descendedTransformation (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (_ι : E →ₐ[ℚ_[l]] Ω)
    (n : ℕ) (hn : 1 ≤ n) (r : ℕ)
    (α : pointFiniteSections D.k (Padic.coefficientExtensionRing l E n) ⟶
      pullback D (Padic.coefficientExtensionRing l E n) (r + 1) ⋙
        pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)) :
    evaluation D (Padic.coefficientExtensionRing l E n) ⟶
      derivedPullback D (Padic.coefficientExtensionRing l E n) (r + 1) ⋙
        evaluation D (Padic.coefficientExtensionRing l E n) :=
  Classical.choose (descent D l hl E Ω _ι n hn r α).exists

/-- Restrict the same derived transformation to the full bounded constructible source.
No maps are chosen anew: whiskering retains every component and every naturality square.
The target is viewed in the ambient D(A), as in `evaluation_restriction`.
Source: Stacks Tag 04VG and blueprint `def-weil-finite-coefficient-point`, clause 1
(blueprint: lem-trf-point-exact-derived-model). -/
def restrictedTransformation (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (_ι : E →ₐ[ℚ_[l]] Ω)
    (n : ℕ) (hn : 1 ≤ n) (r : ℕ)
    (α : pointFiniteSections D.k (Padic.coefficientExtensionRing l E n) ⟶
      pullback D (Padic.coefficientExtensionRing l E n) (r + 1) ⋙
        pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)) :=
  Functor.whiskerLeft
    (intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k))).ι
    (descendedTransformation D l hl E Ω _ι n hn r α)

end WeilConjectures.PointExactDerivedModel
