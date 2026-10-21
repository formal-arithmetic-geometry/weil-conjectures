/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.SupportedExteriorProduct
public import Sheaf.AlgebraicGeometry.EtaleSupportedSections
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.Paper.EtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Topology.InverseImageModule
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Topology.Sheaves.Functors
public import WeilConjectures.AlgebraicGeometry.Picard.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Topology.Constructible
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.AlgebraicGeometry.SupportRestrictionTriangle
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution
import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
import Sheaf.AlgebraicGeometry.NormalizedSupportTriangle
import Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing
import Sheaf.AlgebraicGeometry.SupportSiteComparison
import Sheaf.AlgebraicGeometry.SupportedProductLocalization

/-!
# Kunneth for cohomology with closed support

Source: blueprint, sec-smooth-purity/sk-prop-a1-kummer,
`lem-pur-kunneth-supported`, order 1939 (blueprint: lem-pur-kunneth-supported).

The coefficient ring is the existing finite extension quotient. Its discrete topology
and finiteness instances implement the coefficient convention for origin witnesses.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Finiteness of the specified positive-level coefficient ring, from its existing
finiteness theorem. Source: blueprint `def-weil-finite-field-fiber`, coefficient clause
(blueprint: lem-pur-kunneth-supported). -/
noncomputable instance supportedKunnethCoefficient_finite
    (l : ℕ) [Fact l.Prime] (E : Type v) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)] :
    Finite (Padic.coefficientExtensionRing l E n) :=
  Padic.finite_coefficientExtensionRing l E n (Fact.out : 1 ≤ n)

/-- Finite coefficients carry the discrete topology.
Source: blueprint `def-weil-pbc-etale-origin-witness`, finite coefficient convention
(blueprint: lem-pur-kunneth-supported). -/
instance supportedKunnethCoefficient_topology
    (l : ℕ) [Fact l.Prime] (E : Type v) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    TopologicalSpace (Padic.coefficientExtensionRing l E n) := ⊥

/-- Discreteness of the coefficient convention.
Source: blueprint `def-weil-pbc-etale-origin-witness`
(blueprint: lem-pur-kunneth-supported). -/
instance supportedKunnethCoefficient_discrete
    (l : ℕ) [Fact l.Prime] (E : Type v) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    DiscreteTopology (Padic.coefficientExtensionRing l E n) := ⟨rfl⟩

/-- The supported exterior product is an isomorphism for bounded complexes with the
second factor of finite Tor amplitude, including every specified pro-etale realization.
Source: blueprint `lem-pur-kunneth-supported`, order 1939
(blueprint: lem-pur-kunneth-supported).

Proof:
1. Set U = X minus Z, V = Y minus W, and F = p_X^*K tensor^L p_Y^*L.
Finite-type schemes over the field are Noetherian. Finite basic-open covers show U,V
are finite type, and restricting the closed diagonals shows they are separated. The
same affine-chart and diagonal argument applies to X times Y. Choose a lower bound c
for K and Tor bounds a,b for L. The K-flat flat-term representative of L supplied by
lem-kun-0f1m starts in degree a and retains these properties under pullback. Exact
inverse image preserves the lower bound c for K. The total tensor and every required
open restriction start in degree c+a. Thus all support triangles apply.
2. Apply lem-pur-support-restriction-triangle on Y for W, tensor with RΓ(X,K),
and compare with the support triangle of X times W. The actual supported and ordinary
exterior products form a morphism of triangles, including the connecting map, by
lem-pur-supported-product-localization. Ordinary Kunneth for (X,Y) and (X,V), from
lem-pur-ordinary-kunneth-finite-ring, makes the other two components isomorphisms.
lem-sf-triangle-morphism-iso gives the supported product for X times W.
3. Repeat step 2 with U in place of X to obtain the supported product for U times W.
4. Tensor the support triangle for Z in X with RΓ_W(Y,L). Compare with the triangle
for the supports Z times W inside X times W in X times Y. Its three components are
exactly the supported products for (Z,W), (X,W), and (U,W), by the localization
compatibility. Steps 2 and 3 and the triangle isomorphism lemma give the first clause.
5. For canonical etale-origin witnesses, lem-pur-support-site-comparison identifies
the pro-etale product with the etale product conjugated by the supported comparison
isomorphisms and the external-product comparison. Every factor is invertible. For
arbitrary specified witnesses alpha,beta, naturality of supported sections, pullback,
and tensor identifies the product with that for the canonical witnesses conjugated
by RΓ_Z(alpha) tensor RΓ_W(beta) and RΓ_{Z times W}(alpha external beta).
These are isomorphisms, proving the second clause for the actual pro-etale product.
-/
theorem isIso_supportedExteriorProduct
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)]
    {X Y Z W : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of D.k))]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory.Bounded
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))))
    (L : DerivedCategory.Bounded
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))))
    (_hL : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) Y a b
      L.obj) :
    IsIso (supportedExteriorProduct (Padic.coefficientExtensionRing l E n)
      (X ↘ Spec (CommRingCat.of D.k)) (Y ↘ Spec (CommRingCat.of D.k)) i j K.obj L.obj) ∧
    ∀ (Kp : ProEtale.FiniteCoefficientDerivedCategoryPlus X (Padic.coefficientExtensionRing l E n))
      (Lp : ProEtale.FiniteCoefficientDerivedCategoryPlus Y (Padic.coefficientExtensionRing l E n))
      (wx : ProEtale.EtaleOriginWitness X (Padic.coefficientExtensionRing l E n) Kp)
      (wy : ProEtale.EtaleOriginWitness Y (Padic.coefficientExtensionRing l E n) Lp)
      (_hx : wx.L.obj ≅ K.obj) (_hy : wy.L.obj ≅ L.obj),
      IsIso (ProEtale.supportedExteriorProductOverField (Padic.coefficientExtensionRing l E n) D.k
        (X ↘ Spec (CommRingCat.of D.k)) (Y ↘ Spec (CommRingCat.of D.k)) i j
        ((ProEtale.fixedRingDerivedTransport X (Padic.coefficientExtensionRing l E n)).obj Kp.obj)
        ((ProEtale.fixedRingDerivedTransport Y (Padic.coefficientExtensionRing l E n)).obj Lp.obj))
          := by
  sorry

end AlgebraicGeometry.Etale
