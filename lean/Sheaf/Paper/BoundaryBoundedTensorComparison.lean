/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.Paper.FiniteCoefficientFlatModel
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.SiteOneSidedTensorNormalization
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Bounded tensor preparation for boundary comparison

Source: Stacks Project, sites-cohomology.tex, Tags 06YQ, 0G7E and 06YU;
proetale.tex, Tag 099R; the small-etale clause of lem-sf-flat-model
(blueprint: lem-sf-boundary-bounded-tensor-comparison).

The coefficient ring is the canonical universe lift of the same quotient A_{E,n}.
Complex tensor is the signed direct-sum total tensor, with second differential
multiplied by (-1)^j in bidegree (j,h). The general quasi-isomorphism-localizer
K-flat predicate applies to the ordinary ModuleCat-valued sheaf presentation;
its acyclic-tensor characterization is HomotopyCategory.kFlat_iff_preserves_acyclic.
-/

@[expose] public section

set_option autoImplicit false

universe w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- Bounded representatives and the specified invertible comparison for their tensor.
Source: Stacks Project, sites-cohomology.tex, Tags 06YQ, 0G7E, 06YU; proetale.tex,
Tag 099R; lem-sf-flat-model, small-etale clause
(blueprint: lem-sf-boundary-bounded-tensor-comparison).

Proof:
1. Apply lem-sfb-bounded-representative in ordinary A-module etale sheaves to B
   and [r,s]. This uses no Tor hypothesis on B.
2. Apply lem-sf-flat-model on T to M and [u,v]. Its flat terms give exact tensor
   functors by right exactness (lem-weil-pbc-independent-sheaf-tensor-colimits)
   and symmetry (def-pur-sheaf-tensor-product). Bounded-above flat complexes are
   K-flat by lem-pc-bounded-above-flat-kflat-site.
3. The constant-coefficient inverse image is exact by
   prop-weil-pbc-inverse-image-modules-exact. Its derived factorization
   (lem-weil-pbc-exact-functor-derived-factorization) identifies termwise lV
   with lM. Apply lem-weil-pbc-ringed-topos-kflat-pullback (0G7E) to V.
4. The right-factor clause of lem-trf-site-one-sided-tensor-normalization
   identifies the signed total B' tensor lV with B tensor-derived lM, even
   though B' need not be flat or K-flat.
5. A nonzero total summand has j in [r,s], h in [u,v], and j+h=d. Hence the
   total is zero outside [r+u,s+v], and its cohomology has the same bound.
   This gives bounded and bounded-below membership of the actual tensor Q.
6. A closed immersion is proper (lem-weil-pbc-closed-immersion-proper), hence
   quasi-compact and separated, and therefore quasi-separated by
   lem-pc-separated-quasi-separated.
7. The coefficient ring is finite by def-weil-l-adic-coefficient-extension.
   Apply lem-weil-pbc-comparison-direct-image-canonical-mate to this Q in D+.
   It proves invertibility of the named mate. The argument includes zero
   inputs, the empty scheme, and singleton intervals; it never requires
   finite Tor amplitude of B or locally free terms of V. -/
theorem boundary_bounded_tensor_comparison
    (D : WeilConjectures.FiniteFieldDatum.{w})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) :
    (fun (A : Type (w + 1)) [inst : CommRing A] [fin : Finite A] ↦
    ∀ (Z T : Scheme.{w}) [Z.Over (Spec (.of D.k))] [T.Over (Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [IsSeparated (T ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    (i : Z ⟶ T) [i.IsOver (Spec (.of D.k))] [IsClosedImmersion i]
    (r s u v : ℤ) (_hrs : r ≤ s) (_huv : u ≤ v)
    (B : DerivedCategoryModule A Z)
    (M : DerivedCategoryModule A T)
    (_hB : DerivedCategory.isBoundedConstructible A Z B)
    (_hM : DerivedCategory.isBoundedConstructible A T M)
    (_hBrs : ∀ j : ℤ, j < r ∨ s < j →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ j).obj B))
    (_hMuv : DerivedCategory.hasTorAmplitudeIn A T u v M),
    ∃ (B' : CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{w + 1} A)) ℤ)
      (V : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{w + 1} A)) ℤ)
      (lV : CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{w + 1} A)) ℤ)
      (Q : _root_.DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{w + 1} A))),
      lV = ((upperStar (ModuleCat.{w + 1} A) i).mapHomologicalComplex (.up ℤ)).obj V ∧
      (∀ j : ℤ, j < r ∨ s < j → IsZero (B'.X j)) ∧
      Nonempty (B ≅ _root_.DerivedCategory.Q.obj B') ∧
      (∀ h : ℤ, h < u ∨ v < h → IsZero (V.X h)) ∧
      (∀ h : ℤ, exactFunctor _ _ (tensorRight (V.X h))) ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat V ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat lV ∧
      Nonempty (M ≅ _root_.DerivedCategory.Q.obj V) ∧
      Nonempty (((upperStar (ModuleCat.{w + 1} A) i).mapDerivedCategory).obj M ≅
          _root_.DerivedCategory.Q.obj lV) ∧
      Q.obj = ((derivedTensor (ModuleCat.{w + 1} A) Z).obj B).obj
          (((upperStar (ModuleCat.{w + 1} A) i).mapDerivedCategory).obj M) ∧
      Nonempty (Q.obj ≅ _root_.DerivedCategory.Q.obj
        (CochainComplex.mapBifunctor B' lV (curriedTensor _))) ∧
      (∀ d : ℤ, d < r + u ∨ s + v < d →
        IsZero ((CochainComplex.mapBifunctor B' lV (curriedTensor _)).X d)) ∧
      (∀ d : ℤ, d < r + u ∨ s + v < d →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ d).obj Q.obj)) ∧
      (_root_.DerivedCategory.TStructure.t).bounded Q.obj ∧
      IsIso ((ProEtale.fixedComparisonDirectImageMatePlus A i).app Q))
      (ULift.{w + 1, w} (Padic.coefficientExtensionRing l E n))
      (inst := inferInstance)
      (fin := Equiv.ulift.finite_iff.mpr
        (Padic.finite_coefficientExtensionRing l E n hn)) := by
  sorry

end AlgebraicGeometry.Etale
