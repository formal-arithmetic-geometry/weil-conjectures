/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleExternalKunneth
import WeilConjectures.AlgebraicGeometry.ProEtaleExternalKunnethFactorization
import WeilConjectures.AlgebraicGeometry.ProEtaleExternalKunnethFiniteField
import WeilConjectures.AlgebraicGeometry.ProEtaleExternalKunnethResidueData
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothBaseChangeCoefficients
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersionBaseChange
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.FiniteRingResidueConservativity
import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LocalSite
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Topology.Constructible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModulePullbackComposition
import WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModelsSerre
import WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModelsPullback
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.AlgebraicGeometry.Flat.FlatModel
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarCompCoherence

/-!
# Ordinary external Künneth over a finite or algebraically closed field

Source: current blueprint, sk-lem-sf-kunneth-star, statement and formula (12.2),
with the standing field scope of det-def-sf-operations (Wei Yang #1441)
(blueprint: sk-lem-sf-kunneth-star).

These statements extend the field scope of the published geometric-finite-field
statements. They use the same canonical counit adjuncts and the same intrinsic
bounded constructible finite-Tor domain, without introducing new coefficient objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable (A : Type (u + 1)) [CommRing A] [Finite A]

omit [Finite A] in
private theorem externalKunneth_classical_origin
    (S : Scheme.{u}) [IsNoetherian S]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)))
    (hK : exceptionalTransportProEtaleObjects A S K) :
    ∃ E : Etale.DerivedCategoryModule A S,
      DerivedCategory.TStructure.t.plus E ∧
        Nonempty ((comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj E ≅ K) := by
  obtain ⟨E, hE, e⟩ := (congrFun (exceptionalTransport_constructible_comparison A S) K).mp
    ⟨hK.1, hK.2.1⟩
  obtain ⟨a, b, _, hv⟩ := hE.2
  exact ⟨E, ⟨a, (DerivedCategory.isGE_iff E a).mpr (fun i hi ↦ hv i (Or.inl hi))⟩, e⟩

/-- Identity-factor ordinary external Künneth, formula (12.2), with the full field scope.
Source: current blueprint, sk-lem-sf-kunneth-star, identity-factor formula
(blueprint: sk-lem-sf-kunneth-star).

Proof: Apply steps 1--4 of the unit proof. Independent base change
handles constant finite free second factors, and retracts handle projective constants.
For finite field coefficients, finite-cover comparison and constructible embedding
reduce to these constants: the exact source cohomology functors and the target long
exact sequence prove injectivity and then surjectivity by degree induction. Negative
degrees vanish after shifting. Truncation triangles extend to bounded complexes.
For finite rings, ctf stability and the unit/counit-compatible scalar-six comparisons
identify each residue reduction with this field-coefficient map; classical residue
conservativity kills its cone. Throughout, the map is precisely the adjunct of the
pulled-back first counit tensored with identity, as required by (12.2).
-/
theorem isIso_externalKunnethIdentityMap_of_finite_or_isAlgClosed
    (k : Type u) [Field k] (_hk : Finite k ∨ IsAlgClosed k)
    (_hp : (ringChar k).Prime) (l : ℕ) (_hl : l.Prime)
    (_hne : l ≠ ringChar k)
    (_hA : ∃ n : ℕ, 0 < n ∧ ((l ^ n : ℕ) : A) = 0)
    {X Y T : Scheme.{u}} (b : Y ⟶ Spec (.of k)) (c : T ⟶ Spec (.of k))
    (f : X ⟶ Y)
    [LocallyOfFiniteType b] [QuasiCompact b] [IsSeparated b]
    [LocallyOfFiniteType c] [QuasiCompact c] [IsSeparated c]
    [LocallyOfFiniteType (f ≫ b)] [QuasiCompact (f ≫ b)] [IsSeparated (f ≫ b)]
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (Q : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (_hM : exceptionalTransportProEtaleObjects A X M)
    (_hQ : exceptionalTransportProEtaleObjects A T Q) :
    IsIso (externalKunnethIdentityMap A
      ⟨(pullback.mapOverBaseRight_fst f b c).symm⟩
      (pullback.mapOverBaseRight_snd f b c) M Q) := by
  classical
  obtain ⟨_, hK, hK', hres⟩ :=
    externalKunnethIdentityMap_residue_data A k _hk _hp l _hl _hne _hA b c f M Q _hM _hQ
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace b
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated b
  have : QuasiSeparatedSpace (CategoryTheory.Limits.pullback b c : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst b c)
  have : CompactSpace (CategoryTheory.Limits.pullback b c : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst b c)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian b
  have : IsLocallyNoetherian (CategoryTheory.Limits.pullback b c : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst b c)
  have : IsNoetherian (CategoryTheory.Limits.pullback b c : Scheme.{u}) := ⟨⟩
  apply finiteRing_residue_conservativity A (pullback b c) hK hK'
    (externalKunneth_classical_origin A _ _ hK) (externalKunneth_classical_origin A _ _ hK')
  intro m hm
  have : Finite (A ⧸ m) :=
    Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := m))
  let : m.IsMaximal := hm
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  obtain ⟨hML, hQL, e, e', he⟩ := hres m hm
  have hAl : ∃ n : ℕ, 0 < n ∧ ((l ^ n : ℕ) : A ⧸ m) = 0 := by
    obtain ⟨n, hn, he⟩ := _hA
    refine ⟨n, hn, ?_⟩
    simpa only [map_natCast, map_zero] using congrArg (Ideal.Quotient.mk m) he
  have hi := isIso_externalKunnethIdentityMap_finiteField (A ⧸ m) k _hk _hp l _hl
    _hne hAl b c f _ _ hML hQL
  exact IsIso.of_isIso_fac_right he

/-- Ordinary external Künneth over the full standing field domain.
Source: current blueprint, sk-lem-sf-kunneth-star, two-morphism formula
(blueprint: sk-lem-sf-kunneth-star).

Proof:
1. Start with the identity-factor map, the adjunct of the pulled-back first counit
   tensored with the identity. For constant finite free second factor, independent
   base change gives a finite sum of isomorphisms; finite projective constants follow
   by retracts. Use the sheaf-valued image on Spec k, including when k is finite.
   Constructible and direct-image comparison identify the etale and pro-etale maps
   and counits. The exact ordinary/module-object equivalence transports tensor and
   Tor bounds and preserves K-injectives by the acyclic-Hom criterion.
2. For finite field coefficients and sheaf inputs, finite-cover tensor-counit
   comparison gives the map for finite sums of finite pushforwards of constants.
   Embed any constructible second factor into such a sum with constructible quotient.
   After a shift the first factor is connective. In each nonnegative degree the
   source cohomology functor is exact in the second factor; the target has the long
   exact sequence of a short exact sequence. Naturality of the embedding gives
   injectivity. Induction on the degree identifies the target kernel with the source
   and gives surjectivity. Negative cohomology vanishes.
3. Tensor, pullback and direct image are triangulated, with the same counit adjunct
   on flat models. Bounded truncation triangles and two-out-of-three extend the
   sheaf calculation to bounded constructible field-coefficient complexes.
4. For arbitrary finite A, ctf stability on the standing finite-or-algebraically-
   closed base puts both endpoints in the intrinsic ctf domain. For every maximal
   ideal, the listed scalar-six comparison to its finite residue field preserves
   pullback, tensor, direct image, units and counits. It identifies the reduction
   of this specified map with the field-coefficient map from step 3. Constructible
   comparison makes the cone classical; finite-ring residue conservativity kills
   it. This proves invertibility, without inferring equality of maps from reduction.
5. Factor the product morphism into two identity-factor morphisms, interchanging
   factors for the first leg. Stability supplies the intermediate ctf input.
   Direct-image composition identifies the composite adjunct with the tensor of
   the two pulled-back counits, hence identifies the composite with the stated map.
-/
theorem isIso_externalKunnethMap_of_finite_or_isAlgClosed
    (k : Type u) [Field k] (_hk : Finite k ∨ IsAlgClosed k)
    (_hp : (ringChar k).Prime) (l : ℕ) (_hl : l.Prime)
    (_hne : l ≠ ringChar k)
    (_hA : ∃ n : ℕ, 0 < n ∧ ((l ^ n : ℕ) : A) = 0)
    {X₁ X₂ Y₁ Y₂ : Scheme.{u}}
    (b₁ : Y₁ ⟶ Spec (.of k)) (b₂ : Y₂ ⟶ Spec (.of k))
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    [LocallyOfFiniteType b₁] [QuasiCompact b₁] [IsSeparated b₁]
    [LocallyOfFiniteType b₂] [QuasiCompact b₂] [IsSeparated b₂]
    [LocallyOfFiniteType (f₁ ≫ b₁)] [QuasiCompact (f₁ ≫ b₁)] [IsSeparated (f₁ ≫ b₁)]
    [LocallyOfFiniteType (f₂ ≫ b₂)] [QuasiCompact (f₂ ≫ b₂)] [IsSeparated (f₂ ≫ b₂)]
    (M₁ : DerivedCategory (Sheaf (Scheme.ProEt.topology X₁) (ModuleCat.{u + 1} A)))
    (M₂ : DerivedCategory (Sheaf (Scheme.ProEt.topology X₂) (ModuleCat.{u + 1} A)))
    (_hM₁ : exceptionalTransportProEtaleObjects A X₁ M₁)
    (_hM₂ : exceptionalTransportProEtaleObjects A X₂ M₂) :
    IsIso (externalKunnethMap A
      ⟨(pullback.mapOverBase_fst f₁ f₂ b₁ b₂).symm⟩
      ⟨(pullback.mapOverBase_snd f₁ f₂ b₁ b₂).symm⟩ M₁ M₂) := by
  have hR₂ := (externalKunnethIdentityMap_residue_data A k _hk _hp l _hl _hne _hA
    b₂ (f₁ ≫ b₁) f₂ M₂ M₁ _hM₂ _hM₁).1
  have h₁ := isIso_externalKunnethIdentityMap_of_finite_or_isAlgClosed A k _hk _hp l _hl
    _hne _hA b₁ b₂ f₁ M₁
      ((lowerStar (ModuleCat.{u + 1} A) f₂).rightDerivedFunctor.obj M₂) _hM₁ hR₂
  have h₂ := isIso_externalKunnethIdentityMap_of_finite_or_isAlgClosed A k _hk _hp l _hl
    _hne _hA b₂ (f₁ ≫ b₁) f₂ M₂ M₁ _hM₂ _hM₁
  have he := externalKunnethMap_factorization A b₁ b₂ f₁ f₂ M₁ M₂
  rw [he]
  infer_instance

end AlgebraicGeometry.ProEtale
