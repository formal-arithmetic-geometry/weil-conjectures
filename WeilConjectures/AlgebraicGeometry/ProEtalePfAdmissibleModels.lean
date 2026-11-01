/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-! # Admissible models for the finite-coefficient projection comparison

Source: Stacks Project, Tags 09AL, 08G1, 06YQ, 03DJ and 06YU; the finite-coefficient
transport paragraph of the current blueprint `thm-sf-pf-proetale.proof.md`
(blueprint: lem-sf-proetale-pf-admissible-models).

All objects use ordinary fixed-ring module sheaves on the original small sites.
The model assertions retain the literal termwise functors and the signed total tensor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProEtale

/-- For fixed etale antecedents, every cohomological support interval admits the
simultaneous bounded models needed for the proper comparison. The `letI` declarations
in this definition only install the existing sheaf tensor, with its original data.
Source: Stacks Tags 08G1, 06YQ, 03DJ and 06YU; blueprint finite-coefficient transport
paragraph (blueprint: lem-sf-proetale-pf-admissible-models). -/
def pfAdmissibleModelAssertions (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (r : Z ⟶ Y)
    (K0 : Etale.DerivedCategoryModule A X) (L0 : Etale.DerivedCategoryModule A Y)
    (a b : ℤ) : Prop :=
  letI := Sheaf.monoidalCategory Y.smallEtaleTopology (ModuleCat.{u + 1} A)
  letI := Sheaf.monoidalCategory Z.smallEtaleTopology (ModuleCat.{u + 1} A)
  letI := Sheaf.symmetricCategory Y.smallEtaleTopology (ModuleCat.{u + 1} A)
  letI := Sheaf.symmetricCategory Z.smallEtaleTopology (ModuleCat.{u + 1} A)
  let M0 := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K0
  let RL0 := (Etale.upperStar (ModuleCat.{u + 1} A) r).mapDerivedCategory.obj L0
  let Q0 := ((Etale.derivedTensor (ModuleCat.{u + 1} A) Z).obj M0).obj RL0
  ∀ u0 v0 : ℤ, u0 ≤ v0 →
    (∀ i : ℤ, (i < u0 ∨ v0 < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj K0)) →
    ∃ (C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
      (P : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ),
      Nonempty ((_root_.DerivedCategory.Q.obj C) ≅ K0) ∧
      (∀ i : ℤ, (i < u0 ∨ v0 < i) → IsZero (C.X i)) ∧
      Nonempty ((_root_.DerivedCategory.Q.obj P) ≅ L0) ∧
      (∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i)) ∧
      (∀ i : ℤ, exactFunctor _ _ (tensorRight (P.X i))) ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P ∧
      let RP := ((Etale.upperStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex
        (.up ℤ)).obj P
      let JC := ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex
        (.up ℤ)).obj C
      let T := CochainComplex.mapBifunctor JC RP (curriedTensor _)
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat RP ∧
      Nonempty ((_root_.DerivedCategory.Q.obj RP) ≅ RL0) ∧
      Nonempty ((_root_.DerivedCategory.Q.obj JC) ≅ M0) ∧
      (∀ i : ℤ, (i < u0 ∨ v0 < i) → IsZero (JC.X i)) ∧
      Nonempty ((_root_.DerivedCategory.Q.obj T) ≅ Q0) ∧
      (∀ m : ℤ, (m < u0 + a ∨ v0 + b < m) → IsZero (T.X m)) ∧
      _root_.DerivedCategory.TStructure.t.plus M0 ∧
      _root_.DerivedCategory.TStructure.t.plus Q0 ∧
      QuasiCompact r ∧ QuasiSeparated r

end AlgebraicGeometry.ProEtale
