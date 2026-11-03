/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteProperLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators

/-!
# Flat models and generators for finite discrete condensed coefficients

This records the current condensed discrete-coefficient formulation of
`sk-lem-sf-flat-model`.  The constructibility and finite Tor predicates are the
published `ConstantModelConstructibleFiniteTor` predicates.

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-ctf-finite-foundations/sk-lem-sf-flat-model/_section.md
(blueprint: sk-lem-sf-flat-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale


namespace AlgebraicGeometry.ProEtale

/-- The finite-projective local-model clause for a module over a condensed coefficient.
The displayed retract is the finite-projective condition over the ordinary scalar ring
`Λ(*)`; the second display uses the published canonical scalar-extension functor.
For the finite discrete coefficient of `A`, this scalar ring is canonically `A`.
This strengthens the recorded finite-presentation local-model condition only by replacing
finite presentation with the finite-projective condition required by this node.
Source: current blueprint `sk-lem-sf-flat-model`, second and third assertions
(blueprint: sk-lem-sf-flat-model).
-/
def HasFiniteProjectiveConstantLocalModel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
    ∃ P : Mod Ab.{u + 1} (scalarRingObj Λ),
      (∃ n : ℕ, Nonempty (Retract P (Mod.finiteFree (scalarRingObj Λ) n))) ∧
      Nonempty ((CondensedRing.upperStar Λ (𝒰.f i)).obj M ≅
        (finiteConstantScalarExtension Λ (𝒰.X i)).obj P)

/-- The generators obtained from all locally closed immersions and finite-projective
constant local models.  The extension `a_! = g_* j_!` is the recorded locally closed
coefficient extension `coefficientHeartLocallyClosedExtension` (node
def-sfb-locally-closed-coefficient-extension): the open extension by zero along
`a.toImage` followed by the direct image along the closed immersion `a.imageι` of the
scheme-theoretic image. The Noetherian hypothesis supplies its topological Noetherian
instance.
Source: current blueprint `sk-lem-sf-flat-model`, generation clause
(blueprint: sk-lem-sf-flat-model).
-/
def condensedFlatModelGenerators
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {k : Type u} [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] :
    ObjectProperty
      (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  letI : IsNoetherian X := {}
  exact fun K ↦ ∃ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)),
    HasFiniteProjectiveConstantLocalModel Λ S L ∧
      Nonempty (K ≅
        (_root_.DerivedCategory.singleFunctor _ 0).obj
          ((coefficientHeartLocallyClosedExtension Λ a ha).obj L))

end AlgebraicGeometry.ProEtale
