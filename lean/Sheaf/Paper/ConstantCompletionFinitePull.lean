/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Sheaf.Paper.FlatRingedIdealCompleteEquivalence
public import Sheaf.CategoryTheory.RingedKoszulSystem
public import Sheaf.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Sheaf.Paper.RingedSiteIdeal
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Sites.Over
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.Paper.RingedTopoiTensorSections
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import all Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Adjunction.Additive
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Sheaf.Paper.ConstantCompletionOrdinaryFinitePull
import all Sheaf.Paper.ConstantCompletionCore
import all Sheaf.Paper.ConstantCompletionInverseImage
import all Sheaf.Paper.ConstantCompletionDerivedPull

/-!
# Constant coefficient completion: FinitePull

The derived finite pullback comparison, pointwise tower pullback and composition predicates.

Part of the split of `Sheaf.Paper.ConstantCompletionEquivalence`.
Source: Stacks Project, Tags 093M, 099I, 099L, 099M, 0A0E, 06YY and 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence).
-/

@[expose] public noncomputable section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

attribute [local irreducible] completed
variable {J A I}
attribute [local irreducible] derivedExtension
attribute [local irreducible] SheafOfModules.monoidalCategory
variable (J A I)
variable {J A I}
attribute [local irreducible] strictLimit
variable (J A I)
attribute [local irreducible] ordinaryUnit
attribute [local irreducible] quotientPresentation
variable {J A I}
variable {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}
variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)
attribute [local semireducible] completed
attribute [local irreducible] completed
variable (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
variable [hL : PreservesFiniteLimits L]
attribute [local irreducible] derivedPull pull change


/-- The canonical ordinary finite pullback comparison, not an arbitrary isomorphism.
Source: Stacks 06YY, 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def ordinaryFinitePull (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    pull F (constantMap F A) ⋙ change (quotient J' A I n) ≅
      change (quotient J A I n) ⋙ pull F (constantMap F (A ⧸ I ^ (n + 1))) :=
  (ordinaryFinitePull_existsUnique F V adj A I n).exists.choose

/-- The representative square for the derived finite-reduction comparison.
The ordinary tensor comparison is lifted with abstract functors before specialization.
Source: Stacks 06YY, 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def FinitePullComparisonFormula
    {M₀ M₁ M₂ M₃ D₀ D₁ D₂ D₃ : Type*}
    [Category M₀] [Category M₁] [Category M₂] [Category M₃]
    [Preadditive M₀] [Preadditive M₁] [Preadditive M₂] [Preadditive M₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    (q₀ : CochainComplex M₀ ℤ ⥤ D₀) (q₁ : CochainComplex M₁ ℤ ⥤ D₁)
    (q₂ : CochainComplex M₂ ℤ ⥤ D₂) (q₃ : CochainComplex M₃ ℤ ⥤ D₃)
    (r : M₀ ⥤ M₁) (s : M₂ ⥤ M₃) (p : M₁ ⥤ M₃) (b : M₀ ⥤ M₂)
    [r.PreservesZeroMorphisms] [s.PreservesZeroMorphisms]
    [p.PreservesZeroMorphisms] [b.PreservesZeroMorphisms]
    {dr : D₀ ⥤ D₁} {ds : D₂ ⥤ D₃} {dp : D₁ ⥤ D₃} {db : D₀ ⥤ D₂}
    (α : q₀ ⋙ dr ⟶ r.mapHomologicalComplex (.up ℤ) ⋙ q₁)
    (β : q₁ ⋙ dp ⟶ p.mapHomologicalComplex (.up ℤ) ⋙ q₃)
    (γ : r ⋙ p ≅ b ⋙ s)
    (δ : q₀ ⋙ db ⟶ b.mapHomologicalComplex (.up ℤ) ⋙ q₂)
    (ε : q₂ ⋙ ds ⟶ s.mapHomologicalComplex (.up ℤ) ⋙ q₃)
    (e : dr ⋙ dp ≅ db ⋙ ds) (P : CochainComplex M₀ ℤ) : Prop :=
  dp.map (α.app P) ≫ β.app ((r.mapHomologicalComplex (.up ℤ)).obj P) ≫
      q₃.map ((NatIso.mapHomologicalComplex γ (.up ℤ)).hom.app P) =
    e.hom.app (q₀.obj P) ≫ ds.map (δ.app P) ≫
      ε.app ((b.mapHomologicalComplex (.up ℤ)).obj P)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem resolving_module_square_iso
    {M₀ M₁ M₂ M₃ D₁ D₂ D₃ : Type*}
    [Category M₀] [Category M₁] [Category M₂] [Category M₃]
    [Abelian M₀] [HasDerivedCategory M₀] [Preadditive M₁] [Preadditive M₂] [Preadditive M₃]
    [Category D₁] [Category D₂] [Category D₃]
    (q₁ : CochainComplex M₁ ℤ ⥤ D₁)
    (q₂ : CochainComplex M₂ ℤ ⥤ D₂) (q₃ : CochainComplex M₃ ℤ ⥤ D₃)
    (r : M₀ ⥤ M₁) (s : M₂ ⥤ M₃) (p : M₁ ⥤ M₃) (b : M₀ ⥤ M₂)
    [r.PreservesZeroMorphisms] [s.PreservesZeroMorphisms]
    [p.PreservesZeroMorphisms] [b.PreservesZeroMorphisms]
    {dr : DerivedCategory M₀ ⥤ D₁} {ds : D₂ ⥤ D₃} {dp : D₁ ⥤ D₃}
    {db : DerivedCategory M₀ ⥤ D₂}
    (α : DerivedCategory.Q ⋙ dr ⟶ r.mapHomologicalComplex (.up ℤ) ⋙ q₁)
    (β : q₁ ⋙ dp ⟶ p.mapHomologicalComplex (.up ℤ) ⋙ q₃)
    (γ : r ⋙ p ≅ b ⋙ s)
    (δ : DerivedCategory.Q ⋙ db ⟶ b.mapHomologicalComplex (.up ℤ) ⋙ q₂)
    (ε : q₂ ⋙ ds ⟶ s.mapHomologicalComplex (.up ℤ) ⋙ q₃)
    (P : CochainComplex M₀ ℤ → Prop)
    (hres : ∀ X : CochainComplex M₀ ℤ,
      ∃ (K : CochainComplex M₀ ℤ) (f : K ⟶ X), P K ∧ QuasiIso f)
    (hα : ∀ X, P X → IsIso (α.app X))
    (hβ : ∀ X, P X → IsIso (β.app ((r.mapHomologicalComplex (.up ℤ)).obj X)))
    (hδ : ∀ X, P X → IsIso (δ.app X))
    (hε : ∀ X, P X → IsIso (ε.app ((b.mapHomologicalComplex (.up ℤ)).obj X))) :
    ∃! e : dr ⋙ dp ≅ db ⋙ ds, ∀ X, P X →
      FinitePullComparisonFormula DerivedCategory.Q q₁ q₂ q₃ r s p b α β γ δ ε e X := by
  exact resolving_square_iso q₁ q₂ q₃
    (r.mapHomologicalComplex (.up ℤ)) (b.mapHomologicalComplex (.up ℤ))
    (p.mapHomologicalComplex (.up ℤ)) (s.mapHomologicalComplex (.up ℤ))
    dr db dp ds α β (NatIso.mapHomologicalComplex γ (.up ℤ)) δ ε
    P hres hα hβ hδ hε

section
attribute [local irreducible] dres

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Derived constant pullback and finite reduction commute by the prescribed ordinary
comparison on every flat-term K-flat representative. Source: Stacks 06YY, 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: ringed pullback and scalar extension preserve K-flat complexes with flat terms.
Consequently the two iterated derived functors are computed on the same representative.
Use ordinaryFinitePull there and descend through their universal computation counits.
The displayed square determines the resulting natural isomorphism uniquely. -/
theorem finitePull_existsUnique (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    ∃! e : (derivedPull F V adj (constantMap F A)).functor ⋙ extend (quotient J' A I n) ≅
        extend (quotient J A I n) ⋙
          (derivedPull F V adj (constantMap F (A ⧸ I ^ (n + 1)))).functor,
      ∀ P : Cx (constant J A), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        FinitePullComparisonFormula (Q (constant J A)) (Q (constant J' A))
          (Q (finite J A I n)) (Q (finite J' A I n))
          (pull F (constantMap F A)) (pull F (constantMap F (A ⧸ I ^ (n + 1))))
          (change (quotient J' A I n)) (change (quotient J A I n))
          (derivedPull F V adj (constantMap F A)).comparison
          (extendComparison (quotient J' A I n)) (ordinaryFinitePull F V adj A I n)
          (extendComparison (quotient J A I n))
          (derivedPull F V adj (constantMap F (A ⧸ I ^ (n + 1)))).comparison e P
        := by
  let := HasDerivedCategory.standard (Mod (constant J A))
  let := HasDerivedCategory.standard (Mod (constant J' A))
  let := HasDerivedCategory.standard (Mod (finite J A I n))
  let := HasDerivedCategory.standard (Mod (finite J' A I n))
  let p := derivedPull F V adj (constantMap F A)
  let f := derivedPull F V adj (constantMap F (A ⧸ I ^ (n + 1)))
  let q := quotient J A I n
  let q' := quotient J' A I n
  let P (X : Cx (constant J A)) :=
    X.IsAcyclicTensorKFlat ∧ ∀ q : ℤ, SheafOfModules.IsFlat (X.X q)
  obtain ⟨e, he, hu⟩ := resolving_module_square_iso
    (Q (constant J' A)) (Q (finite J A I n)) (Q (finite J' A I n))
    (pull F (constantMap F A)) (pull F (constantMap F (A ⧸ I ^ (n + 1))))
    (change q') (change q)
    p.comparison (extendComparison q')
    (ordinaryFinitePull F V adj A I n)
    (extendComparison q) f.comparison P (module_flat_kFlat_resolution (J := J))
    (fun X hX ↦ p.computation X hX.1 hX.2)
    (fun X hX ↦ (derivedExtension q').computation _
      (pull_flat_kFlat F V adj (constantMap F A) X hX.1 hX.2).1)
    (fun X hX ↦ (derivedExtension q).computation X hX.1)
    (fun X hX ↦ by
      have h := change_flat_kFlat q X hX.1 hX.2
      exact f.computation _ h.1 h.2)
  refine ⟨e, ?_, ?_⟩
  · intro X hk hf
    exact he X ⟨hk, hf⟩
  · intro t ht
    apply hu t
    intro X hX
    exact ht X hX.1 hX.2


end

/-- The specified derived finite constant pullback comparison.
Source: Stacks 06YY, 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def finitePull (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    (derivedPull F V adj (constantMap F A)).functor ⋙ extend (quotient J' A I n) ≅
      extend (quotient J A I n) ⋙
        (derivedPull F V adj (constantMap F (A ⧸ I ^ (n + 1)))).functor :=
  (finitePull_existsUnique F V adj A I n).exists.choose


/-- Pointwise application of a module pullback to a strict tower.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def pullTowers (A : Type u) [CommRing A] :
    (ℕᵒᵖ ⥤ Mod (constant J A)) ⥤ (ℕᵒᵖ ⥤ Mod (constant J' A)) :=
  (Functor.whiskeringRight ℕᵒᵖ (Mod (constant J A)) (Mod (constant J' A))).obj
    (pull F (constantMap F A))


variable {C'' : Type u} [SmallCategory C''] {J'' : GrothendieckTopology C''}
variable {L₂ : Sheaf J' (Type u) ⥤ Sheaf J'' (Type u)}
variable (G : InverseImageData L₂) (H : InverseImageData (L ⋙ L₂))
variable (V₂ : Sheaf J'' (Type u) ⥤ Sheaf J' (Type u)) (adj₂ : L₂ ⊣ V₂)
variable [PreservesFiniteLimits L₂]

/-- Tensor insertion fixes the ordinary pullback composition comparison.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def IsPullComposition {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    {T : Sheaf J'' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) (d : G.rings.obj S ⟶ T) (e : H.rings.obj R ⟶ T)
    (a : pull H e ≅ pull F c ⋙ pull G d) : Prop :=
  ∀ M : Mod R, pullInsertion H e M ≫ (underlying T).map (a.hom.app M) =
    L₂.map (pullInsertion F c M) ≫ pullInsertion G d ((pull F c).obj M)

/-- The derived composition comparison is the ordinary tensor comparison on K-flat models.
Source: Stacks 06YY, 0G7E (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def IsDerivedPullComposition {R : Sheaf J CommRingCat.{u}}
    {S : Sheaf J' CommRingCat.{u}} {T : Sheaf J'' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) (d : G.rings.obj S ⟶ T) (e : H.rings.obj R ⟶ T)
    (a : pull H e ≅ pull F c ⋙ pull G d)
    (α : (derivedPull H (V₂ ⋙ V) (adj.comp adj₂) e).functor ≅
      (derivedPull F V adj c).functor ⋙ (derivedPull G V₂ adj₂ d).functor) : Prop :=
  ∀ P : Cx R, P.IsAcyclicTensorKFlat → (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
    α.hom.app ((Q R).obj P) ≫
        (derivedPull G V₂ adj₂ d).functor.map
          ((derivedPull F V adj c).comparison.app P) ≫
        (derivedPull G V₂ adj₂ d).comparison.app
          (((pull F c).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
      (derivedPull H (V₂ ⋙ V) (adj.comp adj₂) e).comparison.app P ≫
        (Q T).map ((NatIso.mapHomologicalComplex a (ComplexShape.up ℤ)).hom.app P)

end CategoryTheory.ConstantCompletion
